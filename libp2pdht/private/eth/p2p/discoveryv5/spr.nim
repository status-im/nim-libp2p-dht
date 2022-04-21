# Copyright (c) 2020-2022 Status Research & Development GmbH
# Licensed and distributed under either of
#   * MIT license (license terms in the root directory or at https://opensource.org/licenses/MIT).
#   * Apache v2 license (license terms in the root directory or at https://www.apache.org/licenses/LICENSE-2.0).
# at your option. This file may not be copied, modified, or distributed except according to those terms.
#
import
  chronicles,
  std/[options, strutils, sugar],
  pkg/stew/[results, byteutils, arrayops],
  stew/endians2,
  stew/shims/net,
  stew/base64,
  libp2p/crypto/crypto,
  libp2p/crypto/secp,
  libp2p/routing_record,
  libp2p/multicodec

export routing_record

from chronos import TransportAddress, initTAddress

export options, results

type
  SprUri* = distinct string

  RecordResult*[T] = Result[T, cstring]

proc seqNum*(r: SignedPeerRecord): uint64 =
    r.data.seqNo

proc fromBytes(r: var SignedPeerRecord, s: openArray[byte]): bool =

  let decoded = SignedPeerRecord.decode(@s)
  if decoded.isErr:
    error "Error decoding SignedPeerRecord", error = decoded.error
    return false

  r = decoded.get
  return true

proc get*(r: SignedPeerRecord, T: type PublicKey): Option[T] =
  ## Get the `PublicKey` from provided `Record`. Return `none` when there is
  ## no `PublicKey` in the record.
  ## PublicKey* = distinct SkPublicKey
  r.envelope.publicKey.some

proc incSeqNo*(
    r: var SignedPeerRecord,
    pk: PrivateKey): RecordResult[void] =

  r.data.seqNo.inc()
  r = ? SignedPeerRecord.init(pk, r.data).mapErr(
        (e: CryptoError) =>
          ("Error initialising SignedPeerRecord with incremented seqNo: " &
          $e).cstring
      )
  ok()


proc update*(r: var SignedPeerRecord, pk: crypto.PrivateKey,
                            ip: Option[ValidIpAddress],
                            tcpPort, udpPort: Option[Port] = none[Port]()):
                            RecordResult[void] =
  ## Update a `SignedPeerRecord` with given ip address, tcp port, udp port and optional
  ## custom k:v pairs.
  ##
  ## In case any of the k:v pairs is updated or added (new), the sequence number
  ## of the `Record` will be incremented and a new signature will be applied.
  ##
  ## Can fail in case of wrong `PrivateKey`, if the size of the resulting record
  ## exceeds `maxSprSize` or if maximum sequence number is reached. The `Record`
  ## will not be altered in these cases.

  # TODO: handle custom field pairs?
  # TODO: We have a mapping issue here because PeerRecord has multiple
  # addresses and the proc signature only allows updating of a single
  # ip/tcpPort/udpPort/extraFields

  let
    sprPubKey = r.get(PublicKey)
    pubKey = pk.getPublicKey
  if sprPubKey.isNone or pubKey.isErr or sprPubKey.get != pubKey.get:
    return err("Public key does not correspond with given private key")

  var
    changed = false
    transProto = IpTransportProtocol.udpProtocol
    transProtoPort: Port

  var updated: MultiAddress

  if r.data.addresses.len == 0:
    changed = true
    if ip.isNone:
      return err "No existing address in SignedPeerRecord with no IP provided"

    if udpPort.isNone and tcpPort.isNone:
      return err "No existing address in SignedPeerRecord with no port provided"

    let ipAddr = try: ValidIpAddress.init(ip.get)
                 except ValueError as e:
                   return err ("Existing address contains invalid address: " & $e.msg).cstring
    if tcpPort.isSome:
      transProto = IpTransportProtocol.tcpProtocol
      transProtoPort = tcpPort.get
    if udpPort.isSome:
      transProto = IpTransportProtocol.udpProtocol
      transProtoPort = udpPort.get

    updated = MultiAddress.init(ipAddr, transProto, transProtoPort)

  else:
    let
      existing = r.data.addresses[0].address
      existingNetProto = ? existing[0].mapErr((e: string) => e.cstring)
      existingTransProto = ? existing[1].mapErr((e: string) => e.cstring)
      existingNetProtoFam = ? existingNetProto.protoCode
                               .mapErr((e: string) => e.cstring)
      existingNetProtoAddr = ? existingNetProto.protoAddress
                               .mapErr((e: string) => e.cstring)
      existingTransProtoCodec = ? existingTransProto.protoCode
                              .mapErr((e: string) => e.cstring)
      existingTransProtoPort = ? existingTransProto.protoAddress
                                 .mapErr((e: string) => e.cstring)
      existingIp =
        if existingNetProtoFam == MultiCodec.codec("ip6"):
          ipv6 array[16, byte].initCopyFrom(existingNetProtoAddr)
        else:
          ipv4 array[4, byte].initCopyFrom(existingNetProtoAddr)

      ipAddr = ip.get(existingIp)


    if tcpPort.isNone and udpPort.isNone:
      transProto =
        if existingTransProtoCodec == MultiCodec.codec("udp"):
            IpTransportProtocol.udpProtocol
        else: IpTransportProtocol.tcpProtocol
      transProtoPort = Port(uint16.fromBytesBE(existingTransProtoPort))

    else:
      if tcpPort.isSome:
        transProto = IpTransportProtocol.tcpProtocol
        transProtoPort = tcpPort.get
      if udpPort.isSome:
        transProto = IpTransportProtocol.udpProtocol
        transProtoPort = udpPort.get

    updated = MultiAddress.init(ipAddr, transProto, transProtoPort)
    changed = existing != updated

  r.data.addresses[0].address = updated

  # increase the sequence number only if we've updated the multiaddress
  if changed: r.data.seqNo.inc()

  r = ? SignedPeerRecord.init(pk, r.data)
          .mapErr((e: CryptoError) =>
            ("Failed to update SignedPeerRecord: " & $e).cstring
          )

  return ok()

proc toTypedRecord*(r: SignedPeerRecord) : RecordResult[SignedPeerRecord] = ok(r)

proc ip*(r: SignedPeerRecord): Option[array[4, byte]] =
    for address in r.data.addresses:
      let ma = address.address
      let code = ma[0].get.protoCode()
      if code.isOk and code.get == multiCodec("ip4"):
        var ipbuf: array[4, byte]
        let res = ma[0].get.protoArgument(ipbuf)
        if res.isOk:
          return some(ipbuf)

#         err("Incorrect IPv4 address")
#       else:
#         if (?(?ma[1]).protoArgument(pbuf)) == 0:
#           err("Incorrect port number")
#         else:
#           res.port = Port(fromBytesBE(uint16, pbuf))
#           ok(res)
#     else:

#   else:
#     err("MultiAddress must be wire address (tcp, udp or unix)")

proc udp*(r: SignedPeerRecord): Option[int] =
    for address in r.data.addresses:
      let ma = address.address

      let code = ma[1].get.protoCode()
      if code.isOk and code.get == multiCodec("udp"):
        var pbuf: array[2, byte]
        let res = ma[1].get.protoArgument(pbuf)
        if res.isOk:
          let p = fromBytesBE(uint16, pbuf)
          return some(p.int)

proc fromBase64*(r: var SignedPeerRecord, s: string): bool =
  ## Loads SPR from base64-encoded protobuf-encoded bytes, and validates the
  ## signature.
  let bytes = Base64Url.decode(s)
  r.fromBytes(bytes)

proc fromURI*(r: var SignedPeerRecord, s: string): bool =
  ## Loads SignedPeerRecord from its text encoding. Validates the signature.
  ## TODO
  const prefix = "spr:"
  if s.startsWith(prefix):
    result = r.fromBase64(s[prefix.len .. ^1])

template fromURI*(r: var SignedPeerRecord, url: SprUri): bool =
  fromURI(r, string(url))

proc toBase64*(r: SignedPeerRecord): string =
  let encoded = r.encode
  if encoded.isErr:
    error "Failed to encode SignedPeerRecord", error = encoded.error
  result = Base64Url.encode(encoded.get(@[]))

proc toURI*(r: SignedPeerRecord): string = "spr:" & r.toBase64

proc init*(T: type SignedPeerRecord, seqNum: uint64,
                           pk: PrivateKey,
                           ip: Option[ValidIpAddress],
                           tcpPort, udpPort: Option[Port]):
                           RecordResult[T] =
  ## Initialize a `SignedPeerRecord` with given sequence number, private key, optional
  ## ip address, tcp port, udp port, and optional custom k:v pairs.
  ##
  ## Can fail in case the record exceeds the `maxSprSize`.

  let peerId = PeerId.init(pk).get

  if tcpPort.isSome() and udpPort.isSome:
    warn "Both tcp and udp ports specified, using udp in multiaddress",
      tcpPort, udpPort

  var
    ipAddr = try: ValidIpAddress.init("127.0.0.1")
             except ValueError as e:
               return err ("Existing address contains invalid address: " & $e.msg).cstring
    proto: IpTransportProtocol
    protoPort: Port

  if ip.isSome():

    ipAddr = ip.get

    if tcpPort.isSome():
      proto = IpTransportProtocol.tcpProtocol
      protoPort = tcpPort.get()
    if udpPort.isSome():
      proto = IpTransportProtocol.udpProtocol
      protoPort = udpPort.get()
  else:
    if tcpPort.isSome():
      proto = IpTransportProtocol.tcpProtocol
      protoPort = tcpPort.get()
    if udpPort.isSome():
      proto = IpTransportProtocol.udpProtocol
      protoPort = udpPort.get()


  let ma = MultiAddress.init(ipAddr, proto, protoPort)

  let pr = PeerRecord.init(peerId, @[ma], seqNum)
  SignedPeerRecord.init(pk, pr).mapErr((e: CryptoError) => ("Failed to init SignedPeerRecord: " & $e).cstring)

proc contains*(r: SignedPeerRecord, fp: (string, seq[byte])): bool =
  # TODO: use FieldPair for this, but that is a bit cumbersome. Perhaps the
  # `get` call can be improved to make this easier.
  # let field = r.tryGet(fp[0], seq[byte])
  # if field.isSome():
  #   if field.get() == fp[1]:
  #     return true
  # TODO: Implement if SignedPeerRecord custom field pairs are implemented
  debugEcho "`contains` is not yet implemented for SignedPeerRecords"
  return false

proc `==`*(a, b: SignedPeerRecord): bool = a.data == b.data
