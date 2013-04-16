class pulseaudio_writer client_name stream_name channels rate =
object (self)
  val dev =
    let sample =
      {
        Pulseaudio.
        sample_format = Pulseaudio.Sample_format_float32le;
        sample_rate = rate;
        sample_chans = channels;
      }
    in
    Pulseaudio.Simple.create ~client_name ~dir:Pulseaudio.Dir_playback ~stream_name ~sample ()

  method write buf ofs len =
    Pulseaudio.Simple.write dev buf ofs len

  method close =
    Pulseaudio.Simple.free dev
end

module Array = struct
  include Array

  let play =
    let w = ref None in
    fun ?(samplerate=44100) buf ->
      let w =
        match !w with
        | Some w -> w
        | None ->
          let wr = new pulseaudio_writer "SAML" "sound" 1 samplerate in
          w := Some wr;
          wr
      in
    w#write [|buf|] 0 (Array.length buf)
end
