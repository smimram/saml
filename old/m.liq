#!/usr/bin/liquidsoap -v --errors-as-warnings

set("log.file",false)
set("log.level",123)
#set("server.telnet",true)

def mksafe(s)
  fallback(id="mksafe",track_sensitive=false,[s,blank(id="safe_blank")])
end

s = single("test.mid")
s = midi.remove([9],s)
s = mux_audio(audio=blank(),s)
s = synth.all.dssi.saml_synth(s)
#s = synth.all.dssi.nekobee(s)
#s = synth.all.saw(s)
#s = filter(mode="low", freq=2000., s)
#s = echo(ping_pong=true, s)
#s = comb(s)
#s = flanger(s)
#s = nrj(s)
#s = drop_midi(s)
#s = sky(s)
s = drop_midi(s)
s = mksafe(s)
s = audio_to_stereo(s)
s = output.file(%mp3,"m.mp3",s)
output.pulseaudio(s)
