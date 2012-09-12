$(document).ready(function()
{
    $("#header").append('<a href="index.html"><img class="logo" width="20%" src="saml.svg"/></a><div class="nav"><ul><li><a href="index.html">Home</a></li><li><a href="https://sourceforge.net/projects/samlsound/" target="_blank">Sourceforge</a></li></ul></div>');

    var year = (new Date).getFullYear();
    $("#footer").append('Copyright 2012&ndash;'+year+' Samuel Mimram');
});