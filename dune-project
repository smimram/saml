(lang dune 2.0)
(name saml)
(source (github smimram/saml))
(license GPL-3.0)
(authors "Samuel Mimram <smimram@gmail.com>")
(maintainers "Samuel Mimram <smimram@gmail.com>")

(generate_opam_files true)

(package
 (name saml)
 (synopsis "A compiler for sound generators and effects")
 (description "A compiler for sound generators and effects.")
 (depends
   menhir)
)
(using menhir 2.0)
