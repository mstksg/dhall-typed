dhall-typed
===========

A statically typed version of the Dhall AST.  This means that

*   It is impossible to create an ill-typed Dhall AST value
*   You can convert any Dhall AST term into a Haskell value representing a
    type you can know statically.
*   You can parse an Dhall expression (or an untyped AST value) into a typed
    Dhall expression with the type you want.

The actual AST is in *Dhall.Typed.Core*, and the conversion functions between
untyped and typed are in *Dhall.Typed*.

Be warned -- the implementation gets extremely deep into type-level Haskell,
and involves things like singletons of GADTs, and singletons of singletons of
GADTs.

Some notes:

*   Only a limited set of term and type constructors are implemented, in order
    to make prototyping faster.  These will all be filled in eventually.
*   Term variables and type variables are supported, but they are all
    represented using De Bruijn indices in separate namespaces.  That is, `3` as
    a type variable represents the third bound *type variable*, even if there
    might be many term variables bound before that one.  We may move to the
    Morte/Dhall style hybrid De Bruijn at some point, but that is not a current
    priority.  Converting from untyped AST normalizes this appropriately.
*   Kind variables are not currently supported.  I don't believe there is any
    technical limitation for this, but I have chosen to omit them for now to
    simplify prototyping.  They may be implemented at some point.
*   Notes are not supported (they are ignored and treated as `()`).  There is
    no technical reason for this limitation; they were omitted to simplify
    prototyping.
*   Embeds are not supported.  In Dhall expressions, embeds arise through
    imports, though users may directly embed values in to any Dhall AST value.
    Dhall expression imports and embeds are inherently "dynamically" typed.
    Embeds could some day be supported, but they would have to be statically
    typed, making them unusable for imports (unless imports are given specific
    type annotations; however, type annotations are removed during
    normalization, so they cannot be a reliable attachment).  Embeds may one
    day be supported, but it is not a particularly high priority at the moment.

Todo
----

### Before completion

*   Implement all term and type constructors.
*   Finish conversion functions between typed and untyped
*   Implement kind variables.  Maybe think of a system to generalize the
    hierarchy instead of making it ad-hoc as it is now.

### Would be nice

*   Add notes and embeds.
*   Use hybrid indices like Morte/Dhall, instead of pure De Bruijn ones.

