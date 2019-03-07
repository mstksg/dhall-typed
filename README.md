dhall-typed
===========

A statically typed version of the Dhall AST.  This means that

*   It is impossible to create an ill-typed Dhall AST value
*   You can convert any typed Dhall AST term into a Haskell value representing a
    type you can know statically.
*   You can parse an Dhall expression (or an untyped AST value) into a typed
    Dhall expression with the type you want.
*   You can simultaneously typecheck and parse a typed Dhall expression, and
    figure out what you want to do at runtime.

The main POC is in *Dhall.Typed.LC*, and the actual AST itself is in
*Dhall.Typed.Core*.  Conversion between typed and untyped is in *Dhall.Typed*.

Be warned -- the implementation gets extremely deep into type-level Haskell,
and involves things like singletons of GADTs, and singletons of singletons of
GADTs.

The end goal is to have a one-to-one correspondence between untyped dhall AST
values and typed dhall AST values.

Some notes:

*   Only a limited set of term and type constructors are currently implemented,
    in order to make prototyping faster.  These will all be filled in
    eventually.
*   Term, type, and kind variables are supported, but they are all represented
    using De Bruijn indices in separate namespaces.  That is, `3` as a type
    variable represents the third bound *type variable*, even if there might be
    many term and kind variables bound before that one.  We may move to the
    Morte/Dhall style hybrid De Bruijn at some point, but that is not a current
    priority. Converting from untyped AST normalizes this appropriately.
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

Some important differences between this implementation and the standard:

*   "Kind-polymorphic values" (functions from kinds to terms) are not yet
    supported.  I haven't quite figured out the implementation yet.  However,
    all of the other rule pairs (term-term, type-term, type-type, kind-type,
    kind-kind) are implemented.
*   Although we can manipulate type-level functions (and kind-polymorphic
    types), we can't yet create values of those types.  The main difficulty is
    in the implementation of `TNormalize`, which normalizes types.  It could be
    that type families are not expressive enough to implement this.
*   For some reason, Dhall forbids kind-records if any of the fields
    aren't `Kind` (so `Kind -> Kind` fields are not allowed).  This
    implementation allows them, and it would be somewhat complicated to
    special-case this limitation.
*   Let statements cannot bind anything lower-level than their final result.
    This means that things like `let x = 10 in Natural` is disallowed.  If
    your `let` produces a type, then you can't bind terms; if you produce a
    kind, you can't bind types or terms, etc.  In practice this should not be
    too big of a deal because, while this is allowed in Dhall, you can never
    actually *use* such a binding in the result anyway.

Todo
----

### Critical conceptual issues

*   Normalization of type function application, which allows for values of
    such types.  This is pretty important, and comes up a lot in Dhall, so this
    is a pretty critical deficiency.
*   Kind-polymorphic values.  This isn't as big a deal, but it still seems
    important to an extent.

### Currently incomplete, but just a matter of work

*   Uniqueness requirements for union and record fields
*   Fully implement `TNormalize` for type normalization
*   Fully implement `Sub` and `Shift` type families
*   Implement all term and type constructors
    *   `Let`
    *   Record/Union type-level operations (merge, etc.)

### Would be nice

*   Add notes and embeds.
*   Use hybrid indices like Morte/Dhall, instead of pure De Bruijn ones.
*   `let` statements being able to bind values "lower-level" than the final
    result.  This is never technically necessary, but it would be nice to have
    a 1-to-1 correspondence with Dhall terms.
*   Compilation currently takes 37 minutes, so that should probably be
    addressed :)
