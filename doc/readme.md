# hevm Book

The hevm book is built using `mdbook` and `yarn`. Known good versions of both are included in the nix-shell.

## Running the mdBook server

You can then serve the documentation locally by calling the [`serve` command][mdbook-serve]
from the `book` directory:

```sh
mdbook serve
```

Alternatively it can be called from the root of the repository:

```sh
mdbook serve doc
```

[mdbook-serve]: https://rust-lang.github.io/mdBook/cli/serve.html

## Updating syntax highlighting

In order to highlight the Solidity code examples in the book we override mdBook's built-in [highlight.js] with our own.
To update the highlighting code, run the following commands using [yarn]:

```sh
yarn install
yarn build
```

This will build `theme/theme.js` and copy a minified version of the output into `theme/highlight.js`
where it will be picked up by mdbook during build. You should not need to do this unless you want to
modify syntax highlighting in some way.

[highlight.js]: https://highlightjs.org/
[Yarn]: (https://yarnpkg.com/)

