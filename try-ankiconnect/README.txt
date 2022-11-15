Parse markdown files, adding cards to Anki if they don't exist, and updating them if they do.

Install it (See "Installation" in [1]).
browse to localhost:8765 and see "AnkiConnect v.6"

Most of the basic functionality can be found on the API documentation: [1] but one exception is simply adding cards. There is no "add card", you have to understand notes [2] and use the "addNote" action.

See test.py.

1. https://foosoft.net/projects/anki-connect/index.html
2. https://docs.ankiweb.net/getting-started.html#notes--fields

