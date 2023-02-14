Generate ANKI deck from markdown with AnkiConnect [1]

Quickstart:

1. Install AnkiConnect (See "Installation" in [1]).
2. run Anki
3. browse to localhost:8765 and verify that you see "AnkiConnect v.6"
4. create a deck named "test"

Now you can run `./sync.py` to send cards in Information.md to the Anki deck named "test". If there are already note ID's assigned in the markdown, first run `./sync.py reset` to clear them.

For experimenting, use `./cli.py` for a command-line interface to manipulate the deck.

## Notes

Most of the basic functionality can be found on the API documentation: [1] but one exception is simply adding cards. There is no "add card", you have to understand notes [2] and use the "addNote" action.

Here's how it works. In Anki, when you add a card, what you're actually doing is adding a note. And each note has a note type, also called a model. The default type is Basic, which has fields "Front" and "Back". Every note has associated card types, which determine how fields from the note are rendered on a flashcard. When you add a note, cards are automatically generated. For example, if you add a note type "Basic", a single card is generated with the value of the note's "Front" field rendered on the front of the card, and the value of the note's "Back" field rendered on the back of the card. If you add a note of type "Basic (front and back)", there are two associated card types, one rendered the value of the note field "Front" to its front, value of note field "Back" to its back (just like note type "Basic"), but the second card type does the opposite: rendered the note's "Front" to its back, and the note's "Back" to its front.

This is important. Usually when you create a note of type Basic, the resulting card will have the same card id as the note id, but not always. So using card id (as previous experiments did) is a trap, because things will mostly work with this simplified, yet false, view.

1. https://foosoft.net/projects/anki-connect/index.html
2. https://docs.ankiweb.net/getting-started.html#notes--fields
3. https://github.com/ankidroid/Anki-Android/wiki/Database-Structure
4. https://github.com/FooSoft/anki-connect/blob/master/plugin/__init__.py
