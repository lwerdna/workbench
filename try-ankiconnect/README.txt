Experiment with AnkiConnect [1]

## Experiment #1: listing decks, listing cards, adding cards

1. Install AnkiConnect (See "Installation" in [1]).
2. browse to localhost:8765 and verify that you see "AnkiConnect v.6"
3. run Anki
4. run `./experiment1.py decks` and see a list of all decks
5. create a deck named "test"
6. run `./experiment1.py addbasic` and see a new card appear in Anki (may have to refresh query "deck:test")
7. run `./experiment1.py cards` and see the card appear in the list of cards for deck "test"

## Experiment #2: markdown content updates cards

Here we'll parse markdown files, adding cards to Anki if they don't exist, and updating them if they do.

Suppose you have some information on dogs (Dogs.md) and cats (Cats.md) and other stuff (Test1.md, Test2.md).

1. If Dogs.md or Cats.md has note id's in them (eg: NID: 1234578), delete those lines
2. run `./experiment2.py`
3. verify the cards from the markdown files are now in the deck "test" and the markdown files have note id's assigned within the code fences
4. change the content of one of the cards in the markdown files and run `./experiment2.py` and verify the Anki deck is updated

## Notes

Most of the basic functionality can be found on the API documentation: [1] but one exception is simply adding cards. There is no "add card", you have to understand notes [2] and use the "addNote" action.

Here's how it works. In Anki, when you add a card, what you're actually doing is adding a note. And each note has a note type, also called a model. The default type is Basic, which has fields "Front" and "Back". Every note has associated card types, which determine how fields from the note are rendered on a flashcard. When you add a note, cards are automatically generated. For example, if you add a note type "Basic", a single card is generated with the value of the note's "Front" field rendered on the front of the card, and the value of the note's "Back" field rendered on the back of the card. If you add a note of type "Basic (front and back)", there are two associated card types, one rendered the value of the note field "Front" to its front, value of note field "Back" to its back (just like note type "Basic"), but the second card type does the opposite: rendered the note's "Front" to its back, and the note's "Back" to its front.

This is important. Usually when you create a note of type Basic, the resulting card will have the same card id as the note id, but not always. So using card id (as previous experiments did) is a trap, because things will mostly work with this simplified, yet false, view.

1. https://foosoft.net/projects/anki-connect/index.html
2. https://docs.ankiweb.net/getting-started.html#notes--fields

