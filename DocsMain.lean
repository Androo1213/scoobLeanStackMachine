import VersoManual
import Docs

open Verso.Genre.Manual
open Verso.Output (Html)

def config : Config := {
  extraHead := #[
    Html.text (escape := false)
      "<style>main .content-wrapper > nav.prev-next-buttons:first-child { display: none; }</style>"
  ]
}

def main := manualMain (%doc Docs) (config := config)
