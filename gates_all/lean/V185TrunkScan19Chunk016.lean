import V185TrunkScan19Chunk015

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental

namespace V185TrunkScan19Incremental

def tailWord_161056 : List Nat := [2, 1, 1, 5, 3, 7]
def baseStart_161056 : Nat := 118140960795 + 161056 * 2 ^ 59
def prefixEnd_161056 : Nat := 4983230072969 + 3 ^ 40 * 161056 * 2
def baseEnd_161056 : Nat := 5445210883333471694441

theorem tailTrace_161056 : CollatzResearch.WordTrace tailWord_161056 prefixEnd_161056 5445210883333471694441 := by
  unfold tailWord_161056
  simp only [CollatzResearch.WordTrace]
  refine ⟨2937097452264546510015511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3916129936352728680020681 2937097452264546510015511)
  ·
    refine ⟨4405646178396819765023267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2937097452264546510015511 4405646178396819765023267)
    ·
      refine ⟨6608469267595229647534901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4405646178396819765023267 6608469267595229647534901)
      ·
        refine ⟨619543993837052779456397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6608469267595229647534901 619543993837052779456397)
        ·
          refine ⟨232328997688894792296149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 619543993837052779456397 232328997688894792296149)
          ·
            refine ⟨5445210883333471694441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 232328997688894792296149 5445210883333471694441)
            ·
              rfl

theorem cell19_161056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 7].length) (baseStart_161056 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_161056 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_161056 prefixEnd_161056 := by exact prefixLift 161056
  have htrace : WordTrace (prefixWord ++ tailWord_161056) baseStart_161056 baseEnd_161056 := by
    simpa [prefixWord, tailWord_161056, baseEnd_161056] using wordTrace_append hprefix tailTrace_161056
  have hstable : (prefixWord ++ tailWord_161056).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161056).length < 2 ^ (prefixWord ++ tailWord_161056).sum := by decide
  have hdescent : baseEnd_161056 < baseStart_161056 := by decide
  rcases family_descends (prefixWord ++ tailWord_161056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161073 : List Nat := [1, 2, 2, 3, 3, 3, 1, 4]
def baseStart_161073 : Nat := 118140960795 + 161073 * 2 ^ 59
def prefixEnd_161073 : Nat := 4983230072969 + 3 ^ 40 * 161073 * 2
def baseEnd_161073 : Nat := 49012070792150242872145

theorem tailTrace_161073 : CollatzResearch.WordTrace tailWord_161073 prefixEnd_161073 49012070792150242872145 := by
  unfold tailWord_161073
  simp only [CollatzResearch.WordTrace]
  refine ⟨5874814945467504923399873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3916543296978336615599915 5874814945467504923399873)
  ·
    refine ⟨4406111209100628692549905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5874814945467504923399873 4406111209100628692549905)
    ·
      refine ⟨3304583406825471519412429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4406111209100628692549905 3304583406825471519412429)
      ·
        refine ⟨1239218777559551819779661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3304583406825471519412429 1239218777559551819779661)
        ·
          refine ⟨464707041584831932417373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1239218777559551819779661 464707041584831932417373)
          ·
            refine ⟨174265140594311974656515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 464707041584831932417373 174265140594311974656515)
            ·
              refine ⟨261397710891467961984773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 174265140594311974656515 261397710891467961984773)
              ·
                refine ⟨49012070792150242872145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 261397710891467961984773 49012070792150242872145)
                ·
                  rfl

theorem cell19_161073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 1, 4].length) (baseStart_161073 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_161073 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_161073 prefixEnd_161073 := by exact prefixLift 161073
  have htrace : WordTrace (prefixWord ++ tailWord_161073) baseStart_161073 baseEnd_161073 := by
    simpa [prefixWord, tailWord_161073, baseEnd_161073] using wordTrace_append hprefix tailTrace_161073
  have hstable : (prefixWord ++ tailWord_161073).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161073).length < 2 ^ (prefixWord ++ tailWord_161073).sum := by decide
  have hdescent : baseEnd_161073 < baseStart_161073 := by decide
  rcases family_descends (prefixWord ++ tailWord_161073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161075 : List Nat := [1, 1, 1, 2, 5, 2, 3, 4]
def baseStart_161075 : Nat := 118140960795 + 161075 * 2 ^ 59
def prefixEnd_161075 : Nat := 4983230072969 + 3 ^ 40 * 161075 * 2
def baseEnd_161075 : Nat := 49012679361814830827695

theorem tailTrace_161075 : CollatzResearch.WordTrace tailWord_161075 prefixEnd_161075 49012679361814830827695 := by
  unfold tailWord_161075
  simp only [CollatzResearch.WordTrace]
  refine ⟨5874887891460259264972679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3916591927640172843315119 5874887891460259264972679)
  ·
    refine ⟨8812331837190388897459019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5874887891460259264972679 8812331837190388897459019)
    ·
      refine ⟨13218497755785583346188529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8812331837190388897459019 13218497755785583346188529)
      ·
        refine ⟨9913873316839187509641397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13218497755785583346188529 9913873316839187509641397)
        ·
          refine ⟨929425623453673829028881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9913873316839187509641397 929425623453673829028881)
          ·
            refine ⟨697069217590255371771661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 929425623453673829028881 697069217590255371771661)
            ·
              refine ⟨261400956596345764414373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 697069217590255371771661 261400956596345764414373)
              ·
                refine ⟨49012679361814830827695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 261400956596345764414373 49012679361814830827695)
                ·
                  rfl

theorem cell19_161075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 3, 4].length) (baseStart_161075 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_161075 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_161075 prefixEnd_161075 := by exact prefixLift 161075
  have htrace : WordTrace (prefixWord ++ tailWord_161075) baseStart_161075 baseEnd_161075 := by
    simpa [prefixWord, tailWord_161075, baseEnd_161075] using wordTrace_append hprefix tailTrace_161075
  have hstable : (prefixWord ++ tailWord_161075).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161075).length < 2 ^ (prefixWord ++ tailWord_161075).sum := by decide
  have hdescent : baseEnd_161075 < baseStart_161075 := by decide
  rcases family_descends (prefixWord ++ tailWord_161075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161166 : List Nat := [4, 1, 1, 4, 3, 1, 5]
def baseStart_161166 : Nat := 118140960795 + 161166 * 2 ^ 59
def prefixEnd_161166 : Nat := 4983230072969 + 3 ^ 40 * 161166 * 2
def baseEnd_161166 : Nat := 16346789760517860935075

theorem tailTrace_161166 : CollatzResearch.WordTrace tailWord_161166 prefixEnd_161166 16346789760517860935075 := by
  unfold tailWord_161166
  simp only [CollatzResearch.WordTrace]
  refine ⟨734775866766322725816919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3918804622753721204356901 734775866766322725816919)
  ·
    refine ⟨1102163800149484088725379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 734775866766322725816919 1102163800149484088725379)
    ·
      refine ⟨1653245700224226133088069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1102163800149484088725379 1653245700224226133088069)
      ·
        refine ⟨309983568792042399954013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1653245700224226133088069 309983568792042399954013)
        ·
          refine ⟨116243838297015899982755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 309983568792042399954013 116243838297015899982755)
          ·
            refine ⟨174365757445523849974133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116243838297015899982755 174365757445523849974133)
            ·
              refine ⟨16346789760517860935075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 174365757445523849974133 16346789760517860935075)
              ·
                rfl

theorem cell19_161166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 5].length) (baseStart_161166 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_161166 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_161166 prefixEnd_161166 := by exact prefixLift 161166
  have htrace : WordTrace (prefixWord ++ tailWord_161166) baseStart_161166 baseEnd_161166 := by
    simpa [prefixWord, tailWord_161166, baseEnd_161166] using wordTrace_append hprefix tailTrace_161166
  have hstable : (prefixWord ++ tailWord_161166).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161166).length < 2 ^ (prefixWord ++ tailWord_161166).sum := by decide
  have hdescent : baseEnd_161166 < baseStart_161166 := by decide
  rcases family_descends (prefixWord ++ tailWord_161166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161248 : List Nat := [2, 1, 1, 3, 1, 1, 2, 8]
def baseStart_161248 : Nat := 118140960795 + 161248 * 2 ^ 59
def prefixEnd_161248 : Nat := 4983230072969 + 3 ^ 40 * 161248 * 2
def baseEnd_161248 : Nat := 49065320637801688982779

theorem tailTrace_161248 : CollatzResearch.WordTrace tailWord_161248 prefixEnd_161248 49065320637801688982779 := by
  unfold tailWord_161248
  simp only [CollatzResearch.WordTrace]
  refine ⟨2940598859916754905510199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3920798479889006540680265 2940598859916754905510199)
  ·
    refine ⟨4410898289875132358265299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2940598859916754905510199 4410898289875132358265299)
    ·
      refine ⟨6616347434812698537397949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4410898289875132358265299 6616347434812698537397949)
      ·
        refine ⟨2481130288054761951524231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6616347434812698537397949 2481130288054761951524231)
        ·
          refine ⟨3721695432082142927286347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2481130288054761951524231 3721695432082142927286347)
          ·
            refine ⟨5582543148123214390929521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3721695432082142927286347 5582543148123214390929521)
            ·
              refine ⟨4186907361092410793197141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5582543148123214390929521 4186907361092410793197141)
              ·
                refine ⟨49065320637801688982779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4186907361092410793197141 49065320637801688982779)
                ·
                  rfl

theorem cell19_161248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 8].length) (baseStart_161248 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_161248 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_161248 prefixEnd_161248 := by exact prefixLift 161248
  have htrace : WordTrace (prefixWord ++ tailWord_161248) baseStart_161248 baseEnd_161248 := by
    simpa [prefixWord, tailWord_161248, baseEnd_161248] using wordTrace_append hprefix tailTrace_161248
  have hstable : (prefixWord ++ tailWord_161248).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161248).length < 2 ^ (prefixWord ++ tailWord_161248).sum := by decide
  have hdescent : baseEnd_161248 < baseStart_161248 := by decide
  rcases family_descends (prefixWord ++ tailWord_161248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161261 : List Nat := [1, 5, 1, 3, 2, 1, 3, 3]
def baseStart_161261 : Nat := 118140960795 + 161261 * 2 ^ 59
def prefixEnd_161261 : Nat := 4983230072969 + 3 ^ 40 * 161261 * 2
def baseEnd_161261 : Nat := 49069276340621510693855

theorem tailTrace_161261 : CollatzResearch.WordTrace tailWord_161261 prefixEnd_161261 49069276340621510693855 := by
  unfold tailWord_161261
  simp only [CollatzResearch.WordTrace]
  refine ⟨5881671868786413031243637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3921114579190942020829091 5881671868786413031243637)
  ·
    refine ⟨551406737698726221679091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5881671868786413031243637 551406737698726221679091)
    ·
      refine ⟨827110106548089332518637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 551406737698726221679091 827110106548089332518637)
      ·
        refine ⟨310166289955533499694489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 827110106548089332518637 310166289955533499694489)
        ·
          refine ⟨232624717466650124770867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 310166289955533499694489 232624717466650124770867)
          ·
            refine ⟨348937076199975187156301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 232624717466650124770867 348937076199975187156301)
            ·
              refine ⟨130851403574990695183613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 348937076199975187156301 130851403574990695183613)
              ·
                refine ⟨49069276340621510693855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 130851403574990695183613 49069276340621510693855)
                ·
                  rfl

theorem cell19_161261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 3, 3].length) (baseStart_161261 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_161261 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_161261 prefixEnd_161261 := by exact prefixLift 161261
  have htrace : WordTrace (prefixWord ++ tailWord_161261) baseStart_161261 baseEnd_161261 := by
    simpa [prefixWord, tailWord_161261, baseEnd_161261] using wordTrace_append hprefix tailTrace_161261
  have hstable : (prefixWord ++ tailWord_161261).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161261).length < 2 ^ (prefixWord ++ tailWord_161261).sum := by decide
  have hdescent : baseEnd_161261 < baseStart_161261 := by decide
  rcases family_descends (prefixWord ++ tailWord_161261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161282 : List Nat := [3, 4, 1, 2, 1, 2, 6]
def baseStart_161282 : Nat := 118140960795 + 161282 * 2 ^ 59
def prefixEnd_161282 : Nat := 4983230072969 + 3 ^ 40 * 161282 * 2
def baseEnd_161282 : Nat := 16358555440699894742377

theorem tailTrace_161282 : CollatzResearch.WordTrace tailWord_161282 prefixEnd_161282 16358555440699894742377 := by
  unfold tailWord_161282
  simp only [CollatzResearch.WordTrace]
  refine ⟨1470609450427583404439525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3921625201140222411838733 1470609450427583404439525)
  ·
    refine ⟨275739271955171888332411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1470609450427583404439525 275739271955171888332411)
    ·
      refine ⟨413608907932757832498617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 275739271955171888332411 413608907932757832498617)
      ·
        refine ⟨310206680949568374373963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 413608907932757832498617 310206680949568374373963)
        ·
          refine ⟨465310021424352561560945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 310206680949568374373963 465310021424352561560945)
          ·
            refine ⟨348982516068264421170709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 465310021424352561560945 348982516068264421170709)
            ·
              refine ⟨16358555440699894742377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 348982516068264421170709 16358555440699894742377)
              ·
                rfl

theorem cell19_161282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 6].length) (baseStart_161282 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_161282 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_161282 prefixEnd_161282 := by exact prefixLift 161282
  have htrace : WordTrace (prefixWord ++ tailWord_161282) baseStart_161282 baseEnd_161282 := by
    simpa [prefixWord, tailWord_161282, baseEnd_161282] using wordTrace_append hprefix tailTrace_161282
  have hstable : (prefixWord ++ tailWord_161282).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161282).length < 2 ^ (prefixWord ++ tailWord_161282).sum := by decide
  have hdescent : baseEnd_161282 < baseStart_161282 := by decide
  rcases family_descends (prefixWord ++ tailWord_161282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161320 : List Nat := [2, 1, 5, 2, 2, 1, 1, 5]
def baseStart_161320 : Nat := 118140960795 + 161320 * 2 ^ 59
def prefixEnd_161320 : Nat := 4983230072969 + 3 ^ 40 * 161320 * 2
def baseEnd_161320 : Nat := 49087229145726855382583

theorem tailTrace_161320 : CollatzResearch.WordTrace tailWord_161320 prefixEnd_161320 49087229145726855382583 := by
  unfold tailWord_161320
  simp only [CollatzResearch.WordTrace]
  refine ⟨2941911887786333053820707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3922549183715110738427609 2941911887786333053820707)
  ·
    refine ⟨4412867831679499580731061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2941911887786333053820707 4412867831679499580731061)
    ·
      refine ⟨413706359219953085693537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4412867831679499580731061 413706359219953085693537)
      ·
        refine ⟨310279769414964814270153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 413706359219953085693537 310279769414964814270153)
        ·
          refine ⟨232709827061223610702615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 310279769414964814270153 232709827061223610702615)
          ·
            refine ⟨349064740591835416053923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 232709827061223610702615 349064740591835416053923)
            ·
              refine ⟨523597110887753124080885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 349064740591835416053923 523597110887753124080885)
              ·
                refine ⟨49087229145726855382583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 523597110887753124080885 49087229145726855382583)
                ·
                  rfl

theorem cell19_161320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 5].length) (baseStart_161320 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_161320 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_161320 prefixEnd_161320 := by exact prefixLift 161320
  have htrace : WordTrace (prefixWord ++ tailWord_161320) baseStart_161320 baseEnd_161320 := by
    simpa [prefixWord, tailWord_161320, baseEnd_161320] using wordTrace_append hprefix tailTrace_161320
  have hstable : (prefixWord ++ tailWord_161320).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161320).length < 2 ^ (prefixWord ++ tailWord_161320).sum := by decide
  have hdescent : baseEnd_161320 < baseStart_161320 := by decide
  rcases family_descends (prefixWord ++ tailWord_161320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161322 : List Nat := [3, 1, 4, 1, 1, 1, 3, 5]
def baseStart_161322 : Nat := 118140960795 + 161322 * 2 ^ 59
def prefixEnd_161322 : Nat := 4983230072969 + 3 ^ 40 * 161322 * 2
def baseEnd_161322 : Nat := 49087837715391443338133

theorem tailTrace_161322 : CollatzResearch.WordTrace tailWord_161322 prefixEnd_161322 49087837715391443338133 := by
  unfold tailWord_161322
  simp only [CollatzResearch.WordTrace]
  refine ⟨1470974180391355112303555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3922597814376946966142813 1470974180391355112303555)
  ·
    refine ⟨2206461270587032668455333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1470974180391355112303555 2206461270587032668455333)
    ·
      refine ⟨413711488235068625335375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2206461270587032668455333 413711488235068625335375)
      ·
        refine ⟨620567232352602938003063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 413711488235068625335375 620567232352602938003063)
        ·
          refine ⟨930850848528904407004595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 620567232352602938003063 930850848528904407004595)
          ·
            refine ⟨1396276272793356610506893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 930850848528904407004595 1396276272793356610506893)
            ·
              refine ⟨523603602297508728940085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1396276272793356610506893 523603602297508728940085)
              ·
                refine ⟨49087837715391443338133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 523603602297508728940085 49087837715391443338133)
                ·
                  rfl

theorem cell19_161322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 5].length) (baseStart_161322 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_161322 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_161322 prefixEnd_161322 := by exact prefixLift 161322
  have htrace : WordTrace (prefixWord ++ tailWord_161322) baseStart_161322 baseEnd_161322 := by
    simpa [prefixWord, tailWord_161322, baseEnd_161322] using wordTrace_append hprefix tailTrace_161322
  have hstable : (prefixWord ++ tailWord_161322).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161322).length < 2 ^ (prefixWord ++ tailWord_161322).sum := by decide
  have hdescent : baseEnd_161322 < baseStart_161322 := by decide
  rcases family_descends (prefixWord ++ tailWord_161322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161343 : List Nat := [1, 1, 2, 2, 3, 3, 7]
def baseStart_161343 : Nat := 118140960795 + 161343 * 2 ^ 59
def prefixEnd_161343 : Nat := 4983230072969 + 3 ^ 40 * 161343 * 2
def baseEnd_161343 : Nat := 16364742565623205623803

theorem tailTrace_161343 : CollatzResearch.WordTrace tailWord_161343 prefixEnd_161343 16364742565623205623803 := by
  unfold tailWord_161343
  simp only [CollatzResearch.WordTrace]
  refine ⟨5884662654489341035728683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3923108436326227357152455 5884662654489341035728683)
  ·
    refine ⟨8826993981734011553593025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5884662654489341035728683 8826993981734011553593025)
    ·
      refine ⟨6620245486300508665194769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8826993981734011553593025 6620245486300508665194769)
      ·
        refine ⟨4965184114725381498896077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6620245486300508665194769 4965184114725381498896077)
        ·
          refine ⟨1861944043022018062086029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4965184114725381498896077 1861944043022018062086029)
          ·
            refine ⟨698229016133256773282261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1861944043022018062086029 698229016133256773282261)
            ·
              refine ⟨16364742565623205623803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 698229016133256773282261 16364742565623205623803)
              ·
                rfl

theorem cell19_161343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 7].length) (baseStart_161343 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_161343 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_161343 prefixEnd_161343 := by exact prefixLift 161343
  have htrace : WordTrace (prefixWord ++ tailWord_161343) baseStart_161343 baseEnd_161343 := by
    simpa [prefixWord, tailWord_161343, baseEnd_161343] using wordTrace_append hprefix tailTrace_161343
  have hstable : (prefixWord ++ tailWord_161343).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161343).length < 2 ^ (prefixWord ++ tailWord_161343).sum := by decide
  have hdescent : baseEnd_161343 < baseStart_161343 := by decide
  rcases family_descends (prefixWord ++ tailWord_161343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161398 : List Nat := [5, 1, 1, 2, 2, 8]
def baseStart_161398 : Nat := 118140960795 + 161398 * 2 ^ 59
def prefixEnd_161398 : Nat := 4983230072969 + 3 ^ 40 * 161398 * 2
def baseEnd_161398 : Nat := 5456773706960642849893

theorem tailTrace_161398 : CollatzResearch.WordTrace tailWord_161398 prefixEnd_161398 5456773706960642849893 := by
  unfold tailWord_161398
  simp only [CollatzResearch.WordTrace]
  refine ⟨367916791830630339311303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3924445779526723619320565 367916791830630339311303)
  ·
    refine ⟨551875187745945508966955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 367916791830630339311303 551875187745945508966955)
    ·
      refine ⟨827812781618918263450433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 551875187745945508966955 827812781618918263450433)
      ·
        refine ⟨620859586214188697587825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 827812781618918263450433 620859586214188697587825)
        ·
          refine ⟨465644689660641523190869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 620859586214188697587825 465644689660641523190869)
          ·
            refine ⟨5456773706960642849893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 465644689660641523190869 5456773706960642849893)
            ·
              rfl

theorem cell19_161398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 8].length) (baseStart_161398 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_161398 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_161398 prefixEnd_161398 := by exact prefixLift 161398
  have htrace : WordTrace (prefixWord ++ tailWord_161398) baseStart_161398 baseEnd_161398 := by
    simpa [prefixWord, tailWord_161398, baseEnd_161398] using wordTrace_append hprefix tailTrace_161398
  have hstable : (prefixWord ++ tailWord_161398).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161398).length < 2 ^ (prefixWord ++ tailWord_161398).sum := by decide
  have hdescent : baseEnd_161398 < baseStart_161398 := by decide
  rcases family_descends (prefixWord ++ tailWord_161398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161495 : List Nat := [1, 1, 3, 2, 1, 3, 3, 5]
def baseStart_161495 : Nat := 118140960795 + 161495 * 2 ^ 59
def prefixEnd_161495 : Nat := 4983230072969 + 3 ^ 40 * 161495 * 2
def baseEnd_161495 : Nat := 49140478991378301493217

theorem tailTrace_161495 : CollatzResearch.WordTrace tailWord_161495 prefixEnd_161495 49140478991378301493217 := by
  unfold tailWord_161495
  simp only [CollatzResearch.WordTrace]
  refine ⟨5890206549938670995261939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3926804366625780663507959 5890206549938670995261939)
  ·
    refine ⟨8835309824908006492892909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5890206549938670995261939 8835309824908006492892909)
    ·
      refine ⟨3313241184340502434834841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8835309824908006492892909 3313241184340502434834841)
      ·
        refine ⟨2484930888255376826126131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3313241184340502434834841 2484930888255376826126131)
        ·
          refine ⟨3727396332383065239189197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2484930888255376826126131 3727396332383065239189197)
          ·
            refine ⟨1397773624643649464695949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3727396332383065239189197 1397773624643649464695949)
            ·
              refine ⟨524165109241368549260981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1397773624643649464695949 524165109241368549260981)
              ·
                refine ⟨49140478991378301493217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 524165109241368549260981 49140478991378301493217)
                ·
                  rfl

theorem cell19_161495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 5].length) (baseStart_161495 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_161495 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_161495 prefixEnd_161495 := by exact prefixLift 161495
  have htrace : WordTrace (prefixWord ++ tailWord_161495) baseStart_161495 baseEnd_161495 := by
    simpa [prefixWord, tailWord_161495, baseEnd_161495] using wordTrace_append hprefix tailTrace_161495
  have hstable : (prefixWord ++ tailWord_161495).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161495).length < 2 ^ (prefixWord ++ tailWord_161495).sum := by decide
  have hdescent : baseEnd_161495 < baseStart_161495 := by decide
  rcases family_descends (prefixWord ++ tailWord_161495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161512 : List Nat := [2, 1, 4, 1, 3, 3, 5]
def baseStart_161512 : Nat := 118140960795 + 161512 * 2 ^ 59
def prefixEnd_161512 : Nat := 4983230072969 + 3 ^ 40 * 161512 * 2
def baseEnd_161512 : Nat := 16381883944509099705131

theorem tailTrace_161512 : CollatzResearch.WordTrace tailWord_161512 prefixEnd_161512 16381883944509099705131 := by
  unfold tailWord_161512
  simp only [CollatzResearch.WordTrace]
  refine ⟨2945413295438541449315395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3927217727251388599087193 2945413295438541449315395)
  ·
    refine ⟨4418119943157812173973093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2945413295438541449315395 4418119943157812173973093)
    ·
      refine ⟨828397489342089782619955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4418119943157812173973093 828397489342089782619955)
      ·
        refine ⟨1242596234013134673929933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 828397489342089782619955 1242596234013134673929933)
        ·
          refine ⟨465973587754925502723725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1242596234013134673929933 465973587754925502723725)
          ·
            refine ⟨174740095408097063521397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 465973587754925502723725 174740095408097063521397)
            ·
              refine ⟨16381883944509099705131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 174740095408097063521397 16381883944509099705131)
              ·
                rfl

theorem cell19_161512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 5].length) (baseStart_161512 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_161512 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_161512 prefixEnd_161512 := by exact prefixLift 161512
  have htrace : WordTrace (prefixWord ++ tailWord_161512) baseStart_161512 baseEnd_161512 := by
    simpa [prefixWord, tailWord_161512, baseEnd_161512] using wordTrace_append hprefix tailTrace_161512
  have hstable : (prefixWord ++ tailWord_161512).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161512).length < 2 ^ (prefixWord ++ tailWord_161512).sum := by decide
  have hdescent : baseEnd_161512 < baseStart_161512 := by decide
  rcases family_descends (prefixWord ++ tailWord_161512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161514 : List Nat := [3, 1, 3, 1, 1, 1, 9]
def baseStart_161514 : Nat := 118140960795 + 161514 * 2 ^ 59
def prefixEnd_161514 : Nat := 4983230072969 + 3 ^ 40 * 161514 * 2
def baseEnd_161514 : Nat := 16382086801063962356981

theorem tailTrace_161514 : CollatzResearch.WordTrace tailWord_161514 prefixEnd_161514 16382086801063962356981 := by
  unfold tailWord_161514
  simp only [CollatzResearch.WordTrace]
  refine ⟨1472724884217459310050899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3927266357913224826802397 1472724884217459310050899)
  ·
    refine ⟨2209087326326188965076349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1472724884217459310050899 2209087326326188965076349)
    ·
      refine ⟨828407747372320861903631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2209087326326188965076349 828407747372320861903631)
      ·
        refine ⟨1242611621058481292855447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 828407747372320861903631 1242611621058481292855447)
        ·
          refine ⟨1863917431587721939283171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1242611621058481292855447 1863917431587721939283171)
          ·
            refine ⟨2795876147381582908924757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1863917431587721939283171 2795876147381582908924757)
            ·
              refine ⟨16382086801063962356981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2795876147381582908924757 16382086801063962356981)
              ·
                rfl

theorem cell19_161514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 9].length) (baseStart_161514 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_161514 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_161514 prefixEnd_161514 := by exact prefixLift 161514
  have htrace : WordTrace (prefixWord ++ tailWord_161514) baseStart_161514 baseEnd_161514 := by
    simpa [prefixWord, tailWord_161514, baseEnd_161514] using wordTrace_append hprefix tailTrace_161514
  have hstable : (prefixWord ++ tailWord_161514).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161514).length < 2 ^ (prefixWord ++ tailWord_161514).sum := by decide
  have hdescent : baseEnd_161514 < baseStart_161514 := by decide
  rcases family_descends (prefixWord ++ tailWord_161514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161662 : List Nat := [4, 2, 3, 1, 1, 2, 1, 5]
def baseStart_161662 : Nat := 118140960795 + 161662 * 2 ^ 59
def prefixEnd_161662 : Nat := 4983230072969 + 3 ^ 40 * 161662 * 2
def baseEnd_161662 : Nat := 49191294558371395781651

theorem tailTrace_161662 : CollatzResearch.WordTrace tailWord_161662 prefixEnd_161662 49191294558371395781651 := by
  unfold tailWord_161662
  simp only [CollatzResearch.WordTrace]
  refine ⟨737037192541707314573905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3930865026889105677727493 737037192541707314573905)
  ·
    refine ⟨552777894406280485930429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 737037192541707314573905 552777894406280485930429)
    ·
      refine ⟨207291710402355182223911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 552777894406280485930429 207291710402355182223911)
      ·
        refine ⟨310937565603532773335867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 207291710402355182223911 310937565603532773335867)
        ·
          refine ⟨466406348405299160003801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 310937565603532773335867 466406348405299160003801)
          ·
            refine ⟨349804761303974370002851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 466406348405299160003801 349804761303974370002851)
            ·
              refine ⟨524707141955961555004277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 349804761303974370002851 524707141955961555004277)
              ·
                refine ⟨49191294558371395781651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 524707141955961555004277 49191294558371395781651)
                ·
                  rfl

theorem cell19_161662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 5].length) (baseStart_161662 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_161662 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_161662 prefixEnd_161662 := by exact prefixLift 161662
  have htrace : WordTrace (prefixWord ++ tailWord_161662) baseStart_161662 baseEnd_161662 := by
    simpa [prefixWord, tailWord_161662, baseEnd_161662] using wordTrace_append hprefix tailTrace_161662
  have hstable : (prefixWord ++ tailWord_161662).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161662).length < 2 ^ (prefixWord ++ tailWord_161662).sum := by decide
  have hdescent : baseEnd_161662 < baseStart_161662 := by decide
  rcases family_descends (prefixWord ++ tailWord_161662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161757 : List Nat := [1, 4, 3, 1, 3, 2, 1, 4]
def baseStart_161757 : Nat := 118140960795 + 161757 * 2 ^ 59
def prefixEnd_161757 : Nat := 4983230072969 + 3 ^ 40 * 161757 * 2
def baseEnd_161757 : Nat := 49220201617439323670281

theorem tailTrace_161757 : CollatzResearch.WordTrace tailWord_161757 prefixEnd_161757 49220201617439323670281 := by
  unfold tailWord_161757
  simp only [CollatzResearch.WordTrace]
  refine ⟨5899762474989489741299525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3933174983326326494199683 5899762474989489741299525)
  ·
    refine ⟨1106205464060529326493661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5899762474989489741299525 1106205464060529326493661)
    ·
      refine ⟨414827049022698497435123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1106205464060529326493661 414827049022698497435123)
      ·
        refine ⟨622240573534047746152685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 414827049022698497435123 622240573534047746152685)
        ·
          refine ⟨233340215075267904807257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 622240573534047746152685 233340215075267904807257)
          ·
            refine ⟨175005161306450928605443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 233340215075267904807257 175005161306450928605443)
            ·
              refine ⟨262507741959676392908165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 175005161306450928605443 262507741959676392908165)
              ·
                refine ⟨49220201617439323670281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 262507741959676392908165 49220201617439323670281)
                ·
                  rfl

theorem cell19_161757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 1, 4].length) (baseStart_161757 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_161757 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_161757 prefixEnd_161757 := by exact prefixLift 161757
  have htrace : WordTrace (prefixWord ++ tailWord_161757) baseStart_161757 baseEnd_161757 := by
    simpa [prefixWord, tailWord_161757, baseEnd_161757] using wordTrace_append hprefix tailTrace_161757
  have hstable : (prefixWord ++ tailWord_161757).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161757).length < 2 ^ (prefixWord ++ tailWord_161757).sum := by decide
  have hdescent : baseEnd_161757 < baseStart_161757 := by decide
  rcases family_descends (prefixWord ++ tailWord_161757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161759 : List Nat := [1, 1, 2, 3, 4, 3, 1, 4]
def baseStart_161759 : Nat := 118140960795 + 161759 * 2 ^ 59
def prefixEnd_161759 : Nat := 4983230072969 + 3 ^ 40 * 161759 * 2
def baseEnd_161759 : Nat := 49220810187103911625831

theorem tailTrace_161759 : CollatzResearch.WordTrace tailWord_161759 prefixEnd_161759 49220810187103911625831 := by
  unfold tailWord_161759
  simp only [CollatzResearch.WordTrace]
  refine ⟨5899835420982244082872331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3933223613988162721914887 5899835420982244082872331)
  ·
    refine ⟨8849753131473366124308497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5899835420982244082872331 8849753131473366124308497)
    ·
      refine ⟨6637314848605024593231373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8849753131473366124308497 6637314848605024593231373)
      ·
        refine ⟨2488993068226884222461765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6637314848605024593231373 2488993068226884222461765)
        ·
          refine ⟨466686200292540791711581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2488993068226884222461765 466686200292540791711581)
          ·
            refine ⟨175007325109702796891843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 466686200292540791711581 175007325109702796891843)
            ·
              refine ⟨262510987664554195337765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 175007325109702796891843 262510987664554195337765)
              ·
                refine ⟨49220810187103911625831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 262510987664554195337765 49220810187103911625831)
                ·
                  rfl

theorem cell19_161759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 1, 4].length) (baseStart_161759 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_161759 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_161759 prefixEnd_161759 := by exact prefixLift 161759
  have htrace : WordTrace (prefixWord ++ tailWord_161759) baseStart_161759 baseEnd_161759 := by
    simpa [prefixWord, tailWord_161759, baseEnd_161759] using wordTrace_append hprefix tailTrace_161759
  have hstable : (prefixWord ++ tailWord_161759).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161759).length < 2 ^ (prefixWord ++ tailWord_161759).sum := by decide
  have hdescent : baseEnd_161759 < baseStart_161759 := by decide
  rcases family_descends (prefixWord ++ tailWord_161759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161761 : List Nat := [1, 2, 3, 1, 2, 1, 5, 4]
def baseStart_161761 : Nat := 118140960795 + 161761 * 2 ^ 59
def prefixEnd_161761 : Nat := 4983230072969 + 3 ^ 40 * 161761 * 2
def baseEnd_161761 : Nat := 49221418756768499581381

theorem tailTrace_161761 : CollatzResearch.WordTrace tailWord_161761 prefixEnd_161761 49221418756768499581381 := by
  unfold tailWord_161761
  simp only [CollatzResearch.WordTrace]
  refine ⟨5899908366974998424445137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3933272244649998949630091 5899908366974998424445137)
  ·
    refine ⟨4424931275231248818333853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5899908366974998424445137 4424931275231248818333853)
    ·
      refine ⟨1659349228211718306875195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4424931275231248818333853 1659349228211718306875195)
      ·
        refine ⟨2489023842317577460312793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1659349228211718306875195 2489023842317577460312793)
        ·
          refine ⟨1866767881738183095234595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2489023842317577460312793 1866767881738183095234595)
          ·
            refine ⟨2800151822607274642851893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1866767881738183095234595 2800151822607274642851893)
            ·
              refine ⟨262514233369431997767365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2800151822607274642851893 262514233369431997767365)
              ·
                refine ⟨49221418756768499581381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 262514233369431997767365 49221418756768499581381)
                ·
                  rfl

theorem cell19_161761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 5, 4].length) (baseStart_161761 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_161761 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_161761 prefixEnd_161761 := by exact prefixLift 161761
  have htrace : WordTrace (prefixWord ++ tailWord_161761) baseStart_161761 baseEnd_161761 := by
    simpa [prefixWord, tailWord_161761, baseEnd_161761] using wordTrace_append hprefix tailTrace_161761
  have hstable : (prefixWord ++ tailWord_161761).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161761).length < 2 ^ (prefixWord ++ tailWord_161761).sum := by decide
  have hdescent : baseEnd_161761 < baseStart_161761 := by decide
  rcases family_descends (prefixWord ++ tailWord_161761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161799 : List Nat := [1, 1, 4, 3, 1, 3, 6]
def baseStart_161799 : Nat := 118140960795 + 161799 * 2 ^ 59
def prefixEnd_161799 : Nat := 4983230072969 + 3 ^ 40 * 161799 * 2
def baseEnd_161799 : Nat := 16410993860131890245611

theorem tailTrace_161799 : CollatzResearch.WordTrace tailWord_161799 prefixEnd_161799 16410993860131890245611 := by
  unfold tailWord_161799
  simp only [CollatzResearch.WordTrace]
  refine ⟨5901294340837330914328451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3934196227224887276218967 5901294340837330914328451)
  ·
    refine ⟨8851941511255996371492677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5901294340837330914328451 8851941511255996371492677)
    ·
      refine ⟨1659739033360499319654877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8851941511255996371492677 1659739033360499319654877)
      ·
        refine ⟨622402137510187244870579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1659739033360499319654877 622402137510187244870579)
        ·
          refine ⟨933603206265280867305869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 622402137510187244870579 933603206265280867305869)
          ·
            refine ⟨350101202349480325239701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 933603206265280867305869 350101202349480325239701)
            ·
              refine ⟨16410993860131890245611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 350101202349480325239701 16410993860131890245611)
              ·
                rfl

theorem cell19_161799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 6].length) (baseStart_161799 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_161799 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_161799 prefixEnd_161799 := by exact prefixLift 161799
  have htrace : WordTrace (prefixWord ++ tailWord_161799) baseStart_161799 baseEnd_161799 := by
    simpa [prefixWord, tailWord_161799, baseEnd_161799] using wordTrace_append hprefix tailTrace_161799
  have hstable : (prefixWord ++ tailWord_161799).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161799).length < 2 ^ (prefixWord ++ tailWord_161799).sum := by decide
  have hdescent : baseEnd_161799 < baseStart_161799 := by decide
  rcases family_descends (prefixWord ++ tailWord_161799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161831 : List Nat := [1, 1, 7, 1, 2, 2, 2, 3]
def baseStart_161831 : Nat := 118140960795 + 161831 * 2 ^ 59
def prefixEnd_161831 : Nat := 4983230072969 + 3 ^ 40 * 161831 * 2
def baseEnd_161831 : Nat := 49242718695029078025635

theorem tailTrace_161831 : CollatzResearch.WordTrace tailWord_161831 prefixEnd_161831 49242718695029078025635 := by
  unfold tailWord_161831
  simp only [CollatzResearch.WordTrace]
  refine ⟨5902461476721400379493347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3934974317814266919662231 5902461476721400379493347)
  ·
    refine ⟨8853692215082100569240021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5902461476721400379493347 8853692215082100569240021)
    ·
      refine ⟨207508411290986732091563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 8853692215082100569240021 207508411290986732091563)
      ·
        refine ⟨311262616936480098137345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 207508411290986732091563 311262616936480098137345)
        ·
          refine ⟨233446962702360073603009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 311262616936480098137345 233446962702360073603009)
          ·
            refine ⟨175085222026770055202257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 233446962702360073603009 175085222026770055202257)
            ·
              refine ⟨131313916520077541401693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 175085222026770055202257 131313916520077541401693)
              ·
                refine ⟨49242718695029078025635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 131313916520077541401693 49242718695029078025635)
                ·
                  rfl

theorem cell19_161831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 2, 3].length) (baseStart_161831 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_161831 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_161831 prefixEnd_161831 := by exact prefixLift 161831
  have htrace : WordTrace (prefixWord ++ tailWord_161831) baseStart_161831 baseEnd_161831 := by
    simpa [prefixWord, tailWord_161831, baseEnd_161831] using wordTrace_append hprefix tailTrace_161831
  have hstable : (prefixWord ++ tailWord_161831).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161831).length < 2 ^ (prefixWord ++ tailWord_161831).sum := by decide
  have hdescent : baseEnd_161831 < baseStart_161831 := by decide
  rcases family_descends (prefixWord ++ tailWord_161831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161856 : List Nat := [2, 1, 1, 2, 2, 6, 5]
def baseStart_161856 : Nat := 118140960795 + 161856 * 2 ^ 59
def prefixEnd_161856 : Nat := 4983230072969 + 3 ^ 40 * 161856 * 2
def baseEnd_161856 : Nat := 16416775271945475823337

theorem tailTrace_161856 : CollatzResearch.WordTrace tailWord_161856 prefixEnd_161856 16416775271945475823337 := by
  unfold tailWord_161856
  simp only [CollatzResearch.WordTrace]
  refine ⟨2951686650815414824576711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3935582201087219766102281 2951686650815414824576711)
  ·
    refine ⟨4427529976223122236865067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2951686650815414824576711 4427529976223122236865067)
    ·
      refine ⟨6641294964334683355297601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4427529976223122236865067 6641294964334683355297601)
      ·
        refine ⟨4980971223251012516473201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6641294964334683355297601 4980971223251012516473201)
        ·
          refine ⟨3735728417438259387354901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4980971223251012516473201 3735728417438259387354901)
          ·
            refine ⟨175112269567418408782261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 3735728417438259387354901 175112269567418408782261)
            ·
              refine ⟨16416775271945475823337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 175112269567418408782261 16416775271945475823337)
              ·
                rfl

theorem cell19_161856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 5].length) (baseStart_161856 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_161856 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_161856 prefixEnd_161856 := by exact prefixLift 161856
  have htrace : WordTrace (prefixWord ++ tailWord_161856) baseStart_161856 baseEnd_161856 := by
    simpa [prefixWord, tailWord_161856, baseEnd_161856] using wordTrace_append hprefix tailTrace_161856
  have hstable : (prefixWord ++ tailWord_161856).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161856).length < 2 ^ (prefixWord ++ tailWord_161856).sum := by decide
  have hdescent : baseEnd_161856 < baseStart_161856 := by decide
  rcases family_descends (prefixWord ++ tailWord_161856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161930 : List Nat := [3, 1, 2, 3, 1, 4, 1, 4]
def baseStart_161930 : Nat := 118140960795 + 161930 * 2 ^ 59
def prefixEnd_161930 : Nat := 4983230072969 + 3 ^ 40 * 161930 * 2
def baseEnd_161930 : Nat := 49272842893426181825365

theorem tailTrace_161930 : CollatzResearch.WordTrace tailWord_161930 prefixEnd_161930 49272842893426181825365 := by
  unfold tailWord_161930
  simp only [CollatzResearch.WordTrace]
  refine ⟨1476518075840685071836811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3937381535575160191564829 1476518075840685071836811)
  ·
    refine ⟨2214777113761027607755217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1476518075840685071836811 2214777113761027607755217)
    ·
      refine ⟨1661082835320770705816413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2214777113761027607755217 1661082835320770705816413)
      ·
        refine ⟨622906063245289014681155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1661082835320770705816413 622906063245289014681155)
        ·
          refine ⟨934359094867933522021733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 622906063245289014681155 934359094867933522021733)
          ·
            refine ⟨175192330287737535379075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 934359094867933522021733 175192330287737535379075)
            ·
              refine ⟨262788495431606303068613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 175192330287737535379075 262788495431606303068613)
              ·
                refine ⟨49272842893426181825365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 262788495431606303068613 49272842893426181825365)
                ·
                  rfl

theorem cell19_161930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 1, 4].length) (baseStart_161930 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_161930 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_161930 prefixEnd_161930 := by exact prefixLift 161930
  have htrace : WordTrace (prefixWord ++ tailWord_161930) baseStart_161930 baseEnd_161930 := by
    simpa [prefixWord, tailWord_161930, baseEnd_161930] using wordTrace_append hprefix tailTrace_161930
  have hstable : (prefixWord ++ tailWord_161930).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161930).length < 2 ^ (prefixWord ++ tailWord_161930).sum := by decide
  have hdescent : baseEnd_161930 < baseStart_161930 := by decide
  rcases family_descends (prefixWord ++ tailWord_161930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161949 : List Nat := [1, 4, 2, 1, 1, 4, 3, 3]
def baseStart_161949 : Nat := 118140960795 + 161949 * 2 ^ 59
def prefixEnd_161949 : Nat := 4983230072969 + 3 ^ 40 * 161949 * 2
def baseEnd_161949 : Nat := 49278624305239767403091

theorem tailTrace_161949 : CollatzResearch.WordTrace tailWord_161949 prefixEnd_161949 49278624305239767403091 := by
  unfold tailWord_161949
  simp only [CollatzResearch.WordTrace]
  refine ⟨5906765290293906532288901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3937843526862604354859267 5906765290293906532288901)
  ·
    refine ⟨1107518491930107474804169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5906765290293906532288901 1107518491930107474804169)
    ·
      refine ⟨830638868947580606103127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1107518491930107474804169 830638868947580606103127)
      ·
        refine ⟨1245958303421370909154691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 830638868947580606103127 1245958303421370909154691)
        ·
          refine ⟨1868937455132056363732037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1245958303421370909154691 1868937455132056363732037)
          ·
            refine ⟨350425772837260568199757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1868937455132056363732037 350425772837260568199757)
            ·
              refine ⟨131409664813972713074909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 350425772837260568199757 131409664813972713074909)
              ·
                refine ⟨49278624305239767403091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 131409664813972713074909 49278624305239767403091)
                ·
                  rfl

theorem cell19_161949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 3, 3].length) (baseStart_161949 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_161949 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_161949 prefixEnd_161949 := by exact prefixLift 161949
  have htrace : WordTrace (prefixWord ++ tailWord_161949) baseStart_161949 baseEnd_161949 := by
    simpa [prefixWord, tailWord_161949, baseEnd_161949] using wordTrace_append hprefix tailTrace_161949
  have hstable : (prefixWord ++ tailWord_161949).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161949).length < 2 ^ (prefixWord ++ tailWord_161949).sum := by decide
  have hdescent : baseEnd_161949 < baseStart_161949 := by decide
  rcases family_descends (prefixWord ++ tailWord_161949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161966 : List Nat := [4, 1, 4, 2, 1, 1, 6]
def baseStart_161966 : Nat := 118140960795 + 161966 * 2 ^ 59
def prefixEnd_161966 : Nat := 4983230072969 + 3 ^ 40 * 161966 * 2
def baseEnd_161966 : Nat := 16427932382462921675089

theorem tailTrace_161966 : CollatzResearch.WordTrace tailWord_161966 prefixEnd_161966 16427932382462921675089 := by
  unfold tailWord_161966
  simp only [CollatzResearch.WordTrace]
  refine ⟨738423166404039804457219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3938256887488212290438501 738423166404039804457219)
  ·
    refine ⟨1107634749606059706685829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 738423166404039804457219 1107634749606059706685829)
    ·
      refine ⟨207681515551136195003593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1107634749606059706685829 207681515551136195003593)
      ·
        refine ⟨155761136663352146252695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 207681515551136195003593 155761136663352146252695)
        ·
          refine ⟨233641704995028219379043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155761136663352146252695 233641704995028219379043)
          ·
            refine ⟨350462557492542329068565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 233641704995028219379043 350462557492542329068565)
            ·
              refine ⟨16427932382462921675089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 350462557492542329068565 16427932382462921675089)
              ·
                rfl

theorem cell19_161966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 6].length) (baseStart_161966 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_161966 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_161966 prefixEnd_161966 := by exact prefixLift 161966
  have htrace : WordTrace (prefixWord ++ tailWord_161966) baseStart_161966 baseEnd_161966 := by
    simpa [prefixWord, tailWord_161966, baseEnd_161966] using wordTrace_append hprefix tailTrace_161966
  have hstable : (prefixWord ++ tailWord_161966).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161966).length < 2 ^ (prefixWord ++ tailWord_161966).sum := by decide
  have hdescent : baseEnd_161966 < baseStart_161966 := by decide
  rcases family_descends (prefixWord ++ tailWord_161966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162008 : List Nat := [2, 1, 2, 2, 4, 2, 1, 5]
def baseStart_162008 : Nat := 118140960795 + 162008 * 2 ^ 59
def prefixEnd_162008 : Nat := 4983230072969 + 3 ^ 40 * 162008 * 2
def baseEnd_162008 : Nat := 49296577110345112091819

theorem tailTrace_162008 : CollatzResearch.WordTrace tailWord_162008 prefixEnd_162008 49296577110345112091819 := by
  unfold tailWord_162008
  simp only [CollatzResearch.WordTrace]
  refine ⟨2954458598540079804343339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3939278131386773072457785 2954458598540079804343339)
  ·
    refine ⟨4431687897810119706515009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2954458598540079804343339 4431687897810119706515009)
    ·
      refine ⟨3323765923357589779886257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4431687897810119706515009 3323765923357589779886257)
      ·
        refine ⟨2492824442518192334914693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3323765923357589779886257 2492824442518192334914693)
        ·
          refine ⟨467404582972161062796505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2492824442518192334914693 467404582972161062796505)
          ·
            refine ⟨350553437229120797097379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 467404582972161062796505 350553437229120797097379)
            ·
              refine ⟨525830155843681195646069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 350553437229120797097379 525830155843681195646069)
              ·
                refine ⟨49296577110345112091819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 525830155843681195646069 49296577110345112091819)
                ·
                  rfl

theorem cell19_162008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 5].length) (baseStart_162008 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_162008 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_162008 prefixEnd_162008 := by exact prefixLift 162008
  have htrace : WordTrace (prefixWord ++ tailWord_162008) baseStart_162008 baseEnd_162008 := by
    simpa [prefixWord, tailWord_162008, baseEnd_162008] using wordTrace_append hprefix tailTrace_162008
  have hstable : (prefixWord ++ tailWord_162008).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162008).length < 2 ^ (prefixWord ++ tailWord_162008).sum := by decide
  have hdescent : baseEnd_162008 < baseStart_162008 := by decide
  rcases family_descends (prefixWord ++ tailWord_162008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162048 : List Nat := [2, 1, 1, 2, 1, 1, 5, 6]
def baseStart_162048 : Nat := 118140960795 + 162048 * 2 ^ 59
def prefixEnd_162048 : Nat := 4983230072969 + 3 ^ 40 * 162048 * 2
def baseEnd_162048 : Nat := 49308748503636871202821

theorem tailTrace_162048 : CollatzResearch.WordTrace tailWord_162048 prefixEnd_162048 49308748503636871202821 := by
  unfold tailWord_162048
  simp only [CollatzResearch.WordTrace]
  refine ⟨2955188058467623220071399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3940250744623497626761865 2955188058467623220071399)
  ·
    refine ⟨4432782087701434830107099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2955188058467623220071399 4432782087701434830107099)
    ·
      refine ⟨6649173131552152245160649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4432782087701434830107099 6649173131552152245160649)
      ·
        refine ⟨4986879848664114183870487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6649173131552152245160649 4986879848664114183870487)
        ·
          refine ⟨7480319772996171275805731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4986879848664114183870487 7480319772996171275805731)
          ·
            refine ⟨11220479659494256913708597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7480319772996171275805731 11220479659494256913708597)
            ·
              refine ⟨1051919968077586585660181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11220479659494256913708597 1051919968077586585660181)
              ·
                refine ⟨49308748503636871202821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1051919968077586585660181 49308748503636871202821)
                ·
                  rfl

theorem cell19_162048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 6].length) (baseStart_162048 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_162048 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_162048 prefixEnd_162048 := by exact prefixLift 162048
  have htrace : WordTrace (prefixWord ++ tailWord_162048) baseStart_162048 baseEnd_162048 := by
    simpa [prefixWord, tailWord_162048, baseEnd_162048] using wordTrace_append hprefix tailTrace_162048
  have hstable : (prefixWord ++ tailWord_162048).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162048).length < 2 ^ (prefixWord ++ tailWord_162048).sum := by decide
  have hdescent : baseEnd_162048 < baseStart_162048 := by decide
  rcases family_descends (prefixWord ++ tailWord_162048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162177 : List Nat := [1, 2, 4, 3, 1, 1, 4, 3]
def baseStart_162177 : Nat := 118140960795 + 162177 * 2 ^ 59
def prefixEnd_162177 : Nat := 4983230072969 + 3 ^ 40 * 162177 * 2
def baseEnd_162177 : Nat := 49348001247002794335803

theorem tailTrace_162177 : CollatzResearch.WordTrace tailWord_162177 prefixEnd_162177 49348001247002794335803 := by
  unfold tailWord_162177
  simp only [CollatzResearch.WordTrace]
  refine ⟨5915081133467901471588785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3943387422311934314392523 5915081133467901471588785)
  ·
    refine ⟨4436310850100926103691589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5915081133467901471588785 4436310850100926103691589)
    ·
      refine ⟨831808284393923644442173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4436310850100926103691589 831808284393923644442173)
      ·
        refine ⟨311928106647721366665815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 831808284393923644442173 311928106647721366665815)
        ·
          refine ⟨467892159971582049998723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 311928106647721366665815 467892159971582049998723)
          ·
            refine ⟨701838239957373074998085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 467892159971582049998723 701838239957373074998085)
            ·
              refine ⟨131594669992007451562141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 701838239957373074998085 131594669992007451562141)
              ·
                refine ⟨49348001247002794335803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 131594669992007451562141 49348001247002794335803)
                ·
                  rfl

theorem cell19_162177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 4, 3].length) (baseStart_162177 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_162177 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_162177 prefixEnd_162177 := by exact prefixLift 162177
  have htrace : WordTrace (prefixWord ++ tailWord_162177) baseStart_162177 baseEnd_162177 := by
    simpa [prefixWord, tailWord_162177, baseEnd_162177] using wordTrace_append hprefix tailTrace_162177
  have hstable : (prefixWord ++ tailWord_162177).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162177).length < 2 ^ (prefixWord ++ tailWord_162177).sum := by decide
  have hdescent : baseEnd_162177 < baseStart_162177 := by decide
  rcases family_descends (prefixWord ++ tailWord_162177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162179 : List Nat := [1, 1, 1, 3, 6, 1, 1, 5]
def baseStart_162179 : Nat := 118140960795 + 162179 * 2 ^ 59
def prefixEnd_162179 : Nat := 4983230072969 + 3 ^ 40 * 162179 * 2
def baseEnd_162179 : Nat := 49348609816667382291353

theorem tailTrace_162179 : CollatzResearch.WordTrace tailWord_162179 prefixEnd_162179 49348609816667382291353 := by
  unfold tailWord_162179
  simp only [CollatzResearch.WordTrace]
  refine ⟨5915154079460655813161591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3943436052973770542107727 5915154079460655813161591)
  ·
    refine ⟨8872731119190983719742387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5915154079460655813161591 8872731119190983719742387)
    ·
      refine ⟨13309096678786475579613581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8872731119190983719742387 13309096678786475579613581)
      ·
        refine ⟨4990911254544928342355093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13309096678786475579613581 4990911254544928342355093)
        ·
          refine ⟨233948965056793516047895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 4990911254544928342355093 233948965056793516047895)
          ·
            refine ⟨350923447585190274071843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 233948965056793516047895 350923447585190274071843)
            ·
              refine ⟨526385171377785411107765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 350923447585190274071843 526385171377785411107765)
              ·
                refine ⟨49348609816667382291353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 526385171377785411107765 49348609816667382291353)
                ·
                  rfl

theorem cell19_162179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 5].length) (baseStart_162179 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_162179 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_162179 prefixEnd_162179 := by exact prefixLift 162179
  have htrace : WordTrace (prefixWord ++ tailWord_162179) baseStart_162179 baseEnd_162179 := by
    simpa [prefixWord, tailWord_162179, baseEnd_162179] using wordTrace_append hprefix tailTrace_162179
  have hstable : (prefixWord ++ tailWord_162179).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162179).length < 2 ^ (prefixWord ++ tailWord_162179).sum := by decide
  have hdescent : baseEnd_162179 < baseStart_162179 := by decide
  rcases family_descends (prefixWord ++ tailWord_162179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162196 : List Nat := [2, 4, 2, 1, 3, 2, 5]
def baseStart_162196 : Nat := 118140960795 + 162196 * 2 ^ 59
def prefixEnd_162196 : Nat := 4983230072969 + 3 ^ 40 * 162196 * 2
def baseEnd_162196 : Nat := 16451260886272126637843

theorem tailTrace_162196 : CollatzResearch.WordTrace tailWord_162196 prefixEnd_162196 16451260886272126637843 := by
  unfold tailWord_162196
  simp only [CollatzResearch.WordTrace]
  refine ⟨2957887060199533858265221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3943849413599378477686961 2957887060199533858265221)
  ·
    refine ⟨554603823787412598424729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2957887060199533858265221 554603823787412598424729)
    ·
      refine ⟨415952867840559448818547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 554603823787412598424729 415952867840559448818547)
      ·
        refine ⟨623929301760839173227821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 415952867840559448818547 623929301760839173227821)
        ·
          refine ⟨233973488160314689960433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 623929301760839173227821 233973488160314689960433)
          ·
            refine ⟨175480116120236017470325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 233973488160314689960433 175480116120236017470325)
            ·
              refine ⟨16451260886272126637843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 175480116120236017470325 16451260886272126637843)
              ·
                rfl

theorem cell19_162196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 5].length) (baseStart_162196 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_162196 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_162196 prefixEnd_162196 := by exact prefixLift 162196
  have htrace : WordTrace (prefixWord ++ tailWord_162196) baseStart_162196 baseEnd_162196 := by
    simpa [prefixWord, tailWord_162196, baseEnd_162196] using wordTrace_append hprefix tailTrace_162196
  have hstable : (prefixWord ++ tailWord_162196).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162196).length < 2 ^ (prefixWord ++ tailWord_162196).sum := by decide
  have hdescent : baseEnd_162196 < baseStart_162196 := by decide
  rcases family_descends (prefixWord ++ tailWord_162196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162236 : List Nat := [2, 2, 2, 4, 1, 1, 2, 5]
def baseStart_162236 : Nat := 118140960795 + 162236 * 2 ^ 59
def prefixEnd_162236 : Nat := 4983230072969 + 3 ^ 40 * 162236 * 2
def baseEnd_162236 : Nat := 49365954052108139024531

theorem tailTrace_162236 : CollatzResearch.WordTrace tailWord_162236 prefixEnd_162236 49365954052108139024531 := by
  unfold tailWord_162236
  simp only [CollatzResearch.WordTrace]
  refine ⟨2958616520127077273993281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3944822026836103031991041 2958616520127077273993281)
  ·
    refine ⟨2218962390095307955494961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2958616520127077273993281 2218962390095307955494961)
    ·
      refine ⟨1664221792571480966621221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2218962390095307955494961 1664221792571480966621221)
      ·
        refine ⟨312041586107152681241479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1664221792571480966621221 312041586107152681241479)
        ·
          refine ⟨468062379160729021862219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 312041586107152681241479 468062379160729021862219)
          ·
            refine ⟨702093568741093532793329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 468062379160729021862219 702093568741093532793329)
            ·
              refine ⟨526570176555820149594997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 702093568741093532793329 526570176555820149594997)
              ·
                refine ⟨49365954052108139024531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 526570176555820149594997 49365954052108139024531)
                ·
                  rfl

theorem cell19_162236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 5].length) (baseStart_162236 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_162236 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_162236 prefixEnd_162236 := by exact prefixLift 162236
  have htrace : WordTrace (prefixWord ++ tailWord_162236) baseStart_162236 baseEnd_162236 := by
    simpa [prefixWord, tailWord_162236, baseEnd_162236] using wordTrace_append hprefix tailTrace_162236
  have hstable : (prefixWord ++ tailWord_162236).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162236).length < 2 ^ (prefixWord ++ tailWord_162236).sum := by decide
  have hdescent : baseEnd_162236 < baseStart_162236 := by decide
  rcases family_descends (prefixWord ++ tailWord_162236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162314 : List Nat := [3, 1, 2, 2, 2, 1, 8]
def baseStart_162314 : Nat := 118140960795 + 162314 * 2 ^ 59
def prefixEnd_162314 : Nat := 4983230072969 + 3 ^ 40 * 162314 * 2
def baseEnd_162314 : Nat := 16463229423009023096995

theorem tailTrace_162314 : CollatzResearch.WordTrace tailWord_162314 prefixEnd_162314 16463229423009023096995 := by
  unfold tailWord_162314
  simp only [CollatzResearch.WordTrace]
  refine ⟨1480019483492893467331499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3946718622647715912883997 1480019483492893467331499)
  ·
    refine ⟨2220029225239340200997249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1480019483492893467331499 2220029225239340200997249)
    ·
      refine ⟨1665021918929505150747937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2220029225239340200997249 1665021918929505150747937)
      ·
        refine ⟨1248766439197128863060953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1665021918929505150747937 1248766439197128863060953)
        ·
          refine ⟨936574829397846647295715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1248766439197128863060953 936574829397846647295715)
          ·
            refine ⟨1404862244096769970943573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 936574829397846647295715 1404862244096769970943573)
            ·
              refine ⟨16463229423009023096995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1404862244096769970943573 16463229423009023096995)
              ·
                rfl

theorem cell19_162314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 8].length) (baseStart_162314 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_162314 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_162314 prefixEnd_162314 := by exact prefixLift 162314
  have htrace : WordTrace (prefixWord ++ tailWord_162314) baseStart_162314 baseEnd_162314 := by
    simpa [prefixWord, tailWord_162314, baseEnd_162314] using wordTrace_append hprefix tailTrace_162314
  have hstable : (prefixWord ++ tailWord_162314).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162314).length < 2 ^ (prefixWord ++ tailWord_162314).sum := by decide
  have hdescent : baseEnd_162314 < baseStart_162314 := by decide
  rcases family_descends (prefixWord ++ tailWord_162314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162369 : List Nat := [1, 2, 5, 1, 1, 4, 5]
def baseStart_162369 : Nat := 118140960795 + 162369 * 2 ^ 59
def prefixEnd_162369 : Nat := 4983230072969 + 3 ^ 40 * 162369 * 2
def baseEnd_162369 : Nat := 16468807978267746022871

theorem tailTrace_162369 : CollatzResearch.WordTrace tailWord_162369 prefixEnd_162369 16468807978267746022871 := by
  unfold tailWord_162369
  simp only [CollatzResearch.WordTrace]
  refine ⟨5922083948772318262578161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3948055965848212175052107 5922083948772318262578161)
  ·
    refine ⟨4441562961579238696933621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5922083948772318262578161 4441562961579238696933621)
    ·
      refine ⟨416396527648053627837527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4441562961579238696933621 416396527648053627837527)
      ·
        refine ⟨624594791472080441756291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 416396527648053627837527 624594791472080441756291)
        ·
          refine ⟨936892187208120662634437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 624594791472080441756291 936892187208120662634437)
          ·
            refine ⟨175667285101522624243957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 936892187208120662634437 175667285101522624243957)
            ·
              refine ⟨16468807978267746022871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 175667285101522624243957 16468807978267746022871)
              ·
                rfl

theorem cell19_162369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 5].length) (baseStart_162369 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_162369 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_162369 prefixEnd_162369 := by exact prefixLift 162369
  have htrace : WordTrace (prefixWord ++ tailWord_162369) baseStart_162369 baseEnd_162369 := by
    simpa [prefixWord, tailWord_162369, baseEnd_162369] using wordTrace_append hprefix tailTrace_162369
  have hstable : (prefixWord ++ tailWord_162369).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162369).length < 2 ^ (prefixWord ++ tailWord_162369).sum := by decide
  have hdescent : baseEnd_162369 < baseStart_162369 := by decide
  rcases family_descends (prefixWord ++ tailWord_162369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162388 : List Nat := [2, 4, 1, 1, 1, 4, 2, 4]
def baseStart_162388 : Nat := 118140960795 + 162388 * 2 ^ 59
def prefixEnd_162388 : Nat := 4983230072969 + 3 ^ 40 * 162388 * 2
def baseEnd_162388 : Nat := 49412205346616823646339

theorem tailTrace_162388 : CollatzResearch.WordTrace tailWord_162388 prefixEnd_162388 49412205346616823646339 := by
  unfold tailWord_162388
  simp only [CollatzResearch.WordTrace]
  refine ⟨2961388467851742253759909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3948517957135656338346545 2961388467851742253759909)
  ·
    refine ⟨555260337722201672579983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2961388467851742253759909 555260337722201672579983)
    ·
      refine ⟨832890506583302508869975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 555260337722201672579983 832890506583302508869975)
      ·
        refine ⟨1249335759874953763304963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 832890506583302508869975 1249335759874953763304963)
        ·
          refine ⟨1874003639812430644957445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1249335759874953763304963 1874003639812430644957445)
          ·
            refine ⟨351375682464830745929521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1874003639812430644957445 351375682464830745929521)
            ·
              refine ⟨263531761848623059447141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 351375682464830745929521 263531761848623059447141)
              ·
                refine ⟨49412205346616823646339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 263531761848623059447141 49412205346616823646339)
                ·
                  rfl

theorem cell19_162388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 2, 4].length) (baseStart_162388 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_162388 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_162388 prefixEnd_162388 := by exact prefixLift 162388
  have htrace : WordTrace (prefixWord ++ tailWord_162388) baseStart_162388 baseEnd_162388 := by
    simpa [prefixWord, tailWord_162388, baseEnd_162388] using wordTrace_append hprefix tailTrace_162388
  have hstable : (prefixWord ++ tailWord_162388).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162388).length < 2 ^ (prefixWord ++ tailWord_162388).sum := by decide
  have hdescent : baseEnd_162388 < baseStart_162388 := by decide
  rcases family_descends (prefixWord ++ tailWord_162388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162462 : List Nat := [4, 3, 1, 1, 1, 1, 5, 3]
def baseStart_162462 : Nat := 118140960795 + 162462 * 2 ^ 59
def prefixEnd_162462 : Nat := 4983230072969 + 3 ^ 40 * 162462 * 2
def baseEnd_162462 : Nat := 49434722424206578001693

theorem tailTrace_162462 : CollatzResearch.WordTrace tailWord_162462 prefixEnd_162462 49434722424206578001693 := by
  unfold tailWord_162462
  simp only [CollatzResearch.WordTrace]
  refine ⟨740684492179424393214205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3950317291623596763809093 740684492179424393214205)
  ·
    refine ⟨277756684567284147455327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 740684492179424393214205 277756684567284147455327)
    ·
      refine ⟨416635026850926221182991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 277756684567284147455327 416635026850926221182991)
      ·
        refine ⟨624952540276389331774487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 416635026850926221182991 624952540276389331774487)
        ·
          refine ⟨937428810414583997661731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 624952540276389331774487 937428810414583997661731)
          ·
            refine ⟨1406143215621875996492597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 937428810414583997661731 1406143215621875996492597)
            ·
              refine ⟨131825926464550874671181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1406143215621875996492597 131825926464550874671181)
              ·
                refine ⟨49434722424206578001693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 131825926464550874671181 49434722424206578001693)
                ·
                  rfl

theorem cell19_162462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 5, 3].length) (baseStart_162462 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_162462 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_162462 prefixEnd_162462 := by exact prefixLift 162462
  have htrace : WordTrace (prefixWord ++ tailWord_162462) baseStart_162462 baseEnd_162462 := by
    simpa [prefixWord, tailWord_162462, baseEnd_162462] using wordTrace_append hprefix tailTrace_162462
  have hstable : (prefixWord ++ tailWord_162462).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162462).length < 2 ^ (prefixWord ++ tailWord_162462).sum := by decide
  have hdescent : baseEnd_162462 < baseStart_162462 := by decide
  rcases family_descends (prefixWord ++ tailWord_162462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162517 : List Nat := [1, 3, 2, 5, 1, 2, 2, 3]
def baseStart_162517 : Nat := 118140960795 + 162517 * 2 ^ 59
def prefixEnd_162517 : Nat := 4983230072969 + 3 ^ 40 * 162517 * 2
def baseEnd_162517 : Nat := 49451458089982746779321

theorem tailTrace_162517 : CollatzResearch.WordTrace tailWord_162517 prefixEnd_162517 49451458089982746779321 := by
  unfold tailWord_162517
  simp only [CollatzResearch.WordTrace]
  refine ⟨5927481952236139538965805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3951654634824093025977203 5927481952236139538965805)
  ·
    refine ⟨2222805732088552327112177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5927481952236139538965805 2222805732088552327112177)
    ·
      refine ⟨1667104299066414245334133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2222805732088552327112177 1667104299066414245334133)
      ·
        refine ⟨156291028037476335500075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1667104299066414245334133 156291028037476335500075)
        ·
          refine ⟨234436542056214503250113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156291028037476335500075 234436542056214503250113)
          ·
            refine ⟨175827406542160877437585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 234436542056214503250113 175827406542160877437585)
            ·
              refine ⟨131870554906620658078189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 175827406542160877437585 131870554906620658078189)
              ·
                refine ⟨49451458089982746779321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 131870554906620658078189 49451458089982746779321)
                ·
                  rfl

theorem cell19_162517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 2, 3].length) (baseStart_162517 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_162517 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_162517 prefixEnd_162517 := by exact prefixLift 162517
  have htrace : WordTrace (prefixWord ++ tailWord_162517) baseStart_162517 baseEnd_162517 := by
    simpa [prefixWord, tailWord_162517, baseEnd_162517] using wordTrace_append hprefix tailTrace_162517
  have hstable : (prefixWord ++ tailWord_162517).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162517).length < 2 ^ (prefixWord ++ tailWord_162517).sum := by decide
  have hdescent : baseEnd_162517 < baseStart_162517 := by decide
  rcases family_descends (prefixWord ++ tailWord_162517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162542 : List Nat := [4, 1, 2, 1, 1, 3, 7]
def baseStart_162542 : Nat := 118140960795 + 162542 * 2 ^ 59
def prefixEnd_162542 : Nat := 4983230072969 + 3 ^ 40 * 162542 * 2
def baseEnd_162542 : Nat := 16486355070263365407899

theorem tailTrace_162542 : CollatzResearch.WordTrace tailWord_162542 prefixEnd_162542 16486355070263365407899 := by
  unfold tailWord_162542
  simp only [CollatzResearch.WordTrace]
  refine ⟨741049222143196101078235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3952262518097045872417253 741049222143196101078235)
  ·
    refine ⟨1111573833214794151617353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 741049222143196101078235 1111573833214794151617353)
    ·
      refine ⟨833680374911095613713015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1111573833214794151617353 833680374911095613713015)
      ·
        refine ⟨1250520562366643420569523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 833680374911095613713015 1250520562366643420569523)
        ·
          refine ⟨1875780843549965130854285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1250520562366643420569523 1875780843549965130854285)
          ·
            refine ⟨703417816331236924070357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1875780843549965130854285 703417816331236924070357)
            ·
              refine ⟨16486355070263365407899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 703417816331236924070357 16486355070263365407899)
              ·
                rfl

theorem cell19_162542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 7].length) (baseStart_162542 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_162542 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_162542 prefixEnd_162542 := by exact prefixLift 162542
  have htrace : WordTrace (prefixWord ++ tailWord_162542) baseStart_162542 baseEnd_162542 := by
    simpa [prefixWord, tailWord_162542, baseEnd_162542] using wordTrace_append hprefix tailTrace_162542
  have hstable : (prefixWord ++ tailWord_162542).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162542).length < 2 ^ (prefixWord ++ tailWord_162542).sum := by decide
  have hdescent : baseEnd_162542 < baseStart_162542 := by decide
  rcases family_descends (prefixWord ++ tailWord_162542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162612 : List Nat := [2, 5, 1, 1, 4, 1, 1, 4]
def baseStart_162612 : Nat := 118140960795 + 162612 * 2 ^ 59
def prefixEnd_162612 : Nat := 4983230072969 + 3 ^ 40 * 162612 * 2
def baseEnd_162612 : Nat := 49480365149050674667951

theorem tailTrace_162612 : CollatzResearch.WordTrace tailWord_162612 prefixEnd_162612 49480365149050674667951 := by
  unfold tailWord_162612
  simp only [CollatzResearch.WordTrace]
  refine ⟨2965473443445985381837045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3953964591261313842449393 2965473443445985381837045)
  ·
    refine ⟨278013135323061129547223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2965473443445985381837045 278013135323061129547223)
    ·
      refine ⟨417019702984591694320835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 278013135323061129547223 417019702984591694320835)
      ·
        refine ⟨625529554476887541481253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 417019702984591694320835 625529554476887541481253)
        ·
          refine ⟨117286791464416414027735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 625529554476887541481253 117286791464416414027735)
          ·
            refine ⟨175930187196624621041603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117286791464416414027735 175930187196624621041603)
            ·
              refine ⟨263895280794936931562405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 175930187196624621041603 263895280794936931562405)
              ·
                refine ⟨49480365149050674667951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 263895280794936931562405 49480365149050674667951)
                ·
                  rfl

theorem cell19_162612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 1, 4].length) (baseStart_162612 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_162612 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_162612 prefixEnd_162612 := by exact prefixLift 162612
  have htrace : WordTrace (prefixWord ++ tailWord_162612) baseStart_162612 baseEnd_162612 := by
    simpa [prefixWord, tailWord_162612, baseEnd_162612] using wordTrace_append hprefix tailTrace_162612
  have hstable : (prefixWord ++ tailWord_162612).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162612).length < 2 ^ (prefixWord ++ tailWord_162612).sum := by decide
  have hdescent : baseEnd_162612 < baseStart_162612 := by decide
  rcases family_descends (prefixWord ++ tailWord_162612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162686 : List Nat := [4, 2, 3, 1, 3, 1, 2, 3]
def baseStart_162686 : Nat := 118140960795 + 162686 * 2 ^ 59
def prefixEnd_162686 : Nat := 4983230072969 + 3 ^ 40 * 162686 * 2
def baseEnd_162686 : Nat := 49502882226640429023305

theorem tailTrace_162686 : CollatzResearch.WordTrace tailWord_162686 prefixEnd_162686 49502882226640429023305 := by
  unfold tailWord_162686
  simp only [CollatzResearch.WordTrace]
  refine ⟨741705736077985175233489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3955763925749254267911941 741705736077985175233489)
  ·
    refine ⟨556279302058488881425117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 741705736077985175233489 556279302058488881425117)
    ·
      refine ⟨208604738271933330534419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 556279302058488881425117 208604738271933330534419)
      ·
        refine ⟨312907107407899995801629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208604738271933330534419 312907107407899995801629)
        ·
          refine ⟨117340165277962498425611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 312907107407899995801629 117340165277962498425611)
          ·
            refine ⟨176010247916943747638417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117340165277962498425611 176010247916943747638417)
            ·
              refine ⟨132007685937707810728813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 176010247916943747638417 132007685937707810728813)
              ·
                refine ⟨49502882226640429023305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 132007685937707810728813 49502882226640429023305)
                ·
                  rfl

theorem cell19_162686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 2, 3].length) (baseStart_162686 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_162686 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_162686 prefixEnd_162686 := by exact prefixLift 162686
  have htrace : WordTrace (prefixWord ++ tailWord_162686) baseStart_162686 baseEnd_162686 := by
    simpa [prefixWord, tailWord_162686, baseEnd_162686] using wordTrace_append hprefix tailTrace_162686
  have hstable : (prefixWord ++ tailWord_162686).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162686).length < 2 ^ (prefixWord ++ tailWord_162686).sum := by decide
  have hdescent : baseEnd_162686 < baseStart_162686 := by decide
  rcases family_descends (prefixWord ++ tailWord_162686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162770 : List Nat := [3, 2, 2, 3, 1, 8]
def baseStart_162770 : Nat := 118140960795 + 162770 * 2 ^ 59
def prefixEnd_162770 : Nat := 4983230072969 + 3 ^ 40 * 162770 * 2
def baseEnd_162770 : Nat := 5503160239172569239601

theorem tailTrace_162770 : CollatzResearch.WordTrace tailWord_162770 prefixEnd_162770 5503160239172569239601 := by
  unfold tailWord_162770
  simp only [CollatzResearch.WordTrace]
  refine ⟨1484177405079890936981441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3957806413546375831950509 1484177405079890936981441)
  ·
    refine ⟨1113133053809918202736081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1484177405079890936981441 1113133053809918202736081)
    ·
      refine ⟨834849790357438652052061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1113133053809918202736081 834849790357438652052061)
      ·
        refine ⟨313068671384039494519523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 834849790357438652052061 313068671384039494519523)
        ·
          refine ⟨469603007076059241779285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 313068671384039494519523 469603007076059241779285)
          ·
            refine ⟨5503160239172569239601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 469603007076059241779285 5503160239172569239601)
            ·
              rfl

theorem cell19_162770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 8].length) (baseStart_162770 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_162770 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_162770 prefixEnd_162770 := by exact prefixLift 162770
  have htrace : WordTrace (prefixWord ++ tailWord_162770) baseStart_162770 baseEnd_162770 := by
    simpa [prefixWord, tailWord_162770, baseEnd_162770] using wordTrace_append hprefix tailTrace_162770
  have hstable : (prefixWord ++ tailWord_162770).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162770).length < 2 ^ (prefixWord ++ tailWord_162770).sum := by decide
  have hdescent : baseEnd_162770 < baseStart_162770 := by decide
  rcases family_descends (prefixWord ++ tailWord_162770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162810 : List Nat := [3, 1, 1, 1, 1, 2, 1, 9]
def baseStart_162810 : Nat := 118140960795 + 162810 * 2 ^ 59
def prefixEnd_162810 : Nat := 4983230072969 + 3 ^ 40 * 162810 * 2
def baseEnd_162810 : Nat := 49540613545844882267411

theorem tailTrace_162810 : CollatzResearch.WordTrace tailWord_162810 prefixEnd_162810 49540613545844882267411 := by
  unfold tailWord_162810
  simp only [CollatzResearch.WordTrace]
  refine ⟨1484542135043662644845471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3958779026783100386254589 1484542135043662644845471)
  ·
    refine ⟨2226813202565493967268207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1484542135043662644845471 2226813202565493967268207)
    ·
      refine ⟨3340219803848240950902311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2226813202565493967268207 3340219803848240950902311)
      ·
        refine ⟨5010329705772361426353467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3340219803848240950902311 5010329705772361426353467)
        ·
          refine ⟨7515494558658542139530201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5010329705772361426353467 7515494558658542139530201)
          ·
            refine ⟨5636620918993906604647651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7515494558658542139530201 5636620918993906604647651)
            ·
              refine ⟨8454931378490859906971477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5636620918993906604647651 8454931378490859906971477)
              ·
                refine ⟨49540613545844882267411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8454931378490859906971477 49540613545844882267411)
                ·
                  rfl

theorem cell19_162810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 9].length) (baseStart_162810 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_162810 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_162810 prefixEnd_162810 := by exact prefixLift 162810
  have htrace : WordTrace (prefixWord ++ tailWord_162810) baseStart_162810 baseEnd_162810 := by
    simpa [prefixWord, tailWord_162810, baseEnd_162810] using wordTrace_append hprefix tailTrace_162810
  have hstable : (prefixWord ++ tailWord_162810).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162810).length < 2 ^ (prefixWord ++ tailWord_162810).sum := by decide
  have hdescent : baseEnd_162810 < baseStart_162810 := by decide
  rcases family_descends (prefixWord ++ tailWord_162810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162922 : List Nat := [3, 1, 3, 2, 2, 1, 2, 5]
def baseStart_162922 : Nat := 118140960795 + 162922 * 2 ^ 59
def prefixEnd_162922 : Nat := 4983230072969 + 3 ^ 40 * 162922 * 2
def baseEnd_162922 : Nat := 49574693447061807778217

theorem tailTrace_162922 : CollatzResearch.WordTrace tailWord_162922 prefixEnd_162922 49574693447061807778217 := by
  unfold tailWord_162922
  simp only [CollatzResearch.WordTrace]
  refine ⟨1485563378942223426864755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3961502343845929138306013 1485563378942223426864755)
  ·
    refine ⟨2228345068413335140297133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1485563378942223426864755 2228345068413335140297133)
    ·
      refine ⟨835629400655000677611425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2228345068413335140297133 835629400655000677611425)
      ·
        refine ⟨626722050491250508208569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 835629400655000677611425 626722050491250508208569)
        ·
          refine ⟨470041537868437881156427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 626722050491250508208569 470041537868437881156427)
          ·
            refine ⟨705062306802656821734641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 470041537868437881156427 705062306802656821734641)
            ·
              refine ⟨528796730101992616300981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 705062306802656821734641 528796730101992616300981)
              ·
                refine ⟨49574693447061807778217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 528796730101992616300981 49574693447061807778217)
                ·
                  rfl

theorem cell19_162922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 5].length) (baseStart_162922 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_162922 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_162922 prefixEnd_162922 := by exact prefixLift 162922
  have htrace : WordTrace (prefixWord ++ tailWord_162922) baseStart_162922 baseEnd_162922 := by
    simpa [prefixWord, tailWord_162922, baseEnd_162922] using wordTrace_append hprefix tailTrace_162922
  have hstable : (prefixWord ++ tailWord_162922).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162922).length < 2 ^ (prefixWord ++ tailWord_162922).sum := by decide
  have hdescent : baseEnd_162922 < baseStart_162922 := by decide
  rcases family_descends (prefixWord ++ tailWord_162922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162924 : List Nat := [2, 2, 1, 1, 3, 2, 1, 7]
def baseStart_162924 : Nat := 118140960795 + 162924 * 2 ^ 59
def prefixEnd_162924 : Nat := 4983230072969 + 3 ^ 40 * 162924 * 2
def baseEnd_162924 : Nat := 49575302016726395733767

theorem tailTrace_162924 : CollatzResearch.WordTrace tailWord_162924 prefixEnd_162924 49575302016726395733767 := by
  unfold tailWord_162924
  simp only [CollatzResearch.WordTrace]
  refine ⟨2971163230880824024515913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3961550974507765366021217 2971163230880824024515913)
  ·
    refine ⟨2228372423160618018386935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2971163230880824024515913 2228372423160618018386935)
    ·
      refine ⟨3342558634740927027580403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2228372423160618018386935 3342558634740927027580403)
      ·
        refine ⟨5013837952111390541370605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3342558634740927027580403 5013837952111390541370605)
        ·
          refine ⟨1880189232041771453013977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5013837952111390541370605 1880189232041771453013977)
          ·
            refine ⟨1410141924031328589760483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1880189232041771453013977 1410141924031328589760483)
            ·
              refine ⟨2115212886046992884640725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1410141924031328589760483 2115212886046992884640725)
              ·
                refine ⟨49575302016726395733767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2115212886046992884640725 49575302016726395733767)
                ·
                  rfl

theorem cell19_162924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 7].length) (baseStart_162924 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_162924 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_162924 prefixEnd_162924 := by exact prefixLift 162924
  have htrace : WordTrace (prefixWord ++ tailWord_162924) baseStart_162924 baseEnd_162924 := by
    simpa [prefixWord, tailWord_162924, baseEnd_162924] using wordTrace_append hprefix tailTrace_162924
  have hstable : (prefixWord ++ tailWord_162924).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162924).length < 2 ^ (prefixWord ++ tailWord_162924).sum := by decide
  have hdescent : baseEnd_162924 < baseStart_162924 := by decide
  rcases family_descends (prefixWord ++ tailWord_162924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162958 : List Nat := [4, 1, 1, 3, 2, 3, 1, 4]
def baseStart_162958 : Nat := 118140960795 + 162958 * 2 ^ 59
def prefixEnd_162958 : Nat := 4983230072969 + 3 ^ 40 * 162958 * 2
def baseEnd_162958 : Nat := 49585647701024390978119

theorem tailTrace_162958 : CollatzResearch.WordTrace tailWord_162958 prefixEnd_162958 49585647701024390978119 := by
  unfold tailWord_162958
  simp only [CollatzResearch.WordTrace]
  refine ⟨742945817954808981971191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3962377695758981237179685 742945817954808981971191)
  ·
    refine ⟨1114418726932213472956787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 742945817954808981971191 1114418726932213472956787)
    ·
      refine ⟨1671628090398320209435181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1114418726932213472956787 1671628090398320209435181)
      ·
        refine ⟨626860533899370078538193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1671628090398320209435181 626860533899370078538193)
        ·
          refine ⟨470145400424527558903645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 626860533899370078538193 470145400424527558903645)
          ·
            refine ⟨176304525159197834588867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 470145400424527558903645 176304525159197834588867)
            ·
              refine ⟨264456787738796751883301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 176304525159197834588867 264456787738796751883301)
              ·
                refine ⟨49585647701024390978119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 264456787738796751883301 49585647701024390978119)
                ·
                  rfl

theorem cell19_162958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 1, 4].length) (baseStart_162958 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_162958 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_162958 prefixEnd_162958 := by exact prefixLift 162958
  have htrace : WordTrace (prefixWord ++ tailWord_162958) baseStart_162958 baseEnd_162958 := by
    simpa [prefixWord, tailWord_162958, baseEnd_162958] using wordTrace_append hprefix tailTrace_162958
  have hstable : (prefixWord ++ tailWord_162958).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162958).length < 2 ^ (prefixWord ++ tailWord_162958).sum := by decide
  have hdescent : baseEnd_162958 < baseStart_162958 := by decide
  rcases family_descends (prefixWord ++ tailWord_162958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163030 : List Nat := [5, 2, 1, 2, 2, 2, 2, 3]
def baseStart_163030 : Nat := 118140960795 + 163030 * 2 ^ 59
def prefixEnd_163030 : Nat := 4983230072969 + 3 ^ 40 * 163030 * 2
def baseEnd_163030 : Nat := 49607556208949557377923

theorem tailTrace_163030 : CollatzResearch.WordTrace tailWord_163030 prefixEnd_163030 49607556208949557377923 := by
  unfold tailWord_163030
  simp only [CollatzResearch.WordTrace]
  refine ⟨371637037461101759524409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3964128399585085434927029 371637037461101759524409)
  ·
    refine ⟨278727778095826319643307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 371637037461101759524409 278727778095826319643307)
    ·
      refine ⟨418091667143739479464961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 278727778095826319643307 418091667143739479464961)
      ·
        refine ⟨313568750357804609598721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 418091667143739479464961 313568750357804609598721)
        ·
          refine ⟨235176562768353457199041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 313568750357804609598721 235176562768353457199041)
          ·
            refine ⟨176382422076265092899281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 235176562768353457199041 176382422076265092899281)
            ·
              refine ⟨132286816557198819674461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 176382422076265092899281 132286816557198819674461)
              ·
                refine ⟨49607556208949557377923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 132286816557198819674461 49607556208949557377923)
                ·
                  rfl

theorem cell19_163030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 2, 3].length) (baseStart_163030 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_163030 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_163030 prefixEnd_163030 := by exact prefixLift 163030
  have htrace : WordTrace (prefixWord ++ tailWord_163030) baseStart_163030 baseEnd_163030 := by
    simpa [prefixWord, tailWord_163030, baseEnd_163030] using wordTrace_append hprefix tailTrace_163030
  have hstable : (prefixWord ++ tailWord_163030).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163030).length < 2 ^ (prefixWord ++ tailWord_163030).sum := by decide
  have hdescent : baseEnd_163030 < baseStart_163030 := by decide
  rcases family_descends (prefixWord ++ tailWord_163030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163032 : List Nat := [2, 1, 2, 2, 6, 1, 2, 3]
def baseStart_163032 : Nat := 118140960795 + 163032 * 2 ^ 59
def prefixEnd_163032 : Nat := 4983230072969 + 3 ^ 40 * 163032 * 2
def baseEnd_163032 : Nat := 49608164778614145333473

theorem tailTrace_163032 : CollatzResearch.WordTrace tailWord_163032 prefixEnd_163032 49608164778614145333473 := by
  unfold tailWord_163032
  simp only [CollatzResearch.WordTrace]
  refine ⟨2973132772685191246981675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3964177030246921662642233 2973132772685191246981675)
  ·
    refine ⟨4459699159027786870472513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2973132772685191246981675 4459699159027786870472513)
    ·
      refine ⟨3344774369270840152854385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4459699159027786870472513 3344774369270840152854385)
      ·
        refine ⟨2508580776953130114640789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3344774369270840152854385 2508580776953130114640789)
        ·
          refine ⟨117589723919677974123787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 2508580776953130114640789 117589723919677974123787)
          ·
            refine ⟨176384585879516961185681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117589723919677974123787 176384585879516961185681)
            ·
              refine ⟨132288439409637720889261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 176384585879516961185681 132288439409637720889261)
              ·
                refine ⟨49608164778614145333473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 132288439409637720889261 49608164778614145333473)
                ·
                  rfl

theorem cell19_163032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 2, 3].length) (baseStart_163032 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_163032 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_163032 prefixEnd_163032 := by exact prefixLift 163032
  have htrace : WordTrace (prefixWord ++ tailWord_163032) baseStart_163032 baseEnd_163032 := by
    simpa [prefixWord, tailWord_163032, baseEnd_163032] using wordTrace_append hprefix tailTrace_163032
  have hstable : (prefixWord ++ tailWord_163032).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163032).length < 2 ^ (prefixWord ++ tailWord_163032).sum := by decide
  have hdescent : baseEnd_163032 < baseStart_163032 := by decide
  rcases family_descends (prefixWord ++ tailWord_163032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163055 : List Nat := [1, 1, 2, 1, 7, 2, 5]
def baseStart_163055 : Nat := 118140960795 + 163055 * 2 ^ 59
def prefixEnd_163055 : Nat := 4983230072969 + 3 ^ 40 * 163055 * 2
def baseEnd_163055 : Nat := 16538387776585635607433

theorem tailTrace_163055 : CollatzResearch.WordTrace tailWord_163055 prefixEnd_163055 16538387776585635607433 := by
  unfold tailWord_163055
  simp only [CollatzResearch.WordTrace]
  refine ⟨5947104424287057422050619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3964736282858038281367079 5947104424287057422050619)
  ·
    refine ⟨8920656636430586133075929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5947104424287057422050619 8920656636430586133075929)
    ·
      refine ⟨6690492477322939599806947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8920656636430586133075929 6690492477322939599806947)
      ·
        refine ⟨10035738715984409399710421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6690492477322939599806947 10035738715984409399710421)
        ·
          refine ⟨235212626155884595305713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 10035738715984409399710421 235212626155884595305713)
          ·
            refine ⟨176409469616913446479285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 235212626155884595305713 176409469616913446479285)
            ·
              refine ⟨16538387776585635607433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 176409469616913446479285 16538387776585635607433)
              ·
                rfl

theorem cell19_163055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 5].length) (baseStart_163055 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_163055 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_163055 prefixEnd_163055 := by exact prefixLift 163055
  have htrace : WordTrace (prefixWord ++ tailWord_163055) baseStart_163055 baseEnd_163055 := by
    simpa [prefixWord, tailWord_163055, baseEnd_163055] using wordTrace_append hprefix tailTrace_163055
  have hstable : (prefixWord ++ tailWord_163055).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163055).length < 2 ^ (prefixWord ++ tailWord_163055).sum := by decide
  have hdescent : baseEnd_163055 < baseStart_163055 := by decide
  rcases family_descends (prefixWord ++ tailWord_163055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163095 : List Nat := [1, 1, 3, 4, 1, 1, 1, 7]
def baseStart_163095 : Nat := 118140960795 + 163095 * 2 ^ 59
def prefixEnd_163095 : Nat := 4983230072969 + 3 ^ 40 * 163095 * 2
def baseEnd_163095 : Nat := 49627334723048665933301

theorem tailTrace_163095 : CollatzResearch.WordTrace tailWord_163095 prefixEnd_163095 49627334723048665933301 := by
  unfold tailWord_163095
  simp only [CollatzResearch.WordTrace]
  refine ⟨5948563344142144253506739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3965708896094762835671159 5948563344142144253506739)
  ·
    refine ⟨8922845016213216380260109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5948563344142144253506739 8922845016213216380260109)
    ·
      refine ⟨3346066881079956142597541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8922845016213216380260109 3346066881079956142597541)
      ·
        refine ⟨627387540202491776737039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3346066881079956142597541 627387540202491776737039)
        ·
          refine ⟨941081310303737665105559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 627387540202491776737039 941081310303737665105559)
          ·
            refine ⟨1411621965455606497658339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 941081310303737665105559 1411621965455606497658339)
            ·
              refine ⟨2117432948183409746487509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1411621965455606497658339 2117432948183409746487509)
              ·
                refine ⟨49627334723048665933301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2117432948183409746487509 49627334723048665933301)
                ·
                  rfl

theorem cell19_163095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 7].length) (baseStart_163095 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_163095 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_163095 prefixEnd_163095 := by exact prefixLift 163095
  have htrace : WordTrace (prefixWord ++ tailWord_163095) baseStart_163095 baseEnd_163095 := by
    simpa [prefixWord, tailWord_163095, baseEnd_163095] using wordTrace_append hprefix tailTrace_163095
  have hstable : (prefixWord ++ tailWord_163095).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163095).length < 2 ^ (prefixWord ++ tailWord_163095).sum := by decide
  have hdescent : baseEnd_163095 < baseStart_163095 := by decide
  rcases family_descends (prefixWord ++ tailWord_163095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163129 : List Nat := [1, 2, 1, 6, 2, 2, 1, 4]
def baseStart_163129 : Nat := 118140960795 + 163129 * 2 ^ 59
def prefixEnd_163129 : Nat := 4983230072969 + 3 ^ 40 * 163129 * 2
def baseEnd_163129 : Nat := 49637680407346661177653

theorem tailTrace_163129 : CollatzResearch.WordTrace tailWord_163129 prefixEnd_163129 49637680407346661177653 := by
  unfold tailWord_163129
  simp only [CollatzResearch.WordTrace]
  refine ⟨5949803426018968060244441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3966535617345978706829627 5949803426018968060244441)
  ·
    refine ⟨4462352569514226045183331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5949803426018968060244441 4462352569514226045183331)
    ·
      refine ⟨6693528854271339067774997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4462352569514226045183331 6693528854271339067774997)
      ·
        refine ⟨313759165043969018801953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 6693528854271339067774997 313759165043969018801953)
        ·
          refine ⟨235319373782976764101465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 313759165043969018801953 235319373782976764101465)
          ·
            refine ⟨176489530337232573076099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 235319373782976764101465 176489530337232573076099)
            ·
              refine ⟨264734295505848859614149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 176489530337232573076099 264734295505848859614149)
              ·
                refine ⟨49637680407346661177653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 264734295505848859614149 49637680407346661177653)
                ·
                  rfl

theorem cell19_163129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 1, 4].length) (baseStart_163129 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_163129 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_163129 prefixEnd_163129 := by exact prefixLift 163129
  have htrace : WordTrace (prefixWord ++ tailWord_163129) baseStart_163129 baseEnd_163129 := by
    simpa [prefixWord, tailWord_163129, baseEnd_163129] using wordTrace_append hprefix tailTrace_163129
  have hstable : (prefixWord ++ tailWord_163129).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163129).length < 2 ^ (prefixWord ++ tailWord_163129).sum := by decide
  have hdescent : baseEnd_163129 < baseStart_163129 := by decide
  rcases family_descends (prefixWord ++ tailWord_163129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163150 : List Nat := [4, 1, 1, 1, 1, 1, 7, 3]
def baseStart_163150 : Nat := 118140960795 + 163150 * 2 ^ 59
def prefixEnd_163150 : Nat := 4983230072969 + 3 ^ 40 * 163150 * 2
def baseEnd_163150 : Nat := 49644070388824834710929

theorem tailTrace_163150 : CollatzResearch.WordTrace tailWord_163150 prefixEnd_163150 49644070388824834710929 := by
  unfold tailWord_163150
  simp only [CollatzResearch.WordTrace]
  refine ⟨743821169867861080844863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3967046239295259097839269 743821169867861080844863)
  ·
    refine ⟨1115731754801791621267295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 743821169867861080844863 1115731754801791621267295)
    ·
      refine ⟨1673597632202687431900943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1115731754801791621267295 1673597632202687431900943)
      ·
        refine ⟨2510396448304031147851415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1673597632202687431900943 2510396448304031147851415)
        ·
          refine ⟨3765594672456046721777123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2510396448304031147851415 3765594672456046721777123)
          ·
            refine ⟨5648392008684070082665685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3765594672456046721777123 5648392008684070082665685)
            ·
              refine ⟨132384187703532892562477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 5648392008684070082665685 132384187703532892562477)
              ·
                refine ⟨49644070388824834710929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 132384187703532892562477 49644070388824834710929)
                ·
                  rfl

theorem cell19_163150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 7, 3].length) (baseStart_163150 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_163150 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_163150 prefixEnd_163150 := by exact prefixLift 163150
  have htrace : WordTrace (prefixWord ++ tailWord_163150) baseStart_163150 baseEnd_163150 := by
    simpa [prefixWord, tailWord_163150, baseEnd_163150] using wordTrace_append hprefix tailTrace_163150
  have hstable : (prefixWord ++ tailWord_163150).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163150).length < 2 ^ (prefixWord ++ tailWord_163150).sum := by decide
  have hdescent : baseEnd_163150 < baseStart_163150 := by decide
  rcases family_descends (prefixWord ++ tailWord_163150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163165 : List Nat := [1, 4, 5, 1, 1, 1, 6]
def baseStart_163165 : Nat := 118140960795 + 163165 * 2 ^ 59
def prefixEnd_163165 : Nat := 4983230072969 + 3 ^ 40 * 163165 * 2
def baseEnd_163165 : Nat := 16549544887103081459185

theorem tailTrace_163165 : CollatzResearch.WordTrace tailWord_163165 prefixEnd_163165 16549544887103081459185 := by
  unfold tailWord_163165
  simp only [CollatzResearch.WordTrace]
  refine ⟨5951116453888546208554949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3967410969259030805703299 5951116453888546208554949)
  ·
    refine ⟨1115834335104102414104053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5951116453888546208554949 1115834335104102414104053)
    ·
      refine ⟨104609468916009601322255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1115834335104102414104053 104609468916009601322255)
      ·
        refine ⟨156914203374014401983383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104609468916009601322255 156914203374014401983383)
        ·
          refine ⟨235371305061021602975075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156914203374014401983383 235371305061021602975075)
          ·
            refine ⟨353056957591532404462613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 235371305061021602975075 353056957591532404462613)
            ·
              refine ⟨16549544887103081459185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 353056957591532404462613 16549544887103081459185)
              ·
                rfl

theorem cell19_163165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 6].length) (baseStart_163165 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_163165 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_163165 prefixEnd_163165 := by exact prefixLift 163165
  have htrace : WordTrace (prefixWord ++ tailWord_163165) baseStart_163165 baseEnd_163165 := by
    simpa [prefixWord, tailWord_163165, baseEnd_163165] using wordTrace_append hprefix tailTrace_163165
  have hstable : (prefixWord ++ tailWord_163165).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163165).length < 2 ^ (prefixWord ++ tailWord_163165).sum := by decide
  have hdescent : baseEnd_163165 < baseStart_163165 := by decide
  rcases family_descends (prefixWord ++ tailWord_163165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163171 : List Nat := [1, 1, 1, 5, 2, 3, 6]
def baseStart_163171 : Nat := 118140960795 + 163171 * 2 ^ 59
def prefixEnd_163171 : Nat := 4983230072969 + 3 ^ 40 * 163171 * 2
def baseEnd_163171 : Nat := 16550153456767669414735

theorem tailTrace_163171 : CollatzResearch.WordTrace tailWord_163171 prefixEnd_163171 16550153456767669414735 := by
  unfold tailWord_163171
  simp only [CollatzResearch.WordTrace]
  refine ⟨5951335291866809233273367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3967556861244539488848911 5951335291866809233273367)
  ·
    refine ⟨8927002937800213849910051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5951335291866809233273367 8927002937800213849910051)
    ·
      refine ⟨13390504406700320774865077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8927002937800213849910051 13390504406700320774865077)
      ·
        refine ⟨1255359788128155072643601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13390504406700320774865077 1255359788128155072643601)
        ·
          refine ⟨941519841096116304482701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1255359788128155072643601 941519841096116304482701)
          ·
            refine ⟨353069940411043614181013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 941519841096116304482701 353069940411043614181013)
            ·
              refine ⟨16550153456767669414735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 353069940411043614181013 16550153456767669414735)
              ·
                rfl

theorem cell19_163171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 6].length) (baseStart_163171 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_163171 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_163171 prefixEnd_163171 := by exact prefixLift 163171
  have htrace : WordTrace (prefixWord ++ tailWord_163171) baseStart_163171 baseEnd_163171 := by
    simpa [prefixWord, tailWord_163171, baseEnd_163171] using wordTrace_append hprefix tailTrace_163171
  have hstable : (prefixWord ++ tailWord_163171).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163171).length < 2 ^ (prefixWord ++ tailWord_163171).sum := by decide
  have hdescent : baseEnd_163171 < baseStart_163171 := by decide
  rcases family_descends (prefixWord ++ tailWord_163171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163207 : List Nat := [1, 1, 4, 2, 2, 2, 4, 3]
def baseStart_163207 : Nat := 118140960795 + 163207 * 2 ^ 59
def prefixEnd_163207 : Nat := 4983230072969 + 3 ^ 40 * 163207 * 2
def baseEnd_163207 : Nat := 49661414624265591444107

theorem tailTrace_163207 : CollatzResearch.WordTrace tailWord_163207 prefixEnd_163207 49661414624265591444107 := by
  unfold tailWord_163207
  simp only [CollatzResearch.WordTrace]
  refine ⟨5952648319736387381583875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3968432213157591587722583 5952648319736387381583875)
  ·
    refine ⟨8928972479604581072375813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5952648319736387381583875 8928972479604581072375813)
    ·
      refine ⟨1674182339925858951070465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8928972479604581072375813 1674182339925858951070465)
      ·
        refine ⟨1255636754944394213302849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1674182339925858951070465 1255636754944394213302849)
        ·
          refine ⟨941727566208295659977137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1255636754944394213302849 941727566208295659977137)
          ·
            refine ⟨706295674656221744982853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 941727566208295659977137 706295674656221744982853)
            ·
              refine ⟨132430438998041577184285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 706295674656221744982853 132430438998041577184285)
              ·
                refine ⟨49661414624265591444107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 132430438998041577184285 49661414624265591444107)
                ·
                  rfl

theorem cell19_163207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 4, 3].length) (baseStart_163207 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_163207 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_163207 prefixEnd_163207 := by exact prefixLift 163207
  have htrace : WordTrace (prefixWord ++ tailWord_163207) baseStart_163207 baseEnd_163207 := by
    simpa [prefixWord, tailWord_163207, baseEnd_163207] using wordTrace_append hprefix tailTrace_163207
  have hstable : (prefixWord ++ tailWord_163207).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163207).length < 2 ^ (prefixWord ++ tailWord_163207).sum := by decide
  have hdescent : baseEnd_163207 < baseStart_163207 := by decide
  rcases family_descends (prefixWord ++ tailWord_163207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163224 : List Nat := [2, 1, 2, 5, 3, 1, 5]
def baseStart_163224 : Nat := 118140960795 + 163224 * 2 ^ 59
def prefixEnd_163224 : Nat := 4983230072969 + 3 ^ 40 * 163224 * 2
def baseEnd_163224 : Nat := 16555529155471529688761

theorem tailTrace_163224 : CollatzResearch.WordTrace tailWord_163224 prefixEnd_163224 16555529155471529688761 := by
  unfold tailWord_163224
  simp only [CollatzResearch.WordTrace]
  refine ⟨2976634180337399642476363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3968845573783199523301817 2976634180337399642476363)
  ·
    refine ⟨4464951270506099463714545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2976634180337399642476363 4464951270506099463714545)
    ·
      refine ⟨3348713452879574597785909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4464951270506099463714545 3348713452879574597785909)
      ·
        refine ⟨313941886207460118542429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3348713452879574597785909 313941886207460118542429)
        ·
          refine ⟨117728207327797544453411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 313941886207460118542429 117728207327797544453411)
          ·
            refine ⟨176592310991696316680117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117728207327797544453411 176592310991696316680117)
            ·
              refine ⟨16555529155471529688761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 176592310991696316680117 16555529155471529688761)
              ·
                rfl

theorem cell19_163224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 5].length) (baseStart_163224 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_163224 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_163224 prefixEnd_163224 := by exact prefixLift 163224
  have htrace : WordTrace (prefixWord ++ tailWord_163224) baseStart_163224 baseEnd_163224 := by
    simpa [prefixWord, tailWord_163224, baseEnd_163224] using wordTrace_append hprefix tailTrace_163224
  have hstable : (prefixWord ++ tailWord_163224).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163224).length < 2 ^ (prefixWord ++ tailWord_163224).sum := by decide
  have hdescent : baseEnd_163224 < baseStart_163224 := by decide
  rcases family_descends (prefixWord ++ tailWord_163224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163245 : List Nat := [1, 5, 2, 2, 1, 1, 1, 6]
def baseStart_163245 : Nat := 118140960795 + 163245 * 2 ^ 59
def prefixEnd_163245 : Nat := 4983230072969 + 3 ^ 40 * 163245 * 2
def baseEnd_163245 : Nat := 49672977447892762599559

theorem tailTrace_163245 : CollatzResearch.WordTrace tailWord_163245 prefixEnd_163245 49672977447892762599559 := by
  unfold tailWord_163245
  simp only [CollatzResearch.WordTrace]
  refine ⟨5954034293598719871467189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3969356195732479914311459 5954034293598719871467189)
  ·
    refine ⟨558190715024879987950049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5954034293598719871467189 558190715024879987950049)
    ·
      refine ⟨418643036268659990962537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 558190715024879987950049 418643036268659990962537)
      ·
        refine ⟨313982277201494993221903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 418643036268659990962537 313982277201494993221903)
        ·
          refine ⟨470973415802242489832855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 313982277201494993221903 470973415802242489832855)
          ·
            refine ⟨706460123703363734749283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 470973415802242489832855 706460123703363734749283)
            ·
              refine ⟨1059690185555045602123925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 706460123703363734749283 1059690185555045602123925)
              ·
                refine ⟨49672977447892762599559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1059690185555045602123925 49672977447892762599559)
                ·
                  rfl

theorem cell19_163245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 6].length) (baseStart_163245 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_163245 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_163245 prefixEnd_163245 := by exact prefixLift 163245
  have htrace : WordTrace (prefixWord ++ tailWord_163245) baseStart_163245 baseEnd_163245 := by
    simpa [prefixWord, tailWord_163245, baseEnd_163245] using wordTrace_append hprefix tailTrace_163245
  have hstable : (prefixWord ++ tailWord_163245).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163245).length < 2 ^ (prefixWord ++ tailWord_163245).sum := by decide
  have hdescent : baseEnd_163245 < baseStart_163245 := by decide
  rcases family_descends (prefixWord ++ tailWord_163245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163492 : List Nat := [2, 3, 1, 2, 2, 3, 3, 3]
def baseStart_163492 : Nat := 118140960795 + 163492 * 2 ^ 59
def prefixEnd_163492 : Nat := 4983230072969 + 3 ^ 40 * 163492 * 2
def baseEnd_163492 : Nat := 49748135801469375109997

theorem tailTrace_163492 : CollatzResearch.WordTrace tailWord_163492 prefixEnd_163492 49748135801469375109997 := by
  unfold tailWord_163492
  simp only [CollatzResearch.WordTrace]
  refine ⟨2981521561851940527854365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3975362082469254037139153 2981521561851940527854365)
  ·
    refine ⟨1118070585694477697945387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2981521561851940527854365 1118070585694477697945387)
    ·
      refine ⟨1677105878541716546918081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1118070585694477697945387 1677105878541716546918081)
      ·
        refine ⟨1257829408906287410188561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1677105878541716546918081 1257829408906287410188561)
        ·
          refine ⟨943372056679715557641421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1257829408906287410188561 943372056679715557641421)
          ·
            refine ⟨353764521254893334115533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 943372056679715557641421 353764521254893334115533)
            ·
              refine ⟨132661695470585000293325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 353764521254893334115533 132661695470585000293325)
              ·
                refine ⟨49748135801469375109997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 132661695470585000293325 49748135801469375109997)
                ·
                  rfl

theorem cell19_163492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 3, 3].length) (baseStart_163492 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_163492 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_163492 prefixEnd_163492 := by exact prefixLift 163492
  have htrace : WordTrace (prefixWord ++ tailWord_163492) baseStart_163492 baseEnd_163492 := by
    simpa [prefixWord, tailWord_163492, baseEnd_163492] using wordTrace_append hprefix tailTrace_163492
  have hstable : (prefixWord ++ tailWord_163492).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163492).length < 2 ^ (prefixWord ++ tailWord_163492).sum := by decide
  have hdescent : baseEnd_163492 < baseStart_163492 := by decide
  rcases family_descends (prefixWord ++ tailWord_163492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163661 : List Nat := [1, 6, 1, 2, 1, 2, 3, 3]
def baseStart_163661 : Nat := 118140960795 + 163661 * 2 ^ 59
def prefixEnd_163661 : Nat := 4983230072969 + 3 ^ 40 * 163661 * 2
def baseEnd_163661 : Nat := 49799559938127057353981

theorem tailTrace_163661 : CollatzResearch.WordTrace tailWord_163661 prefixEnd_163661 49799559938127057353981 := by
  unfold tailWord_163661
  simp only [CollatzResearch.WordTrace]
  refine ⟨5969207060091622918610837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3979471373394415279073891 5969207060091622918610837)
  ·
    refine ⟨279806580941794824309883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 5969207060091622918610837 279806580941794824309883)
    ·
      refine ⟨419709871412692236464825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 279806580941794824309883 419709871412692236464825)
      ·
        refine ⟨314782403559519177348619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 419709871412692236464825 314782403559519177348619)
        ·
          refine ⟨472173605339278766022929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 314782403559519177348619 472173605339278766022929)
          ·
            refine ⟨354130204004459074517197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 472173605339278766022929 354130204004459074517197)
            ·
              refine ⟨132798826501672152943949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 354130204004459074517197 132798826501672152943949)
              ·
                refine ⟨49799559938127057353981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 132798826501672152943949 49799559938127057353981)
                ·
                  rfl

theorem cell19_163661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 3, 3].length) (baseStart_163661 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_163661 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_163661 prefixEnd_163661 := by exact prefixLift 163661
  have htrace : WordTrace (prefixWord ++ tailWord_163661) baseStart_163661 baseEnd_163661 := by
    simpa [prefixWord, tailWord_163661, baseEnd_163661] using wordTrace_append hprefix tailTrace_163661
  have hstable : (prefixWord ++ tailWord_163661).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163661).length < 2 ^ (prefixWord ++ tailWord_163661).sum := by decide
  have hdescent : baseEnd_163661 < baseStart_163661 := by decide
  rcases family_descends (prefixWord ++ tailWord_163661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163684 : List Nat := [2, 3, 1, 1, 5, 1, 6]
def baseStart_163684 : Nat := 118140960795 + 163684 * 2 ^ 59
def prefixEnd_163684 : Nat := 4983230072969 + 3 ^ 40 * 163684 * 2
def baseEnd_163684 : Nat := 16602186163089939614269

theorem tailTrace_163684 : CollatzResearch.WordTrace tailWord_163684 prefixEnd_163684 16602186163089939614269 := by
  unfold tailWord_163684
  simp only [CollatzResearch.WordTrace]
  refine ⟨2985022969504148923349053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3980030626005531897798737 2985022969504148923349053)
  ·
    refine ⟨1119383613564055846255895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2985022969504148923349053 1119383613564055846255895)
    ·
      refine ⟨1679075420346083769383843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1119383613564055846255895 1679075420346083769383843)
      ·
        refine ⟨2518613130519125654075765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1679075420346083769383843 2518613130519125654075765)
        ·
          refine ⟨236119980986168030069603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2518613130519125654075765 236119980986168030069603)
          ·
            refine ⟨354179971479252045104405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 236119980986168030069603 354179971479252045104405)
            ·
              refine ⟨16602186163089939614269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 354179971479252045104405 16602186163089939614269)
              ·
                rfl

theorem cell19_163684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 6].length) (baseStart_163684 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_163684 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_163684 prefixEnd_163684 := by exact prefixLift 163684
  have htrace : WordTrace (prefixWord ++ tailWord_163684) baseStart_163684 baseEnd_163684 := by
    simpa [prefixWord, tailWord_163684, baseEnd_163684] using wordTrace_append hprefix tailTrace_163684
  have hstable : (prefixWord ++ tailWord_163684).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163684).length < 2 ^ (prefixWord ++ tailWord_163684).sum := by decide
  have hdescent : baseEnd_163684 < baseStart_163684 := by decide
  rcases family_descends (prefixWord ++ tailWord_163684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163705 : List Nat := [1, 2, 1, 3, 2, 2, 2, 6]
def baseStart_163705 : Nat := 118140960795 + 163705 * 2 ^ 59
def prefixEnd_163705 : Nat := 4983230072969 + 3 ^ 40 * 163705 * 2
def baseEnd_163705 : Nat := 49812948470747992376083

theorem tailTrace_163705 : CollatzResearch.WordTrace tailWord_163705 prefixEnd_163705 49812948470747992376083 := by
  unfold tailWord_163705
  simp only [CollatzResearch.WordTrace]
  refine ⟨5970811871932218433212569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3980541247954812288808379 5970811871932218433212569)
  ·
    refine ⟨4478108903949163824909427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5970811871932218433212569 4478108903949163824909427)
    ·
      refine ⟨6717163355923745737364141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4478108903949163824909427 6717163355923745737364141)
      ·
        refine ⟨2518936258471404651511553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6717163355923745737364141 2518936258471404651511553)
        ·
          refine ⟨1889202193853553488633665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2518936258471404651511553 1889202193853553488633665)
          ·
            refine ⟨1416901645390165116475249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1889202193853553488633665 1416901645390165116475249)
            ·
              refine ⟨1062676234042623837356437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1416901645390165116475249 1062676234042623837356437)
              ·
                refine ⟨49812948470747992376083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1062676234042623837356437 49812948470747992376083)
                ·
                  rfl

theorem cell19_163705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 6].length) (baseStart_163705 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_163705 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_163705 prefixEnd_163705 := by exact prefixLift 163705
  have htrace : WordTrace (prefixWord ++ tailWord_163705) baseStart_163705 baseEnd_163705 := by
    simpa [prefixWord, tailWord_163705, baseEnd_163705] using wordTrace_append hprefix tailTrace_163705
  have hstable : (prefixWord ++ tailWord_163705).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163705).length < 2 ^ (prefixWord ++ tailWord_163705).sum := by decide
  have hdescent : baseEnd_163705 < baseStart_163705 := by decide
  rcases family_descends (prefixWord ++ tailWord_163705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163741 : List Nat := [1, 4, 2, 1, 2, 4, 5]
def baseStart_163741 : Nat := 118140960795 + 163741 * 2 ^ 59
def prefixEnd_163741 : Nat := 4983230072969 + 3 ^ 40 * 163741 * 2
def baseEnd_163741 : Nat := 16607967574903525191995

theorem tailTrace_163741 : CollatzResearch.WordTrace tailWord_163741 prefixEnd_163741 16607967574903525191995 := by
  unfold tailWord_163741
  simp only [CollatzResearch.WordTrace]
  refine ⟨5972124899801796581523077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3981416599867864387682051 5972124899801796581523077)
  ·
    refine ⟨1119773418712836859035577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5972124899801796581523077 1119773418712836859035577)
    ·
      refine ⟨839830064034627644276683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1119773418712836859035577 839830064034627644276683)
      ·
        refine ⟨1259745096051941466415025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 839830064034627644276683 1259745096051941466415025)
        ·
          refine ⟨944808822038956099811269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1259745096051941466415025 944808822038956099811269)
          ·
            refine ⟨177151654132304268714613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 944808822038956099811269 177151654132304268714613)
            ·
              refine ⟨16607967574903525191995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 177151654132304268714613 16607967574903525191995)
              ·
                rfl

theorem cell19_163741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 5].length) (baseStart_163741 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_163741 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_163741 prefixEnd_163741 := by exact prefixLift 163741
  have htrace : WordTrace (prefixWord ++ tailWord_163741) baseStart_163741 baseEnd_163741 := by
    simpa [prefixWord, tailWord_163741, baseEnd_163741] using wordTrace_append hprefix tailTrace_163741
  have hstable : (prefixWord ++ tailWord_163741).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163741).length < 2 ^ (prefixWord ++ tailWord_163741).sum := by decide
  have hdescent : baseEnd_163741 < baseStart_163741 := by decide
  rcases family_descends (prefixWord ++ tailWord_163741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163798 : List Nat := [5, 2, 1, 1, 10]
def baseStart_163798 : Nat := 118140960795 + 163798 * 2 ^ 59
def prefixEnd_163798 : Nat := 4983230072969 + 3 ^ 40 * 163798 * 2
def baseEnd_163798 : Nat := 1845972109635234529969

theorem tailTrace_163798 : CollatzResearch.WordTrace tailWord_163798 prefixEnd_163798 1845972109635234529969 := by
  unfold tailWord_163798
  simp only [CollatzResearch.WordTrace]
  refine ⟨373387741287205957271753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3982802573730196877565365 373387741287205957271753)
  ·
    refine ⟨280040805965404467953815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 373387741287205957271753 280040805965404467953815)
    ·
      refine ⟨420061208948106701930723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 280040805965404467953815 420061208948106701930723)
      ·
        refine ⟨630091813422160052896085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 420061208948106701930723 630091813422160052896085)
        ·
          refine ⟨1845972109635234529969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 630091813422160052896085 1845972109635234529969)
          ·
            rfl

theorem cell19_163798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 10].length) (baseStart_163798 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_163798 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_163798 prefixEnd_163798 := by exact prefixLift 163798
  have htrace : WordTrace (prefixWord ++ tailWord_163798) baseStart_163798 baseEnd_163798 := by
    simpa [prefixWord, tailWord_163798, baseEnd_163798] using wordTrace_append hprefix tailTrace_163798
  have hstable : (prefixWord ++ tailWord_163798).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163798).length < 2 ^ (prefixWord ++ tailWord_163798).sum := by decide
  have hdescent : baseEnd_163798 < baseStart_163798 := by decide
  rcases family_descends (prefixWord ++ tailWord_163798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163815 : List Nat := [1, 1, 5, 2, 3, 2, 1, 4]
def baseStart_163815 : Nat := 118140960795 + 163815 * 2 ^ 59
def prefixEnd_163815 : Nat := 4983230072969 + 3 ^ 40 * 163815 * 2
def baseEnd_163815 : Nat := 49846419802300329931339

theorem tailTrace_163815 : CollatzResearch.WordTrace tailWord_163815 prefixEnd_163815 49846419802300329931339 := by
  unfold tailWord_163815
  simp only [CollatzResearch.WordTrace]
  refine ⟨5974823901533707219716899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3983215934355804813144599 5974823901533707219716899)
  ·
    refine ⟨8962235852300560829575349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5974823901533707219716899 8962235852300560829575349)
    ·
      refine ⟨840209611153177577772689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8962235852300560829575349 840209611153177577772689)
      ·
        refine ⟨630157208364883183329517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 840209611153177577772689 630157208364883183329517)
        ·
          refine ⟨236308953136831193748569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 630157208364883183329517 236308953136831193748569)
          ·
            refine ⟨177231714852623395311427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 236308953136831193748569 177231714852623395311427)
            ·
              refine ⟨265847572278935092967141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 177231714852623395311427 265847572278935092967141)
              ·
                refine ⟨49846419802300329931339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 265847572278935092967141 49846419802300329931339)
                ·
                  rfl

theorem cell19_163815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 1, 4].length) (baseStart_163815 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_163815 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_163815 prefixEnd_163815 := by exact prefixLift 163815
  have htrace : WordTrace (prefixWord ++ tailWord_163815) baseStart_163815 baseEnd_163815 := by
    simpa [prefixWord, tailWord_163815, baseEnd_163815] using wordTrace_append hprefix tailTrace_163815
  have hstable : (prefixWord ++ tailWord_163815).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163815).length < 2 ^ (prefixWord ++ tailWord_163815).sum := by decide
  have hdescent : baseEnd_163815 < baseStart_163815 := by decide
  rcases family_descends (prefixWord ++ tailWord_163815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163836 : List Nat := [2, 2, 2, 1, 2, 2, 5, 3]
def baseStart_163836 : Nat := 118140960795 + 163836 * 2 ^ 59
def prefixEnd_163836 : Nat := 4983230072969 + 3 ^ 40 * 163836 * 2
def baseEnd_163836 : Nat := 49852809783778503464615

theorem tailTrace_163836 : CollatzResearch.WordTrace tailWord_163836 prefixEnd_163836 49852809783778503464615 := by
  unfold tailWord_163836
  simp only [CollatzResearch.WordTrace]
  refine ⟨2987794917228813903115681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3983726556305085204154241 2987794917228813903115681)
  ·
    refine ⟨2240846187921610427336761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2987794917228813903115681 2240846187921610427336761)
    ·
      refine ⟨1680634640941207820502571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2240846187921610427336761 1680634640941207820502571)
      ·
        refine ⟨2520951961411811730753857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1680634640941207820502571 2520951961411811730753857)
        ·
          refine ⟨1890713971058858798065393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2520951961411811730753857 1890713971058858798065393)
          ·
            refine ⟨1418035478294144098549045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1890713971058858798065393 1418035478294144098549045)
            ·
              refine ⟨132940826090076009238973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1418035478294144098549045 132940826090076009238973)
              ·
                refine ⟨49852809783778503464615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 132940826090076009238973 49852809783778503464615)
                ·
                  rfl

theorem cell19_163836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 5, 3].length) (baseStart_163836 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_163836 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_163836 prefixEnd_163836 := by exact prefixLift 163836
  have htrace : WordTrace (prefixWord ++ tailWord_163836) baseStart_163836 baseEnd_163836 := by
    simpa [prefixWord, tailWord_163836, baseEnd_163836] using wordTrace_append hprefix tailTrace_163836
  have hstable : (prefixWord ++ tailWord_163836).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163836).length < 2 ^ (prefixWord ++ tailWord_163836).sum := by decide
  have hdescent : baseEnd_163836 < baseStart_163836 := by decide
  rcases family_descends (prefixWord ++ tailWord_163836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163893 : List Nat := [1, 3, 3, 1, 1, 1, 6, 3]
def baseStart_163893 : Nat := 118140960795 + 163893 * 2 ^ 59
def prefixEnd_163893 : Nat := 4983230072969 + 3 ^ 40 * 163893 * 2
def baseEnd_163893 : Nat := 49870154019219260197793

theorem tailTrace_163893 : CollatzResearch.WordTrace tailWord_163893 prefixEnd_163893 49870154019219260197793 := by
  unfold tailWord_163893
  simp only [CollatzResearch.WordTrace]
  refine ⟨5977668795251126541056333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3985112530167417694037555 5977668795251126541056333)
  ·
    refine ⟨2241625798219172452896125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5977668795251126541056333 2241625798219172452896125)
    ·
      refine ⟨840609674332189669836047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2241625798219172452896125 840609674332189669836047)
      ·
        refine ⟨1260914511498284504754071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 840609674332189669836047 1260914511498284504754071)
        ·
          refine ⟨1891371767247426757131107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1260914511498284504754071 1891371767247426757131107)
          ·
            refine ⟨2837057650871140135696661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1891371767247426757131107 2837057650871140135696661)
            ·
              refine ⟨132987077384584693860781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 2837057650871140135696661 132987077384584693860781)
              ·
                refine ⟨49870154019219260197793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 132987077384584693860781 49870154019219260197793)
                ·
                  rfl

theorem cell19_163893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 6, 3].length) (baseStart_163893 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_163893 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_163893 prefixEnd_163893 := by exact prefixLift 163893
  have htrace : WordTrace (prefixWord ++ tailWord_163893) baseStart_163893 baseEnd_163893 := by
    simpa [prefixWord, tailWord_163893, baseEnd_163893] using wordTrace_append hprefix tailTrace_163893
  have hstable : (prefixWord ++ tailWord_163893).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163893).length < 2 ^ (prefixWord ++ tailWord_163893).sum := by decide
  have hdescent : baseEnd_163893 < baseStart_163893 := by decide
  rcases family_descends (prefixWord ++ tailWord_163893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163952 : List Nat := [2, 1, 1, 1, 5, 2, 2, 5]
def baseStart_163952 : Nat := 118140960795 + 163952 * 2 ^ 59
def prefixEnd_163952 : Nat := 4983230072969 + 3 ^ 40 * 163952 * 2
def baseEnd_163952 : Nat := 49888106824324604886521

theorem tailTrace_163952 : CollatzResearch.WordTrace tailWord_163952 prefixEnd_163952 49888106824324604886521 := by
  unfold tailWord_163952
  simp only [CollatzResearch.WordTrace]
  refine ⟨2989910351018689808727055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3986547134691586411636073 2989910351018689808727055)
  ·
    refine ⟨4484865526528034713090583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2989910351018689808727055 4484865526528034713090583)
    ·
      refine ⟨6727298289792052069635875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4484865526528034713090583 6727298289792052069635875)
      ·
        refine ⟨10090947434688078104453813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6727298289792052069635875 10090947434688078104453813)
        ·
          refine ⟨946026322002007322292545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10090947434688078104453813 946026322002007322292545)
          ·
            refine ⟨709519741501505491719409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 946026322002007322292545 709519741501505491719409)
            ·
              refine ⟨532139806126129118789557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 709519741501505491719409 532139806126129118789557)
              ·
                refine ⟨49888106824324604886521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 532139806126129118789557 49888106824324604886521)
                ·
                  rfl

theorem cell19_163952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 5].length) (baseStart_163952 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_163952 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_163952 prefixEnd_163952 := by exact prefixLift 163952
  have htrace : WordTrace (prefixWord ++ tailWord_163952) baseStart_163952 baseEnd_163952 := by
    simpa [prefixWord, tailWord_163952, baseEnd_163952] using wordTrace_append hprefix tailTrace_163952
  have hstable : (prefixWord ++ tailWord_163952).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163952).length < 2 ^ (prefixWord ++ tailWord_163952).sum := by decide
  have hdescent : baseEnd_163952 < baseStart_163952 := by decide
  rcases family_descends (prefixWord ++ tailWord_163952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163969 : List Nat := [1, 2, 4, 2, 4, 6]
def baseStart_163969 : Nat := 118140960795 + 163969 * 2 ^ 59
def prefixEnd_163969 : Nat := 4983230072969 + 3 ^ 40 * 163969 * 2
def baseEnd_163969 : Nat := 5543697740719289167633

theorem tailTrace_163969 : CollatzResearch.WordTrace tailWord_163969 prefixEnd_163969 5543697740719289167633 := by
  unfold tailWord_163969
  simp only [CollatzResearch.WordTrace]
  refine ⟨5980440742975791520822961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3986960495317194347215307 5980440742975791520822961)
  ·
    refine ⟨4485330557231843640617221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5980440742975791520822961 4485330557231843640617221)
    ·
      refine ⟨840999479480970682615729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4485330557231843640617221 840999479480970682615729)
      ·
        refine ⟨630749609610728011961797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 840999479480970682615729 630749609610728011961797)
        ·
          refine ⟨118265551802011502242837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 630749609610728011961797 118265551802011502242837)
          ·
            refine ⟨5543697740719289167633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 118265551802011502242837 5543697740719289167633)
            ·
              rfl

theorem cell19_163969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 6].length) (baseStart_163969 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_163969 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_163969 prefixEnd_163969 := by exact prefixLift 163969
  have htrace : WordTrace (prefixWord ++ tailWord_163969) baseStart_163969 baseEnd_163969 := by
    simpa [prefixWord, tailWord_163969, baseEnd_163969] using wordTrace_append hprefix tailTrace_163969
  have hstable : (prefixWord ++ tailWord_163969).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163969).length < 2 ^ (prefixWord ++ tailWord_163969).sum := by decide
  have hdescent : baseEnd_163969 < baseStart_163969 := by decide
  rcases family_descends (prefixWord ++ tailWord_163969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164104 : List Nat := [2, 1, 3, 2, 3, 1, 1, 6]
def baseStart_164104 : Nat := 118140960795 + 164104 * 2 ^ 59
def prefixEnd_164104 : Nat := 4983230072969 + 3 ^ 40 * 164104 * 2
def baseEnd_164104 : Nat := 49934358118833289508329

theorem tailTrace_164104 : CollatzResearch.WordTrace tailWord_164104 prefixEnd_164104 49934358118833289508329 := by
  unfold tailWord_164104
  simp only [CollatzResearch.WordTrace]
  refine ⟨2992682298743354788493683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3990243064991139717991577 2992682298743354788493683)
  ·
    refine ⟨4489023448115032182740525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2992682298743354788493683 4489023448115032182740525)
    ·
      refine ⟨1683383793043137068527697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4489023448115032182740525 1683383793043137068527697)
      ·
        refine ⟨1262537844782352801395773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1683383793043137068527697 1262537844782352801395773)
        ·
          refine ⟨473451691793382300523415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1262537844782352801395773 473451691793382300523415)
          ·
            refine ⟨710177537690073450785123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 473451691793382300523415 710177537690073450785123)
            ·
              refine ⟨1065266306535110176177685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 710177537690073450785123 1065266306535110176177685)
              ·
                refine ⟨49934358118833289508329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1065266306535110176177685 49934358118833289508329)
                ·
                  rfl

theorem cell19_164104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 6].length) (baseStart_164104 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_164104 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_164104 prefixEnd_164104 := by exact prefixLift 164104
  have htrace : WordTrace (prefixWord ++ tailWord_164104) baseStart_164104 baseEnd_164104 := by
    simpa [prefixWord, tailWord_164104, baseEnd_164104] using wordTrace_append hprefix tailTrace_164104
  have hstable : (prefixWord ++ tailWord_164104).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164104).length < 2 ^ (prefixWord ++ tailWord_164104).sum := by decide
  have hdescent : baseEnd_164104 < baseStart_164104 := by decide
  rcases family_descends (prefixWord ++ tailWord_164104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164199 : List Nat := [1, 1, 5, 1, 3, 2, 6]
def baseStart_164199 : Nat := 118140960795 + 164199 * 2 ^ 59
def prefixEnd_164199 : Nat := 4983230072969 + 3 ^ 40 * 164199 * 2
def baseEnd_164199 : Nat := 16654421725967072465653

theorem tailTrace_164199 : CollatzResearch.WordTrace tailWord_164199 prefixEnd_164199 16654421725967072465653 := by
  unfold tailWord_164199
  simp only [CollatzResearch.WordTrace]
  refine ⟨5988829532142540801695651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3992553021428360534463767 5988829532142540801695651)
  ·
    refine ⟨8983244298213811202543477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5988829532142540801695651 8983244298213811202543477)
    ·
      refine ⟨842179152957544800238451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8983244298213811202543477 842179152957544800238451)
      ·
        refine ⟨1263268729436317200357677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 842179152957544800238451 1263268729436317200357677)
        ·
          refine ⟨473725773538618950134129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1263268729436317200357677 473725773538618950134129)
          ·
            refine ⟨355294330153964212600597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 473725773538618950134129 355294330153964212600597)
            ·
              refine ⟨16654421725967072465653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 355294330153964212600597 16654421725967072465653)
              ·
                rfl

theorem cell19_164199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 6].length) (baseStart_164199 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_164199 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_164199 prefixEnd_164199 := by exact prefixLift 164199
  have htrace : WordTrace (prefixWord ++ tailWord_164199) baseStart_164199 baseEnd_164199 := by
    simpa [prefixWord, tailWord_164199, baseEnd_164199] using wordTrace_append hprefix tailTrace_164199
  have hstable : (prefixWord ++ tailWord_164199).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164199).length < 2 ^ (prefixWord ++ tailWord_164199).sum := by decide
  have hdescent : baseEnd_164199 < baseStart_164199 := by decide
  rcases family_descends (prefixWord ++ tailWord_164199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164201 : List Nat := [1, 2, 1, 1, 1, 3, 10]
def baseStart_164201 : Nat := 118140960795 + 164201 * 2 ^ 59
def prefixEnd_164201 : Nat := 4983230072969 + 3 ^ 40 * 164201 * 2
def baseEnd_164201 : Nat := 16654624582521935117503

theorem tailTrace_164201 : CollatzResearch.WordTrace tailWord_164201 prefixEnd_164201 16654624582521935117503 := by
  unfold tailWord_164201
  simp only [CollatzResearch.WordTrace]
  refine ⟨5988902478135295143268457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3992601652090196762178971 5988902478135295143268457)
  ·
    refine ⟨4491676858601471357451343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5988902478135295143268457 4491676858601471357451343)
    ·
      refine ⟨6737515287902207036177015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4491676858601471357451343 6737515287902207036177015)
      ·
        refine ⟨10106272931853310554265523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6737515287902207036177015 10106272931853310554265523)
        ·
          refine ⟨15159409397779965831398285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10106272931853310554265523 15159409397779965831398285)
          ·
            refine ⟨5684778524167487186774357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15159409397779965831398285 5684778524167487186774357)
            ·
              refine ⟨16654624582521935117503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 5684778524167487186774357 16654624582521935117503)
              ·
                rfl

theorem cell19_164201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 10].length) (baseStart_164201 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_164201 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_164201 prefixEnd_164201 := by exact prefixLift 164201
  have htrace : WordTrace (prefixWord ++ tailWord_164201) baseStart_164201 baseEnd_164201 := by
    simpa [prefixWord, tailWord_164201, baseEnd_164201] using wordTrace_append hprefix tailTrace_164201
  have hstable : (prefixWord ++ tailWord_164201).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164201).length < 2 ^ (prefixWord ++ tailWord_164201).sum := by decide
  have hdescent : baseEnd_164201 < baseStart_164201 := by decide
  rcases family_descends (prefixWord ++ tailWord_164201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164235 : List Nat := [1, 1, 1, 1, 4, 6, 2, 3]
def baseStart_164235 : Nat := 118140960795 + 164235 * 2 ^ 59
def prefixEnd_164235 : Nat := 4983230072969 + 3 ^ 40 * 164235 * 2
def baseEnd_164235 : Nat := 49974219431863800596861

theorem tailTrace_164235 : CollatzResearch.WordTrace tailWord_164235 prefixEnd_164235 49974219431863800596861 := by
  unfold tailWord_164235
  simp only [CollatzResearch.WordTrace]
  refine ⟨5990142560012118950006159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3993428373341412633337439 5990142560012118950006159)
  ·
    refine ⟨8985213840018178425009239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5990142560012118950006159 8985213840018178425009239)
    ·
      refine ⟨13477820760027267637513859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8985213840018178425009239 13477820760027267637513859)
      ·
        refine ⟨20216731140040901456270789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13477820760027267637513859 20216731140040901456270789)
        ·
          refine ⟨3790637088757669023050773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20216731140040901456270789 3790637088757669023050773)
          ·
            refine ⟨177686113535515735455505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 3790637088757669023050773 177686113535515735455505)
            ·
              refine ⟨133264585151636801591629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 177686113535515735455505 133264585151636801591629)
              ·
                refine ⟨49974219431863800596861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 133264585151636801591629 49974219431863800596861)
                ·
                  rfl

theorem cell19_164235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 2, 3].length) (baseStart_164235 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_164235 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_164235 prefixEnd_164235 := by exact prefixLift 164235
  have htrace : WordTrace (prefixWord ++ tailWord_164235) baseStart_164235 baseEnd_164235 := by
    simpa [prefixWord, tailWord_164235, baseEnd_164235] using wordTrace_append hprefix tailTrace_164235
  have hstable : (prefixWord ++ tailWord_164235).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164235).length < 2 ^ (prefixWord ++ tailWord_164235).sum := by decide
  have hdescent : baseEnd_164235 < baseStart_164235 := by decide
  rcases family_descends (prefixWord ++ tailWord_164235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164254 : List Nat := [4, 3, 1, 2, 1, 1, 7]
def baseStart_164254 : Nat := 118140960795 + 164254 * 2 ^ 59
def prefixEnd_164254 : Nat := 4983230072969 + 3 ^ 40 * 164254 * 2
def baseEnd_164254 : Nat := 16660000281225795391529

theorem tailTrace_164254 : CollatzResearch.WordTrace tailWord_164254 prefixEnd_164254 16660000281225795391529 := by
  unfold tailWord_164254
  simp only [CollatzResearch.WordTrace]
  refine ⟨748854443367910649368477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3993890364628856796631877 748854443367910649368477)
  ·
    refine ⟨280820416262966493513179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 748854443367910649368477 280820416262966493513179)
    ·
      refine ⟨421230624394449740269769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 280820416262966493513179 421230624394449740269769)
      ·
        refine ⟨315922968295837305202327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 421230624394449740269769 315922968295837305202327)
        ·
          refine ⟨473884452443755957803491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 315922968295837305202327 473884452443755957803491)
          ·
            refine ⟨710826678665633936705237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 473884452443755957803491 710826678665633936705237)
            ·
              refine ⟨16660000281225795391529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 710826678665633936705237 16660000281225795391529)
              ·
                rfl

theorem cell19_164254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 7].length) (baseStart_164254 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_164254 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_164254 prefixEnd_164254 := by exact prefixLift 164254
  have htrace : WordTrace (prefixWord ++ tailWord_164254) baseStart_164254 baseEnd_164254 := by
    simpa [prefixWord, tailWord_164254, baseEnd_164254] using wordTrace_append hprefix tailTrace_164254
  have hstable : (prefixWord ++ tailWord_164254).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164254).length < 2 ^ (prefixWord ++ tailWord_164254).sum := by decide
  have hdescent : baseEnd_164254 < baseStart_164254 := by decide
  rcases family_descends (prefixWord ++ tailWord_164254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164256 : List Nat := [2, 1, 1, 4, 1, 5, 5]
def baseStart_164256 : Nat := 118140960795 + 164256 * 2 ^ 59
def prefixEnd_164256 : Nat := 4983230072969 + 3 ^ 40 * 164256 * 2
def baseEnd_164256 : Nat := 16660203137780658043379

theorem tailTrace_164256 : CollatzResearch.WordTrace tailWord_164256 prefixEnd_164256 16660203137780658043379 := by
  unfold tailWord_164256
  simp only [CollatzResearch.WordTrace]
  refine ⟨2995454246468019768260311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3993938995290693024347081 2995454246468019768260311)
  ·
    refine ⟨4493181369702029652390467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2995454246468019768260311 4493181369702029652390467)
    ·
      refine ⟨6739772054553044478585701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4493181369702029652390467 6739772054553044478585701)
      ·
        refine ⟨1263707260228695839734819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6739772054553044478585701 1263707260228695839734819)
        ·
          refine ⟨1895560890343043759602229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1263707260228695839734819 1895560890343043759602229)
          ·
            refine ⟨177708833469660352462709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1895560890343043759602229 177708833469660352462709)
            ·
              refine ⟨16660203137780658043379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 177708833469660352462709 16660203137780658043379)
              ·
                rfl

theorem cell19_164256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 5].length) (baseStart_164256 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_164256 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_164256 prefixEnd_164256 := by exact prefixLift 164256
  have htrace : WordTrace (prefixWord ++ tailWord_164256) baseStart_164256 baseEnd_164256 := by
    simpa [prefixWord, tailWord_164256, baseEnd_164256] using wordTrace_append hprefix tailTrace_164256
  have hstable : (prefixWord ++ tailWord_164256).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164256).length < 2 ^ (prefixWord ++ tailWord_164256).sum := by decide
  have hdescent : baseEnd_164256 < baseStart_164256 := by decide
  rcases family_descends (prefixWord ++ tailWord_164256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164330 : List Nat := [3, 1, 3, 1, 3, 3, 1, 4]
def baseStart_164330 : Nat := 118140960795 + 164330 * 2 ^ 59
def prefixEnd_164330 : Nat := 4983230072969 + 3 ^ 40 * 164330 * 2
def baseEnd_164330 : Nat := 50003126490931728485491

theorem tailTrace_164330 : CollatzResearch.WordTrace tailWord_164330 prefixEnd_164330 50003126490931728485491 := by
  unfold tailWord_164330
  simp only [CollatzResearch.WordTrace]
  refine ⟨1498401873666987543678611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3995738329778633449809629 1498401873666987543678611)
  ·
    refine ⟨2247602810500481315517917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1498401873666987543678611 2247602810500481315517917)
    ·
      refine ⟨842851053937680493319219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2247602810500481315517917 842851053937680493319219)
      ·
        refine ⟨1264276580906520739978829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 842851053937680493319219 1264276580906520739978829)
        ·
          refine ⟨474103717839945277492061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1264276580906520739978829 474103717839945277492061)
          ·
            refine ⟨177788894189979479059523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 474103717839945277492061 177788894189979479059523)
            ·
              refine ⟨266683341284969218589285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 177788894189979479059523 266683341284969218589285)
              ·
                refine ⟨50003126490931728485491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 266683341284969218589285 50003126490931728485491)
                ·
                  rfl

theorem cell19_164330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 1, 4].length) (baseStart_164330 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_164330 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_164330 prefixEnd_164330 := by exact prefixLift 164330
  have htrace : WordTrace (prefixWord ++ tailWord_164330) baseStart_164330 baseEnd_164330 := by
    simpa [prefixWord, tailWord_164330, baseEnd_164330] using wordTrace_append hprefix tailTrace_164330
  have hstable : (prefixWord ++ tailWord_164330).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164330).length < 2 ^ (prefixWord ++ tailWord_164330).sum := by decide
  have hdescent : baseEnd_164330 < baseStart_164330 := by decide
  rcases family_descends (prefixWord ++ tailWord_164330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164351 : List Nat := [1, 1, 2, 2, 1, 2, 7, 3]
def baseStart_164351 : Nat := 118140960795 + 164351 * 2 ^ 59
def prefixEnd_164351 : Nat := 4983230072969 + 3 ^ 40 * 164351 * 2
def baseEnd_164351 : Nat := 50009516472409902018767

theorem tailTrace_164351 : CollatzResearch.WordTrace tailWord_164351 prefixEnd_164351 50009516472409902018767 := by
  unfold tailWord_164351
  simp only [CollatzResearch.WordTrace]
  refine ⟨5994373427591870761228907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3996248951727913840819271 5994373427591870761228907)
  ·
    refine ⟨8991560141387806141843361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5994373427591870761228907 8991560141387806141843361)
    ·
      refine ⟨6743670106040854606382521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8991560141387806141843361 6743670106040854606382521)
      ·
        refine ⟨5057752579530640954786891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6743670106040854606382521 5057752579530640954786891)
        ·
          refine ⟨7586628869295961432180337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5057752579530640954786891 7586628869295961432180337)
          ·
            refine ⟨5689971651971971074135253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7586628869295961432180337 5689971651971971074135253)
            ·
              refine ⟨133358710593093072050045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 5689971651971971074135253 133358710593093072050045)
              ·
                refine ⟨50009516472409902018767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 133358710593093072050045 50009516472409902018767)
                ·
                  rfl

theorem cell19_164351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 7, 3].length) (baseStart_164351 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_164351 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_164351 prefixEnd_164351 := by exact prefixLift 164351
  have htrace : WordTrace (prefixWord ++ tailWord_164351) baseStart_164351 baseEnd_164351 := by
    simpa [prefixWord, tailWord_164351, baseEnd_164351] using wordTrace_append hprefix tailTrace_164351
  have hstable : (prefixWord ++ tailWord_164351).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164351).length < 2 ^ (prefixWord ++ tailWord_164351).sum := by decide
  have hdescent : baseEnd_164351 < baseStart_164351 := by decide
  rcases family_descends (prefixWord ++ tailWord_164351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164404 : List Nat := [2, 5, 1, 3, 1, 1, 1, 5]
def baseStart_164404 : Nat := 118140960795 + 164404 * 2 ^ 59
def prefixEnd_164404 : Nat := 4983230072969 + 3 ^ 40 * 164404 * 2
def baseEnd_164404 : Nat := 50025643568521482840845

theorem tailTrace_164404 : CollatzResearch.WordTrace tailWord_164404 prefixEnd_164404 50025643568521482840845 := by
  unfold tailWord_164404
  simp only [CollatzResearch.WordTrace]
  refine ⟨2998153248199930406454133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3997537664266573875272177 2998153248199930406454133)
  ·
    refine ⟨281076867018743475605075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2998153248199930406454133 281076867018743475605075)
    ·
      refine ⟨421615300528115213407613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 281076867018743475605075 421615300528115213407613)
      ·
        refine ⟨158105737698043205027855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 421615300528115213407613 158105737698043205027855)
        ·
          refine ⟨237158606547064807541783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158105737698043205027855 237158606547064807541783)
          ·
            refine ⟨355737909820597211312675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 237158606547064807541783 355737909820597211312675)
            ·
              refine ⟨533606864730895816969013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 355737909820597211312675 533606864730895816969013)
              ·
                refine ⟨50025643568521482840845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 533606864730895816969013 50025643568521482840845)
                ·
                  rfl

theorem cell19_164404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 5].length) (baseStart_164404 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_164404 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_164404 prefixEnd_164404 := by exact prefixLift 164404
  have htrace : WordTrace (prefixWord ++ tailWord_164404) baseStart_164404 baseEnd_164404 := by
    simpa [prefixWord, tailWord_164404, baseEnd_164404] using wordTrace_append hprefix tailTrace_164404
  have hstable : (prefixWord ++ tailWord_164404).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164404).length < 2 ^ (prefixWord ++ tailWord_164404).sum := by decide
  have hdescent : baseEnd_164404 < baseStart_164404 := by decide
  rcases family_descends (prefixWord ++ tailWord_164404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164406 : List Nat := [5, 1, 2, 1, 2, 2, 1, 5]
def baseStart_164406 : Nat := 118140960795 + 164406 * 2 ^ 59
def prefixEnd_164406 : Nat := 4983230072969 + 3 ^ 40 * 164406 * 2
def baseEnd_164406 : Nat := 50026252138186070796395

theorem tailTrace_164406 : CollatzResearch.WordTrace tailWord_164406 prefixEnd_164406 50026252138186070796395 := by
  unfold tailWord_164406
  simp only [CollatzResearch.WordTrace]
  refine ⟨374773715149538447155067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3997586294928410102987381 374773715149538447155067)
  ·
    refine ⟨562160572724307670732601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 374773715149538447155067 562160572724307670732601)
    ·
      refine ⟨421620429543230753049451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 562160572724307670732601 421620429543230753049451)
      ·
        refine ⟨632430644314846129574177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 421620429543230753049451 632430644314846129574177)
        ·
          refine ⟨474322983236134597180633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 632430644314846129574177 474322983236134597180633)
          ·
            refine ⟨355742237427100947885475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 474322983236134597180633 355742237427100947885475)
            ·
              refine ⟨533613356140651421828213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 355742237427100947885475 533613356140651421828213)
              ·
                refine ⟨50026252138186070796395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 533613356140651421828213 50026252138186070796395)
                ·
                  rfl

theorem cell19_164406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 5].length) (baseStart_164406 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_164406 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_164406 prefixEnd_164406 := by exact prefixLift 164406
  have htrace : WordTrace (prefixWord ++ tailWord_164406) baseStart_164406 baseEnd_164406 := by
    simpa [prefixWord, tailWord_164406, baseEnd_164406] using wordTrace_append hprefix tailTrace_164406
  have hstable : (prefixWord ++ tailWord_164406).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164406).length < 2 ^ (prefixWord ++ tailWord_164406).sum := by decide
  have hdescent : baseEnd_164406 < baseStart_164406 := by decide
  rcases family_descends (prefixWord ++ tailWord_164406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164444 : List Nat := [2, 2, 4, 1, 3, 1, 2, 4]
def baseStart_164444 : Nat := 118140960795 + 164444 * 2 ^ 59
def prefixEnd_164444 : Nat := 4983230072969 + 3 ^ 40 * 164444 * 2
def baseEnd_164444 : Nat := 50037814961813241951847

theorem tailTrace_164444 : CollatzResearch.WordTrace tailWord_164444 prefixEnd_164444 50037814961813241951847 := by
  unfold tailWord_164444
  simp only [CollatzResearch.WordTrace]
  refine ⟨2998882708127473822182193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3998510277503298429576257 2998882708127473822182193)
  ·
    refine ⟨2249162031095605366636645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2998882708127473822182193 2249162031095605366636645)
    ·
      refine ⟨421717880830426006244371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2249162031095605366636645 421717880830426006244371)
      ·
        refine ⟨632576821245639009366557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 421717880830426006244371 632576821245639009366557)
        ·
          refine ⟨237216307967114628512459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 632576821245639009366557 237216307967114628512459)
          ·
            refine ⟨355824461950671942768689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 237216307967114628512459 355824461950671942768689)
            ·
              refine ⟨266868346463003957076517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 355824461950671942768689 266868346463003957076517)
              ·
                refine ⟨50037814961813241951847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 266868346463003957076517 50037814961813241951847)
                ·
                  rfl

theorem cell19_164444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 2, 4].length) (baseStart_164444 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_164444 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_164444 prefixEnd_164444 := by exact prefixLift 164444
  have htrace : WordTrace (prefixWord ++ tailWord_164444) baseStart_164444 baseEnd_164444 := by
    simpa [prefixWord, tailWord_164444, baseEnd_164444] using wordTrace_append hprefix tailTrace_164444
  have hstable : (prefixWord ++ tailWord_164444).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164444).length < 2 ^ (prefixWord ++ tailWord_164444).sum := by decide
  have hdescent : baseEnd_164444 < baseStart_164444 := by decide
  rcases family_descends (prefixWord ++ tailWord_164444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164448 : List Nat := [2, 1, 1, 3, 2, 1, 3, 6]
def baseStart_164448 : Nat := 118140960795 + 164448 * 2 ^ 59
def prefixEnd_164448 : Nat := 4983230072969 + 3 ^ 40 * 164448 * 2
def baseEnd_164448 : Nat := 50039032101142417862947

theorem tailTrace_164448 : CollatzResearch.WordTrace tailWord_164448 prefixEnd_164448 50039032101142417862947 := by
  unfold tailWord_164448
  simp only [CollatzResearch.WordTrace]
  refine ⟨2998955654120228163754999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3998607538826970885006665 2998955654120228163754999)
  ·
    refine ⟨4498433481180342245632499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2998955654120228163754999 4498433481180342245632499)
    ·
      refine ⟨6747650221770513368448749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4498433481180342245632499 6747650221770513368448749)
      ·
        refine ⟨2530368833163942513168281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6747650221770513368448749 2530368833163942513168281)
        ·
          refine ⟨1897776624872956884876211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2530368833163942513168281 1897776624872956884876211)
          ·
            refine ⟨2846664937309435327314317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1897776624872956884876211 2846664937309435327314317)
            ·
              refine ⟨1067499351491038247742869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2846664937309435327314317 1067499351491038247742869)
              ·
                refine ⟨50039032101142417862947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1067499351491038247742869 50039032101142417862947)
                ·
                  rfl

theorem cell19_164448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 6].length) (baseStart_164448 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_164448 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_164448 prefixEnd_164448 := by exact prefixLift 164448
  have htrace : WordTrace (prefixWord ++ tailWord_164448) baseStart_164448 baseEnd_164448 := by
    simpa [prefixWord, tailWord_164448, baseEnd_164448] using wordTrace_append hprefix tailTrace_164448
  have hstable : (prefixWord ++ tailWord_164448).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164448).length < 2 ^ (prefixWord ++ tailWord_164448).sum := by decide
  have hdescent : baseEnd_164448 < baseStart_164448 := by decide
  rcases family_descends (prefixWord ++ tailWord_164448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164543 : List Nat := [1, 1, 2, 2, 2, 5, 6]
def baseStart_164543 : Nat := 118140960795 + 164543 * 2 ^ 59
def prefixEnd_164543 : Nat := 4983230072969 + 3 ^ 40 * 164543 * 2
def baseEnd_164543 : Nat := 16689313053403448583859

theorem tailTrace_164543 : CollatzResearch.WordTrace tailWord_164543 prefixEnd_164543 16689313053403448583859 := by
  unfold tailWord_164543
  simp only [CollatzResearch.WordTrace]
  refine ⟨6001376242896287552218283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4000917495264191701478855 6001376242896287552218283)
  ·
    refine ⟨9002064364344431328327425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6001376242896287552218283 9002064364344431328327425)
    ·
      refine ⟨6751548273258323496245569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9002064364344431328327425 6751548273258323496245569)
      ·
        refine ⟨5063661204943742622184177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6751548273258323496245569 5063661204943742622184177)
        ·
          refine ⟨3797745903707806966638133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5063661204943742622184177 3797745903707806966638133)
          ·
            refine ⟨356038678472606903122325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3797745903707806966638133 356038678472606903122325)
            ·
              refine ⟨16689313053403448583859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 356038678472606903122325 16689313053403448583859)
              ·
                rfl

theorem cell19_164543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 6].length) (baseStart_164543 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_164543 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_164543 prefixEnd_164543 := by exact prefixLift 164543
  have htrace : WordTrace (prefixWord ++ tailWord_164543) baseStart_164543 baseEnd_164543 := by
    simpa [prefixWord, tailWord_164543, baseEnd_164543] using wordTrace_append hprefix tailTrace_164543
  have hstable : (prefixWord ++ tailWord_164543).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164543).length < 2 ^ (prefixWord ++ tailWord_164543).sum := by decide
  have hdescent : baseEnd_164543 < baseStart_164543 := by decide
  rcases family_descends (prefixWord ++ tailWord_164543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164577 : List Nat := [1, 2, 3, 1, 4, 3, 2, 3]
def baseStart_164577 : Nat := 118140960795 + 164577 * 2 ^ 59
def prefixEnd_164577 : Nat := 4983230072969 + 3 ^ 40 * 164577 * 2
def baseEnd_164577 : Nat := 50078284844508340995929

theorem tailTrace_164577 : CollatzResearch.WordTrace tailWord_164577 prefixEnd_164577 50078284844508340995929 := by
  unfold tailWord_164577
  simp only [CollatzResearch.WordTrace]
  refine ⟨6002616324773111358955985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4001744216515407572637323 6002616324773111358955985)
  ·
    refine ⟨4501962243579833519216989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6002616324773111358955985 4501962243579833519216989)
    ·
      refine ⟨1688235841342437569706371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4501962243579833519216989 1688235841342437569706371)
      ·
        refine ⟨2532353762013656354559557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1688235841342437569706371 2532353762013656354559557)
        ·
          refine ⟨474816330377560566479917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2532353762013656354559557 474816330377560566479917)
          ·
            refine ⟨178056123891585212429969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 474816330377560566479917 178056123891585212429969)
            ·
              refine ⟨133542092918688909322477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 178056123891585212429969 133542092918688909322477)
              ·
                refine ⟨50078284844508340995929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 133542092918688909322477 50078284844508340995929)
                ·
                  rfl

theorem cell19_164577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 2, 3].length) (baseStart_164577 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_164577 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_164577 prefixEnd_164577 := by exact prefixLift 164577
  have htrace : WordTrace (prefixWord ++ tailWord_164577) baseStart_164577 baseEnd_164577 := by
    simpa [prefixWord, tailWord_164577, baseEnd_164577] using wordTrace_append hprefix tailTrace_164577
  have hstable : (prefixWord ++ tailWord_164577).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164577).length < 2 ^ (prefixWord ++ tailWord_164577).sum := by decide
  have hdescent : baseEnd_164577 < baseStart_164577 := by decide
  rcases family_descends (prefixWord ++ tailWord_164577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164579 : List Nat := [1, 1, 1, 7, 1, 2, 1, 5]
def baseStart_164579 : Nat := 118140960795 + 164579 * 2 ^ 59
def prefixEnd_164579 : Nat := 4983230072969 + 3 ^ 40 * 164579 * 2
def baseEnd_164579 : Nat := 50078893414172928951479

theorem tailTrace_164579 : CollatzResearch.WordTrace tailWord_164579 prefixEnd_164579 50078893414172928951479 := by
  unfold tailWord_164579
  simp only [CollatzResearch.WordTrace]
  refine ⟨6002689270765865700528791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4001792847177243800352527 6002689270765865700528791)
  ·
    refine ⟨9004033906148798550793187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6002689270765865700528791 9004033906148798550793187)
    ·
      refine ⟨13506050859223197826189781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9004033906148798550793187 13506050859223197826189781)
      ·
        refine ⟨316548067013043699051323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 13506050859223197826189781 316548067013043699051323)
        ·
          refine ⟨474822100519565548576985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 316548067013043699051323 474822100519565548576985)
          ·
            refine ⟨356116575389674161432739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 474822100519565548576985 356116575389674161432739)
            ·
              refine ⟨534174863084511242149109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 356116575389674161432739 534174863084511242149109)
              ·
                refine ⟨50078893414172928951479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 534174863084511242149109 50078893414172928951479)
                ·
                  rfl

theorem cell19_164579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 5].length) (baseStart_164579 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_164579 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_164579 prefixEnd_164579 := by exact prefixLift 164579
  have htrace : WordTrace (prefixWord ++ tailWord_164579) baseStart_164579 baseEnd_164579 := by
    simpa [prefixWord, tailWord_164579, baseEnd_164579] using wordTrace_append hprefix tailTrace_164579
  have hstable : (prefixWord ++ tailWord_164579).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164579).length < 2 ^ (prefixWord ++ tailWord_164579).sum := by decide
  have hdescent : baseEnd_164579 < baseStart_164579 := by decide
  rcases family_descends (prefixWord ++ tailWord_164579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164653 : List Nat := [1, 5, 3, 2, 1, 7]
def baseStart_164653 : Nat := 118140960795 + 164653 * 2 ^ 59
def prefixEnd_164653 : Nat := 4983230072969 + 3 ^ 40 * 164653 * 2
def baseEnd_164653 : Nat := 5566823387973631478537

theorem tailTrace_164653 : CollatzResearch.WordTrace tailWord_164653 prefixEnd_164653 5566823387973631478537 := by
  unfold tailWord_164653
  simp only [CollatzResearch.WordTrace]
  refine ⟨6005388272497776338722613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4003592181665184225815075 6005388272497776338722613)
  ·
    refine ⟨563005150546666531755245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6005388272497776338722613 563005150546666531755245)
    ·
      refine ⟨211126931454999949408217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 563005150546666531755245 211126931454999949408217)
      ·
        refine ⟨158345198591249962056163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 211126931454999949408217 158345198591249962056163)
        ·
          refine ⟨237517797886874943084245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158345198591249962056163 237517797886874943084245)
          ·
            refine ⟨5566823387973631478537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 237517797886874943084245 5566823387973631478537)
            ·
              rfl

theorem cell19_164653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 7].length) (baseStart_164653 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_164653 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_164653 prefixEnd_164653 := by exact prefixLift 164653
  have htrace : WordTrace (prefixWord ++ tailWord_164653) baseStart_164653 baseEnd_164653 := by
    simpa [prefixWord, tailWord_164653, baseEnd_164653] using wordTrace_append hprefix tailTrace_164653
  have hstable : (prefixWord ++ tailWord_164653).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164653).length < 2 ^ (prefixWord ++ tailWord_164653).sum := by decide
  have hdescent : baseEnd_164653 < baseStart_164653 := by decide
  rcases family_descends (prefixWord ++ tailWord_164653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164670 : List Nat := [4, 2, 1, 2, 4, 1, 1, 4]
def baseStart_164670 : Nat := 118140960795 + 164670 * 2 ^ 59
def prefixEnd_164670 : Nat := 4983230072969 + 3 ^ 40 * 164670 * 2
def baseEnd_164670 : Nat := 50106583333911680929009

theorem tailTrace_164670 : CollatzResearch.WordTrace tailWord_164670 prefixEnd_164670 50106583333911680929009 := by
  unfold tailWord_164670
  simp only [CollatzResearch.WordTrace]
  refine ⟨750751039179523530261433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4004005542290792161394309 750751039179523530261433)
  ·
    refine ⟨563063279384642647696075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 750751039179523530261433 563063279384642647696075)
    ·
      refine ⟨844594919076963971544113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 563063279384642647696075 844594919076963971544113)
      ·
        refine ⟨633446189307722978658085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 844594919076963971544113 633446189307722978658085)
        ·
          refine ⟨118771160495198058498391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 633446189307722978658085 118771160495198058498391)
          ·
            refine ⟨178156740742797087747587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118771160495198058498391 178156740742797087747587)
            ·
              refine ⟨267235111114195631621381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 178156740742797087747587 267235111114195631621381)
              ·
                refine ⟨50106583333911680929009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 267235111114195631621381 50106583333911680929009)
                ·
                  rfl

theorem cell19_164670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 1, 4].length) (baseStart_164670 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_164670 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_164670 prefixEnd_164670 := by exact prefixLift 164670
  have htrace : WordTrace (prefixWord ++ tailWord_164670) baseStart_164670 baseEnd_164670 := by
    simpa [prefixWord, tailWord_164670, baseEnd_164670] using wordTrace_append hprefix tailTrace_164670
  have hstable : (prefixWord ++ tailWord_164670).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164670).length < 2 ^ (prefixWord ++ tailWord_164670).sum := by decide
  have hdescent : baseEnd_164670 < baseStart_164670 := by decide
  rcases family_descends (prefixWord ++ tailWord_164670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164693 : List Nat := [1, 3, 2, 2, 2, 1, 5, 3]
def baseStart_164693 : Nat := 118140960795 + 164693 * 2 ^ 59
def prefixEnd_164693 : Nat := 4983230072969 + 3 ^ 40 * 164693 * 2
def baseEnd_164693 : Nat := 50113581885054442417835

theorem tailTrace_164693 : CollatzResearch.WordTrace tailWord_164693 prefixEnd_164693 50113581885054442417835 := by
  unfold tailWord_164693
  simp only [CollatzResearch.WordTrace]
  refine ⟨6006847192352863170178733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4004564794901908780119155 6006847192352863170178733)
  ·
    refine ⟨2252567697132323688817025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6006847192352863170178733 2252567697132323688817025)
    ·
      refine ⟨1689425772849242766612769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2252567697132323688817025 1689425772849242766612769)
      ·
        refine ⟨1267069329636932074959577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1689425772849242766612769 1267069329636932074959577)
        ·
          refine ⟨950301997227699056219683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1267069329636932074959577 950301997227699056219683)
          ·
            refine ⟨1425452995841548584329525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 950301997227699056219683 1425452995841548584329525)
            ·
              refine ⟨133636218360145179780893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1425452995841548584329525 133636218360145179780893)
              ·
                refine ⟨50113581885054442417835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 133636218360145179780893 50113581885054442417835)
                ·
                  rfl

theorem cell19_164693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 5, 3].length) (baseStart_164693 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_164693 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_164693 prefixEnd_164693 := by exact prefixLift 164693
  have htrace : WordTrace (prefixWord ++ tailWord_164693) baseStart_164693 baseEnd_164693 := by
    simpa [prefixWord, tailWord_164693, baseEnd_164693] using wordTrace_append hprefix tailTrace_164693
  have hstable : (prefixWord ++ tailWord_164693).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164693).length < 2 ^ (prefixWord ++ tailWord_164693).sum := by decide
  have hdescent : baseEnd_164693 < baseStart_164693 := by decide
  rcases family_descends (prefixWord ++ tailWord_164693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164769 : List Nat := [1, 2, 3, 4, 1, 3, 5]
def baseStart_164769 : Nat := 118140960795 + 164769 * 2 ^ 59
def prefixEnd_164769 : Nat := 4983230072969 + 3 ^ 40 * 164769 * 2
def baseEnd_164769 : Nat := 16712235844102928242913

theorem tailTrace_164769 : CollatzResearch.WordTrace tailWord_164769 prefixEnd_164769 16712235844102928242913 := by
  unfold tailWord_164769
  simp only [CollatzResearch.WordTrace]
  refine ⟨6009619140077528149945361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4006412760051685433296907 6009619140077528149945361)
  ·
    refine ⟨4507214355058146112459021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6009619140077528149945361 4507214355058146112459021)
    ·
      refine ⟨1690205383146804792172133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4507214355058146112459021 1690205383146804792172133)
      ·
        refine ⟨316913509340025898532275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1690205383146804792172133 316913509340025898532275)
        ·
          refine ⟨475370264010038847798413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 316913509340025898532275 475370264010038847798413)
          ·
            refine ⟨178263849003764567924405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 475370264010038847798413 178263849003764567924405)
            ·
              refine ⟨16712235844102928242913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 178263849003764567924405 16712235844102928242913)
              ·
                rfl

theorem cell19_164769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 5].length) (baseStart_164769 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_164769 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_164769 prefixEnd_164769 := by exact prefixLift 164769
  have htrace : WordTrace (prefixWord ++ tailWord_164769) baseStart_164769 baseEnd_164769 := by
    simpa [prefixWord, tailWord_164769, baseEnd_164769] using wordTrace_append hprefix tailTrace_164769
  have hstable : (prefixWord ++ tailWord_164769).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164769).length < 2 ^ (prefixWord ++ tailWord_164769).sum := by decide
  have hdescent : baseEnd_164769 < baseStart_164769 := by decide
  rcases family_descends (prefixWord ++ tailWord_164769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164847 : List Nat := [1, 1, 2, 1, 4, 3, 3, 4]
def baseStart_164847 : Nat := 118140960795 + 164847 * 2 ^ 59
def prefixEnd_164847 : Nat := 4983230072969 + 3 ^ 40 * 164847 * 2
def baseEnd_164847 : Nat := 50160441749227714995193

theorem tailTrace_164847 : CollatzResearch.WordTrace tailWord_164847 prefixEnd_164847 50160441749227714995193 := by
  unfold tailWord_164847
  simp only [CollatzResearch.WordTrace]
  refine ⟨6012464033794947471284795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4008309355863298314189863 6012464033794947471284795)
  ·
    refine ⟨9018696050692421206927193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6012464033794947471284795 9018696050692421206927193)
    ·
      refine ⟨6764022038019315905195395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9018696050692421206927193 6764022038019315905195395)
      ·
        refine ⟨10146033057028973857793093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6764022038019315905195395 10146033057028973857793093)
        ·
          refine ⟨1902381198192932598336205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10146033057028973857793093 1902381198192932598336205)
          ·
            refine ⟨713392949322349724376077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1902381198192932598336205 713392949322349724376077)
            ·
              refine ⟨267522355995881146641029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 713392949322349724376077 267522355995881146641029)
              ·
                refine ⟨50160441749227714995193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 267522355995881146641029 50160441749227714995193)
                ·
                  rfl

theorem cell19_164847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 3, 4].length) (baseStart_164847 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_164847 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_164847 prefixEnd_164847 := by exact prefixLift 164847
  have htrace : WordTrace (prefixWord ++ tailWord_164847) baseStart_164847 baseEnd_164847 := by
    simpa [prefixWord, tailWord_164847, baseEnd_164847] using wordTrace_append hprefix tailTrace_164847
  have hstable : (prefixWord ++ tailWord_164847).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164847).length < 2 ^ (prefixWord ++ tailWord_164847).sum := by decide
  have hdescent : baseEnd_164847 < baseStart_164847 := by decide
  rcases family_descends (prefixWord ++ tailWord_164847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164885 : List Nat := [1, 3, 2, 1, 4, 2, 6]
def baseStart_164885 : Nat := 118140960795 + 164885 * 2 ^ 59
def prefixEnd_164885 : Nat := 4983230072969 + 3 ^ 40 * 164885 * 2
def baseEnd_164885 : Nat := 16724001524284962050215

theorem tailTrace_164885 : CollatzResearch.WordTrace tailWord_164885 prefixEnd_164885 16724001524284962050215 := by
  unfold tailWord_164885
  simp only [CollatzResearch.WordTrace]
  refine ⟨6013850007657279961168109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4009233338438186640778739 6013850007657279961168109)
  ·
    refine ⟨2255193752871479985438041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6013850007657279961168109 2255193752871479985438041)
    ·
      refine ⟨1691395314653609989078531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2255193752871479985438041 1691395314653609989078531)
      ·
        refine ⟨2537092971980414983617797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1691395314653609989078531 2537092971980414983617797)
        ·
          refine ⟨475704932246327809428337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2537092971980414983617797 475704932246327809428337)
          ·
            refine ⟨356778699184745857071253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 475704932246327809428337 356778699184745857071253)
            ·
              refine ⟨16724001524284962050215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 356778699184745857071253 16724001524284962050215)
              ·
                rfl

theorem cell19_164885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 6].length) (baseStart_164885 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_164885 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_164885 prefixEnd_164885 := by exact prefixLift 164885
  have htrace : WordTrace (prefixWord ++ tailWord_164885) baseStart_164885 baseEnd_164885 := by
    simpa [prefixWord, tailWord_164885, baseEnd_164885] using wordTrace_append hprefix tailTrace_164885
  have hstable : (prefixWord ++ tailWord_164885).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164885).length < 2 ^ (prefixWord ++ tailWord_164885).sum := by decide
  have hdescent : baseEnd_164885 < baseStart_164885 := by decide
  rcases family_descends (prefixWord ++ tailWord_164885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164921 : List Nat := [1, 2, 1, 5, 2, 1, 4, 3]
def baseStart_164921 : Nat := 118140960795 + 164921 * 2 ^ 59
def prefixEnd_164921 : Nat := 4983230072969 + 3 ^ 40 * 164921 * 2
def baseEnd_164921 : Nat := 50182958826817469350547

theorem tailTrace_164921 : CollatzResearch.WordTrace tailWord_164921 prefixEnd_164921 50182958826817469350547 := by
  unfold tailWord_164921
  simp only [CollatzResearch.WordTrace]
  refine ⟨6015163035526858109478617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4010108690351238739652411 6015163035526858109478617)
  ·
    refine ⟨4511372276645143582108963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6015163035526858109478617 4511372276645143582108963)
    ·
      refine ⟨6767058414967715373163445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4511372276645143582108963 6767058414967715373163445)
      ·
        refine ⟨634411726403223316234073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6767058414967715373163445 634411726403223316234073)
        ·
          refine ⟨475808794802417487175555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 634411726403223316234073 475808794802417487175555)
          ·
            refine ⟨713713192203626230763333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 475808794802417487175555 713713192203626230763333)
            ·
              refine ⟨133821223538179918268125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 713713192203626230763333 133821223538179918268125)
              ·
                refine ⟨50182958826817469350547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 133821223538179918268125 50182958826817469350547)
                ·
                  rfl

theorem cell19_164921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 4, 3].length) (baseStart_164921 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_164921 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_164921 prefixEnd_164921 := by exact prefixLift 164921
  have htrace : WordTrace (prefixWord ++ tailWord_164921) baseStart_164921 baseEnd_164921 := by
    simpa [prefixWord, tailWord_164921, baseEnd_164921] using wordTrace_append hprefix tailTrace_164921
  have hstable : (prefixWord ++ tailWord_164921).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164921).length < 2 ^ (prefixWord ++ tailWord_164921).sum := by decide
  have hdescent : baseEnd_164921 < baseStart_164921 := by decide
  rcases family_descends (prefixWord ++ tailWord_164921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164957 : List Nat := [1, 4, 4, 1, 2, 1, 2, 4]
def baseStart_164957 : Nat := 118140960795 + 164957 * 2 ^ 59
def prefixEnd_164957 : Nat := 4983230072969 + 3 ^ 40 * 164957 * 2
def baseEnd_164957 : Nat := 50193913080780052550449

theorem tailTrace_164957 : CollatzResearch.WordTrace tailWord_164957 prefixEnd_164957 50193913080780052550449 := by
  unfold tailWord_164957
  simp only [CollatzResearch.WordTrace]
  refine ⟨6016476063396436257789125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4010984042264290838526083 6016476063396436257789125)
  ·
    refine ⟨1128089261886831798335461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6016476063396436257789125 1128089261886831798335461)
    ·
      refine ⟨211516736603780962187899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1128089261886831798335461 211516736603780962187899)
      ·
        refine ⟨317275104905671443281849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211516736603780962187899 317275104905671443281849)
        ·
          refine ⟨237956328679253582461387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 317275104905671443281849 237956328679253582461387)
          ·
            refine ⟨356934493018880373692081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 237956328679253582461387 356934493018880373692081)
            ·
              refine ⟨267700869764160280269061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 356934493018880373692081 267700869764160280269061)
              ·
                refine ⟨50193913080780052550449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 267700869764160280269061 50193913080780052550449)
                ·
                  rfl

theorem cell19_164957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 2, 4].length) (baseStart_164957 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_164957 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_164957 prefixEnd_164957 := by exact prefixLift 164957
  have htrace : WordTrace (prefixWord ++ tailWord_164957) baseStart_164957 baseEnd_164957 := by
    simpa [prefixWord, tailWord_164957, baseEnd_164957] using wordTrace_append hprefix tailTrace_164957
  have hstable : (prefixWord ++ tailWord_164957).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164957).length < 2 ^ (prefixWord ++ tailWord_164957).sum := by decide
  have hdescent : baseEnd_164957 < baseStart_164957 := by decide
  rcases family_descends (prefixWord ++ tailWord_164957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165001 : List Nat := [1, 2, 1, 1, 4, 10]
def baseStart_165001 : Nat := 118140960795 + 165001 * 2 ^ 59
def prefixEnd_165001 : Nat := 4983230072969 + 3 ^ 40 * 165001 * 2
def baseEnd_165001 : Nat := 5578589068155665285839

theorem tailTrace_165001 : CollatzResearch.WordTrace tailWord_165001 prefixEnd_165001 5578589068155665285839 := by
  unfold tailWord_165001
  simp only [CollatzResearch.WordTrace]
  refine ⟨6018080875237031772390857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4012053916824687848260571 6018080875237031772390857)
  ·
    refine ⟨4513560656427773829293143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6018080875237031772390857 4513560656427773829293143)
    ·
      refine ⟨6770340984641660743939715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4513560656427773829293143 6770340984641660743939715)
      ·
        refine ⟨10155511476962491115909573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6770340984641660743939715 10155511476962491115909573)
        ·
          refine ⟨1904158401930467084233045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10155511476962491115909573 1904158401930467084233045)
          ·
            refine ⟨5578589068155665285839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1904158401930467084233045 5578589068155665285839)
            ·
              rfl

theorem cell19_165001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 10].length) (baseStart_165001 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_165001 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_165001 prefixEnd_165001 := by exact prefixLift 165001
  have htrace : WordTrace (prefixWord ++ tailWord_165001) baseStart_165001 baseEnd_165001 := by
    simpa [prefixWord, tailWord_165001, baseEnd_165001] using wordTrace_append hprefix tailTrace_165001
  have hstable : (prefixWord ++ tailWord_165001).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165001).length < 2 ^ (prefixWord ++ tailWord_165001).sum := by decide
  have hdescent : baseEnd_165001 < baseStart_165001 := by decide
  rcases family_descends (prefixWord ++ tailWord_165001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165016 : List Nat := [2, 1, 2, 4, 2, 3, 1, 4]
def baseStart_165016 : Nat := 118140960795 + 165016 * 2 ^ 59
def prefixEnd_165016 : Nat := 4983230072969 + 3 ^ 40 * 165016 * 2
def baseEnd_165016 : Nat := 50211865885885397239177

theorem tailTrace_165016 : CollatzResearch.WordTrace tailWord_165016 prefixEnd_165016 50211865885885397239177 := by
  unfold tailWord_165016
  simp only [CollatzResearch.WordTrace]
  refine ⟨3009313985091344667093451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4012418646788459556124601 3009313985091344667093451)
  ·
    refine ⟨4513970977637017000640177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3009313985091344667093451 4513970977637017000640177)
    ·
      refine ⟨3385478233227762750480133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4513970977637017000640177 3385478233227762750480133)
      ·
        refine ⟨634777168730205515715025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3385478233227762750480133 634777168730205515715025)
        ·
          refine ⟨476082876547654136786269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 634777168730205515715025 476082876547654136786269)
          ·
            refine ⟨178531078705370301294851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 476082876547654136786269 178531078705370301294851)
            ·
              refine ⟨267796618058055451942277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 178531078705370301294851 267796618058055451942277)
              ·
                refine ⟨50211865885885397239177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 267796618058055451942277 50211865885885397239177)
                ·
                  rfl

theorem cell19_165016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 1, 4].length) (baseStart_165016 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_165016 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_165016 prefixEnd_165016 := by exact prefixLift 165016
  have htrace : WordTrace (prefixWord ++ tailWord_165016) baseStart_165016 baseEnd_165016 := by
    simpa [prefixWord, tailWord_165016, baseEnd_165016] using wordTrace_append hprefix tailTrace_165016
  have hstable : (prefixWord ++ tailWord_165016).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165016).length < 2 ^ (prefixWord ++ tailWord_165016).sum := by decide
  have hdescent : baseEnd_165016 < baseStart_165016 := by decide
  rcases family_descends (prefixWord ++ tailWord_165016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165039 : List Nat := [1, 1, 2, 1, 2, 3, 2, 7]
def baseStart_165039 : Nat := 118140960795 + 165039 * 2 ^ 59
def prefixEnd_165039 : Nat := 4983230072969 + 3 ^ 40 * 165039 * 2
def baseEnd_165039 : Nat := 50218864437028158728003

theorem tailTrace_165039 : CollatzResearch.WordTrace tailWord_165039 prefixEnd_165039 50218864437028158728003 := by
  unfold tailWord_165039
  simp only [CollatzResearch.WordTrace]
  refine ⟨6019466849099364262274171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4012977899399576174849447 6019466849099364262274171)
  ·
    refine ⟨9029200273649046393411257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6019466849099364262274171 9029200273649046393411257)
    ·
      refine ⟨6771900205236784795058443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9029200273649046393411257 6771900205236784795058443)
      ·
        refine ⟨10157850307855177192587665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6771900205236784795058443 10157850307855177192587665)
        ·
          refine ⟨7618387730891382894440749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10157850307855177192587665 7618387730891382894440749)
          ·
            refine ⟨2856895399084268585415281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7618387730891382894440749 2856895399084268585415281)
            ·
              refine ⟨2142671549313201439061461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2856895399084268585415281 2142671549313201439061461)
              ·
                refine ⟨50218864437028158728003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2142671549313201439061461 50218864437028158728003)
                ·
                  rfl

theorem cell19_165039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 7].length) (baseStart_165039 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_165039 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_165039 prefixEnd_165039 := by exact prefixLift 165039
  have htrace : WordTrace (prefixWord ++ tailWord_165039) baseStart_165039 baseEnd_165039 := by
    simpa [prefixWord, tailWord_165039, baseEnd_165039] using wordTrace_append hprefix tailTrace_165039
  have hstable : (prefixWord ++ tailWord_165039).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165039).length < 2 ^ (prefixWord ++ tailWord_165039).sum := by decide
  have hdescent : baseEnd_165039 < baseStart_165039 := by decide
  rcases family_descends (prefixWord ++ tailWord_165039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165056 : List Nat := [2, 1, 1, 2, 6, 1, 6]
def baseStart_165056 : Nat := 118140960795 + 165056 * 2 ^ 59
def prefixEnd_165056 : Nat := 4983230072969 + 3 ^ 40 * 165056 * 2
def baseEnd_165056 : Nat := 16741345759725718783393

theorem tailTrace_165056 : CollatzResearch.WordTrace tailWord_165056 prefixEnd_165056 16741345759725718783393 := by
  unfold tailWord_165056
  simp only [CollatzResearch.WordTrace]
  refine ⟨3010043445018888082821511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4013391260025184110428681 3010043445018888082821511)
  ·
    refine ⟨4515065167528332124232267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3010043445018888082821511 4515065167528332124232267)
    ·
      refine ⟨6772597751292498186348401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4515065167528332124232267 6772597751292498186348401)
      ·
        refine ⟨5079448313469373639761301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6772597751292498186348401 5079448313469373639761301)
        ·
          refine ⟨238099139693876889363811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 5079448313469373639761301 238099139693876889363811)
          ·
            refine ⟨357148709540815334045717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 238099139693876889363811 357148709540815334045717)
            ·
              refine ⟨16741345759725718783393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 357148709540815334045717 16741345759725718783393)
              ·
                rfl

theorem cell19_165056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 6].length) (baseStart_165056 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_165056 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_165056 prefixEnd_165056 := by exact prefixLift 165056
  have htrace : WordTrace (prefixWord ++ tailWord_165056) baseStart_165056 baseEnd_165056 := by
    simpa [prefixWord, tailWord_165056, baseEnd_165056] using wordTrace_append hprefix tailTrace_165056
  have hstable : (prefixWord ++ tailWord_165056).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165056).length < 2 ^ (prefixWord ++ tailWord_165056).sum := by decide
  have hdescent : baseEnd_165056 < baseStart_165056 := by decide
  rcases family_descends (prefixWord ++ tailWord_165056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165132 : List Nat := [2, 2, 1, 2, 2, 4, 2, 4]
def baseStart_165132 : Nat := 118140960795 + 165132 * 2 ^ 59
def prefixEnd_165132 : Nat := 4983230072969 + 3 ^ 40 * 165132 * 2
def baseEnd_165132 : Nat := 50247162926431498661083

theorem tailTrace_165132 : CollatzResearch.WordTrace tailWord_165132 prefixEnd_165132 50247162926431498661083 := by
  unfold tailWord_165132
  simp only [CollatzResearch.WordTrace]
  refine ⟨3011429418881220572704825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4015239225174960763606433 3011429418881220572704825)
  ·
    refine ⟨2258572064160915429528619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3011429418881220572704825 2258572064160915429528619)
    ·
      refine ⟨3387858096241373144292929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2258572064160915429528619 3387858096241373144292929)
      ·
        refine ⟨2540893572181029858219697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3387858096241373144292929 2540893572181029858219697)
        ·
          refine ⟨1905670179135772393664773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2540893572181029858219697 1905670179135772393664773)
          ·
            refine ⟨357313158587957323812145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1905670179135772393664773 357313158587957323812145)
            ·
              refine ⟨267984868940967992859109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 357313158587957323812145 267984868940967992859109)
              ·
                refine ⟨50247162926431498661083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 267984868940967992859109 50247162926431498661083)
                ·
                  rfl

theorem cell19_165132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 2, 4].length) (baseStart_165132 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_165132 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_165132 prefixEnd_165132 := by exact prefixLift 165132
  have htrace : WordTrace (prefixWord ++ tailWord_165132) baseStart_165132 baseEnd_165132 := by
    simpa [prefixWord, tailWord_165132, baseEnd_165132] using wordTrace_append hprefix tailTrace_165132
  have hstable : (prefixWord ++ tailWord_165132).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165132).length < 2 ^ (prefixWord ++ tailWord_165132).sum := by decide
  have hdescent : baseEnd_165132 < baseStart_165132 := by decide
  rcases family_descends (prefixWord ++ tailWord_165132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165208 : List Nat := [2, 1, 2, 2, 1, 1, 7, 3]
def baseStart_165208 : Nat := 118140960795 + 165208 * 2 ^ 59
def prefixEnd_165208 : Nat := 4983230072969 + 3 ^ 40 * 165208 * 2
def baseEnd_165208 : Nat := 50270288573685840971987

theorem tailTrace_165208 : CollatzResearch.WordTrace tailWord_165208 prefixEnd_165208 50270288573685840971987 := by
  unfold tailWord_165208
  simp only [CollatzResearch.WordTrace]
  refine ⟨3012815392743553062588139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4017087190324737416784185 3012815392743553062588139)
  ·
    refine ⟨4519223089115329593882209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3012815392743553062588139 4519223089115329593882209)
    ·
      refine ⟨3389417316836497195411657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4519223089115329593882209 3389417316836497195411657)
      ·
        refine ⟨2542062987627372896558743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3389417316836497195411657 2542062987627372896558743)
        ·
          refine ⟨3813094481441059344838115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2542062987627372896558743 3813094481441059344838115)
          ·
            refine ⟨5719641722161589017257173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3813094481441059344838115 5719641722161589017257173)
            ·
              refine ⟨134054102863162242591965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 5719641722161589017257173 134054102863162242591965)
              ·
                refine ⟨50270288573685840971987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 134054102863162242591965 50270288573685840971987)
                ·
                  rfl

theorem cell19_165208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 7, 3].length) (baseStart_165208 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_165208 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_165208 prefixEnd_165208 := by exact prefixLift 165208
  have htrace : WordTrace (prefixWord ++ tailWord_165208) baseStart_165208 baseEnd_165208 := by
    simpa [prefixWord, tailWord_165208, baseEnd_165208] using wordTrace_append hprefix tailTrace_165208
  have hstable : (prefixWord ++ tailWord_165208).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165208).length < 2 ^ (prefixWord ++ tailWord_165208).sum := by decide
  have hdescent : baseEnd_165208 < baseStart_165208 := by decide
  rcases family_descends (prefixWord ++ tailWord_165208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165210 : List Nat := [3, 1, 1, 2, 1, 2, 2, 7]
def baseStart_165210 : Nat := 118140960795 + 165210 * 2 ^ 59
def prefixEnd_165210 : Nat := 4983230072969 + 3 ^ 40 * 165210 * 2
def baseEnd_165210 : Nat := 50270897143350428927537

theorem tailTrace_165210 : CollatzResearch.WordTrace tailWord_165210 prefixEnd_165210 50270897143350428927537 := by
  unfold tailWord_165210
  simp only [CollatzResearch.WordTrace]
  refine ⟨1506425932869965116687271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4017135820986573644499389 1506425932869965116687271)
  ·
    refine ⟨2259638899304947675030907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1506425932869965116687271 2259638899304947675030907)
    ·
      refine ⟨3389458348957421512546361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2259638899304947675030907 3389458348957421512546361)
      ·
        refine ⟨2542093761718066134409771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3389458348957421512546361 2542093761718066134409771)
        ·
          refine ⟨3813140642577099201614657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2542093761718066134409771 3813140642577099201614657)
          ·
            refine ⟨2859855481932824401210993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3813140642577099201614657 2859855481932824401210993)
            ·
              refine ⟨2144891611449618300908245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2859855481932824401210993 2144891611449618300908245)
              ·
                refine ⟨50270897143350428927537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2144891611449618300908245 50270897143350428927537)
                ·
                  rfl

theorem cell19_165210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 7].length) (baseStart_165210 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_165210 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_165210 prefixEnd_165210 := by exact prefixLift 165210
  have htrace : WordTrace (prefixWord ++ tailWord_165210) baseStart_165210 baseEnd_165210 := by
    simpa [prefixWord, tailWord_165210, baseEnd_165210] using wordTrace_append hprefix tailTrace_165210
  have hstable : (prefixWord ++ tailWord_165210).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165210).length < 2 ^ (prefixWord ++ tailWord_165210).sum := by decide
  have hdescent : baseEnd_165210 < baseStart_165210 := by decide
  rcases family_descends (prefixWord ++ tailWord_165210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165360 : List Nat := [2, 1, 1, 1, 3, 6, 1, 4]
def baseStart_165360 : Nat := 118140960795 + 165360 * 2 ^ 59
def prefixEnd_165360 : Nat := 4983230072969 + 3 ^ 40 * 165360 * 2
def baseEnd_165360 : Nat := 50316539868194525593795

theorem tailTrace_165360 : CollatzResearch.WordTrace tailWord_165360 prefixEnd_165360 50316539868194525593795 := by
  unfold tailWord_165360
  simp only [CollatzResearch.WordTrace]
  refine ⟨3015587340468218042354767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4020783120624290723139689 3015587340468218042354767)
  ·
    refine ⟨4523381010702327063532151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3015587340468218042354767 4523381010702327063532151)
    ·
      refine ⟨6785071516053490595298227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4523381010702327063532151 6785071516053490595298227)
      ·
        refine ⟨10177607274080235892947341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6785071516053490595298227 10177607274080235892947341)
        ·
          refine ⟨3816602727780088459855253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10177607274080235892947341 3816602727780088459855253)
          ·
            refine ⟨178903252864691646555715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 3816602727780088459855253 178903252864691646555715)
            ·
              refine ⟨268354879297037469833573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 178903252864691646555715 268354879297037469833573)
              ·
                refine ⟨50316539868194525593795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 268354879297037469833573 50316539868194525593795)
                ·
                  rfl

theorem cell19_165360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 1, 4].length) (baseStart_165360 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_165360 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_165360 prefixEnd_165360 := by exact prefixLift 165360
  have htrace : WordTrace (prefixWord ++ tailWord_165360) baseStart_165360 baseEnd_165360 := by
    simpa [prefixWord, tailWord_165360, baseEnd_165360] using wordTrace_append hprefix tailTrace_165360
  have hstable : (prefixWord ++ tailWord_165360).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165360).length < 2 ^ (prefixWord ++ tailWord_165360).sum := by decide
  have hdescent : baseEnd_165360 < baseStart_165360 := by decide
  rcases family_descends (prefixWord ++ tailWord_165360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165377 : List Nat := [1, 2, 4, 1, 4, 1, 3, 3]
def baseStart_165377 : Nat := 118140960795 + 165377 * 2 ^ 59
def prefixEnd_165377 : Nat := 4983230072969 + 3 ^ 40 * 165377 * 2
def baseEnd_165377 : Nat := 50321712710343523215971

theorem tailTrace_165377 : CollatzResearch.WordTrace tailWord_165377 prefixEnd_165377 50321712710343523215971 := by
  unfold tailWord_165377
  simp only [CollatzResearch.WordTrace]
  refine ⟨6031794721874847988078385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4021196481249898658718923 6031794721874847988078385)
  ·
    refine ⟨4523846041406135991058789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6031794721874847988078385 4523846041406135991058789)
    ·
      refine ⟨848221132763650498323523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4523846041406135991058789 848221132763650498323523)
      ·
        refine ⟨1272331699145475747485285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 848221132763650498323523 1272331699145475747485285)
        ·
          refine ⟨238562193589776702653491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1272331699145475747485285 238562193589776702653491)
          ·
            refine ⟨357843290384665053980237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 238562193589776702653491 357843290384665053980237)
            ·
              refine ⟨134191233894249395242589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 357843290384665053980237 134191233894249395242589)
              ·
                refine ⟨50321712710343523215971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 134191233894249395242589 50321712710343523215971)
                ·
                  rfl

theorem cell19_165377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 3, 3].length) (baseStart_165377 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_165377 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_165377 prefixEnd_165377 := by exact prefixLift 165377
  have htrace : WordTrace (prefixWord ++ tailWord_165377) baseStart_165377 baseEnd_165377 := by
    simpa [prefixWord, tailWord_165377, baseEnd_165377] using wordTrace_append hprefix tailTrace_165377
  have hstable : (prefixWord ++ tailWord_165377).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165377).length < 2 ^ (prefixWord ++ tailWord_165377).sum := by decide
  have hdescent : baseEnd_165377 < baseStart_165377 := by decide
  rcases family_descends (prefixWord ++ tailWord_165377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165396 : List Nat := [2, 4, 3, 1, 2, 1, 6]
def baseStart_165396 : Nat := 118140960795 + 165396 * 2 ^ 59
def prefixEnd_165396 : Nat := 4983230072969 + 3 ^ 40 * 165396 * 2
def baseEnd_165396 : Nat := 16775831374052369597899

theorem tailTrace_165396 : CollatzResearch.WordTrace tailWord_165396 prefixEnd_165396 16775831374052369597899 := by
  unfold tailWord_165396
  simp only [CollatzResearch.WordTrace]
  refine ⟨3016243854403007116510021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4021658472537342822013361 3016243854403007116510021)
  ·
    refine ⟨565545722700563834345629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3016243854403007116510021 565545722700563834345629)
    ·
      refine ⟨212079646012711437879611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 565545722700563834345629 212079646012711437879611)
      ·
        refine ⟨318119469019067156819417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212079646012711437879611 318119469019067156819417)
        ·
          refine ⟨238589601764300367614563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 318119469019067156819417 238589601764300367614563)
          ·
            refine ⟨357884402646450551421845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 238589601764300367614563 357884402646450551421845)
            ·
              refine ⟨16775831374052369597899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 357884402646450551421845 16775831374052369597899)
              ·
                rfl

theorem cell19_165396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 6].length) (baseStart_165396 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_165396 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_165396 prefixEnd_165396 := by exact prefixLift 165396
  have htrace : WordTrace (prefixWord ++ tailWord_165396) baseStart_165396 baseEnd_165396 := by
    simpa [prefixWord, tailWord_165396, baseEnd_165396] using wordTrace_append hprefix tailTrace_165396
  have hstable : (prefixWord ++ tailWord_165396).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165396).length < 2 ^ (prefixWord ++ tailWord_165396).sum := by decide
  have hdescent : baseEnd_165396 < baseStart_165396 := by decide
  rcases family_descends (prefixWord ++ tailWord_165396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165430 : List Nat := [5, 1, 2, 1, 4, 1, 2, 3]
def baseStart_165430 : Nat := 118140960795 + 165430 * 2 ^ 59
def prefixEnd_165430 : Nat := 4983230072969 + 3 ^ 40 * 165430 * 2
def baseEnd_165430 : Nat := 50337839806455104038049

theorem tailTrace_165430 : CollatzResearch.WordTrace tailWord_165430 prefixEnd_165430 50337839806455104038049 := by
  unfold tailWord_165430
  simp only [CollatzResearch.WordTrace]
  refine ⟨377107986917677377484859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4022485193788558693171829 377107986917677377484859)
  ·
    refine ⟨565661980376516066227289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 377107986917677377484859 565661980376516066227289)
    ·
      refine ⟨424246485282387049670467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 565661980376516066227289 424246485282387049670467)
      ·
        refine ⟨636369727923580574505701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 424246485282387049670467 636369727923580574505701)
        ·
          refine ⟨119319323985671357719819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 636369727923580574505701 119319323985671357719819)
          ·
            refine ⟨178978985978507036579729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119319323985671357719819 178978985978507036579729)
            ·
              refine ⟨134234239483880277434797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 178978985978507036579729 134234239483880277434797)
              ·
                refine ⟨50337839806455104038049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 134234239483880277434797 50337839806455104038049)
                ·
                  rfl

theorem cell19_165430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 2, 3].length) (baseStart_165430 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_165430 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_165430 prefixEnd_165430 := by exact prefixLift 165430
  have htrace : WordTrace (prefixWord ++ tailWord_165430) baseStart_165430 baseEnd_165430 := by
    simpa [prefixWord, tailWord_165430, baseEnd_165430] using wordTrace_append hprefix tailTrace_165430
  have hstable : (prefixWord ++ tailWord_165430).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165430).length < 2 ^ (prefixWord ++ tailWord_165430).sum := by decide
  have hdescent : baseEnd_165430 < baseStart_165430 := by decide
  rcases family_descends (prefixWord ++ tailWord_165430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165436 : List Nat := [2, 2, 2, 2, 4, 1, 1, 5]
def baseStart_165436 : Nat := 118140960795 + 165436 * 2 ^ 59
def prefixEnd_165436 : Nat := 4983230072969 + 3 ^ 40 * 165436 * 2
def baseEnd_165436 : Nat := 50339665515448867904699

theorem tailTrace_165436 : CollatzResearch.WordTrace tailWord_165436 prefixEnd_165436 50339665515448867904699 := by
  unfold tailWord_165436
  simp only [CollatzResearch.WordTrace]
  refine ⟨3016973314330550532238081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4022631085774067376317441 3016973314330550532238081)
  ·
    refine ⟨2262729985747912899178561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3016973314330550532238081 2262729985747912899178561)
    ·
      refine ⟨1697047489310934674383921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2262729985747912899178561 1697047489310934674383921)
      ·
        refine ⟨1272785616983201005787941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1697047489310934674383921 1272785616983201005787941)
        ·
          refine ⟨238647303184350188585239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1272785616983201005787941 238647303184350188585239)
          ·
            refine ⟨357970954776525282877859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 238647303184350188585239 357970954776525282877859)
            ·
              refine ⟨536956432164787924316789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 357970954776525282877859 536956432164787924316789)
              ·
                refine ⟨50339665515448867904699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 536956432164787924316789 50339665515448867904699)
                ·
                  rfl

theorem cell19_165436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 5].length) (baseStart_165436 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_165436 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_165436 prefixEnd_165436 := by exact prefixLift 165436
  have htrace : WordTrace (prefixWord ++ tailWord_165436) baseStart_165436 baseEnd_165436 := by
    simpa [prefixWord, tailWord_165436, baseEnd_165436] using wordTrace_append hprefix tailTrace_165436
  have hstable : (prefixWord ++ tailWord_165436).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165436).length < 2 ^ (prefixWord ++ tailWord_165436).sum := by decide
  have hdescent : baseEnd_165436 < baseStart_165436 := by decide
  rcases family_descends (prefixWord ++ tailWord_165436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165453 : List Nat := [1, 6, 1, 1, 3, 2, 5]
def baseStart_165453 : Nat := 118140960795 + 165453 * 2 ^ 59
def prefixEnd_165453 : Nat := 4983230072969 + 3 ^ 40 * 165453 * 2
def baseEnd_165453 : Nat := 16781612785865955175625

theorem tailTrace_165453 : CollatzResearch.WordTrace tailWord_165453 prefixEnd_165453 16781612785865955175625 := by
  unfold tailWord_165453
  simp only [CollatzResearch.WordTrace]
  refine ⟨6034566669599512967845013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4023044446399675311896675 6034566669599512967845013)
  ·
    refine ⟨282870312637477170367735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 6034566669599512967845013 282870312637477170367735)
    ·
      refine ⟨424305468956215755551603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 282870312637477170367735 424305468956215755551603)
      ·
        refine ⟨636458203434323633327405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 424305468956215755551603 636458203434323633327405)
        ·
          refine ⟨238671826287871362497777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 636458203434323633327405 238671826287871362497777)
          ·
            refine ⟨179003869715903521873333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 238671826287871362497777 179003869715903521873333)
            ·
              refine ⟨16781612785865955175625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 179003869715903521873333 16781612785865955175625)
              ·
                rfl

theorem cell19_165453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 5].length) (baseStart_165453 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_165453 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_165453 prefixEnd_165453 := by exact prefixLift 165453
  have htrace : WordTrace (prefixWord ++ tailWord_165453) baseStart_165453 baseEnd_165453 := by
    simpa [prefixWord, tailWord_165453, baseEnd_165453] using wordTrace_append hprefix tailTrace_165453
  have hstable : (prefixWord ++ tailWord_165453).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165453).length < 2 ^ (prefixWord ++ tailWord_165453).sum := by decide
  have hdescent : baseEnd_165453 < baseStart_165453 := by decide
  rcases family_descends (prefixWord ++ tailWord_165453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165476 : List Nat := [2, 3, 1, 1, 2, 3, 1, 6]
def baseStart_165476 : Nat := 118140960795 + 165476 * 2 ^ 59
def prefixEnd_165476 : Nat := 4983230072969 + 3 ^ 40 * 165476 * 2
def baseEnd_165476 : Nat := 50351836908740627015701

theorem tailTrace_165476 : CollatzResearch.WordTrace tailWord_165476 prefixEnd_165476 50351836908740627015701 := by
  unfold tailWord_165476
  simp only [CollatzResearch.WordTrace]
  refine ⟨3017702774258093947966141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4023603699010791930621521 3017702774258093947966141)
  ·
    refine ⟨1131638540346785230487303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3017702774258093947966141 1131638540346785230487303)
    ·
      refine ⟨1697457810520177845730955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1131638540346785230487303 1697457810520177845730955)
      ·
        refine ⟨2546186715780266768596433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1697457810520177845730955 2546186715780266768596433)
        ·
          refine ⟨1909640036835200076447325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2546186715780266768596433 1909640036835200076447325)
          ·
            refine ⟨716115013813200028667747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1909640036835200076447325 716115013813200028667747)
            ·
              refine ⟨1074172520719800043001621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 716115013813200028667747 1074172520719800043001621)
              ·
                refine ⟨50351836908740627015701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1074172520719800043001621 50351836908740627015701)
                ·
                  rfl

theorem cell19_165476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 6].length) (baseStart_165476 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_165476 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_165476 prefixEnd_165476 := by exact prefixLift 165476
  have htrace : WordTrace (prefixWord ++ tailWord_165476) baseStart_165476 baseEnd_165476 := by
    simpa [prefixWord, tailWord_165476, baseEnd_165476] using wordTrace_append hprefix tailTrace_165476
  have hstable : (prefixWord ++ tailWord_165476).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165476).length < 2 ^ (prefixWord ++ tailWord_165476).sum := by decide
  have hdescent : baseEnd_165476 < baseStart_165476 := by decide
  rcases family_descends (prefixWord ++ tailWord_165476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165493 : List Nat := [1, 3, 4, 2, 1, 1, 2, 5]
def baseStart_165493 : Nat := 118140960795 + 165493 * 2 ^ 59
def prefixEnd_165493 : Nat := 4983230072969 + 3 ^ 40 * 165493 * 2
def baseEnd_165493 : Nat := 50357009750889624637877

theorem tailTrace_165493 : CollatzResearch.WordTrace tailWord_165493 prefixEnd_165493 50357009750889624637877 := by
  unfold tailWord_165493
  simp only [CollatzResearch.WordTrace]
  refine ⟨6036025589454599799301133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4024017059636399866200755 6036025589454599799301133)
  ·
    refine ⟨2263509596045474924737925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6036025589454599799301133 2263509596045474924737925)
    ·
      refine ⟨424408049258526548388361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2263509596045474924737925 424408049258526548388361)
      ·
        refine ⟨318306036943894911291271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 424408049258526548388361 318306036943894911291271)
        ·
          refine ⟨477459055415842366936907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 318306036943894911291271 477459055415842366936907)
          ·
            refine ⟨716188583123763550405361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 477459055415842366936907 716188583123763550405361)
            ·
              refine ⟨537141437342822662804021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 716188583123763550405361 537141437342822662804021)
              ·
                refine ⟨50357009750889624637877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 537141437342822662804021 50357009750889624637877)
                ·
                  rfl

theorem cell19_165493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 5].length) (baseStart_165493 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_165493 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_165493 prefixEnd_165493 := by exact prefixLift 165493
  have htrace : WordTrace (prefixWord ++ tailWord_165493) baseStart_165493 baseEnd_165493 := by
    simpa [prefixWord, tailWord_165493, baseEnd_165493] using wordTrace_append hprefix tailTrace_165493
  have hstable : (prefixWord ++ tailWord_165493).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165493).length < 2 ^ (prefixWord ++ tailWord_165493).sum := by decide
  have hdescent : baseEnd_165493 < baseStart_165493 := by decide
  rcases family_descends (prefixWord ++ tailWord_165493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165512 : List Nat := [2, 1, 3, 5, 1, 7]
def baseStart_165512 : Nat := 118140960795 + 165512 * 2 ^ 59
def prefixEnd_165512 : Nat := 4983230072969 + 3 ^ 40 * 165512 * 2
def baseEnd_165512 : Nat := 5595865684744801135067

theorem tailTrace_165512 : CollatzResearch.WordTrace tailWord_165512 prefixEnd_165512 5595865684744801135067 := by
  unfold tailWord_165512
  simp only [CollatzResearch.WordTrace]
  refine ⟨3018359288192883022121395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4024479050923844029495193 3018359288192883022121395)
  ·
    refine ⟨4527538932289324533182093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3018359288192883022121395 4527538932289324533182093)
    ·
      refine ⟨1697827099608496699943285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4527538932289324533182093 1697827099608496699943285)
      ·
        refine ⟨159171290588296565619683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1697827099608496699943285 159171290588296565619683)
        ·
          refine ⟨238756935882444848429525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159171290588296565619683 238756935882444848429525)
          ·
            refine ⟨5595865684744801135067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 238756935882444848429525 5595865684744801135067)
            ·
              rfl

theorem cell19_165512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 7].length) (baseStart_165512 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_165512 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_165512 prefixEnd_165512 := by exact prefixLift 165512
  have htrace : WordTrace (prefixWord ++ tailWord_165512) baseStart_165512 baseEnd_165512 := by
    simpa [prefixWord, tailWord_165512, baseEnd_165512] using wordTrace_append hprefix tailTrace_165512
  have hstable : (prefixWord ++ tailWord_165512).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165512).length < 2 ^ (prefixWord ++ tailWord_165512).sum := by decide
  have hdescent : baseEnd_165512 < baseStart_165512 := by decide
  rcases family_descends (prefixWord ++ tailWord_165512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165514 : List Nat := [3, 1, 2, 3, 2, 8]
def baseStart_165514 : Nat := 118140960795 + 165514 * 2 ^ 59
def prefixEnd_165514 : Nat := 4983230072969 + 3 ^ 40 * 165514 * 2
def baseEnd_165514 : Nat := 5595933303596422019017

theorem tailTrace_165514 : CollatzResearch.WordTrace tailWord_165514 prefixEnd_165514 5595933303596422019017 := by
  unfold tailWord_165514
  simp only [CollatzResearch.WordTrace]
  refine ⟨1509197880594630096453899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4024527681585680257210397 1509197880594630096453899)
  ·
    refine ⟨2263796820891945144680849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1509197880594630096453899 2263796820891945144680849)
    ·
      refine ⟨1697847615668958858510637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2263796820891945144680849 1697847615668958858510637)
      ·
        refine ⟨636692855875859571941489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1697847615668958858510637 636692855875859571941489)
        ·
          refine ⟨477519641906894678956117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 636692855875859571941489 477519641906894678956117)
          ·
            refine ⟨5595933303596422019017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 477519641906894678956117 5595933303596422019017)
            ·
              rfl

theorem cell19_165514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 8].length) (baseStart_165514 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_165514 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_165514 prefixEnd_165514 := by exact prefixLift 165514
  have htrace : WordTrace (prefixWord ++ tailWord_165514) baseStart_165514 baseEnd_165514 := by
    simpa [prefixWord, tailWord_165514, baseEnd_165514] using wordTrace_append hprefix tailTrace_165514
  have hstable : (prefixWord ++ tailWord_165514).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165514).length < 2 ^ (prefixWord ++ tailWord_165514).sum := by decide
  have hdescent : baseEnd_165514 < baseStart_165514 := by decide
  rcases family_descends (prefixWord ++ tailWord_165514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165544 : List Nat := [2, 1, 7, 1, 1, 1, 3, 3]
def baseStart_165544 : Nat := 118140960795 + 165544 * 2 ^ 59
def prefixEnd_165544 : Nat := 4983230072969 + 3 ^ 40 * 165544 * 2
def baseEnd_165544 : Nat := 50372528277336617504405

theorem tailTrace_165544 : CollatzResearch.WordTrace tailWord_165544 prefixEnd_165544 50372528277336617504405 := by
  unfold tailWord_165544
  simp only [CollatzResearch.WordTrace]
  refine ⟨3018942856134917754703843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4025257141513223672938457 3018942856134917754703843)
  ·
    refine ⟨4528414284202376632055765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3018942856134917754703843 4528414284202376632055765)
    ·
      refine ⟨106134709785993202313807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 4528414284202376632055765 106134709785993202313807)
      ·
        refine ⟨159202064678989803470711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106134709785993202313807 159202064678989803470711)
        ·
          refine ⟨238803097018484705206067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159202064678989803470711 238803097018484705206067)
          ·
            refine ⟨358204645527727057809101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 238803097018484705206067 358204645527727057809101)
            ·
              refine ⟨134326742072897646678413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 358204645527727057809101 134326742072897646678413)
              ·
                refine ⟨50372528277336617504405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 134326742072897646678413 50372528277336617504405)
                ·
                  rfl

theorem cell19_165544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 3, 3].length) (baseStart_165544 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_165544 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_165544 prefixEnd_165544 := by exact prefixLift 165544
  have htrace : WordTrace (prefixWord ++ tailWord_165544) baseStart_165544 baseEnd_165544 := by
    simpa [prefixWord, tailWord_165544, baseEnd_165544] using wordTrace_append hprefix tailTrace_165544
  have hstable : (prefixWord ++ tailWord_165544).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165544).length < 2 ^ (prefixWord ++ tailWord_165544).sum := by decide
  have hdescent : baseEnd_165544 < baseStart_165544 := by decide
  rcases family_descends (prefixWord ++ tailWord_165544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165603 : List Nat := [1, 1, 1, 7, 3, 1, 2, 3]
def baseStart_165603 : Nat := 118140960795 + 165603 * 2 ^ 59
def prefixEnd_165603 : Nat := 4983230072969 + 3 ^ 40 * 165603 * 2
def baseEnd_165603 : Nat := 50390481082441962193133

theorem tailTrace_165603 : CollatzResearch.WordTrace tailWord_165603 prefixEnd_165603 50390481082441962193133 := by
  unfold tailWord_165603
  simp only [CollatzResearch.WordTrace]
  refine ⟨6040037619056088585805463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4026691746037392390536975 6040037619056088585805463)
  ·
    refine ⟨9060056428584132878708195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6040037619056088585805463 9060056428584132878708195)
    ·
      refine ⟨13590084642876199318062293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9060056428584132878708195 13590084642876199318062293)
      ·
        refine ⟨318517608817410921517085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 13590084642876199318062293 318517608817410921517085)
        ·
          refine ⟨119444103306529095568907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 318517608817410921517085 119444103306529095568907)
          ·
            refine ⟨179166154959793643353361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119444103306529095568907 179166154959793643353361)
            ·
              refine ⟨134374616219845232515021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 179166154959793643353361 134374616219845232515021)
              ·
                refine ⟨50390481082441962193133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 134374616219845232515021 50390481082441962193133)
                ·
                  rfl

theorem cell19_165603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 2, 3].length) (baseStart_165603 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_165603 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_165603 prefixEnd_165603 := by exact prefixLift 165603
  have htrace : WordTrace (prefixWord ++ tailWord_165603) baseStart_165603 baseEnd_165603 := by
    simpa [prefixWord, tailWord_165603, baseEnd_165603] using wordTrace_append hprefix tailTrace_165603
  have hstable : (prefixWord ++ tailWord_165603).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165603).length < 2 ^ (prefixWord ++ tailWord_165603).sum := by decide
  have hdescent : baseEnd_165603 < baseStart_165603 := by decide
  rcases family_descends (prefixWord ++ tailWord_165603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165666 : List Nat := [3, 3, 1, 1, 2, 1, 1, 7]
def baseStart_165666 : Nat := 118140960795 + 165666 * 2 ^ 59
def prefixEnd_165666 : Nat := 4983230072969 + 3 ^ 40 * 165666 * 2
def baseEnd_165666 : Nat := 50409651026876482792961

theorem tailTrace_165666 : CollatzResearch.WordTrace tailWord_165666 prefixEnd_165666 50409651026876482792961 := by
  unfold tailWord_165666
  simp only [CollatzResearch.WordTrace]
  refine ⟨1510583854456962586337213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4028223611885233563565901 1510583854456962586337213)
  ·
    refine ⟨566468945421360969876455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1510583854456962586337213 566468945421360969876455)
    ·
      refine ⟨849703418132041454814683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 566468945421360969876455 849703418132041454814683)
      ·
        refine ⟨1274555127198062182222025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 849703418132041454814683 1274555127198062182222025)
        ·
          refine ⟨955916345398546636666519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1274555127198062182222025 955916345398546636666519)
          ·
            refine ⟨1433874518097819954999779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 955916345398546636666519 1433874518097819954999779)
            ·
              refine ⟨2150811777146729932499669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1433874518097819954999779 2150811777146729932499669)
              ·
                refine ⟨50409651026876482792961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2150811777146729932499669 50409651026876482792961)
                ·
                  rfl

theorem cell19_165666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 7].length) (baseStart_165666 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_165666 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_165666 prefixEnd_165666 := by exact prefixLift 165666
  have htrace : WordTrace (prefixWord ++ tailWord_165666) baseStart_165666 baseEnd_165666 := by
    simpa [prefixWord, tailWord_165666, baseEnd_165666] using wordTrace_append hprefix tailTrace_165666
  have hstable : (prefixWord ++ tailWord_165666).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165666).length < 2 ^ (prefixWord ++ tailWord_165666).sum := by decide
  have hdescent : baseEnd_165666 < baseStart_165666 := by decide
  rcases family_descends (prefixWord ++ tailWord_165666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165685 : List Nat := [1, 3, 3, 1, 4, 7]
def baseStart_165685 : Nat := 118140960795 + 165685 * 2 ^ 59
def prefixEnd_165685 : Nat := 4983230072969 + 3 ^ 40 * 165685 * 2
def baseEnd_165685 : Nat := 5601714715410007596743

theorem tailTrace_165685 : CollatzResearch.WordTrace tailWord_165685 prefixEnd_165685 5601714715410007596743 := by
  unfold tailWord_165685
  simp only [CollatzResearch.WordTrace]
  refine ⟨6043028404759016590290509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4028685603172677726860339 6043028404759016590290509)
  ·
    refine ⟨2266135651784631221358941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6043028404759016590290509 2266135651784631221358941)
    ·
      refine ⟨849800869419236708009603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2266135651784631221358941 849800869419236708009603)
      ·
        refine ⟨1274701304128855062014405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 849800869419236708009603 1274701304128855062014405)
        ·
          refine ⟨239006494524160324127701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1274701304128855062014405 239006494524160324127701)
          ·
            refine ⟨5601714715410007596743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 239006494524160324127701 5601714715410007596743)
            ·
              rfl

theorem cell19_165685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 7].length) (baseStart_165685 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_165685 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_165685 prefixEnd_165685 := by exact prefixLift 165685
  have htrace : WordTrace (prefixWord ++ tailWord_165685) baseStart_165685 baseEnd_165685 := by
    simpa [prefixWord, tailWord_165685, baseEnd_165685] using wordTrace_append hprefix tailTrace_165685
  have hstable : (prefixWord ++ tailWord_165685).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165685).length < 2 ^ (prefixWord ++ tailWord_165685).sum := by decide
  have hdescent : baseEnd_165685 < baseStart_165685 := by decide
  rcases family_descends (prefixWord ++ tailWord_165685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165704 : List Nat := [2, 1, 3, 1, 1, 4, 3, 4]
def baseStart_165704 : Nat := 118140960795 + 165704 * 2 ^ 59
def prefixEnd_165704 : Nat := 4983230072969 + 3 ^ 40 * 165704 * 2
def baseEnd_165704 : Nat := 50421213850503653948413

theorem tailTrace_165704 : CollatzResearch.WordTrace tailWord_165704 prefixEnd_165704 50421213850503653948413 := by
  unfold tailWord_165704
  simp only [CollatzResearch.WordTrace]
  refine ⟨3021860695845091417616083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4029147594460121890154777 3021860695845091417616083)
  ·
    refine ⟨4532791043767637126424125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3021860695845091417616083 4532791043767637126424125)
    ·
      refine ⟨1699796641412863922409047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4532791043767637126424125 1699796641412863922409047)
      ·
        refine ⟨2549694962119295883613571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1699796641412863922409047 2549694962119295883613571)
        ·
          refine ⟨3824542443178943825420357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2549694962119295883613571 3824542443178943825420357)
          ·
            refine ⟨717101708096051967266317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3824542443178943825420357 717101708096051967266317)
            ·
              refine ⟨268913140536019487724869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 717101708096051967266317 268913140536019487724869)
              ·
                refine ⟨50421213850503653948413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 268913140536019487724869 50421213850503653948413)
                ·
                  rfl

theorem cell19_165704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 3, 4].length) (baseStart_165704 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_165704 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_165704 prefixEnd_165704 := by exact prefixLift 165704
  have htrace : WordTrace (prefixWord ++ tailWord_165704) baseStart_165704 baseEnd_165704 := by
    simpa [prefixWord, tailWord_165704, baseEnd_165704] using wordTrace_append hprefix tailTrace_165704
  have hstable : (prefixWord ++ tailWord_165704).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165704).length < 2 ^ (prefixWord ++ tailWord_165704).sum := by decide
  have hdescent : baseEnd_165704 < baseStart_165704 := by decide
  rcases family_descends (prefixWord ++ tailWord_165704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165774 : List Nat := [4, 1, 1, 5, 1, 2, 2, 3]
def baseStart_165774 : Nat := 118140960795 + 165774 * 2 ^ 59
def prefixEnd_165774 : Nat := 4983230072969 + 3 ^ 40 * 165774 * 2
def baseEnd_165774 : Nat := 50442513788764232392667

theorem tailTrace_165774 : CollatzResearch.WordTrace tailWord_165774 prefixEnd_165774 50442513788764232392667 := by
  unfold tailWord_165774
  simp only [CollatzResearch.WordTrace]
  refine ⟨755784312679573098785047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4030849667624389860186917 755784312679573098785047)
  ·
    refine ⟨1133676469019359648177571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 755784312679573098785047 1133676469019359648177571)
    ·
      refine ⟨1700514703529039472266357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1133676469019359648177571 1700514703529039472266357)
      ·
        refine ⟨159423253455847450524971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1700514703529039472266357 159423253455847450524971)
        ·
          refine ⟨239134880183771175787457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159423253455847450524971 239134880183771175787457)
          ·
            refine ⟨179351160137828381840593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 239134880183771175787457 179351160137828381840593)
            ·
              refine ⟨134513370103371286380445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 179351160137828381840593 134513370103371286380445)
              ·
                refine ⟨50442513788764232392667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 134513370103371286380445 50442513788764232392667)
                ·
                  rfl

theorem cell19_165774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 2, 3].length) (baseStart_165774 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_165774 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_165774 prefixEnd_165774 := by exact prefixLift 165774
  have htrace : WordTrace (prefixWord ++ tailWord_165774) baseStart_165774 baseEnd_165774 := by
    simpa [prefixWord, tailWord_165774, baseEnd_165774] using wordTrace_append hprefix tailTrace_165774
  have hstable : (prefixWord ++ tailWord_165774).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165774).length < 2 ^ (prefixWord ++ tailWord_165774).sum := by decide
  have hdescent : baseEnd_165774 < baseStart_165774 := by decide
  rcases family_descends (prefixWord ++ tailWord_165774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165778 : List Nat := [3, 2, 3, 2, 1, 2, 1, 5]
def baseStart_165778 : Nat := 118140960795 + 165778 * 2 ^ 59
def prefixEnd_165778 : Nat := 4983230072969 + 3 ^ 40 * 165778 * 2
def baseEnd_165778 : Nat := 50443730928093408303767

theorem tailTrace_165778 : CollatzResearch.WordTrace tailWord_165778 prefixEnd_165778 50443730928093408303767 := by
  unfold tailWord_165778
  simp only [CollatzResearch.WordTrace]
  refine ⟨1511605098355523368356497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4030946928948062315617325 1511605098355523368356497)
  ·
    refine ⟨1133703823766642526267373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1511605098355523368356497 1133703823766642526267373)
    ·
      refine ⟨425138933912490947350265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1133703823766642526267373 425138933912490947350265)
      ·
        refine ⟨318854200434368210512699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 425138933912490947350265 318854200434368210512699)
        ·
          refine ⟨478281300651552315769049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 318854200434368210512699 478281300651552315769049)
          ·
            refine ⟨358710975488664236826787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 478281300651552315769049 358710975488664236826787)
            ·
              refine ⟨538066463232996355240181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 358710975488664236826787 538066463232996355240181)
              ·
                refine ⟨50443730928093408303767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 538066463232996355240181 50443730928093408303767)
                ·
                  rfl

theorem cell19_165778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 5].length) (baseStart_165778 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_165778 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_165778 prefixEnd_165778 := by exact prefixLift 165778
  have htrace : WordTrace (prefixWord ++ tailWord_165778) baseStart_165778 baseEnd_165778 := by
    simpa [prefixWord, tailWord_165778, baseEnd_165778] using wordTrace_append hprefix tailTrace_165778
  have hstable : (prefixWord ++ tailWord_165778).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165778).length < 2 ^ (prefixWord ++ tailWord_165778).sum := by decide
  have hdescent : baseEnd_165778 < baseStart_165778 := by decide
  rcases family_descends (prefixWord ++ tailWord_165778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165799 : List Nat := [1, 1, 6, 1, 2, 1, 7]
def baseStart_165799 : Nat := 118140960795 + 165799 * 2 ^ 59
def prefixEnd_165799 : Nat := 4983230072969 + 3 ^ 40 * 165799 * 2
def baseEnd_165799 : Nat := 16816706969857193945681

theorem tailTrace_165799 : CollatzResearch.WordTrace tailWord_165799 prefixEnd_165799 16816706969857193945681 := by
  unfold tailWord_165799
  simp only [CollatzResearch.WordTrace]
  refine ⟨6047186326346014059940451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4031457550897342706626967 6047186326346014059940451)
  ·
    refine ⟨9070779489519021089910677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6047186326346014059940451 9070779489519021089910677)
    ·
      refine ⟨425192788571204113589563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 9070779489519021089910677 425192788571204113589563)
      ·
        refine ⟨637789182856806170384345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 425192788571204113589563 637789182856806170384345)
        ·
          refine ⟨478341887142604627788259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 637789182856806170384345 478341887142604627788259)
          ·
            refine ⟨717512830713906941682389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 478341887142604627788259 717512830713906941682389)
            ·
              refine ⟨16816706969857193945681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 717512830713906941682389 16816706969857193945681)
              ·
                rfl

theorem cell19_165799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 7].length) (baseStart_165799 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_165799 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_165799 prefixEnd_165799 := by exact prefixLift 165799
  have htrace : WordTrace (prefixWord ++ tailWord_165799) baseStart_165799 baseEnd_165799 := by
    simpa [prefixWord, tailWord_165799, baseEnd_165799] using wordTrace_append hprefix tailTrace_165799
  have hstable : (prefixWord ++ tailWord_165799).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165799).length < 2 ^ (prefixWord ++ tailWord_165799).sum := by decide
  have hdescent : baseEnd_165799 < baseStart_165799 := by decide
  rcases family_descends (prefixWord ++ tailWord_165799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165839 : List Nat := [1, 1, 2, 1, 1, 5, 1, 7]
def baseStart_165839 : Nat := 118140960795 + 165839 * 2 ^ 59
def prefixEnd_165839 : Nat := 4983230072969 + 3 ^ 40 * 165839 * 2
def baseEnd_165839 : Nat := 50462292302863340948045

theorem tailTrace_165839 : CollatzResearch.WordTrace tailWord_165839 prefixEnd_165839 50462292302863340948045 := by
  unfold tailWord_165839
  simp only [CollatzResearch.WordTrace]
  refine ⟨6048645246201100891396571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4032430164134067260931047 6048645246201100891396571)
  ·
    refine ⟨9072967869301651337094857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6048645246201100891396571 9072967869301651337094857)
    ·
      refine ⟨6804725901976238502821143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9072967869301651337094857 6804725901976238502821143)
      ·
        refine ⟨10207088852964357754231715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6804725901976238502821143 10207088852964357754231715)
        ·
          refine ⟨15310633279446536631347573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10207088852964357754231715 15310633279446536631347573)
          ·
            refine ⟨1435371869948112809188835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15310633279446536631347573 1435371869948112809188835)
            ·
              refine ⟨2153057804922169213783253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1435371869948112809188835 2153057804922169213783253)
              ·
                refine ⟨50462292302863340948045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2153057804922169213783253 50462292302863340948045)
                ·
                  rfl

theorem cell19_165839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 7].length) (baseStart_165839 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_165839 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_165839 prefixEnd_165839 := by exact prefixLift 165839
  have htrace : WordTrace (prefixWord ++ tailWord_165839) baseStart_165839 baseEnd_165839 := by
    simpa [prefixWord, tailWord_165839, baseEnd_165839] using wordTrace_append hprefix tailTrace_165839
  have hstable : (prefixWord ++ tailWord_165839).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165839).length < 2 ^ (prefixWord ++ tailWord_165839).sum := by decide
  have hdescent : baseEnd_165839 < baseStart_165839 := by decide
  rcases family_descends (prefixWord ++ tailWord_165839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165852 : List Nat := [2, 2, 6, 1, 1, 7]
def baseStart_165852 : Nat := 118140960795 + 165852 * 2 ^ 59
def prefixEnd_165852 : Nat := 4983230072969 + 3 ^ 40 * 165852 * 2
def baseEnd_165852 : Nat := 5607360889520351406569

theorem tailTrace_165852 : CollatzResearch.WordTrace tailWord_165852 prefixEnd_165852 5607360889520351406569 := by
  unfold tailWord_165852
  simp only [CollatzResearch.WordTrace]
  refine ⟨3024559697577002055809905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4032746263436002741079873 3024559697577002055809905)
  ·
    refine ⟨2268419773182751541857429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3024559697577002055809905 2268419773182751541857429)
    ·
      refine ⟨106332176867941478524567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 2268419773182751541857429 106332176867941478524567)
      ·
        refine ⟨159498265301912217786851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106332176867941478524567 159498265301912217786851)
        ·
          refine ⟨239247397952868326680277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159498265301912217786851 239247397952868326680277)
          ·
            refine ⟨5607360889520351406569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 239247397952868326680277 5607360889520351406569)
            ·
              rfl

theorem cell19_165852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 7].length) (baseStart_165852 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_165852 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_165852 prefixEnd_165852 := by exact prefixLift 165852
  have htrace : WordTrace (prefixWord ++ tailWord_165852) baseStart_165852 baseEnd_165852 := by
    simpa [prefixWord, tailWord_165852, baseEnd_165852] using wordTrace_append hprefix tailTrace_165852
  have hstable : (prefixWord ++ tailWord_165852).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165852).length < 2 ^ (prefixWord ++ tailWord_165852).sum := by decide
  have hdescent : baseEnd_165852 < baseStart_165852 := by decide
  rcases family_descends (prefixWord ++ tailWord_165852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165869 : List Nat := [1, 5, 1, 4, 2, 1, 1, 4]
def baseStart_165869 : Nat := 118140960795 + 165869 * 2 ^ 59
def prefixEnd_165869 : Nat := 4983230072969 + 3 ^ 40 * 165869 * 2
def baseEnd_165869 : Nat := 50471420847832160281297

theorem tailTrace_165869 : CollatzResearch.WordTrace tailWord_165869 prefixEnd_165869 50471420847832160281297 := by
  unfold tailWord_165869
  simp only [CollatzResearch.WordTrace]
  refine ⟨6049739436092416014988661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4033159624061610676659107 6049739436092416014988661)
  ·
    refine ⟨567163072133664001405187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6049739436092416014988661 567163072133664001405187)
    ·
      refine ⟨850744608200496002107781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 567163072133664001405187 850744608200496002107781)
      ·
        refine ⟨159514614037593000395209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 850744608200496002107781 159514614037593000395209)
        ·
          refine ⟨119635960528194750296407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 159514614037593000395209 119635960528194750296407)
          ·
            refine ⟨179453940792292125444611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119635960528194750296407 179453940792292125444611)
            ·
              refine ⟨269180911188438188166917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 179453940792292125444611 269180911188438188166917)
              ·
                refine ⟨50471420847832160281297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 269180911188438188166917 50471420847832160281297)
                ·
                  rfl

theorem cell19_165869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 1, 4].length) (baseStart_165869 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_165869 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_165869 prefixEnd_165869 := by exact prefixLift 165869
  have htrace : WordTrace (prefixWord ++ tailWord_165869) baseStart_165869 baseEnd_165869 := by
    simpa [prefixWord, tailWord_165869, baseEnd_165869] using wordTrace_append hprefix tailTrace_165869
  have hstable : (prefixWord ++ tailWord_165869).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165869).length < 2 ^ (prefixWord ++ tailWord_165869).sum := by decide
  have hdescent : baseEnd_165869 < baseStart_165869 := by decide
  rcases family_descends (prefixWord ++ tailWord_165869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165873 : List Nat := [1, 2, 2, 2, 5, 2, 1, 4]
def baseStart_165873 : Nat := 118140960795 + 165873 * 2 ^ 59
def prefixEnd_165873 : Nat := 4983230072969 + 3 ^ 40 * 165873 * 2
def baseEnd_165873 : Nat := 50472637987161336192397

theorem tailTrace_165873 : CollatzResearch.WordTrace tailWord_165873 prefixEnd_165873 50472637987161336192397 := by
  unfold tailWord_165873
  simp only [CollatzResearch.WordTrace]
  refine ⟨6049885328077924698134273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4033256885385283132089515 6049885328077924698134273)
  ·
    refine ⟨4537413996058443523600705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6049885328077924698134273 4537413996058443523600705)
    ·
      refine ⟨3403060497043832642700529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4537413996058443523600705 3403060497043832642700529)
      ·
        refine ⟨2552295372782874482025397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3403060497043832642700529 2552295372782874482025397)
        ·
          refine ⟨239277691198394482689881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2552295372782874482025397 239277691198394482689881)
          ·
            refine ⟨179458268398795862017411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 239277691198394482689881 179458268398795862017411)
            ·
              refine ⟨269187402598193793026117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 179458268398795862017411 269187402598193793026117)
              ·
                refine ⟨50472637987161336192397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 269187402598193793026117 50472637987161336192397)
                ·
                  rfl

theorem cell19_165873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 1, 4].length) (baseStart_165873 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_165873 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_165873 prefixEnd_165873 := by exact prefixLift 165873
  have htrace : WordTrace (prefixWord ++ tailWord_165873) baseStart_165873 baseEnd_165873 := by
    simpa [prefixWord, tailWord_165873, baseEnd_165873] using wordTrace_append hprefix tailTrace_165873
  have hstable : (prefixWord ++ tailWord_165873).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165873).length < 2 ^ (prefixWord ++ tailWord_165873).sum := by decide
  have hdescent : baseEnd_165873 < baseStart_165873 := by decide
  rcases family_descends (prefixWord ++ tailWord_165873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165951 : List Nat := [1, 1, 2, 2, 3, 1, 6, 3]
def baseStart_165951 : Nat := 118140960795 + 165951 * 2 ^ 59
def prefixEnd_165951 : Nat := 4983230072969 + 3 ^ 40 * 165951 * 2
def baseEnd_165951 : Nat := 50496372204080266458851

theorem tailTrace_165951 : CollatzResearch.WordTrace tailWord_165951 prefixEnd_165951 50496372204080266458851 := by
  unfold tailWord_165951
  simp only [CollatzResearch.WordTrace]
  refine ⟨6052730221795344019473707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4035153481196896012982471 6052730221795344019473707)
  ·
    refine ⟨9079095332693016029210561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6052730221795344019473707 9079095332693016029210561)
    ·
      refine ⟨6809321499519762021907921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9079095332693016029210561 6809321499519762021907921)
      ·
        refine ⟨5106991124639821516430941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6809321499519762021907921 5106991124639821516430941)
        ·
          refine ⟨1915121671739933068661603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5106991124639821516430941 1915121671739933068661603)
          ·
            refine ⟨2872682507609899602992405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1915121671739933068661603 2872682507609899602992405)
            ·
              refine ⟨134656992544214043890269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 2872682507609899602992405 134656992544214043890269)
              ·
                refine ⟨50496372204080266458851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 134656992544214043890269 50496372204080266458851)
                ·
                  rfl

theorem cell19_165951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 6, 3].length) (baseStart_165951 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_165951 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_165951 prefixEnd_165951 := by exact prefixLift 165951
  have htrace : WordTrace (prefixWord ++ tailWord_165951) baseStart_165951 baseEnd_165951 := by
    simpa [prefixWord, tailWord_165951, baseEnd_165951] using wordTrace_append hprefix tailTrace_165951
  have hstable : (prefixWord ++ tailWord_165951).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165951).length < 2 ^ (prefixWord ++ tailWord_165951).sum := by decide
  have hdescent : baseEnd_165951 < baseStart_165951 := by decide
  rcases family_descends (prefixWord ++ tailWord_165951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165989 : List Nat := [1, 3, 1, 3, 2, 3, 2, 4]
def baseStart_165989 : Nat := 118140960795 + 165989 * 2 ^ 59
def prefixEnd_165989 : Nat := 4983230072969 + 3 ^ 40 * 165989 * 2
def baseEnd_165989 : Nat := 50507935027707437614303

theorem tailTrace_165989 : CollatzResearch.WordTrace tailWord_165989 prefixEnd_165989 50507935027707437614303 := by
  unfold tailWord_165989
  simp only [CollatzResearch.WordTrace]
  refine ⟨6054116195657676509357021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4036077463771784339571347 6054116195657676509357021)
  ·
    refine ⟨2270293573371628691008883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6054116195657676509357021 2270293573371628691008883)
    ·
      refine ⟨3405440360057443036513325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2270293573371628691008883 3405440360057443036513325)
      ·
        refine ⟨1277040135021541138692497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3405440360057443036513325 1277040135021541138692497)
        ·
          refine ⟨957780101266155854019373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1277040135021541138692497 957780101266155854019373)
          ·
            refine ⟨359167537974808445257265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 957780101266155854019373 359167537974808445257265)
            ·
              refine ⟨269375653481106333942949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 359167537974808445257265 269375653481106333942949)
              ·
                refine ⟨50507935027707437614303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 269375653481106333942949 50507935027707437614303)
                ·
                  rfl

theorem cell19_165989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 2, 4].length) (baseStart_165989 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_165989 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_165989 prefixEnd_165989 := by exact prefixLift 165989
  have htrace : WordTrace (prefixWord ++ tailWord_165989) baseStart_165989 baseEnd_165989 := by
    simpa [prefixWord, tailWord_165989, baseEnd_165989] using wordTrace_append hprefix tailTrace_165989
  have hstable : (prefixWord ++ tailWord_165989).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165989).length < 2 ^ (prefixWord ++ tailWord_165989).sum := by decide
  have hdescent : baseEnd_165989 < baseStart_165989 := by decide
  rcases family_descends (prefixWord ++ tailWord_165989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166042 : List Nat := [3, 1, 1, 5, 3, 1, 1, 4]
def baseStart_166042 : Nat := 118140960795 + 166042 * 2 ^ 59
def prefixEnd_166042 : Nat := 4983230072969 + 3 ^ 40 * 166042 * 2
def baseEnd_166042 : Nat := 50524062123819018436381

theorem tailTrace_166042 : CollatzResearch.WordTrace tailWord_166042 prefixEnd_166042 50524062123819018436381 := by
  unfold tailWord_166042
  simp only [CollatzResearch.WordTrace]
  refine ⟨1514012316116416640259095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4037366176310444374024253 1514012316116416640259095)
  ·
    refine ⟨2271018474174624960388643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1514012316116416640259095 2271018474174624960388643)
    ·
      refine ⟨3406527711261937440582965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2271018474174624960388643 3406527711261937440582965)
      ·
        refine ⟨319361972930806635054653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3406527711261937440582965 319361972930806635054653)
        ·
          refine ⟨119760739849052488145495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 319361972930806635054653 119760739849052488145495)
          ·
            refine ⟨179641109773578732218243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119760739849052488145495 179641109773578732218243)
            ·
              refine ⟨269461664660368098327365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 179641109773578732218243 269461664660368098327365)
              ·
                refine ⟨50524062123819018436381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 269461664660368098327365 50524062123819018436381)
                ·
                  rfl

theorem cell19_166042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 1, 4].length) (baseStart_166042 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_166042 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_166042 prefixEnd_166042 := by exact prefixLift 166042
  have htrace : WordTrace (prefixWord ++ tailWord_166042) baseStart_166042 baseEnd_166042 := by
    simpa [prefixWord, tailWord_166042, baseEnd_166042] using wordTrace_append hprefix tailTrace_166042
  have hstable : (prefixWord ++ tailWord_166042).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166042).length < 2 ^ (prefixWord ++ tailWord_166042).sum := by decide
  have hdescent : baseEnd_166042 < baseStart_166042 := by decide
  rcases family_descends (prefixWord ++ tailWord_166042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166084 : List Nat := [2, 3, 3, 1, 2, 2, 6]
def baseStart_166084 : Nat := 118140960795 + 166084 * 2 ^ 59
def prefixEnd_166084 : Nat := 4983230072969 + 3 ^ 40 * 166084 * 2
def baseEnd_166084 : Nat := 16845614028925121834311

theorem tailTrace_166084 : CollatzResearch.WordTrace tailWord_166084 prefixEnd_166084 16845614028925121834311 := by
  unfold tailWord_166084
  simp only [CollatzResearch.WordTrace]
  refine ⟨3028790565156753867032653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4038387420209005156043537 3028790565156753867032653)
  ·
    refine ⟨1135796461933782700137245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3028790565156753867032653 1135796461933782700137245)
    ·
      refine ⟨425923673225168512551467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1135796461933782700137245 425923673225168512551467)
      ·
        refine ⟨638885509837752768827201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 425923673225168512551467 638885509837752768827201)
        ·
          refine ⟨479164132378314576620401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 638885509837752768827201 479164132378314576620401)
          ·
            refine ⟨359373099283735932465301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 479164132378314576620401 359373099283735932465301)
            ·
              refine ⟨16845614028925121834311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 359373099283735932465301 16845614028925121834311)
              ·
                rfl

theorem cell19_166084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 6].length) (baseStart_166084 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_166084 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_166084 prefixEnd_166084 := by exact prefixLift 166084
  have htrace : WordTrace (prefixWord ++ tailWord_166084) baseStart_166084 baseEnd_166084 := by
    simpa [prefixWord, tailWord_166084, baseEnd_166084] using wordTrace_append hprefix tailTrace_166084
  have hstable : (prefixWord ++ tailWord_166084).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166084).length < 2 ^ (prefixWord ++ tailWord_166084).sum := by decide
  have hdescent : baseEnd_166084 < baseStart_166084 := by decide
  rcases family_descends (prefixWord ++ tailWord_166084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166114 : List Nat := [3, 3, 4, 1, 1, 2, 2, 3]
def baseStart_166114 : Nat := 118140960795 + 166114 * 2 ^ 59
def prefixEnd_166114 : Nat := 4983230072969 + 3 ^ 40 * 166114 * 2
def baseEnd_166114 : Nat := 50545970631744184836185

theorem tailTrace_166114 : CollatzResearch.WordTrace tailWord_166114 prefixEnd_166114 50545970631744184836185 := by
  unfold tailWord_166114
  simp only [CollatzResearch.WordTrace]
  refine ⟨1514668830051205714414349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4039116880136548571771597 1514668830051205714414349)
  ·
    refine ⟨568000811269202142905381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1514668830051205714414349 568000811269202142905381)
    ·
      refine ⟨106500152112975401794759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 568000811269202142905381 106500152112975401794759)
      ·
        refine ⟨159750228169463102692139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106500152112975401794759 159750228169463102692139)
        ·
          refine ⟨239625342254194654038209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159750228169463102692139 239625342254194654038209)
          ·
            refine ⟨179719006690645990528657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 239625342254194654038209 179719006690645990528657)
            ·
              refine ⟨134789255017984492896493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 179719006690645990528657 134789255017984492896493)
              ·
                refine ⟨50545970631744184836185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 134789255017984492896493 50545970631744184836185)
                ·
                  rfl

theorem cell19_166114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 2, 3].length) (baseStart_166114 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_166114 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_166114 prefixEnd_166114 := by exact prefixLift 166114
  have htrace : WordTrace (prefixWord ++ tailWord_166114) baseStart_166114 baseEnd_166114 := by
    simpa [prefixWord, tailWord_166114, baseEnd_166114] using wordTrace_append hprefix tailTrace_166114
  have hstable : (prefixWord ++ tailWord_166114).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166114).length < 2 ^ (prefixWord ++ tailWord_166114).sum := by decide
  have hdescent : baseEnd_166114 < baseStart_166114 := by decide
  rcases family_descends (prefixWord ++ tailWord_166114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166120 : List Nat := [2, 1, 4, 1, 2, 4, 2, 3]
def baseStart_166120 : Nat := 118140960795 + 166120 * 2 ^ 59
def prefixEnd_166120 : Nat := 4983230072969 + 3 ^ 40 * 166120 * 2
def baseEnd_166120 : Nat := 50547796340737948702835

theorem tailTrace_166120 : CollatzResearch.WordTrace tailWord_166120 prefixEnd_166120 50547796340737948702835 := by
  unfold tailWord_166120
  simp only [CollatzResearch.WordTrace]
  refine ⟨3029447079091542941187907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4039262772122057254917209 3029447079091542941187907)
  ·
    refine ⟨4544170618637314411781861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3029447079091542941187907 4544170618637314411781861)
    ·
      refine ⟨852031990994496452209099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4544170618637314411781861 852031990994496452209099)
      ·
        refine ⟨1278047986491744678313649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 852031990994496452209099 1278047986491744678313649)
        ·
          refine ⟨958535989868808508735237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1278047986491744678313649 958535989868808508735237)
          ·
            refine ⟨179725498100401595387857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 958535989868808508735237 179725498100401595387857)
            ·
              refine ⟨134794123575301196540893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 179725498100401595387857 134794123575301196540893)
              ·
                refine ⟨50547796340737948702835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 134794123575301196540893 50547796340737948702835)
                ·
                  rfl

theorem cell19_166120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 2, 3].length) (baseStart_166120 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_166120 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_166120 prefixEnd_166120 := by exact prefixLift 166120
  have htrace : WordTrace (prefixWord ++ tailWord_166120) baseStart_166120 baseEnd_166120 := by
    simpa [prefixWord, tailWord_166120, baseEnd_166120] using wordTrace_append hprefix tailTrace_166120
  have hstable : (prefixWord ++ tailWord_166120).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166120).length < 2 ^ (prefixWord ++ tailWord_166120).sum := by decide
  have hdescent : baseEnd_166120 < baseStart_166120 := by decide
  rcases family_descends (prefixWord ++ tailWord_166120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166124 : List Nat := [2, 2, 1, 1, 2, 3, 3, 5]
def baseStart_166124 : Nat := 118140960795 + 166124 * 2 ^ 59
def prefixEnd_166124 : Nat := 4983230072969 + 3 ^ 40 * 166124 * 2
def baseEnd_166124 : Nat := 50549013480067124613935

theorem tailTrace_166124 : CollatzResearch.WordTrace tailWord_166124 prefixEnd_166124 50549013480067124613935 := by
  unfold tailWord_166124
  simp only [CollatzResearch.WordTrace]
  refine ⟨3029520025084297282760713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4039360033445729710347617 3029520025084297282760713)
  ·
    refine ⟨2272140018813222962070535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3029520025084297282760713 2272140018813222962070535)
    ·
      refine ⟨3408210028219834443105803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2272140018813222962070535 3408210028219834443105803)
      ·
        refine ⟨5112315042329751664658705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3408210028219834443105803 5112315042329751664658705)
        ·
          refine ⟨3834236281747313748494029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5112315042329751664658705 3834236281747313748494029)
          ·
            refine ⟨1437838605655242655685261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3834236281747313748494029 1437838605655242655685261)
            ·
              refine ⟨539189477120715995881973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1437838605655242655685261 539189477120715995881973)
              ·
                refine ⟨50549013480067124613935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 539189477120715995881973 50549013480067124613935)
                ·
                  rfl

theorem cell19_166124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 5].length) (baseStart_166124 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_166124 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_166124 prefixEnd_166124 := by exact prefixLift 166124
  have htrace : WordTrace (prefixWord ++ tailWord_166124) baseStart_166124 baseEnd_166124 := by
    simpa [prefixWord, tailWord_166124, baseEnd_166124] using wordTrace_append hprefix tailTrace_166124
  have hstable : (prefixWord ++ tailWord_166124).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166124).length < 2 ^ (prefixWord ++ tailWord_166124).sum := by decide
  have hdescent : baseEnd_166124 < baseStart_166124 := by decide
  rcases family_descends (prefixWord ++ tailWord_166124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166276 : List Nat := [2, 3, 2, 1, 1, 2, 2, 6]
def baseStart_166276 : Nat := 118140960795 + 166276 * 2 ^ 59
def prefixEnd_166276 : Nat := 4983230072969 + 3 ^ 40 * 166276 * 2
def baseEnd_166276 : Nat := 50595264774575809235743

theorem tailTrace_166276 : CollatzResearch.WordTrace tailWord_166276 prefixEnd_166276 50595264774575809235743 := by
  unfold tailWord_166276
  simp only [CollatzResearch.WordTrace]
  refine ⟨3032291972808962262527341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4043055963745283016703121 3032291972808962262527341)
  ·
    refine ⟨1137109489803360848447753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3032291972808962262527341 1137109489803360848447753)
    ·
      refine ⟨852832117352520636335815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1137109489803360848447753 852832117352520636335815)
      ·
        refine ⟨1279248176028780954503723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 852832117352520636335815 1279248176028780954503723)
        ·
          refine ⟨1918872264043171431755585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1279248176028780954503723 1918872264043171431755585)
          ·
            refine ⟨1439154198032378573816689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1918872264043171431755585 1439154198032378573816689)
            ·
              refine ⟨1079365648524283930362517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1439154198032378573816689 1079365648524283930362517)
              ·
                refine ⟨50595264774575809235743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1079365648524283930362517 50595264774575809235743)
                ·
                  rfl

theorem cell19_166276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 6].length) (baseStart_166276 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_166276 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_166276 prefixEnd_166276 := by exact prefixLift 166276
  have htrace : WordTrace (prefixWord ++ tailWord_166276) baseStart_166276 baseEnd_166276 := by
    simpa [prefixWord, tailWord_166276, baseEnd_166276] using wordTrace_append hprefix tailTrace_166276
  have hstable : (prefixWord ++ tailWord_166276).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166276).length < 2 ^ (prefixWord ++ tailWord_166276).sum := by decide
  have hdescent : baseEnd_166276 < baseStart_166276 := by decide
  rcases family_descends (prefixWord ++ tailWord_166276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166312 : List Nat := [2, 1, 6, 1, 1, 1, 7]
def baseStart_166312 : Nat := 118140960795 + 166312 * 2 ^ 59
def prefixEnd_166312 : Nat := 4983230072969 + 3 ^ 40 * 166312 * 2
def baseEnd_166312 : Nat := 16868739676179464145215

theorem tailTrace_166312 : CollatzResearch.WordTrace tailWord_166312 prefixEnd_166312 16868739676179464145215 := by
  unfold tailWord_166312
  simp only [CollatzResearch.WordTrace]
  refine ⟨3032948486743751336682595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4043931315658335115576793 3032948486743751336682595)
  ·
    refine ⟨4549422730115627005023893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3032948486743751336682595 4549422730115627005023893)
    ·
      refine ⟨213254190474170015860495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 4549422730115627005023893 213254190474170015860495)
      ·
        refine ⟨319881285711255023790743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213254190474170015860495 319881285711255023790743)
        ·
          refine ⟨479821928566882535686115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 319881285711255023790743 479821928566882535686115)
          ·
            refine ⟨719732892850323803529173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 479821928566882535686115 719732892850323803529173)
            ·
              refine ⟨16868739676179464145215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 719732892850323803529173 16868739676179464145215)
              ·
                rfl

theorem cell19_166312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 7].length) (baseStart_166312 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_166312 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_166312 prefixEnd_166312 := by exact prefixLift 166312
  have htrace : WordTrace (prefixWord ++ tailWord_166312) baseStart_166312 baseEnd_166312 := by
    simpa [prefixWord, tailWord_166312, baseEnd_166312] using wordTrace_append hprefix tailTrace_166312
  have hstable : (prefixWord ++ tailWord_166312).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166312).length < 2 ^ (prefixWord ++ tailWord_166312).sum := by decide
  have hdescent : baseEnd_166312 < baseStart_166312 := by decide
  rcases family_descends (prefixWord ++ tailWord_166312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166333 : List Nat := [1, 4, 1, 2, 2, 2, 1, 6]
def baseStart_166333 : Nat := 118140960795 + 166333 * 2 ^ 59
def prefixEnd_166333 : Nat := 4983230072969 + 3 ^ 40 * 166333 * 2
def baseEnd_166333 : Nat := 50612609010016565968921

theorem tailTrace_166333 : CollatzResearch.WordTrace tailWord_166333 prefixEnd_166333 50612609010016565968921 := by
  unfold tailWord_166333
  simp only [CollatzResearch.WordTrace]
  refine ⟨6066662906411423259879653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4044441937607615506586435 6066662906411423259879653)
  ·
    refine ⟨1137499294952141861227435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6066662906411423259879653 1137499294952141861227435)
    ·
      refine ⟨1706248942428212791841153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1137499294952141861227435 1706248942428212791841153)
      ·
        refine ⟨1279686706821159593880865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1706248942428212791841153 1279686706821159593880865)
        ·
          refine ⟨959765030115869695410649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1279686706821159593880865 959765030115869695410649)
          ·
            refine ⟨719823772586902271557987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 959765030115869695410649 719823772586902271557987)
            ·
              refine ⟨1079735658880353407336981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 719823772586902271557987 1079735658880353407336981)
              ·
                refine ⟨50612609010016565968921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1079735658880353407336981 50612609010016565968921)
                ·
                  rfl

theorem cell19_166333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 6].length) (baseStart_166333 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_166333 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_166333 prefixEnd_166333 := by exact prefixLift 166333
  have htrace : WordTrace (prefixWord ++ tailWord_166333) baseStart_166333 baseEnd_166333 := by
    simpa [prefixWord, tailWord_166333, baseEnd_166333] using wordTrace_append hprefix tailTrace_166333
  have hstable : (prefixWord ++ tailWord_166333).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166333).length < 2 ^ (prefixWord ++ tailWord_166333).sum := by decide
  have hdescent : baseEnd_166333 < baseStart_166333 := by decide
  rcases family_descends (prefixWord ++ tailWord_166333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166371 : List Nat := [1, 1, 1, 6, 3, 7]
def baseStart_166371 : Nat := 118140960795 + 166371 * 2 ^ 59
def prefixEnd_166371 : Nat := 4983230072969 + 3 ^ 40 * 166371 * 2
def baseEnd_166371 : Nat := 5624907981515970791597

theorem tailTrace_166371 : CollatzResearch.WordTrace tailWord_166371 prefixEnd_166371 5624907981515970791597 := by
  unfold tailWord_166371
  simp only [CollatzResearch.WordTrace]
  refine ⟨6068048880273755749762967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4045365920182503833175311 6068048880273755749762967)
  ·
    refine ⟨9102073320410633624644451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6068048880273755749762967 9102073320410633624644451)
    ·
      refine ⟨13653109980615950436966677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9102073320410633624644451 13653109980615950436966677)
      ·
        refine ⟨639989530341372676732813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 13653109980615950436966677 639989530341372676732813)
        ·
          refine ⟨239996073878014753774805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 639989530341372676732813 239996073878014753774805)
          ·
            refine ⟨5624907981515970791597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 239996073878014753774805 5624907981515970791597)
            ·
              rfl

theorem cell19_166371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 7].length) (baseStart_166371 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_166371 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_166371 prefixEnd_166371 := by exact prefixLift 166371
  have htrace : WordTrace (prefixWord ++ tailWord_166371) baseStart_166371 baseEnd_166371 := by
    simpa [prefixWord, tailWord_166371, baseEnd_166371] using wordTrace_append hprefix tailTrace_166371
  have hstable : (prefixWord ++ tailWord_166371).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166371).length < 2 ^ (prefixWord ++ tailWord_166371).sum := by decide
  have hdescent : baseEnd_166371 < baseStart_166371 := by decide
  rcases family_descends (prefixWord ++ tailWord_166371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166386 : List Nat := [3, 2, 1, 4, 2, 2, 1, 4]
def baseStart_166386 : Nat := 118140960795 + 166386 * 2 ^ 59
def prefixEnd_166386 : Nat := 4983230072969 + 3 ^ 40 * 166386 * 2
def baseEnd_166386 : Nat := 50628736106128146790999

theorem tailTrace_166386 : CollatzResearch.WordTrace tailWord_166386 prefixEnd_166386 50628736106128146790999 := by
  unfold tailWord_166386
  simp only [CollatzResearch.WordTrace]
  refine ⟨1517148993804853327889753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4045730650146275541039341 1517148993804853327889753)
  ·
    refine ⟨1137861745353639995917315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1517148993804853327889753 1137861745353639995917315)
    ·
      refine ⟨1706792618030459993875973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1137861745353639995917315 1706792618030459993875973)
      ·
        refine ⟨320023615880711248851745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1706792618030459993875973 320023615880711248851745)
        ·
          refine ⟨240017711910533436638809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 320023615880711248851745 240017711910533436638809)
          ·
            refine ⟨180013283932900077479107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 240017711910533436638809 180013283932900077479107)
            ·
              refine ⟨270019925899350116218661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 180013283932900077479107 270019925899350116218661)
              ·
                refine ⟨50628736106128146790999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 270019925899350116218661 50628736106128146790999)
                ·
                  rfl

theorem cell19_166386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 1, 4].length) (baseStart_166386 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_166386 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_166386 prefixEnd_166386 := by exact prefixLift 166386
  have htrace : WordTrace (prefixWord ++ tailWord_166386) baseStart_166386 baseEnd_166386 := by
    simpa [prefixWord, tailWord_166386, baseEnd_166386] using wordTrace_append hprefix tailTrace_166386
  have hstable : (prefixWord ++ tailWord_166386).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166386).length < 2 ^ (prefixWord ++ tailWord_166386).sum := by decide
  have hdescent : baseEnd_166386 < baseStart_166386 := by decide
  rcases family_descends (prefixWord ++ tailWord_166386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166428 : List Nat := [2, 2, 3, 1, 2, 3, 6]
def baseStart_166428 : Nat := 118140960795 + 166428 * 2 ^ 59
def prefixEnd_166428 : Nat := 4983230072969 + 3 ^ 40 * 166428 * 2
def baseEnd_166428 : Nat := 16880505356361497952517

theorem tailTrace_166428 : CollatzResearch.WordTrace tailWord_166428 prefixEnd_166428 16880505356361497952517 := by
  unfold tailWord_166428
  simp only [CollatzResearch.WordTrace]
  refine ⟨3035063920533627242293969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4046751894044836323058625 3035063920533627242293969)
  ·
    refine ⟨2276297940400220431720477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3035063920533627242293969 2276297940400220431720477)
    ·
      refine ⟨853611727650082661895179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2276297940400220431720477 853611727650082661895179)
      ·
        refine ⟨1280417591475123992842769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 853611727650082661895179 1280417591475123992842769)
        ·
          refine ⟨960313193606342994632077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1280417591475123992842769 960313193606342994632077)
          ·
            refine ⟨360117447602378622987029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 960313193606342994632077 360117447602378622987029)
            ·
              refine ⟨16880505356361497952517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 360117447602378622987029 16880505356361497952517)
              ·
                rfl

theorem cell19_166428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 6].length) (baseStart_166428 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_166428 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_166428 prefixEnd_166428 := by exact prefixLift 166428
  have htrace : WordTrace (prefixWord ++ tailWord_166428) baseStart_166428 baseEnd_166428 := by
    simpa [prefixWord, tailWord_166428, baseEnd_166428] using wordTrace_append hprefix tailTrace_166428
  have hstable : (prefixWord ++ tailWord_166428).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166428).length < 2 ^ (prefixWord ++ tailWord_166428).sum := by decide
  have hdescent : baseEnd_166428 < baseStart_166428 := by decide
  rcases family_descends (prefixWord ++ tailWord_166428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166462 : List Nat := [4, 2, 1, 4, 1, 1, 1, 5]
def baseStart_166462 : Nat := 118140960795 + 166462 * 2 ^ 59
def prefixEnd_166462 : Nat := 4983230072969 + 3 ^ 40 * 166462 * 2
def baseEnd_166462 : Nat := 50651861753382489101903

theorem tailTrace_166462 : CollatzResearch.WordTrace tailWord_166462 prefixEnd_166462 50651861753382489101903 := by
  unfold tailWord_166462
  simp only [CollatzResearch.WordTrace]
  refine ⟨758920990368009786415705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4047578615296052194217093 758920990368009786415705)
  ·
    refine ⟨569190742776007339811779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 758920990368009786415705 569190742776007339811779)
    ·
      refine ⟨853786114164011009717669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 569190742776007339811779 853786114164011009717669)
      ·
        refine ⟨160084896405752064322063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 853786114164011009717669 160084896405752064322063)
        ·
          refine ⟨240127344608628096483095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160084896405752064322063 240127344608628096483095)
          ·
            refine ⟨360191016912942144724643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 240127344608628096483095 360191016912942144724643)
            ·
              refine ⟨540286525369413217086965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 360191016912942144724643 540286525369413217086965)
              ·
                refine ⟨50651861753382489101903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 540286525369413217086965 50651861753382489101903)
                ·
                  rfl

theorem cell19_166462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 5].length) (baseStart_166462 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_166462 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_166462 prefixEnd_166462 := by exact prefixLift 166462
  have htrace : WordTrace (prefixWord ++ tailWord_166462) baseStart_166462 baseEnd_166462 := by
    simpa [prefixWord, tailWord_166462, baseEnd_166462] using wordTrace_append hprefix tailTrace_166462
  have hstable : (prefixWord ++ tailWord_166462).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166462).length < 2 ^ (prefixWord ++ tailWord_166462).sum := by decide
  have hdescent : baseEnd_166462 < baseStart_166462 := by decide
  rcases family_descends (prefixWord ++ tailWord_166462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166563 : List Nat := [1, 1, 1, 4, 1, 1, 2, 8]
def baseStart_166563 : Nat := 118140960795 + 166563 * 2 ^ 59
def prefixEnd_166563 : Nat := 4983230072969 + 3 ^ 40 * 166563 * 2
def baseEnd_166563 : Nat := 50682594521444180857183

theorem tailTrace_166563 : CollatzResearch.WordTrace tailWord_166563 prefixEnd_166563 50682594521444180857183 := by
  unfold tailWord_166563
  simp only [CollatzResearch.WordTrace]
  refine ⟨6075051695578172540752343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4050034463718781693834895 6075051695578172540752343)
  ·
    refine ⟨9112577543367258811128515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6075051695578172540752343 9112577543367258811128515)
    ·
      refine ⟨13668866315050888216692773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9112577543367258811128515 13668866315050888216692773)
      ·
        refine ⟨2562912434072041540629895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13668866315050888216692773 2562912434072041540629895)
        ·
          refine ⟨3844368651108062310944843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2562912434072041540629895 3844368651108062310944843)
          ·
            refine ⟨5766552976662093466417265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3844368651108062310944843 5766552976662093466417265)
            ·
              refine ⟨4324914732496570099812949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5766552976662093466417265 4324914732496570099812949)
              ·
                refine ⟨50682594521444180857183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4324914732496570099812949 50682594521444180857183)
                ·
                  rfl

theorem cell19_166563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 8].length) (baseStart_166563 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_166563 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_166563 prefixEnd_166563 := by exact prefixLift 166563
  have htrace : WordTrace (prefixWord ++ tailWord_166563) baseStart_166563 baseEnd_166563 := by
    simpa [prefixWord, tailWord_166563, baseEnd_166563] using wordTrace_append hprefix tailTrace_166563
  have hstable : (prefixWord ++ tailWord_166563).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166563).length < 2 ^ (prefixWord ++ tailWord_166563).sum := by decide
  have hdescent : baseEnd_166563 < baseStart_166563 := by decide
  rcases family_descends (prefixWord ++ tailWord_166563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166637 : List Nat := [1, 5, 1, 2, 1, 1, 3, 5]
def baseStart_166637 : Nat := 118140960795 + 166637 * 2 ^ 59
def prefixEnd_166637 : Nat := 4983230072969 + 3 ^ 40 * 166637 * 2
def baseEnd_166637 : Nat := 50705111599033935212537

theorem tailTrace_166637 : CollatzResearch.WordTrace tailWord_166637 prefixEnd_166637 50705111599033935212537 := by
  unfold tailWord_166637
  simp only [CollatzResearch.WordTrace]
  refine ⟨6077750697310083178946165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4051833798206722119297443 6077750697310083178946165)
  ·
    refine ⟨569789127872820298026203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6077750697310083178946165 569789127872820298026203)
    ·
      refine ⟨854683691809230447039305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 569789127872820298026203 854683691809230447039305)
      ·
        refine ⟨641012768856922835279479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 854683691809230447039305 641012768856922835279479)
        ·
          refine ⟨961519153285384252919219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 641012768856922835279479 961519153285384252919219)
          ·
            refine ⟨1442278729928076379378829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 961519153285384252919219 1442278729928076379378829)
            ·
              refine ⟨540854523723028642267061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1442278729928076379378829 540854523723028642267061)
              ·
                refine ⟨50705111599033935212537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 540854523723028642267061 50705111599033935212537)
                ·
                  rfl

theorem cell19_166637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 5].length) (baseStart_166637 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_166637 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_166637 prefixEnd_166637 := by exact prefixLift 166637
  have htrace : WordTrace (prefixWord ++ tailWord_166637) baseStart_166637 baseEnd_166637 := by
    simpa [prefixWord, tailWord_166637, baseEnd_166637] using wordTrace_append hprefix tailTrace_166637
  have hstable : (prefixWord ++ tailWord_166637).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166637).length < 2 ^ (prefixWord ++ tailWord_166637).sum := by decide
  have hdescent : baseEnd_166637 < baseStart_166637 := by decide
  rcases family_descends (prefixWord ++ tailWord_166637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166654 : List Nat := [4, 2, 2, 1, 2, 3, 5]
def baseStart_166654 : Nat := 118140960795 + 166654 * 2 ^ 59
def prefixEnd_166654 : Nat := 4983230072969 + 3 ^ 40 * 166654 * 2
def baseEnd_166654 : Nat := 16903428147060977611571

theorem tailTrace_166654 : CollatzResearch.WordTrace tailWord_166654 prefixEnd_166654 16903428147060977611571 := by
  unfold tailWord_166654
  simp only [CollatzResearch.WordTrace]
  refine ⟨759796342281061885289377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4052247158832330054876677 759796342281061885289377)
  ·
    refine ⟨569847256710796413967033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 759796342281061885289377 569847256710796413967033)
    ·
      refine ⟨427385442533097310475275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 569847256710796413967033 427385442533097310475275)
      ·
        refine ⟨641078163799645965712913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 427385442533097310475275 641078163799645965712913)
        ·
          refine ⟨480808622849734474284685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 641078163799645965712913 480808622849734474284685)
          ·
            refine ⟨180303233568650427856757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 480808622849734474284685 180303233568650427856757)
            ·
              refine ⟨16903428147060977611571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 180303233568650427856757 16903428147060977611571)
              ·
                rfl

theorem cell19_166654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 5].length) (baseStart_166654 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_166654 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_166654 prefixEnd_166654 := by exact prefixLift 166654
  have htrace : WordTrace (prefixWord ++ tailWord_166654) baseStart_166654 baseEnd_166654 := by
    simpa [prefixWord, tailWord_166654, baseEnd_166654] using wordTrace_append hprefix tailTrace_166654
  have hstable : (prefixWord ++ tailWord_166654).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166654).length < 2 ^ (prefixWord ++ tailWord_166654).sum := by decide
  have hdescent : baseEnd_166654 < baseStart_166654 := by decide
  rcases family_descends (prefixWord ++ tailWord_166654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166726 : List Nat := [6, 1, 1, 2, 2, 2, 1, 4]
def baseStart_166726 : Nat := 118140960795 + 166726 * 2 ^ 59
def prefixEnd_166726 : Nat := 4983230072969 + 3 ^ 40 * 166726 * 2
def baseEnd_166726 : Nat := 50732192949108099234517

theorem tailTrace_166726 : CollatzResearch.WordTrace tailWord_166726 prefixEnd_166726 50732192949108099234517 := by
  unfold tailWord_166726
  simp only [CollatzResearch.WordTrace]
  refine ⟨190031149812114105591751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 4053997862658434252624021 190031149812114105591751)
  ·
    refine ⟨285046724718171158387627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190031149812114105591751 285046724718171158387627)
    ·
      refine ⟨427570087077256737581441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 285046724718171158387627 427570087077256737581441)
      ·
        refine ⟨320677565307942553186081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 427570087077256737581441 320677565307942553186081)
        ·
          refine ⟨240508173980956914889561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 320677565307942553186081 240508173980956914889561)
          ·
            refine ⟨180381130485717686167171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 240508173980956914889561 180381130485717686167171)
            ·
              refine ⟨270571695728576529250757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 180381130485717686167171 270571695728576529250757)
              ·
                refine ⟨50732192949108099234517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 270571695728576529250757 50732192949108099234517)
                ·
                  rfl

theorem cell19_166726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_166726 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_166726 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_166726 prefixEnd_166726 := by exact prefixLift 166726
  have htrace : WordTrace (prefixWord ++ tailWord_166726) baseStart_166726 baseEnd_166726 := by
    simpa [prefixWord, tailWord_166726, baseEnd_166726] using wordTrace_append hprefix tailTrace_166726
  have hstable : (prefixWord ++ tailWord_166726).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166726).length < 2 ^ (prefixWord ++ tailWord_166726).sum := by decide
  have hdescent : baseEnd_166726 < baseStart_166726 := by decide
  rcases family_descends (prefixWord ++ tailWord_166726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166732 : List Nat := [2, 2, 1, 3, 3, 1, 3, 4]
def baseStart_166732 : Nat := 118140960795 + 166732 * 2 ^ 59
def prefixEnd_166732 : Nat := 4983230072969 + 3 ^ 40 * 166732 * 2
def baseEnd_166732 : Nat := 50734018658101863101167

theorem tailTrace_166732 : CollatzResearch.WordTrace tailWord_166732 prefixEnd_166732 50734018658101863101167 := by
  unfold tailWord_166732
  simp only [CollatzResearch.WordTrace]
  refine ⟨3040607815982957201827225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4054143754643942935769633 3040607815982957201827225)
  ·
    refine ⟨2280455861987217901370419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3040607815982957201827225 2280455861987217901370419)
    ·
      refine ⟨3420683792980826852055629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2280455861987217901370419 3420683792980826852055629)
      ·
        refine ⟨1282756422367810069520861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3420683792980826852055629 1282756422367810069520861)
        ·
          refine ⟨481033658387928776070323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1282756422367810069520861 481033658387928776070323)
          ·
            refine ⟨721550487581893164105485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 481033658387928776070323 721550487581893164105485)
            ·
              refine ⟨270581432843209936539557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 721550487581893164105485 270581432843209936539557)
              ·
                refine ⟨50734018658101863101167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 270581432843209936539557 50734018658101863101167)
                ·
                  rfl

theorem cell19_166732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 3, 4].length) (baseStart_166732 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_166732 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_166732 prefixEnd_166732 := by exact prefixLift 166732
  have htrace : WordTrace (prefixWord ++ tailWord_166732) baseStart_166732 baseEnd_166732 := by
    simpa [prefixWord, tailWord_166732, baseEnd_166732] using wordTrace_append hprefix tailTrace_166732
  have hstable : (prefixWord ++ tailWord_166732).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166732).length < 2 ^ (prefixWord ++ tailWord_166732).sum := by decide
  have hdescent : baseEnd_166732 < baseStart_166732 := by decide
  rcases family_descends (prefixWord ++ tailWord_166732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166751 : List Nat := [1, 1, 2, 3, 1, 3, 5, 3]
def baseStart_166751 : Nat := 118140960795 + 166751 * 2 ^ 59
def prefixEnd_166751 : Nat := 4983230072969 + 3 ^ 40 * 166751 * 2
def baseEnd_166751 : Nat := 50739800069915448678893

theorem tailTrace_166751 : CollatzResearch.WordTrace tailWord_166751 prefixEnd_166751 50739800069915448678893 := by
  unfold tailWord_166751
  simp only [CollatzResearch.WordTrace]
  refine ⟨6081908618897080648596107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4054605745931387099064071 6081908618897080648596107)
  ·
    refine ⟨9122862928345620972894161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6081908618897080648596107 9122862928345620972894161)
    ·
      refine ⟨6842147196259215729670621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9122862928345620972894161 6842147196259215729670621)
      ·
        refine ⟨2565805198597205898626483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6842147196259215729670621 2565805198597205898626483)
        ·
          refine ⟨3848707797895808847939725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2565805198597205898626483 3848707797895808847939725)
          ·
            refine ⟨1443265424210928317977397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3848707797895808847939725 1443265424210928317977397)
            ·
              refine ⟨135306133519774529810381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1443265424210928317977397 135306133519774529810381)
              ·
                refine ⟨50739800069915448678893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 135306133519774529810381 50739800069915448678893)
                ·
                  rfl

theorem cell19_166751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 5, 3].length) (baseStart_166751 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_166751 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_166751 prefixEnd_166751 := by exact prefixLift 166751
  have htrace : WordTrace (prefixWord ++ tailWord_166751) baseStart_166751 baseEnd_166751 := by
    simpa [prefixWord, tailWord_166751, baseEnd_166751] using wordTrace_append hprefix tailTrace_166751
  have hstable : (prefixWord ++ tailWord_166751).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166751).length < 2 ^ (prefixWord ++ tailWord_166751).sum := by decide
  have hdescent : baseEnd_166751 < baseStart_166751 := by decide
  rcases family_descends (prefixWord ++ tailWord_166751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166802 : List Nat := [3, 2, 3, 2, 3, 1, 2, 3]
def baseStart_166802 : Nat := 118140960795 + 166802 * 2 ^ 59
def prefixEnd_166802 : Nat := 4983230072969 + 3 ^ 40 * 166802 * 2
def baseEnd_166802 : Nat := 50755318596362441545421

theorem tailTrace_166802 : CollatzResearch.WordTrace tailWord_166802 prefixEnd_166802 50755318596362441545421 := by
  unfold tailWord_166802
  simp only [CollatzResearch.WordTrace]
  refine ⟨1520942185428079089675665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4055845827808210905801773 1520942185428079089675665)
  ·
    refine ⟨1140706639071059317256749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1520942185428079089675665 1140706639071059317256749)
    ·
      refine ⟨427764989651647243971281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1140706639071059317256749 427764989651647243971281)
      ·
        refine ⟨320823742238735432978461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 427764989651647243971281 320823742238735432978461)
        ·
          refine ⟨120308903339525787366923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 320823742238735432978461 120308903339525787366923)
          ·
            refine ⟨180463355009288681050385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120308903339525787366923 180463355009288681050385)
            ·
              refine ⟨135347516256966510787789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 180463355009288681050385 135347516256966510787789)
              ·
                refine ⟨50755318596362441545421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 135347516256966510787789 50755318596362441545421)
                ·
                  rfl

theorem cell19_166802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 2, 3].length) (baseStart_166802 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_166802 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_166802 prefixEnd_166802 := by exact prefixLift 166802
  have htrace : WordTrace (prefixWord ++ tailWord_166802) baseStart_166802 baseEnd_166802 := by
    simpa [prefixWord, tailWord_166802, baseEnd_166802] using wordTrace_append hprefix tailTrace_166802
  have hstable : (prefixWord ++ tailWord_166802).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166802).length < 2 ^ (prefixWord ++ tailWord_166802).sum := by decide
  have hdescent : baseEnd_166802 < baseStart_166802 := by decide
  rcases family_descends (prefixWord ++ tailWord_166802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166846 : List Nat := [4, 2, 1, 1, 1, 2, 4, 4]
def baseStart_166846 : Nat := 118140960795 + 166846 * 2 ^ 59
def prefixEnd_166846 : Nat := 4983230072969 + 3 ^ 40 * 166846 * 2
def baseEnd_166846 : Nat := 50768707128983376567523

theorem tailTrace_166846 : CollatzResearch.WordTrace tailWord_166846 prefixEnd_166846 50768707128983376567523 := by
  unfold tailWord_166846
  simp only [CollatzResearch.WordTrace]
  refine ⟨760671694194113984163049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4056915702368607915536261 760671694194113984163049)
  ·
    refine ⟨570503770645585488122287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 760671694194113984163049 570503770645585488122287)
    ·
      refine ⟨855755655968378232183431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 570503770645585488122287 855755655968378232183431)
      ·
        refine ⟨1283633483952567348275147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 855755655968378232183431 1283633483952567348275147)
        ·
          refine ⟨1925450225928851022412721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1283633483952567348275147 1925450225928851022412721)
          ·
            refine ⟨1444087669446638266809541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1925450225928851022412721 1444087669446638266809541)
            ·
              refine ⟨270766438021244675026789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1444087669446638266809541 270766438021244675026789)
              ·
                refine ⟨50768707128983376567523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 270766438021244675026789 50768707128983376567523)
                ·
                  rfl

theorem cell19_166846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 4, 4].length) (baseStart_166846 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_166846 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_166846 prefixEnd_166846 := by exact prefixLift 166846
  have htrace : WordTrace (prefixWord ++ tailWord_166846) baseStart_166846 baseEnd_166846 := by
    simpa [prefixWord, tailWord_166846, baseEnd_166846] using wordTrace_append hprefix tailTrace_166846
  have hstable : (prefixWord ++ tailWord_166846).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166846).length < 2 ^ (prefixWord ++ tailWord_166846).sum := by decide
  have hdescent : baseEnd_166846 < baseStart_166846 := by decide
  rcases family_descends (prefixWord ++ tailWord_166846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166848 : List Nat := [2, 1, 1, 2, 3, 3, 1, 6]
def baseStart_166848 : Nat := 118140960795 + 166848 * 2 ^ 59
def prefixEnd_166848 : Nat := 4983230072969 + 3 ^ 40 * 166848 * 2
def baseEnd_166848 : Nat := 50769315698647964523073

theorem tailTrace_166848 : CollatzResearch.WordTrace tailWord_166848 prefixEnd_166848 50769315698647964523073 := by
  unfold tailWord_166848
  simp only [CollatzResearch.WordTrace]
  refine ⟨3042723249772833107438599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4056964333030444143251465 3042723249772833107438599)
  ·
    refine ⟨4564084874659249661157899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3042723249772833107438599 4564084874659249661157899)
    ·
      refine ⟨6846127311988874491736849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4564084874659249661157899 6846127311988874491736849)
      ·
        refine ⟨5134595483991655868802637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6846127311988874491736849 5134595483991655868802637)
        ·
          refine ⟨1925473306496870950800989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5134595483991655868802637 1925473306496870950800989)
          ·
            refine ⟨722052489936326606550371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1925473306496870950800989 722052489936326606550371)
            ·
              refine ⟨1083078734904489909825557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 722052489936326606550371 1083078734904489909825557)
              ·
                refine ⟨50769315698647964523073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1083078734904489909825557 50769315698647964523073)
                ·
                  rfl

theorem cell19_166848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 6].length) (baseStart_166848 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_166848 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_166848 prefixEnd_166848 := by exact prefixLift 166848
  have htrace : WordTrace (prefixWord ++ tailWord_166848) baseStart_166848 baseEnd_166848 := by
    simpa [prefixWord, tailWord_166848, baseEnd_166848] using wordTrace_append hprefix tailTrace_166848
  have hstable : (prefixWord ++ tailWord_166848).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166848).length < 2 ^ (prefixWord ++ tailWord_166848).sum := by decide
  have hdescent : baseEnd_166848 < baseStart_166848 := by decide
  rcases family_descends (prefixWord ++ tailWord_166848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166941 : List Nat := [1, 4, 2, 2, 3, 1, 6]
def baseStart_166941 : Nat := 118140960795 + 166941 * 2 ^ 59
def prefixEnd_166941 : Nat := 4983230072969 + 3 ^ 40 * 166941 * 2
def baseEnd_166941 : Nat := 16932538062683768152051

theorem tailTrace_166941 : CollatzResearch.WordTrace tailWord_166941 prefixEnd_166941 16932538062683768152051 := by
  unfold tailWord_166941
  simp only [CollatzResearch.WordTrace]
  refine ⟨6088838488208743098012677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4059225658805828732008451 6088838488208743098012677)
  ·
    refine ⟨1141657216539139330877377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6088838488208743098012677 1141657216539139330877377)
    ·
      refine ⟨856242912404354498158033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1141657216539139330877377 856242912404354498158033)
      ·
        refine ⟨642182184303265873618525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 856242912404354498158033 642182184303265873618525)
        ·
          refine ⟨240818319113724702606947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 642182184303265873618525 240818319113724702606947)
          ·
            refine ⟨361227478670587053910421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 240818319113724702606947 361227478670587053910421)
            ·
              refine ⟨16932538062683768152051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 361227478670587053910421 16932538062683768152051)
              ·
                rfl

theorem cell19_166941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 6].length) (baseStart_166941 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_166941 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_166941 prefixEnd_166941 := by exact prefixLift 166941
  have htrace : WordTrace (prefixWord ++ tailWord_166941) baseStart_166941 baseEnd_166941 := by
    simpa [prefixWord, tailWord_166941, baseEnd_166941] using wordTrace_append hprefix tailTrace_166941
  have hstable : (prefixWord ++ tailWord_166941).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166941).length < 2 ^ (prefixWord ++ tailWord_166941).sum := by decide
  have hdescent : baseEnd_166941 < baseStart_166941 := by decide
  rcases family_descends (prefixWord ++ tailWord_166941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166943 : List Nat := [1, 1, 2, 4, 1, 4, 6]
def baseStart_166943 : Nat := 118140960795 + 166943 * 2 ^ 59
def prefixEnd_166943 : Nat := 4983230072969 + 3 ^ 40 * 166943 * 2
def baseEnd_166943 : Nat := 16932740919238630803901

theorem tailTrace_166943 : CollatzResearch.WordTrace tailWord_166943 prefixEnd_166943 16932740919238630803901 := by
  unfold tailWord_166943
  simp only [CollatzResearch.WordTrace]
  refine ⟨6088911434201497439585483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4059274289467664959723655 6088911434201497439585483)
  ·
    refine ⟨9133367151302246159378225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6088911434201497439585483 9133367151302246159378225)
    ·
      refine ⟨6850025363476684619533669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9133367151302246159378225 6850025363476684619533669)
      ·
        refine ⟨1284379755651878366162563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6850025363476684619533669 1284379755651878366162563)
        ·
          refine ⟨1926569633477817549243845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1284379755651878366162563 1926569633477817549243845)
          ·
            refine ⟨361231806277090790483221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1926569633477817549243845 361231806277090790483221)
            ·
              refine ⟨16932740919238630803901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 361231806277090790483221 16932740919238630803901)
              ·
                rfl

theorem cell19_166943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 6].length) (baseStart_166943 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_166943 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_166943 prefixEnd_166943 := by exact prefixLift 166943
  have htrace : WordTrace (prefixWord ++ tailWord_166943) baseStart_166943 baseEnd_166943 := by
    simpa [prefixWord, tailWord_166943, baseEnd_166943] using wordTrace_append hprefix tailTrace_166943
  have hstable : (prefixWord ++ tailWord_166943).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166943).length < 2 ^ (prefixWord ++ tailWord_166943).sum := by decide
  have hdescent : baseEnd_166943 < baseStart_166943 := by decide
  rcases family_descends (prefixWord ++ tailWord_166943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166962 : List Nat := [3, 2, 1, 1, 2, 2, 2, 6]
def baseStart_166962 : Nat := 118140960795 + 166962 * 2 ^ 59
def prefixEnd_166962 : Nat := 4983230072969 + 3 ^ 40 * 166962 * 2
def baseEnd_166962 : Nat := 50804004169529477989429

theorem tailTrace_166962 : CollatzResearch.WordTrace tailWord_166962 prefixEnd_166962 50804004169529477989429 := by
  unfold tailWord_166962
  simp only [CollatzResearch.WordTrace]
  refine ⟨1522401105283165921131785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4059736280755109123018093 1522401105283165921131785)
  ·
    refine ⟨1141800828962374440848839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1522401105283165921131785 1141800828962374440848839)
    ·
      refine ⟨1712701243443561661273259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1141800828962374440848839 1712701243443561661273259)
      ·
        refine ⟨2569051865165342491909889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1712701243443561661273259 2569051865165342491909889)
        ·
          refine ⟨1926788898874006868932417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2569051865165342491909889 1926788898874006868932417)
          ·
            refine ⟨1445091674155505151699313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1926788898874006868932417 1445091674155505151699313)
            ·
              refine ⟨1083818755616628863774485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1445091674155505151699313 1083818755616628863774485)
              ·
                refine ⟨50804004169529477989429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1083818755616628863774485 50804004169529477989429)
                ·
                  rfl

theorem cell19_166962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 6].length) (baseStart_166962 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_166962 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_166962 prefixEnd_166962 := by exact prefixLift 166962
  have htrace : WordTrace (prefixWord ++ tailWord_166962) baseStart_166962 baseEnd_166962 := by
    simpa [prefixWord, tailWord_166962, baseEnd_166962] using wordTrace_append hprefix tailTrace_166962
  have hstable : (prefixWord ++ tailWord_166962).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166962).length < 2 ^ (prefixWord ++ tailWord_166962).sum := by decide
  have hdescent : baseEnd_166962 < baseStart_166962 := by decide
  rcases family_descends (prefixWord ++ tailWord_166962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167114 : List Nat := [3, 1, 2, 1, 3, 3, 6]
def baseStart_167114 : Nat := 118140960795 + 167114 * 2 ^ 59
def prefixEnd_167114 : Nat := 4983230072969 + 3 ^ 40 * 167114 * 2
def baseEnd_167114 : Nat := 16950085154679387537079

theorem tailTrace_167114 : CollatzResearch.WordTrace tailWord_167114 prefixEnd_167114 16950085154679387537079 := by
  unfold tailWord_167114
  simp only [CollatzResearch.WordTrace]
  refine ⟨1523787079145498411015099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4063432211054662429373597 1523787079145498411015099)
  ·
    refine ⟨2285680618718247616522649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1523787079145498411015099 2285680618718247616522649)
    ·
      refine ⟨1714260464038685712391987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2285680618718247616522649 1714260464038685712391987)
      ·
        refine ⟨2571390696058028568587981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1714260464038685712391987 2571390696058028568587981)
        ·
          refine ⟨964271511021760713220493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2571390696058028568587981 964271511021760713220493)
          ·
            refine ⟨361601816633160267457685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 964271511021760713220493 361601816633160267457685)
            ·
              refine ⟨16950085154679387537079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 361601816633160267457685 16950085154679387537079)
              ·
                rfl

theorem cell19_167114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 6].length) (baseStart_167114 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_167114 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_167114 prefixEnd_167114 := by exact prefixLift 167114
  have htrace : WordTrace (prefixWord ++ tailWord_167114) baseStart_167114 baseEnd_167114 := by
    simpa [prefixWord, tailWord_167114, baseEnd_167114] using wordTrace_append hprefix tailTrace_167114
  have hstable : (prefixWord ++ tailWord_167114).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167114).length < 2 ^ (prefixWord ++ tailWord_167114).sum := by decide
  have hdescent : baseEnd_167114 < baseStart_167114 := by decide
  rcases family_descends (prefixWord ++ tailWord_167114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167150 : List Nat := [4, 1, 2, 1, 1, 1, 6, 3]
def baseStart_167150 : Nat := 118140960795 + 167150 * 2 ^ 59
def prefixEnd_167150 : Nat := 4983230072969 + 3 ^ 40 * 167150 * 2
def baseEnd_167150 : Nat := 50861209718000745811139

theorem tailTrace_167150 : CollatzResearch.WordTrace tailWord_167150 prefixEnd_167150 50861209718000745811139 := by
  unfold tailWord_167150
  simp only [CollatzResearch.WordTrace]
  refine ⟨762057668056446474046363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4064307562967714528247269 762057668056446474046363)
  ·
    refine ⟨1143086502084669711069545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 762057668056446474046363 1143086502084669711069545)
    ·
      refine ⟨857314876563502283302159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1143086502084669711069545 857314876563502283302159)
      ·
        refine ⟨1285972314845253424953239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 857314876563502283302159 1285972314845253424953239)
        ·
          refine ⟨1928958472267880137429859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1285972314845253424953239 1928958472267880137429859)
          ·
            refine ⟨2893437708401820206144789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1928958472267880137429859 2893437708401820206144789)
            ·
              refine ⟨135629892581335322163037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 2893437708401820206144789 135629892581335322163037)
              ·
                refine ⟨50861209718000745811139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 135629892581335322163037 50861209718000745811139)
                ·
                  rfl

theorem cell19_167150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 6, 3].length) (baseStart_167150 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_167150 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_167150 prefixEnd_167150 := by exact prefixLift 167150
  have htrace : WordTrace (prefixWord ++ tailWord_167150) baseStart_167150 baseEnd_167150 := by
    simpa [prefixWord, tailWord_167150, baseEnd_167150] using wordTrace_append hprefix tailTrace_167150
  have hstable : (prefixWord ++ tailWord_167150).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167150).length < 2 ^ (prefixWord ++ tailWord_167150).sum := by decide
  have hdescent : baseEnd_167150 < baseStart_167150 := by decide
  rcases family_descends (prefixWord ++ tailWord_167150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167171 : List Nat := [1, 1, 1, 3, 2, 6, 5]
def baseStart_167171 : Nat := 118140960795 + 167171 * 2 ^ 59
def prefixEnd_167171 : Nat := 4983230072969 + 3 ^ 40 * 167171 * 2
def baseEnd_167171 : Nat := 16955866566492973114805

theorem tailTrace_167171 : CollatzResearch.WordTrace tailWord_167171 prefixEnd_167171 16955866566492973114805 := by
  unfold tailWord_167171
  simp only [CollatzResearch.WordTrace]
  refine ⟨6097227277375492378885367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4064818184916994919256911 6097227277375492378885367)
  ·
    refine ⟨9145840916063238568328051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6097227277375492378885367 9145840916063238568328051)
    ·
      refine ⟨13718761374094857852492077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9145840916063238568328051 13718761374094857852492077)
      ·
        refine ⟨5144535515285571694684529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13718761374094857852492077 5144535515285571694684529)
        ·
          refine ⟨3858401636464178771013397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5144535515285571694684529 3858401636464178771013397)
          ·
            refine ⟨180862576709258379891253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 3858401636464178771013397 180862576709258379891253)
            ·
              refine ⟨16955866566492973114805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 180862576709258379891253 16955866566492973114805)
              ·
                rfl

theorem cell19_167171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 5].length) (baseStart_167171 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_167171 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_167171 prefixEnd_167171 := by exact prefixLift 167171
  have htrace : WordTrace (prefixWord ++ tailWord_167171) baseStart_167171 baseEnd_167171 := by
    simpa [prefixWord, tailWord_167171, baseEnd_167171] using wordTrace_append hprefix tailTrace_167171
  have hstable : (prefixWord ++ tailWord_167171).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167171).length < 2 ^ (prefixWord ++ tailWord_167171).sum := by decide
  have hdescent : baseEnd_167171 < baseStart_167171 := by decide
  rcases family_descends (prefixWord ++ tailWord_167171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167264 : List Nat := [2, 1, 1, 3, 4, 2, 3, 3]
def baseStart_167264 : Nat := 118140960795 + 167264 * 2 ^ 59
def prefixEnd_167264 : Nat := 4983230072969 + 3 ^ 40 * 167264 * 2
def baseEnd_167264 : Nat := 50895898188882259277495

theorem tailTrace_167264 : CollatzResearch.WordTrace tailWord_167264 prefixEnd_167264 50895898188882259277495 := by
  unfold tailWord_167264
  simp only [CollatzResearch.WordTrace]
  refine ⟨3050309633019284631010423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4067079510692379508013897 3050309633019284631010423)
  ·
    refine ⟨4575464449528926946515635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3050309633019284631010423 4575464449528926946515635)
    ·
      refine ⟨6863196674293390419773453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4575464449528926946515635 6863196674293390419773453)
      ·
        refine ⟨2573698752860021407415045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6863196674293390419773453 2573698752860021407415045)
        ·
          refine ⟨482568516161254013890321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2573698752860021407415045 482568516161254013890321)
          ·
            refine ⟨361926387120940510417741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 482568516161254013890321 361926387120940510417741)
            ·
              refine ⟨135722395170352691406653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 361926387120940510417741 135722395170352691406653)
              ·
                refine ⟨50895898188882259277495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 135722395170352691406653 50895898188882259277495)
                ·
                  rfl

theorem cell19_167264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 3, 3].length) (baseStart_167264 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_167264 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_167264 prefixEnd_167264 := by exact prefixLift 167264
  have htrace : WordTrace (prefixWord ++ tailWord_167264) baseStart_167264 baseEnd_167264 := by
    simpa [prefixWord, tailWord_167264, baseEnd_167264] using wordTrace_append hprefix tailTrace_167264
  have hstable : (prefixWord ++ tailWord_167264).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167264).length < 2 ^ (prefixWord ++ tailWord_167264).sum := by decide
  have hdescent : baseEnd_167264 < baseStart_167264 := by decide
  rcases family_descends (prefixWord ++ tailWord_167264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167287 : List Nat := [1, 1, 3, 1, 1, 2, 10]
def baseStart_167287 : Nat := 118140960795 + 167287 * 2 ^ 59
def prefixEnd_167287 : Nat := 4983230072969 + 3 ^ 40 * 167287 * 2
def baseEnd_167287 : Nat := 16967632246675006922107

theorem tailTrace_167287 : CollatzResearch.WordTrace tailWord_167287 prefixEnd_167287 16967632246675006922107 := by
  unfold tailWord_167287
  simp only [CollatzResearch.WordTrace]
  refine ⟨6101458144955244190108115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4067638763303496126738743 6101458144955244190108115)
  ·
    refine ⟨9152187217432866285162173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6101458144955244190108115 9152187217432866285162173)
    ·
      refine ⟨3432070206537324856935815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9152187217432866285162173 3432070206537324856935815)
      ·
        refine ⟨5148105309805987285403723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3432070206537324856935815 5148105309805987285403723)
        ·
          refine ⟨7722157964708980928105585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5148105309805987285403723 7722157964708980928105585)
          ·
            refine ⟨5791618473531735696079189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7722157964708980928105585 5791618473531735696079189)
            ·
              refine ⟨16967632246675006922107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 5791618473531735696079189 16967632246675006922107)
              ·
                rfl

theorem cell19_167287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 10].length) (baseStart_167287 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_167287 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_167287 prefixEnd_167287 := by exact prefixLift 167287
  have htrace : WordTrace (prefixWord ++ tailWord_167287) baseStart_167287 baseEnd_167287 := by
    simpa [prefixWord, tailWord_167287, baseEnd_167287] using wordTrace_append hprefix tailTrace_167287
  have hstable : (prefixWord ++ tailWord_167287).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167287).length < 2 ^ (prefixWord ++ tailWord_167287).sum := by decide
  have hdescent : baseEnd_167287 < baseStart_167287 := by decide
  rcases family_descends (prefixWord ++ tailWord_167287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167321 : List Nat := [1, 2, 1, 2, 1, 7, 2, 3]
def baseStart_167321 : Nat := 118140960795 + 167321 * 2 ^ 59
def prefixEnd_167321 : Nat := 4983230072969 + 3 ^ 40 * 167321 * 2
def baseEnd_167321 : Nat := 50913242424323016010673

theorem tailTrace_167321 : CollatzResearch.WordTrace tailWord_167321 prefixEnd_167321 50913242424323016010673 := by
  unfold tailWord_167321
  simp only [CollatzResearch.WordTrace]
  refine ⟨6102698226832067996845817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4068465484554711997897211 6102698226832067996845817)
  ·
    refine ⟨4577023670124050997634363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6102698226832067996845817 4577023670124050997634363)
    ·
      refine ⟨6865535505186076496451545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4577023670124050997634363 6865535505186076496451545)
      ·
        refine ⟨5149151628889557372338659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6865535505186076496451545 5149151628889557372338659)
        ·
          refine ⟨7723727443334336058507989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5149151628889557372338659 7723727443334336058507989)
          ·
            refine ⟨181024861953148501371281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 7723727443334336058507989 181024861953148501371281)
            ·
              refine ⟨135768646464861376028461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 181024861953148501371281 135768646464861376028461)
              ·
                refine ⟨50913242424323016010673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 135768646464861376028461 50913242424323016010673)
                ·
                  rfl

theorem cell19_167321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 2, 3].length) (baseStart_167321 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_167321 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_167321 prefixEnd_167321 := by exact prefixLift 167321
  have htrace : WordTrace (prefixWord ++ tailWord_167321) baseStart_167321 baseEnd_167321 := by
    simpa [prefixWord, tailWord_167321, baseEnd_167321] using wordTrace_append hprefix tailTrace_167321
  have hstable : (prefixWord ++ tailWord_167321).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167321).length < 2 ^ (prefixWord ++ tailWord_167321).sum := by decide
  have hdescent : baseEnd_167321 < baseStart_167321 := by decide
  rcases family_descends (prefixWord ++ tailWord_167321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167363 : List Nat := [1, 1, 1, 3, 1, 1, 5, 6]
def baseStart_167363 : Nat := 118140960795 + 167363 * 2 ^ 59
def prefixEnd_167363 : Nat := 4983230072969 + 3 ^ 40 * 167363 * 2
def baseEnd_167363 : Nat := 50926022387279363077225

theorem tailTrace_167363 : CollatzResearch.WordTrace tailWord_167363 prefixEnd_167363 50926022387279363077225 := by
  unfold tailWord_167363
  simp only [CollatzResearch.WordTrace]
  refine ⟨6104230092679909169874743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4069486728453272779916495 6104230092679909169874743)
  ·
    refine ⟨9156345139019863754812115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6104230092679909169874743 9156345139019863754812115)
    ·
      refine ⟨13734517708529795632218173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9156345139019863754812115 13734517708529795632218173)
      ·
        refine ⟨5150444140698673362081815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13734517708529795632218173 5150444140698673362081815)
        ·
          refine ⟨7725666211048010043122723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5150444140698673362081815 7725666211048010043122723)
          ·
            refine ⟨11588499316572015064684085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7725666211048010043122723 11588499316572015064684085)
            ·
              refine ⟨1086421810928626412314133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11588499316572015064684085 1086421810928626412314133)
              ·
                refine ⟨50926022387279363077225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1086421810928626412314133 50926022387279363077225)
                ·
                  rfl

theorem cell19_167363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 6].length) (baseStart_167363 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_167363 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_167363 prefixEnd_167363 := by exact prefixLift 167363
  have htrace : WordTrace (prefixWord ++ tailWord_167363) baseStart_167363 baseEnd_167363 := by
    simpa [prefixWord, tailWord_167363, baseEnd_167363] using wordTrace_append hprefix tailTrace_167363
  have hstable : (prefixWord ++ tailWord_167363).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167363).length < 2 ^ (prefixWord ++ tailWord_167363).sum := by decide
  have hdescent : baseEnd_167363 < baseStart_167363 := by decide
  rcases family_descends (prefixWord ++ tailWord_167363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167435 : List Nat := [1, 1, 1, 1, 8, 1, 3, 3]
def baseStart_167435 : Nat := 118140960795 + 167435 * 2 ^ 59
def prefixEnd_167435 : Nat := 4983230072969 + 3 ^ 40 * 167435 * 2
def baseEnd_167435 : Nat := 50947930895204529477029

theorem tailTrace_167435 : CollatzResearch.WordTrace tailWord_167435 prefixEnd_167435 50947930895204529477029 := by
  unfold tailWord_167435
  simp only [CollatzResearch.WordTrace]
  refine ⟨6106856148419065466495759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4071237432279376977663839 6106856148419065466495759)
  ·
    refine ⟨9160284222628598199743639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6106856148419065466495759 9160284222628598199743639)
    ·
      refine ⟨13740426333942897299615459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9160284222628598199743639 13740426333942897299615459)
      ·
        refine ⟨20610639500914345949423189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13740426333942897299615459 20610639500914345949423189)
        ·
          refine ⟨241530931651339991594803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 20610639500914345949423189 241530931651339991594803)
          ·
            refine ⟨362296397477009987392205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 241530931651339991594803 362296397477009987392205)
            ·
              refine ⟨135861149053878745272077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 362296397477009987392205 135861149053878745272077)
              ·
                refine ⟨50947930895204529477029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 135861149053878745272077 50947930895204529477029)
                ·
                  rfl

theorem cell19_167435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 3, 3].length) (baseStart_167435 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_167435 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_167435 prefixEnd_167435 := by exact prefixLift 167435
  have htrace : WordTrace (prefixWord ++ tailWord_167435) baseStart_167435 baseEnd_167435 := by
    simpa [prefixWord, tailWord_167435, baseEnd_167435] using wordTrace_append hprefix tailTrace_167435
  have hstable : (prefixWord ++ tailWord_167435).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167435).length < 2 ^ (prefixWord ++ tailWord_167435).sum := by decide
  have hdescent : baseEnd_167435 < baseStart_167435 := by decide
  rcases family_descends (prefixWord ++ tailWord_167435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167456 : List Nat := [2, 1, 1, 6, 1, 2, 6]
def baseStart_167456 : Nat := 118140960795 + 167456 * 2 ^ 59
def prefixEnd_167456 : Nat := 4983230072969 + 3 ^ 40 * 167456 * 2
def baseEnd_167456 : Nat := 16984773625560901003435

theorem tailTrace_167456 : CollatzResearch.WordTrace tailWord_167456 prefixEnd_167456 16984773625560901003435 := by
  unfold tailWord_167456
  simp only [CollatzResearch.WordTrace]
  refine ⟨3053811040671493026505111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4071748054228657368673481 3053811040671493026505111)
  ·
    refine ⟨4580716561007239539757667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3053811040671493026505111 4580716561007239539757667)
    ·
      refine ⟨6871074841510859309636501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4580716561007239539757667 6871074841510859309636501)
      ·
        refine ⟨322081633195821530139211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 6871074841510859309636501 322081633195821530139211)
        ·
          refine ⟨483122449793732295208817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 322081633195821530139211 483122449793732295208817)
          ·
            refine ⟨362341837345299221406613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 483122449793732295208817 362341837345299221406613)
            ·
              refine ⟨16984773625560901003435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 362341837345299221406613 16984773625560901003435)
              ·
                rfl

theorem cell19_167456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 6].length) (baseStart_167456 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_167456 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_167456 prefixEnd_167456 := by exact prefixLift 167456
  have htrace : WordTrace (prefixWord ++ tailWord_167456) baseStart_167456 baseEnd_167456 := by
    simpa [prefixWord, tailWord_167456, baseEnd_167456] using wordTrace_append hprefix tailTrace_167456
  have hstable : (prefixWord ++ tailWord_167456).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167456).length < 2 ^ (prefixWord ++ tailWord_167456).sum := by decide
  have hdescent : baseEnd_167456 < baseStart_167456 := by decide
  rcases family_descends (prefixWord ++ tailWord_167456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167570 : List Nat := [3, 2, 3, 1, 3, 7]
def baseStart_167570 : Nat := 118140960795 + 167570 * 2 ^ 59
def prefixEnd_167570 : Nat := 4983230072969 + 3 ^ 40 * 167570 * 2
def baseEnd_167570 : Nat := 5665445483062690719629

theorem tailTrace_167570 : CollatzResearch.WordTrace tailWord_167570 prefixEnd_167570 5665445483062690719629 := by
  unfold tailWord_167570
  simp only [CollatzResearch.WordTrace]
  refine ⟨1527945000732495880665041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4074520001953322348440109 1527945000732495880665041)
  ·
    refine ⟨1145958750549371910498781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1527945000732495880665041 1145958750549371910498781)
    ·
      refine ⟨429734531456014466437043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1145958750549371910498781 429734531456014466437043)
      ·
        refine ⟨644601797184021699655565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 429734531456014466437043 644601797184021699655565)
        ·
          refine ⟨241725673944008137370837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 644601797184021699655565 241725673944008137370837)
          ·
            refine ⟨5665445483062690719629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 241725673944008137370837 5665445483062690719629)
            ·
              rfl

theorem cell19_167570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 7].length) (baseStart_167570 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_167570 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_167570 prefixEnd_167570 := by exact prefixLift 167570
  have htrace : WordTrace (prefixWord ++ tailWord_167570) baseStart_167570 baseEnd_167570 := by
    simpa [prefixWord, tailWord_167570, baseEnd_167570] using wordTrace_append hprefix tailTrace_167570
  have hstable : (prefixWord ++ tailWord_167570).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167570).length < 2 ^ (prefixWord ++ tailWord_167570).sum := by decide
  have hdescent : baseEnd_167570 < baseStart_167570 := by decide
  rcases family_descends (prefixWord ++ tailWord_167570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167665 : List Nat := [1, 2, 2, 2, 2, 3, 4, 3]
def baseStart_167665 : Nat := 118140960795 + 167665 * 2 ^ 59
def prefixEnd_167665 : Nat := 4983230072969 + 3 ^ 40 * 167665 * 2
def baseEnd_167665 : Nat := 51017916406632144365291

theorem tailTrace_167665 : CollatzResearch.WordTrace tailWord_167665 prefixEnd_167665 51017916406632144365291 := by
  unfold tailWord_167665
  simp only [CollatzResearch.WordTrace]
  refine ⟨6115244937585814747368449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4076829958390543164912299 6115244937585814747368449)
  ·
    refine ⟨4586433703189361060526337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6115244937585814747368449 4586433703189361060526337)
    ·
      refine ⟨3439825277392020795394753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4586433703189361060526337 3439825277392020795394753)
      ·
        refine ⟨2579868958044015596546065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3439825277392020795394753 2579868958044015596546065)
        ·
          refine ⟨1934901718533011697409549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2579868958044015596546065 1934901718533011697409549)
          ·
            refine ⟨725588144449879386528581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1934901718533011697409549 725588144449879386528581)
            ·
              refine ⟨136047777084352384974109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 725588144449879386528581 136047777084352384974109)
              ·
                refine ⟨51017916406632144365291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 136047777084352384974109 51017916406632144365291)
                ·
                  rfl

theorem cell19_167665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 4, 3].length) (baseStart_167665 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_167665 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_167665 prefixEnd_167665 := by exact prefixLift 167665
  have htrace : WordTrace (prefixWord ++ tailWord_167665) baseStart_167665 baseEnd_167665 := by
    simpa [prefixWord, tailWord_167665, baseEnd_167665] using wordTrace_append hprefix tailTrace_167665
  have hstable : (prefixWord ++ tailWord_167665).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167665).length < 2 ^ (prefixWord ++ tailWord_167665).sum := by decide
  have hdescent : baseEnd_167665 < baseStart_167665 := by decide
  rcases family_descends (prefixWord ++ tailWord_167665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167684 : List Nat := [2, 3, 2, 2, 1, 4, 5]
def baseStart_167684 : Nat := 118140960795 + 167684 * 2 ^ 59
def prefixEnd_167684 : Nat := 4983230072969 + 3 ^ 40 * 167684 * 2
def baseEnd_167684 : Nat := 17007899272815243314339

theorem tailTrace_167684 : CollatzResearch.WordTrace tailWord_167684 prefixEnd_167684 17007899272815243314339 := by
  unfold tailWord_167684
  simp only [CollatzResearch.WordTrace]
  refine ⟨3057968962258490496155053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4077291949677987328206737 3057968962258490496155053)
  ·
    refine ⟨1146738360846933936058145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3057968962258490496155053 1146738360846933936058145)
    ·
      refine ⟨860053770635200452043609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1146738360846933936058145 860053770635200452043609)
      ·
        refine ⟨645040327976400339032707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 860053770635200452043609 645040327976400339032707)
        ·
          refine ⟨967560491964600508549061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 645040327976400339032707 967560491964600508549061)
          ·
            refine ⟨181417592243362595352949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 967560491964600508549061 181417592243362595352949)
            ·
              refine ⟨17007899272815243314339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 181417592243362595352949 17007899272815243314339)
              ·
                rfl

theorem cell19_167684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 5].length) (baseStart_167684 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_167684 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_167684 prefixEnd_167684 := by exact prefixLift 167684
  have htrace : WordTrace (prefixWord ++ tailWord_167684) baseStart_167684 baseEnd_167684 := by
    simpa [prefixWord, tailWord_167684, baseEnd_167684] using wordTrace_append hprefix tailTrace_167684
  have hstable : (prefixWord ++ tailWord_167684).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167684).length < 2 ^ (prefixWord ++ tailWord_167684).sum := by decide
  have hdescent : baseEnd_167684 < baseStart_167684 := by decide
  rcases family_descends (prefixWord ++ tailWord_167684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167703 : List Nat := [1, 1, 3, 4, 2, 2, 2, 4]
def baseStart_167703 : Nat := 118140960795 + 167703 * 2 ^ 59
def prefixEnd_167703 : Nat := 4983230072969 + 3 ^ 40 * 167703 * 2
def baseEnd_167703 : Nat := 51029479230259315520743

theorem tailTrace_167703 : CollatzResearch.WordTrace tailWord_167703 prefixEnd_167703 51029479230259315520743 := by
  unfold tailWord_167703
  simp only [CollatzResearch.WordTrace]
  refine ⟨6116630911448147237251763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4077753940965431491501175 6116630911448147237251763)
  ·
    refine ⟨9174946367172220855877645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6116630911448147237251763 9174946367172220855877645)
    ·
      refine ⟨3440604887689582820954117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9174946367172220855877645 3440604887689582820954117)
      ·
        refine ⟨645113416441796778928897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3440604887689582820954117 645113416441796778928897)
        ·
          refine ⟨483835062331347584196673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 645113416441796778928897 483835062331347584196673)
          ·
            refine ⟨362876296748510688147505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 483835062331347584196673 362876296748510688147505)
            ·
              refine ⟨272157222561383016110629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 362876296748510688147505 272157222561383016110629)
              ·
                refine ⟨51029479230259315520743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 272157222561383016110629 51029479230259315520743)
                ·
                  rfl

theorem cell19_167703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 2, 4].length) (baseStart_167703 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_167703 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_167703 prefixEnd_167703 := by exact prefixLift 167703
  have htrace : WordTrace (prefixWord ++ tailWord_167703) baseStart_167703 baseEnd_167703 := by
    simpa [prefixWord, tailWord_167703, baseEnd_167703] using wordTrace_append hprefix tailTrace_167703
  have hstable : (prefixWord ++ tailWord_167703).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167703).length < 2 ^ (prefixWord ++ tailWord_167703).sum := by decide
  have hdescent : baseEnd_167703 < baseStart_167703 := by decide
  rcases family_descends (prefixWord ++ tailWord_167703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167724 : List Nat := [2, 2, 1, 1, 1, 5, 2, 5]
def baseStart_167724 : Nat := 118140960795 + 167724 * 2 ^ 59
def prefixEnd_167724 : Nat := 4983230072969 + 3 ^ 40 * 167724 * 2
def baseEnd_167724 : Nat := 51035869211737489054019

theorem tailTrace_167724 : CollatzResearch.WordTrace tailWord_167724 prefixEnd_167724 51035869211737489054019 := by
  unfold tailWord_167724
  simp only [CollatzResearch.WordTrace]
  refine ⟨3058698422186033911883113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4078264562914711882510817 3058698422186033911883113)
  ·
    refine ⟨2294023816639525433912335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3058698422186033911883113 2294023816639525433912335)
    ·
      refine ⟨3441035724959288150868503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2294023816639525433912335 3441035724959288150868503)
      ·
        refine ⟨5161553587438932226302755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3441035724959288150868503 5161553587438932226302755)
        ·
          refine ⟨7742330381158398339454133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5161553587438932226302755 7742330381158398339454133)
          ·
            refine ⟨725843473233599844323825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7742330381158398339454133 725843473233599844323825)
            ·
              refine ⟨544382604925199883242869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 725843473233599844323825 544382604925199883242869)
              ·
                refine ⟨51035869211737489054019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 544382604925199883242869 51035869211737489054019)
                ·
                  rfl

theorem cell19_167724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 5].length) (baseStart_167724 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_167724 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_167724 prefixEnd_167724 := by exact prefixLift 167724
  have htrace : WordTrace (prefixWord ++ tailWord_167724) baseStart_167724 baseEnd_167724 := by
    simpa [prefixWord, tailWord_167724, baseEnd_167724] using wordTrace_append hprefix tailTrace_167724
  have hstable : (prefixWord ++ tailWord_167724).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167724).length < 2 ^ (prefixWord ++ tailWord_167724).sum := by decide
  have hdescent : baseEnd_167724 < baseStart_167724 := by decide
  rcases family_descends (prefixWord ++ tailWord_167724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167743 : List Nat := [1, 1, 2, 2, 6, 7]
def baseStart_167743 : Nat := 118140960795 + 167743 * 2 ^ 59
def prefixEnd_167743 : Nat := 4983230072969 + 3 ^ 40 * 167743 * 2
def baseEnd_167743 : Nat := 5671294513727897181305

theorem tailTrace_167743 : CollatzResearch.WordTrace tailWord_167743 prefixEnd_167743 5671294513727897181305 := by
  unfold tailWord_167743
  simp only [CollatzResearch.WordTrace]
  refine ⟨6118089831303234068707883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4078726554202156045805255 6118089831303234068707883)
  ·
    refine ⟨9177134746954851103061825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6118089831303234068707883 9177134746954851103061825)
    ·
      refine ⟨6882851060216138327296369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9177134746954851103061825 6882851060216138327296369)
      ·
        refine ⟨5162138295162103745472277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6882851060216138327296369 5162138295162103745472277)
        ·
          refine ⟨241975232585723613069013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 5162138295162103745472277 241975232585723613069013)
          ·
            refine ⟨5671294513727897181305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 241975232585723613069013 5671294513727897181305)
            ·
              rfl

theorem cell19_167743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 7].length) (baseStart_167743 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_167743 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_167743 prefixEnd_167743 := by exact prefixLift 167743
  have htrace : WordTrace (prefixWord ++ tailWord_167743) baseStart_167743 baseEnd_167743 := by
    simpa [prefixWord, tailWord_167743, baseEnd_167743] using wordTrace_append hprefix tailTrace_167743
  have hstable : (prefixWord ++ tailWord_167743).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167743).length < 2 ^ (prefixWord ++ tailWord_167743).sum := by decide
  have hdescent : baseEnd_167743 < baseStart_167743 := by decide
  rcases family_descends (prefixWord ++ tailWord_167743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167832 : List Nat := [2, 1, 2, 6, 1, 2, 2, 3]
def baseStart_167832 : Nat := 118140960795 + 167832 * 2 ^ 59
def prefixEnd_167832 : Nat := 4983230072969 + 3 ^ 40 * 167832 * 2
def baseEnd_167832 : Nat := 51068731973625238653725

theorem tailTrace_167832 : CollatzResearch.WordTrace tailWord_167832 prefixEnd_167832 51068731973625238653725 := by
  unfold tailWord_167832
  simp only [CollatzResearch.WordTrace]
  refine ⟨3060667963990401134348875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4080890618653868179131833 3060667963990401134348875)
  ·
    refine ⟨4591001945985601701523313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3060667963990401134348875 4591001945985601701523313)
    ·
      refine ⟨3443251459489201276142485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4591001945985601701523313 3443251459489201276142485)
      ·
        refine ⟨161402412163556309819179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 3443251459489201276142485 161402412163556309819179)
        ·
          refine ⟨242103618245334464728769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161402412163556309819179 242103618245334464728769)
          ·
            refine ⟨181577713684000848546577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 242103618245334464728769 181577713684000848546577)
            ·
              refine ⟨136183285263000636409933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 181577713684000848546577 136183285263000636409933)
              ·
                refine ⟨51068731973625238653725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 136183285263000636409933 51068731973625238653725)
                ·
                  rfl

theorem cell19_167832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 2, 3].length) (baseStart_167832 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_167832 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_167832 prefixEnd_167832 := by exact prefixLift 167832
  have htrace : WordTrace (prefixWord ++ tailWord_167832) baseStart_167832 baseEnd_167832 := by
    simpa [prefixWord, tailWord_167832, baseEnd_167832] using wordTrace_append hprefix tailTrace_167832
  have hstable : (prefixWord ++ tailWord_167832).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167832).length < 2 ^ (prefixWord ++ tailWord_167832).sum := by decide
  have hdescent : baseEnd_167832 < baseStart_167832 := by decide
  rcases family_descends (prefixWord ++ tailWord_167832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167834 : List Nat := [3, 1, 1, 4, 2, 3, 2, 3]
def baseStart_167834 : Nat := 118140960795 + 167834 * 2 ^ 59
def prefixEnd_167834 : Nat := 4983230072969 + 3 ^ 40 * 167834 * 2
def baseEnd_167834 : Nat := 51069340543289826609275

theorem tailTrace_167834 : CollatzResearch.WordTrace tailWord_167834 prefixEnd_167834 51069340543289826609275 := by
  unfold tailWord_167834
  simp only [CollatzResearch.WordTrace]
  refine ⟨1530352218493389152567639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4080939249315704406847037 1530352218493389152567639)
  ·
    refine ⟨2295528327740083728851459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1530352218493389152567639 2295528327740083728851459)
    ·
      refine ⟨3443292491610125593277189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2295528327740083728851459 3443292491610125593277189)
      ·
        refine ⟨645617342176898548739473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3443292491610125593277189 645617342176898548739473)
        ·
          refine ⟨484213006632673911554605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 645617342176898548739473 484213006632673911554605)
          ·
            refine ⟨181579877487252716832977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 484213006632673911554605 181579877487252716832977)
            ·
              refine ⟨136184908115439537624733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 181579877487252716832977 136184908115439537624733)
              ·
                refine ⟨51069340543289826609275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 136184908115439537624733 51069340543289826609275)
                ·
                  rfl

theorem cell19_167834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 2, 3].length) (baseStart_167834 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_167834 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_167834 prefixEnd_167834 := by exact prefixLift 167834
  have htrace : WordTrace (prefixWord ++ tailWord_167834) baseStart_167834 baseEnd_167834 := by
    simpa [prefixWord, tailWord_167834, baseEnd_167834] using wordTrace_append hprefix tailTrace_167834
  have hstable : (prefixWord ++ tailWord_167834).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167834).length < 2 ^ (prefixWord ++ tailWord_167834).sum := by decide
  have hdescent : baseEnd_167834 < baseStart_167834 := by decide
  rcases family_descends (prefixWord ++ tailWord_167834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167836 : List Nat := [2, 2, 3, 3, 1, 2, 1, 5]
def baseStart_167836 : Nat := 118140960795 + 167836 * 2 ^ 59
def prefixEnd_167836 : Nat := 4983230072969 + 3 ^ 40 * 167836 * 2
def baseEnd_167836 : Nat := 51069949112954414564825

theorem tailTrace_167836 : CollatzResearch.WordTrace tailWord_167836 prefixEnd_167836 51069949112954414564825 := by
  unfold tailWord_167836
  simp only [CollatzResearch.WordTrace]
  refine ⟨3060740909983155475921681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4080987879977540634562241 3060740909983155475921681)
  ·
    refine ⟨2295555682487366606941261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3060740909983155475921681 2295555682487366606941261)
    ·
      refine ⟨860833380932762477602973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2295555682487366606941261 860833380932762477602973)
      ·
        refine ⟨322812517849785929101115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 860833380932762477602973 322812517849785929101115)
        ·
          refine ⟨484218776774678893651673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 322812517849785929101115 484218776774678893651673)
          ·
            refine ⟨363164082581009170238755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 484218776774678893651673 363164082581009170238755)
            ·
              refine ⟨544746123871513755358133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 363164082581009170238755 544746123871513755358133)
              ·
                refine ⟨51069949112954414564825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 544746123871513755358133 51069949112954414564825)
                ·
                  rfl

theorem cell19_167836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 5].length) (baseStart_167836 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_167836 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_167836 prefixEnd_167836 := by exact prefixLift 167836
  have htrace : WordTrace (prefixWord ++ tailWord_167836) baseStart_167836 baseEnd_167836 := by
    simpa [prefixWord, tailWord_167836, baseEnd_167836] using wordTrace_append hprefix tailTrace_167836
  have hstable : (prefixWord ++ tailWord_167836).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167836).length < 2 ^ (prefixWord ++ tailWord_167836).sum := by decide
  have hdescent : baseEnd_167836 < baseStart_167836 := by decide
  rcases family_descends (prefixWord ++ tailWord_167836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167857 : List Nat := [1, 2, 2, 4, 2, 1, 7]
def baseStart_167857 : Nat := 118140960795 + 167857 * 2 ^ 59
def prefixEnd_167857 : Nat := 4983230072969 + 3 ^ 40 * 167857 * 2
def baseEnd_167857 : Nat := 17025446364810862699367

theorem tailTrace_167857 : CollatzResearch.WordTrace tailWord_167857 prefixEnd_167857 17025446364810862699367 := by
  unfold tailWord_167857
  simp only [CollatzResearch.WordTrace]
  refine ⟨6122247752890231538357825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4081498501926821025571883 6122247752890231538357825)
  ·
    refine ⟨4591685814667673653768369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6122247752890231538357825 4591685814667673653768369)
    ·
      refine ⟨3443764361000755240326277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4591685814667673653768369 3443764361000755240326277)
      ·
        refine ⟨645705817687641607561177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3443764361000755240326277 645705817687641607561177)
        ·
          refine ⟨484279363265731205670883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 645705817687641607561177 484279363265731205670883)
          ·
            refine ⟨726419044898596808506325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 484279363265731205670883 726419044898596808506325)
            ·
              refine ⟨17025446364810862699367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 726419044898596808506325 17025446364810862699367)
              ·
                rfl

theorem cell19_167857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 7].length) (baseStart_167857 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_167857 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_167857 prefixEnd_167857 := by exact prefixLift 167857
  have htrace : WordTrace (prefixWord ++ tailWord_167857) baseStart_167857 baseEnd_167857 := by
    simpa [prefixWord, tailWord_167857, baseEnd_167857] using wordTrace_append hprefix tailTrace_167857
  have hstable : (prefixWord ++ tailWord_167857).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167857).length < 2 ^ (prefixWord ++ tailWord_167857).sum := by decide
  have hdescent : baseEnd_167857 < baseStart_167857 := by decide
  rcases family_descends (prefixWord ++ tailWord_167857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167933 : List Nat := [1, 4, 1, 1, 1, 2, 5, 4]
def baseStart_167933 : Nat := 118140960795 + 167933 * 2 ^ 59
def prefixEnd_167933 : Nat := 4983230072969 + 3 ^ 40 * 167933 * 2
def baseEnd_167933 : Nat := 51099464741686930409005

theorem tailTrace_167933 : CollatzResearch.WordTrace tailWord_167933 prefixEnd_167933 51099464741686930409005 := by
  unfold tailWord_167933
  simp only [CollatzResearch.WordTrace]
  refine ⟨6125019700614896518124453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4083346467076597678749635 6125019700614896518124453)
  ·
    refine ⟨1148441193865293097148335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6125019700614896518124453 1148441193865293097148335)
    ·
      refine ⟨1722661790797939645722503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1148441193865293097148335 1722661790797939645722503)
      ·
        refine ⟨2583992686196909468583755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1722661790797939645722503 2583992686196909468583755)
        ·
          refine ⟨3875989029295364202875633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2583992686196909468583755 3875989029295364202875633)
          ·
            refine ⟨2906991771971523152156725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3875989029295364202875633 2906991771971523152156725)
            ·
              refine ⟨272530478622330295514693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2906991771971523152156725 272530478622330295514693)
              ·
                refine ⟨51099464741686930409005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 272530478622330295514693 51099464741686930409005)
                ·
                  rfl

theorem cell19_167933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 5, 4].length) (baseStart_167933 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_167933 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_167933 prefixEnd_167933 := by exact prefixLift 167933
  have htrace : WordTrace (prefixWord ++ tailWord_167933) baseStart_167933 baseEnd_167933 := by
    simpa [prefixWord, tailWord_167933, baseEnd_167933] using wordTrace_append hprefix tailTrace_167933
  have hstable : (prefixWord ++ tailWord_167933).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167933).length < 2 ^ (prefixWord ++ tailWord_167933).sum := by decide
  have hdescent : baseEnd_167933 < baseStart_167933 := by decide
  rcases family_descends (prefixWord ++ tailWord_167933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167942 : List Nat := [6, 2, 1, 2, 1, 1, 3, 3]
def baseStart_167942 : Nat := 118140960795 + 167942 * 2 ^ 59
def prefixEnd_167942 : Nat := 4983230072969 + 3 ^ 40 * 167942 * 2
def baseEnd_167942 : Nat := 51102203305177576208981

theorem tailTrace_167942 : CollatzResearch.WordTrace tailWord_167942 prefixEnd_167942 51102203305177576208981 := by
  unfold tailWord_167942
  simp only [CollatzResearch.WordTrace]
  refine ⟨191417123674446595475065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 4083565305054860703468053 191417123674446595475065)
  ·
    refine ⟨143562842755834946606299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191417123674446595475065 143562842755834946606299)
    ·
      refine ⟨215344264133752419909449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143562842755834946606299 215344264133752419909449)
      ·
        refine ⟨161508198100314314932087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 215344264133752419909449 161508198100314314932087)
        ·
          refine ⟨242262297150471472398131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161508198100314314932087 242262297150471472398131)
          ·
            refine ⟨363393445725707208597197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 242262297150471472398131 363393445725707208597197)
            ·
              refine ⟨136272542147140203223949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 363393445725707208597197 136272542147140203223949)
              ·
                refine ⟨51102203305177576208981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 136272542147140203223949 51102203305177576208981)
                ·
                  rfl

theorem cell19_167942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 3, 3].length) (baseStart_167942 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_167942 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_167942 prefixEnd_167942 := by exact prefixLift 167942
  have htrace : WordTrace (prefixWord ++ tailWord_167942) baseStart_167942 baseEnd_167942 := by
    simpa [prefixWord, tailWord_167942, baseEnd_167942] using wordTrace_append hprefix tailTrace_167942
  have hstable : (prefixWord ++ tailWord_167942).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167942).length < 2 ^ (prefixWord ++ tailWord_167942).sum := by decide
  have hdescent : baseEnd_167942 < baseStart_167942 := by decide
  rcases family_descends (prefixWord ++ tailWord_167942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167950 : List Nat := [4, 1, 1, 2, 2, 1, 5, 3]
def baseStart_167950 : Nat := 118140960795 + 167950 * 2 ^ 59
def prefixEnd_167950 : Nat := 4983230072969 + 3 ^ 40 * 167950 * 2
def baseEnd_167950 : Nat := 51104637583835928031181

theorem tailTrace_167950 : CollatzResearch.WordTrace tailWord_167950 prefixEnd_167950 51104637583835928031181 := by
  unfold tailWord_167950
  simp only [CollatzResearch.WordTrace]
  refine ⟨765704967694163552686663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4083759827702205614328869 765704967694163552686663)
  ·
    refine ⟨1148557451541245329029995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 765704967694163552686663 1148557451541245329029995)
    ·
      refine ⟨1722836177311867993544993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1148557451541245329029995 1722836177311867993544993)
      ·
        refine ⟨1292127132983900995158745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1722836177311867993544993 1292127132983900995158745)
        ·
          refine ⟨969095349737925746369059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1292127132983900995158745 969095349737925746369059)
          ·
            refine ⟨1453643024606888619553589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 969095349737925746369059 1453643024606888619553589)
            ·
              refine ⟨136279033556895808083149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1453643024606888619553589 136279033556895808083149)
              ·
                refine ⟨51104637583835928031181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 136279033556895808083149 51104637583835928031181)
                ·
                  rfl

theorem cell19_167950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 5, 3].length) (baseStart_167950 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_167950 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_167950 prefixEnd_167950 := by exact prefixLift 167950
  have htrace : WordTrace (prefixWord ++ tailWord_167950) baseStart_167950 baseEnd_167950 := by
    simpa [prefixWord, tailWord_167950, baseEnd_167950] using wordTrace_append hprefix tailTrace_167950
  have hstable : (prefixWord ++ tailWord_167950).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167950).length < 2 ^ (prefixWord ++ tailWord_167950).sum := by decide
  have hdescent : baseEnd_167950 < baseStart_167950 := by decide
  rcases family_descends (prefixWord ++ tailWord_167950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168011 : List Nat := [1, 1, 1, 1, 3, 1, 2, 9]
def baseStart_168011 : Nat := 118140960795 + 168011 * 2 ^ 59
def prefixEnd_168011 : Nat := 4983230072969 + 3 ^ 40 * 168011 * 2
def baseEnd_168011 : Nat := 51123198958605860675459

theorem tailTrace_168011 : CollatzResearch.WordTrace tailWord_168011 prefixEnd_168011 51123198958605860675459 := by
  unfold tailWord_168011
  simp only [CollatzResearch.WordTrace]
  refine ⟨6127864594332315839463887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4085243062888210559642591 6127864594332315839463887)
  ·
    refine ⟨9191796891498473759195831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6127864594332315839463887 9191796891498473759195831)
    ·
      refine ⟨13787695337247710638793747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9191796891498473759195831 13787695337247710638793747)
      ·
        refine ⟨20681543005871565958190621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13787695337247710638793747 20681543005871565958190621)
        ·
          refine ⟨7755578627201837234321483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20681543005871565958190621 7755578627201837234321483)
          ·
            refine ⟨11633367940802755851482225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7755578627201837234321483 11633367940802755851482225)
            ·
              refine ⟨8725025955602066888611669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11633367940802755851482225 8725025955602066888611669)
              ·
                refine ⟨51123198958605860675459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8725025955602066888611669 51123198958605860675459)
                ·
                  rfl

theorem cell19_168011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 9].length) (baseStart_168011 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_168011 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_168011 prefixEnd_168011 := by exact prefixLift 168011
  have htrace : WordTrace (prefixWord ++ tailWord_168011) baseStart_168011 baseEnd_168011 := by
    simpa [prefixWord, tailWord_168011, baseEnd_168011] using wordTrace_append hprefix tailTrace_168011
  have hstable : (prefixWord ++ tailWord_168011).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168011).length < 2 ^ (prefixWord ++ tailWord_168011).sum := by decide
  have hdescent : baseEnd_168011 < baseStart_168011 := by decide
  rcases family_descends (prefixWord ++ tailWord_168011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168028 : List Nat := [2, 2, 4, 1, 1, 2, 7]
def baseStart_168028 : Nat := 118140960795 + 168028 * 2 ^ 59
def prefixEnd_168028 : Nat := 4983230072969 + 3 ^ 40 * 168028 * 2
def baseEnd_168028 : Nat := 17042790600251619432545

theorem tailTrace_168028 : CollatzResearch.WordTrace tailWord_168028 prefixEnd_168028 17042790600251619432545 := by
  unfold tailWord_168028
  simp only [CollatzResearch.WordTrace]
  refine ⟨3064242317635363871416369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4085656423513818495221825 3064242317635363871416369)
  ·
    refine ⟨2298181738226522903562277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3064242317635363871416369 2298181738226522903562277)
    ·
      refine ⟨430909075917473044417927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2298181738226522903562277 430909075917473044417927)
      ·
        refine ⟨646363613876209566626891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 430909075917473044417927 646363613876209566626891)
        ·
          refine ⟨969545420814314349940337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 646363613876209566626891 969545420814314349940337)
          ·
            refine ⟨727159065610735762455253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 969545420814314349940337 727159065610735762455253)
            ·
              refine ⟨17042790600251619432545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 727159065610735762455253 17042790600251619432545)
              ·
                rfl

theorem cell19_168028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 7].length) (baseStart_168028 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_168028 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_168028 prefixEnd_168028 := by exact prefixLift 168028
  have htrace : WordTrace (prefixWord ++ tailWord_168028) baseStart_168028 baseEnd_168028 := by
    simpa [prefixWord, tailWord_168028, baseEnd_168028] using wordTrace_append hprefix tailTrace_168028
  have hstable : (prefixWord ++ tailWord_168028).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168028).length < 2 ^ (prefixWord ++ tailWord_168028).sum := by decide
  have hdescent : baseEnd_168028 < baseStart_168028 := by decide
  rcases family_descends (prefixWord ++ tailWord_168028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168047 : List Nat := [1, 1, 2, 1, 3, 5, 2, 4]
def baseStart_168047 : Nat := 118140960795 + 168047 * 2 ^ 59
def prefixEnd_168047 : Nat := 4983230072969 + 3 ^ 40 * 168047 * 2
def baseEnd_168047 : Nat := 51134153212568443875361

theorem tailTrace_168047 : CollatzResearch.WordTrace tailWord_168047 prefixEnd_168047 51134153212568443875361 := by
  unfold tailWord_168047
  simp only [CollatzResearch.WordTrace]
  refine ⟨6129177622201893987774395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4086118414801262658516263 6129177622201893987774395)
  ·
    refine ⟨9193766433302840981661593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6129177622201893987774395 9193766433302840981661593)
    ·
      refine ⟨6895324824977130736246195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9193766433302840981661593 6895324824977130736246195)
      ·
        refine ⟨10342987237465696104369293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6895324824977130736246195 10342987237465696104369293)
        ·
          refine ⟨3878620214049636039138485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10342987237465696104369293 3878620214049636039138485)
          ·
            refine ⟨363620645067153378669233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3878620214049636039138485 363620645067153378669233)
            ·
              refine ⟨272715483800365034001925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 363620645067153378669233 272715483800365034001925)
              ·
                refine ⟨51134153212568443875361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 272715483800365034001925 51134153212568443875361)
                ·
                  rfl

theorem cell19_168047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 2, 4].length) (baseStart_168047 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_168047 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_168047 prefixEnd_168047 := by exact prefixLift 168047
  have htrace : WordTrace (prefixWord ++ tailWord_168047) baseStart_168047 baseEnd_168047 := by
    simpa [prefixWord, tailWord_168047, baseEnd_168047] using wordTrace_append hprefix tailTrace_168047
  have hstable : (prefixWord ++ tailWord_168047).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168047).length < 2 ^ (prefixWord ++ tailWord_168047).sum := by decide
  have hdescent : baseEnd_168047 < baseStart_168047 := by decide
  rcases family_descends (prefixWord ++ tailWord_168047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168087 : List Nat := [1, 1, 3, 3, 11]
def baseStart_168087 : Nat := 118140960795 + 168087 * 2 ^ 59
def prefixEnd_168087 : Nat := 4983230072969 + 3 ^ 40 * 168087 * 2
def baseEnd_168087 : Nat := 1894308318735563073569

theorem tailTrace_168087 : CollatzResearch.WordTrace tailWord_168087 prefixEnd_168087 1894308318735563073569 := by
  unfold tailWord_168087
  simp only [CollatzResearch.WordTrace]
  refine ⟨6130636542056980819230515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4087091028037987212820343 6130636542056980819230515)
  ·
    refine ⟨9195954813085471228845773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6130636542056980819230515 9195954813085471228845773)
    ·
      refine ⟨3448483054907051710817165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9195954813085471228845773 3448483054907051710817165)
      ·
        refine ⟨1293181145590144391556437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3448483054907051710817165 1293181145590144391556437)
        ·
          refine ⟨1894308318735563073569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 1293181145590144391556437 1894308318735563073569)
          ·
            rfl

theorem cell19_168087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 11].length) (baseStart_168087 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_168087 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_168087 prefixEnd_168087 := by exact prefixLift 168087
  have htrace : WordTrace (prefixWord ++ tailWord_168087) baseStart_168087 baseEnd_168087 := by
    simpa [prefixWord, tailWord_168087, baseEnd_168087] using wordTrace_append hprefix tailTrace_168087
  have hstable : (prefixWord ++ tailWord_168087).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168087).length < 2 ^ (prefixWord ++ tailWord_168087).sum := by decide
  have hdescent : baseEnd_168087 < baseStart_168087 := by decide
  rcases family_descends (prefixWord ++ tailWord_168087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168100 : List Nat := [2, 3, 1, 2, 5, 1, 1, 4]
def baseStart_168100 : Nat := 118140960795 + 168100 * 2 ^ 59
def prefixEnd_168100 : Nat := 4983230072969 + 3 ^ 40 * 168100 * 2
def baseEnd_168100 : Nat := 51150280308680024697439

theorem tailTrace_168100 : CollatzResearch.WordTrace tailWord_168100 prefixEnd_168100 51150280308680024697439 := by
  unfold tailWord_168100
  simp only [CollatzResearch.WordTrace]
  refine ⟨3065555345504942019726877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4087407127339922692969169 3065555345504942019726877)
  ·
    refine ⟨1149583254564353257397579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3065555345504942019726877 1149583254564353257397579)
    ·
      refine ⟨1724374881846529886096369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1149583254564353257397579 1724374881846529886096369)
      ·
        refine ⟨1293281161384897414572277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1724374881846529886096369 1293281161384897414572277)
        ·
          refine ⟨121245108879834132616151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1293281161384897414572277 121245108879834132616151)
          ·
            refine ⟨181867663319751198924227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121245108879834132616151 181867663319751198924227)
            ·
              refine ⟨272801494979626798386341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 181867663319751198924227 272801494979626798386341)
              ·
                refine ⟨51150280308680024697439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 272801494979626798386341 51150280308680024697439)
                ·
                  rfl

theorem cell19_168100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 1, 4].length) (baseStart_168100 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_168100 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_168100 prefixEnd_168100 := by exact prefixLift 168100
  have htrace : WordTrace (prefixWord ++ tailWord_168100) baseStart_168100 baseEnd_168100 := by
    simpa [prefixWord, tailWord_168100, baseEnd_168100] using wordTrace_append hprefix tailTrace_168100
  have hstable : (prefixWord ++ tailWord_168100).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168100).length < 2 ^ (prefixWord ++ tailWord_168100).sum := by decide
  have hdescent : baseEnd_168100 < baseStart_168100 := by decide
  rcases family_descends (prefixWord ++ tailWord_168100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168123 : List Nat := [1, 1, 1, 1, 1, 2, 9, 3]
def baseStart_168123 : Nat := 118140960795 + 168123 * 2 ^ 59
def prefixEnd_168123 : Nat := 4983230072969 + 3 ^ 40 * 168123 * 2
def baseEnd_168123 : Nat := 51157278859822786186265

theorem tailTrace_168123 : CollatzResearch.WordTrace tailWord_168123 prefixEnd_168123 51157278859822786186265 := by
  unfold tailWord_168123
  simp only [CollatzResearch.WordTrace]
  refine ⟨6131949569926558967541023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4087966379951039311694015 6131949569926558967541023)
  ·
    refine ⟨9197924354889838451311535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6131949569926558967541023 9197924354889838451311535)
    ·
      refine ⟨13796886532334757676967303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9197924354889838451311535 13796886532334757676967303)
      ·
        refine ⟨20695329798502136515450955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13796886532334757676967303 20695329798502136515450955)
        ·
          refine ⟨31042994697753204773176433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20695329798502136515450955 31042994697753204773176433)
          ·
            refine ⟨23282246023314903579882325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31042994697753204773176433 23282246023314903579882325)
            ·
              refine ⟨136419410292860763163373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 23282246023314903579882325 136419410292860763163373)
              ·
                refine ⟨51157278859822786186265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 136419410292860763163373 51157278859822786186265)
                ·
                  rfl

theorem cell19_168123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 9, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 9, 3].length) (baseStart_168123 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_168123 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_168123 prefixEnd_168123 := by exact prefixLift 168123
  have htrace : WordTrace (prefixWord ++ tailWord_168123) baseStart_168123 baseEnd_168123 := by
    simpa [prefixWord, tailWord_168123, baseEnd_168123] using wordTrace_append hprefix tailTrace_168123
  have hstable : (prefixWord ++ tailWord_168123).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168123).length < 2 ^ (prefixWord ++ tailWord_168123).sum := by decide
  have hdescent : baseEnd_168123 < baseStart_168123 := by decide
  rcases family_descends (prefixWord ++ tailWord_168123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168140 : List Nat := [2, 2, 1, 6, 1, 1, 6]
def baseStart_168140 : Nat := 118140960795 + 168140 * 2 ^ 59
def prefixEnd_168140 : Nat := 4983230072969 + 3 ^ 40 * 168140 * 2
def baseEnd_168140 : Nat := 17054150567323927936147

theorem tailTrace_168140 : CollatzResearch.WordTrace tailWord_168140 prefixEnd_168140 17054150567323927936147 := by
  unfold tailWord_168140
  simp only [CollatzResearch.WordTrace]
  refine ⟨3066284805432485435454937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4088379740576647247273249 3066284805432485435454937)
  ·
    refine ⟨2299713604074364076591203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3066284805432485435454937 2299713604074364076591203)
    ·
      refine ⟨3449570406111546114886805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2299713604074364076591203 3449570406111546114886805)
      ·
        refine ⟨161698612786478724135319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 3449570406111546114886805 161698612786478724135319)
        ·
          refine ⟨242547919179718086202979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161698612786478724135319 242547919179718086202979)
          ·
            refine ⟨363821878769577129304469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 242547919179718086202979 363821878769577129304469)
            ·
              refine ⟨17054150567323927936147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 363821878769577129304469 17054150567323927936147)
              ·
                rfl

theorem cell19_168140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 6].length) (baseStart_168140 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_168140 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_168140 prefixEnd_168140 := by exact prefixLift 168140
  have htrace : WordTrace (prefixWord ++ tailWord_168140) baseStart_168140 baseEnd_168140 := by
    simpa [prefixWord, tailWord_168140, baseEnd_168140] using wordTrace_append hprefix tailTrace_168140
  have hstable : (prefixWord ++ tailWord_168140).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168140).length < 2 ^ (prefixWord ++ tailWord_168140).sum := by decide
  have hdescent : baseEnd_168140 < baseStart_168140 := by decide
  rcases family_descends (prefixWord ++ tailWord_168140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168142 : List Nat := [4, 1, 1, 1, 4, 2, 6]
def baseStart_168142 : Nat := 118140960795 + 168142 * 2 ^ 59
def prefixEnd_168142 : Nat := 4983230072969 + 3 ^ 40 * 168142 * 2
def baseEnd_168142 : Nat := 17054353423878790587997

theorem tailTrace_168142 : CollatzResearch.WordTrace tailWord_168142 prefixEnd_168142 17054353423878790587997 := by
  unfold tailWord_168142
  simp only [CollatzResearch.WordTrace]
  refine ⟨766580319607215651560335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4088428371238483474988453 766580319607215651560335)
  ·
    refine ⟨1149870479410823477340503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 766580319607215651560335 1149870479410823477340503)
    ·
      refine ⟨1724805719116235216010755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1149870479410823477340503 1724805719116235216010755)
      ·
        refine ⟨2587208578674352824016133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1724805719116235216010755 2587208578674352824016133)
        ·
          refine ⟨485101608501441154503025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2587208578674352824016133 485101608501441154503025)
          ·
            refine ⟨363826206376080865877269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 485101608501441154503025 363826206376080865877269)
            ·
              refine ⟨17054353423878790587997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 363826206376080865877269 17054353423878790587997)
              ·
                rfl

theorem cell19_168142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 6].length) (baseStart_168142 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_168142 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_168142 prefixEnd_168142 := by exact prefixLift 168142
  have htrace : WordTrace (prefixWord ++ tailWord_168142) baseStart_168142 baseEnd_168142 := by
    simpa [prefixWord, tailWord_168142, baseEnd_168142] using wordTrace_append hprefix tailTrace_168142
  have hstable : (prefixWord ++ tailWord_168142).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168142).length < 2 ^ (prefixWord ++ tailWord_168142).sum := by decide
  have hdescent : baseEnd_168142 < baseStart_168142 := by decide
  rcases family_descends (prefixWord ++ tailWord_168142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168178 : List Nat := [3, 2, 1, 3, 2, 1, 4, 3]
def baseStart_168178 : Nat := 118140960795 + 168178 * 2 ^ 59
def prefixEnd_168178 : Nat := 4983230072969 + 3 ^ 40 * 168178 * 2
def baseEnd_168178 : Nat := 51174014525598954963893

theorem tailTrace_168178 : CollatzResearch.WordTrace tailWord_168178 prefixEnd_168178 51174014525598954963893 := by
  unfold tailWord_168178
  simp only [CollatzResearch.WordTrace]
  refine ⟨1533488896181825840198297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4089303723151535573862125 1533488896181825840198297)
  ·
    refine ⟨1150116672136369380148723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1533488896181825840198297 1150116672136369380148723)
    ·
      refine ⟨1725175008204554070223085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1150116672136369380148723 1725175008204554070223085)
      ·
        refine ⟨646940628076707776333657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1725175008204554070223085 646940628076707776333657)
        ·
          refine ⟨485205471057530832250243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 646940628076707776333657 485205471057530832250243)
          ·
            refine ⟨727808206586296248375365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 485205471057530832250243 727808206586296248375365)
            ·
              refine ⟨136464038734930546570381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 727808206586296248375365 136464038734930546570381)
              ·
                refine ⟨51174014525598954963893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 136464038734930546570381 51174014525598954963893)
                ·
                  rfl

theorem cell19_168178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 4, 3].length) (baseStart_168178 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_168178 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_168178 prefixEnd_168178 := by exact prefixLift 168178
  have htrace : WordTrace (prefixWord ++ tailWord_168178) baseStart_168178 baseEnd_168178 := by
    simpa [prefixWord, tailWord_168178, baseEnd_168178] using wordTrace_append hprefix tailTrace_168178
  have hstable : (prefixWord ++ tailWord_168178).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168178).length < 2 ^ (prefixWord ++ tailWord_168178).sum := by decide
  have hdescent : baseEnd_168178 < baseStart_168178 := by decide
  rcases family_descends (prefixWord ++ tailWord_168178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168201 : List Nat := [1, 2, 1, 1, 3, 4, 7]
def baseStart_168201 : Nat := 118140960795 + 168201 * 2 ^ 59
def prefixEnd_168201 : Nat := 4983230072969 + 3 ^ 40 * 168201 * 2
def baseEnd_168201 : Nat := 17060337692247238817573

theorem tailTrace_168201 : CollatzResearch.WordTrace tailWord_168201 prefixEnd_168201 17060337692247238817573 := by
  unfold tailWord_168201
  simp only [CollatzResearch.WordTrace]
  refine ⟨6134794463643978288880457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4089862975762652192586971 6134794463643978288880457)
  ·
    refine ⟨4601095847732983716660343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6134794463643978288880457 4601095847732983716660343)
    ·
      refine ⟨6901643771599475574990515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4601095847732983716660343 6901643771599475574990515)
      ·
        refine ⟨10352465657399213362485773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6901643771599475574990515 10352465657399213362485773)
        ·
          refine ⟨3882174621524705010932165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10352465657399213362485773 3882174621524705010932165)
          ·
            refine ⟨727907741535882189549781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3882174621524705010932165 727907741535882189549781)
            ·
              refine ⟨17060337692247238817573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 727907741535882189549781 17060337692247238817573)
              ·
                rfl

theorem cell19_168201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 7].length) (baseStart_168201 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_168201 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_168201 prefixEnd_168201 := by exact prefixLift 168201
  have htrace : WordTrace (prefixWord ++ tailWord_168201) baseStart_168201 baseEnd_168201 := by
    simpa [prefixWord, tailWord_168201, baseEnd_168201] using wordTrace_append hprefix tailTrace_168201
  have hstable : (prefixWord ++ tailWord_168201).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168201).length < 2 ^ (prefixWord ++ tailWord_168201).sum := by decide
  have hdescent : baseEnd_168201 < baseStart_168201 := by decide
  rcases family_descends (prefixWord ++ tailWord_168201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168239 : List Nat := [1, 1, 2, 1, 2, 1, 6, 5]
def baseStart_168239 : Nat := 118140960795 + 168239 * 2 ^ 59
def prefixEnd_168239 : Nat := 4983230072969 + 3 ^ 40 * 168239 * 2
def baseEnd_168239 : Nat := 51192575900368887608171

theorem tailTrace_168239 : CollatzResearch.WordTrace tailWord_168239 prefixEnd_168239 51192575900368887608171 := by
  unfold tailWord_168239
  simp only [CollatzResearch.WordTrace]
  refine ⟨6136180437506310778763771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4090786958337540519175847 6136180437506310778763771)
  ·
    refine ⟨9204270656259466168145657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6136180437506310778763771 9204270656259466168145657)
    ·
      refine ⟨6903202992194599626109243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9204270656259466168145657 6903202992194599626109243)
      ·
        refine ⟨10354804488291899439163865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6903202992194599626109243 10354804488291899439163865)
        ·
          refine ⟨7766103366218924579372899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10354804488291899439163865 7766103366218924579372899)
          ·
            refine ⟨11649155049328386869059349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7766103366218924579372899 11649155049328386869059349)
            ·
              refine ⟨546054142937268134487157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 11649155049328386869059349 546054142937268134487157)
              ·
                refine ⟨51192575900368887608171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 546054142937268134487157 51192575900368887608171)
                ·
                  rfl

theorem cell19_168239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 5].length) (baseStart_168239 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_168239 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_168239 prefixEnd_168239 := by exact prefixLift 168239
  have htrace : WordTrace (prefixWord ++ tailWord_168239) baseStart_168239 baseEnd_168239 := by
    simpa [prefixWord, tailWord_168239, baseEnd_168239] using wordTrace_append hprefix tailTrace_168239
  have hstable : (prefixWord ++ tailWord_168239).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168239).length < 2 ^ (prefixWord ++ tailWord_168239).sum := by decide
  have hdescent : baseEnd_168239 < baseStart_168239 := by decide
  rcases family_descends (prefixWord ++ tailWord_168239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168315 : List Nat := [1, 1, 1, 1, 1, 8, 6]
def baseStart_168315 : Nat := 118140960795 + 168315 * 2 ^ 59
def prefixEnd_168315 : Nat := 4983230072969 + 3 ^ 40 * 168315 * 2
def baseEnd_168315 : Nat := 17071900515874409973025

theorem tailTrace_168315 : CollatzResearch.WordTrace tailWord_168315 prefixEnd_168315 17071900515874409973025 := by
  unfold tailWord_168315
  simp only [CollatzResearch.WordTrace]
  refine ⟨6138952385230975758530399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4092634923487317172353599 6138952385230975758530399)
  ·
    refine ⟨9208428577846463637795599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6138952385230975758530399 9208428577846463637795599)
    ·
      refine ⟨13812642866769695456693399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9208428577846463637795599 13812642866769695456693399)
      ·
        refine ⟨20718964300154543185040099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13812642866769695456693399 20718964300154543185040099)
        ·
          refine ⟨31078446450231814777560149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20718964300154543185040099 31078446450231814777560149)
          ·
            refine ⟨364200544338654079424533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 31078446450231814777560149 364200544338654079424533)
            ·
              refine ⟨17071900515874409973025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 364200544338654079424533 17071900515874409973025)
              ·
                rfl

theorem cell19_168315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 6].length) (baseStart_168315 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_168315 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_168315 prefixEnd_168315 := by exact prefixLift 168315
  have htrace : WordTrace (prefixWord ++ tailWord_168315) baseStart_168315 baseEnd_168315 := by
    simpa [prefixWord, tailWord_168315, baseEnd_168315] using wordTrace_append hprefix tailTrace_168315
  have hstable : (prefixWord ++ tailWord_168315).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168315).length < 2 ^ (prefixWord ++ tailWord_168315).sum := by decide
  have hdescent : baseEnd_168315 < baseStart_168315 := by decide
  rcases family_descends (prefixWord ++ tailWord_168315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168391 : List Nat := [1, 1, 4, 1, 1, 4, 1, 6]
def baseStart_168391 : Nat := 118140960795 + 168391 * 2 ^ 59
def prefixEnd_168391 : Nat := 4983230072969 + 3 ^ 40 * 168391 * 2
def baseEnd_168391 : Nat := 51238827194877572229979

theorem tailTrace_168391 : CollatzResearch.WordTrace tailWord_168391 prefixEnd_168391 51238827194877572229979 := by
  unfold tailWord_168391
  simp only [CollatzResearch.WordTrace]
  refine ⟨6141724332955640738297027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4094482888637093825531351 6141724332955640738297027)
  ·
    refine ⟨9212586499433461107445541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6141724332955640738297027 9212586499433461107445541)
    ·
      refine ⟨1727359968643773957646039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9212586499433461107445541 1727359968643773957646039)
      ·
        refine ⟨2591039952965660936469059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1727359968643773957646039 2591039952965660936469059)
        ·
          refine ⟨3886559929448491404703589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2591039952965660936469059 3886559929448491404703589)
          ·
            refine ⟨728729986771592138381923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3886559929448491404703589 728729986771592138381923)
            ·
              refine ⟨1093094980157388207572885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 728729986771592138381923 1093094980157388207572885)
              ·
                refine ⟨51238827194877572229979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1093094980157388207572885 51238827194877572229979)
                ·
                  rfl

theorem cell19_168391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 6].length) (baseStart_168391 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_168391 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_168391 prefixEnd_168391 := by exact prefixLift 168391
  have htrace : WordTrace (prefixWord ++ tailWord_168391) baseStart_168391 baseEnd_168391 := by
    simpa [prefixWord, tailWord_168391, baseEnd_168391] using wordTrace_append hprefix tailTrace_168391
  have hstable : (prefixWord ++ tailWord_168391).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168391).length < 2 ^ (prefixWord ++ tailWord_168391).sum := by decide
  have hdescent : baseEnd_168391 < baseStart_168391 := by decide
  rcases family_descends (prefixWord ++ tailWord_168391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168410 : List Nat := [3, 1, 1, 2, 3, 1, 1, 7]
def baseStart_168410 : Nat := 118140960795 + 168410 * 2 ^ 59
def prefixEnd_168410 : Nat := 4983230072969 + 3 ^ 40 * 168410 * 2
def baseEnd_168410 : Nat := 51244608606691157807705

theorem tailTrace_168410 : CollatzResearch.WordTrace tailWord_168410 prefixEnd_168410 51244608606691157807705 := by
  unfold tailWord_168410
  simp only [CollatzResearch.WordTrace]
  refine ⟨1535604329971701745809671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4094944879924537988825789 1535604329971701745809671)
  ·
    refine ⟨2303406494957552618714507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1535604329971701745809671 2303406494957552618714507)
    ·
      refine ⟨3455109742436328928071761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2303406494957552618714507 3455109742436328928071761)
      ·
        refine ⟨2591332306827246696053821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3455109742436328928071761 2591332306827246696053821)
        ·
          refine ⟨971749615060217511020183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2591332306827246696053821 971749615060217511020183)
          ·
            refine ⟨1457624422590326266530275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 971749615060217511020183 1457624422590326266530275)
            ·
              refine ⟨2186436633885489399795413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1457624422590326266530275 2186436633885489399795413)
              ·
                refine ⟨51244608606691157807705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2186436633885489399795413 51244608606691157807705)
                ·
                  rfl

theorem cell19_168410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 7].length) (baseStart_168410 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_168410 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_168410 prefixEnd_168410 := by exact prefixLift 168410
  have htrace : WordTrace (prefixWord ++ tailWord_168410) baseStart_168410 baseEnd_168410 := by
    simpa [prefixWord, tailWord_168410, baseEnd_168410] using wordTrace_append hprefix tailTrace_168410
  have hstable : (prefixWord ++ tailWord_168410).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168410).length < 2 ^ (prefixWord ++ tailWord_168410).sum := by decide
  have hdescent : baseEnd_168410 < baseStart_168410 := by decide
  rcases family_descends (prefixWord ++ tailWord_168410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168505 : List Nat := [1, 2, 1, 5, 1, 1, 2, 6]
def baseStart_168505 : Nat := 118140960795 + 168505 * 2 ^ 59
def prefixEnd_168505 : Nat := 4983230072969 + 3 ^ 40 * 168505 * 2
def baseEnd_168505 : Nat := 51273515665759085696335

theorem tailTrace_168505 : CollatzResearch.WordTrace tailWord_168505 prefixEnd_168505 51273515665759085696335 := by
  unfold tailWord_168505
  simp only [CollatzResearch.WordTrace]
  refine ⟨6145882254542638207946969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4097254836361758805297979 6145882254542638207946969)
  ·
    refine ⟨4609411690906978655960227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6145882254542638207946969 4609411690906978655960227)
    ·
      refine ⟨6914117536360467983940341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4609411690906978655960227 6914117536360467983940341)
      ·
        refine ⟨648198519033793873494407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6914117536360467983940341 648198519033793873494407)
        ·
          refine ⟨972297778550690810241611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 648198519033793873494407 972297778550690810241611)
          ·
            refine ⟨1458446667826036215362417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 972297778550690810241611 1458446667826036215362417)
            ·
              refine ⟨1093835000869527161521813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1458446667826036215362417 1093835000869527161521813)
              ·
                refine ⟨51273515665759085696335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1093835000869527161521813 51273515665759085696335)
                ·
                  rfl

theorem cell19_168505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 6].length) (baseStart_168505 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_168505 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_168505 prefixEnd_168505 := by exact prefixLift 168505
  have htrace : WordTrace (prefixWord ++ tailWord_168505) baseStart_168505 baseEnd_168505 := by
    simpa [prefixWord, tailWord_168505, baseEnd_168505] using wordTrace_append hprefix tailTrace_168505
  have hstable : (prefixWord ++ tailWord_168505).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168505).length < 2 ^ (prefixWord ++ tailWord_168505).sum := by decide
  have hdescent : baseEnd_168505 < baseStart_168505 := by decide
  rcases family_descends (prefixWord ++ tailWord_168505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168518 : List Nat := [6, 1, 1, 1, 2, 1, 4, 3]
def baseStart_168518 : Nat := 118140960795 + 168518 * 2 ^ 59
def prefixEnd_168518 : Nat := 4983230072969 + 3 ^ 40 * 168518 * 2
def baseEnd_168518 : Nat := 51277471368578907407411

theorem tailTrace_168518 : CollatzResearch.WordTrace tailWord_168518 prefixEnd_168518 51277471368578907407411 := by
  unfold tailWord_168518
  simp only [CollatzResearch.WordTrace]
  refine ⟨192073637609235669630319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 4097570935663694285446805 192073637609235669630319)
  ·
    refine ⟨288110456413853504445479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192073637609235669630319 288110456413853504445479)
    ·
      refine ⟨432165684620780256668219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 288110456413853504445479 432165684620780256668219)
      ·
        refine ⟨648248526931170385002329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 432165684620780256668219 648248526931170385002329)
        ·
          refine ⟨486186395198377788751747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 648248526931170385002329 486186395198377788751747)
          ·
            refine ⟨729279592797566683127621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 486186395198377788751747 729279592797566683127621)
            ·
              refine ⟨136739923649543753086429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 729279592797566683127621 136739923649543753086429)
              ·
                refine ⟨51277471368578907407411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 136739923649543753086429 51277471368578907407411)
                ·
                  rfl

theorem cell19_168518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 4, 3].length) (baseStart_168518 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_168518 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_168518 prefixEnd_168518 := by exact prefixLift 168518
  have htrace : WordTrace (prefixWord ++ tailWord_168518) baseStart_168518 baseEnd_168518 := by
    simpa [prefixWord, tailWord_168518, baseEnd_168518] using wordTrace_append hprefix tailTrace_168518
  have hstable : (prefixWord ++ tailWord_168518).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168518).length < 2 ^ (prefixWord ++ tailWord_168518).sum := by decide
  have hdescent : baseEnd_168518 < baseStart_168518 := by decide
  rcases family_descends (prefixWord ++ tailWord_168518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168522 : List Nat := [3, 1, 2, 1, 1, 4, 4, 3]
def baseStart_168522 : Nat := 118140960795 + 168522 * 2 ^ 59
def prefixEnd_168522 : Nat := 4983230072969 + 3 ^ 40 * 168522 * 2
def baseEnd_168522 : Nat := 51278688507908083318511

theorem tailTrace_168522 : CollatzResearch.WordTrace tailWord_168522 prefixEnd_168522 51278688507908083318511 := by
  unfold tailWord_168522
  simp only [CollatzResearch.WordTrace]
  refine ⟨1536625573870262527828955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4097668196987366740877213 1536625573870262527828955)
  ·
    refine ⟨2304938360805393791743433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1536625573870262527828955 2304938360805393791743433)
    ·
      refine ⟨1728703770604045343807575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2304938360805393791743433 1728703770604045343807575)
      ·
        refine ⟨2593055655906068015711363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1728703770604045343807575 2593055655906068015711363)
        ·
          refine ⟨3889583483859102023567045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2593055655906068015711363 3889583483859102023567045)
          ·
            refine ⟨729296903223581629418821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3889583483859102023567045 729296903223581629418821)
            ·
              refine ⟨136743169354421555516029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 729296903223581629418821 136743169354421555516029)
              ·
                refine ⟨51278688507908083318511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 136743169354421555516029 51278688507908083318511)
                ·
                  rfl

theorem cell19_168522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 4, 3].length) (baseStart_168522 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_168522 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_168522 prefixEnd_168522 := by exact prefixLift 168522
  have htrace : WordTrace (prefixWord ++ tailWord_168522) baseStart_168522 baseEnd_168522 := by
    simpa [prefixWord, tailWord_168522, baseEnd_168522] using wordTrace_append hprefix tailTrace_168522
  have hstable : (prefixWord ++ tailWord_168522).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168522).length < 2 ^ (prefixWord ++ tailWord_168522).sum := by decide
  have hdescent : baseEnd_168522 < baseStart_168522 := by decide
  rcases family_descends (prefixWord ++ tailWord_168522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168524 : List Nat := [2, 2, 1, 3, 1, 2, 3, 5]
def baseStart_168524 : Nat := 118140960795 + 168524 * 2 ^ 59
def prefixEnd_168524 : Nat := 4983230072969 + 3 ^ 40 * 168524 * 2
def baseEnd_168524 : Nat := 51279297077572671274061

theorem tailTrace_168524 : CollatzResearch.WordTrace tailWord_168524 prefixEnd_168524 51279297077572671274061 := by
  unfold tailWord_168524
  simp only [CollatzResearch.WordTrace]
  refine ⟨3073287620736902226444313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4097716827649202968592417 3073287620736902226444313)
  ·
    refine ⟨2304965715552676669833235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3073287620736902226444313 2304965715552676669833235)
    ·
      refine ⟨3457448573329015004749853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2304965715552676669833235 3457448573329015004749853)
      ·
        refine ⟨1296543214998380626781195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3457448573329015004749853 1296543214998380626781195)
        ·
          refine ⟨1944814822497570940171793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1296543214998380626781195 1944814822497570940171793)
          ·
            refine ⟨1458611116873178205128845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1944814822497570940171793 1458611116873178205128845)
            ·
              refine ⟨546979168827441826923317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1458611116873178205128845 546979168827441826923317)
              ·
                refine ⟨51279297077572671274061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 546979168827441826923317 51279297077572671274061)
                ·
                  rfl

theorem cell19_168524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 5].length) (baseStart_168524 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_168524 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_168524 prefixEnd_168524 := by exact prefixLift 168524
  have htrace : WordTrace (prefixWord ++ tailWord_168524) baseStart_168524 baseEnd_168524 := by
    simpa [prefixWord, tailWord_168524, baseEnd_168524] using wordTrace_append hprefix tailTrace_168524
  have hstable : (prefixWord ++ tailWord_168524).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168524).length < 2 ^ (prefixWord ++ tailWord_168524).sum := by decide
  have hdescent : baseEnd_168524 < baseStart_168524 := by decide
  rcases family_descends (prefixWord ++ tailWord_168524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168560 : List Nat := [2, 1, 1, 1, 7, 1, 2, 4]
def baseStart_168560 : Nat := 118140960795 + 168560 * 2 ^ 59
def prefixEnd_168560 : Nat := 4983230072969 + 3 ^ 40 * 168560 * 2
def baseEnd_168560 : Nat := 51290251331535254473963

theorem tailTrace_168560 : CollatzResearch.WordTrace tailWord_168560 prefixEnd_168560 51290251331535254473963 := by
  unfold tailWord_168560
  simp only [CollatzResearch.WordTrace]
  refine ⟨3073944134671691300599567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4098592179562255067466089 3073944134671691300599567)
  ·
    refine ⟨4610916202007536950899351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3073944134671691300599567 4610916202007536950899351)
    ·
      refine ⟨6916374303011305426349027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4610916202007536950899351 6916374303011305426349027)
      ·
        refine ⟨10374561454516958139523541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6916374303011305426349027 10374561454516958139523541)
        ·
          refine ⟨243153784090241206395083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 10374561454516958139523541 243153784090241206395083)
          ·
            refine ⟨364730676135361809592625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 243153784090241206395083 364730676135361809592625)
            ·
              refine ⟨273548007101521357194469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 364730676135361809592625 273548007101521357194469)
              ·
                refine ⟨51290251331535254473963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 273548007101521357194469 51290251331535254473963)
                ·
                  rfl

theorem cell19_168560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 2, 4].length) (baseStart_168560 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_168560 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_168560 prefixEnd_168560 := by exact prefixLift 168560
  have htrace : WordTrace (prefixWord ++ tailWord_168560) baseStart_168560 baseEnd_168560 := by
    simpa [prefixWord, tailWord_168560, baseEnd_168560] using wordTrace_append hprefix tailTrace_168560
  have hstable : (prefixWord ++ tailWord_168560).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168560).length < 2 ^ (prefixWord ++ tailWord_168560).sum := by decide
  have hdescent : baseEnd_168560 < baseStart_168560 := by decide
  rcases family_descends (prefixWord ++ tailWord_168560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168581 : List Nat := [1, 3, 1, 1, 4, 2, 2, 5]
def baseStart_168581 : Nat := 118140960795 + 168581 * 2 ^ 59
def prefixEnd_168581 : Nat := 4983230072969 + 3 ^ 40 * 168581 * 2
def baseEnd_168581 : Nat := 51296641313013428007239

theorem tailTrace_168581 : CollatzResearch.WordTrace tailWord_168581 prefixEnd_168581 51296641313013428007239 := by
  unfold tailWord_168581
  simp only [CollatzResearch.WordTrace]
  refine ⟨6148654202267303187713597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4099102801511535458475731 6148654202267303187713597)
  ·
    refine ⟨2305745325850238695392599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6148654202267303187713597 2305745325850238695392599)
    ·
      refine ⟨3458617988775358043088899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2305745325850238695392599 3458617988775358043088899)
      ·
        refine ⟨5187926983163037064633349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3458617988775358043088899 5187926983163037064633349)
        ·
          refine ⟨972736309343069449618753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5187926983163037064633349 972736309343069449618753)
          ·
            refine ⟨729552232007302087214065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 972736309343069449618753 729552232007302087214065)
            ·
              refine ⟨547164174005476565410549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 729552232007302087214065 547164174005476565410549)
              ·
                refine ⟨51296641313013428007239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 547164174005476565410549 51296641313013428007239)
                ·
                  rfl

theorem cell19_168581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 5].length) (baseStart_168581 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_168581 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_168581 prefixEnd_168581 := by exact prefixLift 168581
  have htrace : WordTrace (prefixWord ++ tailWord_168581) baseStart_168581 baseEnd_168581 := by
    simpa [prefixWord, tailWord_168581, baseEnd_168581] using wordTrace_append hprefix tailTrace_168581
  have hstable : (prefixWord ++ tailWord_168581).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168581).length < 2 ^ (prefixWord ++ tailWord_168581).sum := by decide
  have hdescent : baseEnd_168581 < baseStart_168581 := by decide
  rcases family_descends (prefixWord ++ tailWord_168581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168636 : List Nat := [2, 2, 2, 3, 1, 1, 5, 3]
def baseStart_168636 : Nat := 118140960795 + 168636 * 2 ^ 59
def prefixEnd_168636 : Nat := 4983230072969 + 3 ^ 40 * 168636 * 2
def baseEnd_168636 : Nat := 51313376978789596784867

theorem tailTrace_168636 : CollatzResearch.WordTrace tailWord_168636 prefixEnd_168636 51313376978789596784867 := by
  unfold tailWord_168636
  simp only [CollatzResearch.WordTrace]
  refine ⟨3075330108534023790482881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4100440144712031720643841 3075330108534023790482881)
  ·
    refine ⟨2306497581400517842862161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3075330108534023790482881 2306497581400517842862161)
    ·
      refine ⟨1729873186050388382146621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2306497581400517842862161 1729873186050388382146621)
      ·
        refine ⟨648702444768895643304983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1729873186050388382146621 648702444768895643304983)
        ·
          refine ⟨973053667153343464957475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 648702444768895643304983 973053667153343464957475)
          ·
            refine ⟨1459580500730015197436213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 973053667153343464957475 1459580500730015197436213)
            ·
              refine ⟨136835671943438924759645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1459580500730015197436213 136835671943438924759645)
              ·
                refine ⟨51313376978789596784867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 136835671943438924759645 51313376978789596784867)
                ·
                  rfl

theorem cell19_168636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 5, 3].length) (baseStart_168636 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_168636 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_168636 prefixEnd_168636 := by exact prefixLift 168636
  have htrace : WordTrace (prefixWord ++ tailWord_168636) baseStart_168636 baseEnd_168636 := by
    simpa [prefixWord, tailWord_168636, baseEnd_168636] using wordTrace_append hprefix tailTrace_168636
  have hstable : (prefixWord ++ tailWord_168636).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168636).length < 2 ^ (prefixWord ++ tailWord_168636).sum := by decide
  have hdescent : baseEnd_168636 < baseStart_168636 := by decide
  rcases family_descends (prefixWord ++ tailWord_168636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168653 : List Nat := [1, 6, 2, 1, 2, 1, 6]
def baseStart_168653 : Nat := 118140960795 + 168653 * 2 ^ 59
def prefixEnd_168653 : Nat := 4983230072969 + 3 ^ 40 * 168653 * 2
def baseEnd_168653 : Nat := 17106183273646198135681

theorem tailTrace_168653 : CollatzResearch.WordTrace tailWord_168653 prefixEnd_168653 17106183273646198135681 := by
  unfold tailWord_168653
  simp only [CollatzResearch.WordTrace]
  refine ⟨6151280258006459484334613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4100853505337639656223075 6151280258006459484334613)
  ·
    refine ⟨288341262094052788328185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 6151280258006459484334613 288341262094052788328185)
    ·
      refine ⟨216255946570539591246139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 288341262094052788328185 216255946570539591246139)
      ·
        refine ⟨324383919855809386869209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 216255946570539591246139 324383919855809386869209)
        ·
          refine ⟨243287939891857040151907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 324383919855809386869209 243287939891857040151907)
          ·
            refine ⟨364931909837785560227861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 243287939891857040151907 364931909837785560227861)
            ·
              refine ⟨17106183273646198135681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 364931909837785560227861 17106183273646198135681)
              ·
                rfl

theorem cell19_168653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 6].length) (baseStart_168653 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_168653 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_168653 prefixEnd_168653 := by exact prefixLift 168653
  have htrace : WordTrace (prefixWord ++ tailWord_168653) baseStart_168653 baseEnd_168653 := by
    simpa [prefixWord, tailWord_168653, baseEnd_168653] using wordTrace_append hprefix tailTrace_168653
  have hstable : (prefixWord ++ tailWord_168653).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168653).length < 2 ^ (prefixWord ++ tailWord_168653).sum := by decide
  have hdescent : baseEnd_168653 < baseStart_168653 := by decide
  rcases family_descends (prefixWord ++ tailWord_168653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168750 : List Nat := [4, 1, 3, 2, 1, 1, 2, 5]
def baseStart_168750 : Nat := 118140960795 + 168750 * 2 ^ 59
def prefixEnd_168750 : Nat := 4983230072969 + 3 ^ 40 * 168750 * 2
def baseEnd_168750 : Nat := 51348065449671110251223

theorem tailTrace_168750 : CollatzResearch.WordTrace tailWord_168750 prefixEnd_168750 51348065449671110251223 := by
  unfold tailWord_168750
  simp only [CollatzResearch.WordTrace]
  refine ⟨769352267331880631326963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4103212092436696700410469 769352267331880631326963)
  ·
    refine ⟨1154028400997820946990445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 769352267331880631326963 1154028400997820946990445)
    ·
      refine ⟨432760650374182855121417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1154028400997820946990445 432760650374182855121417)
      ·
        refine ⟨324570487780637141341063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 432760650374182855121417 324570487780637141341063)
        ·
          refine ⟨486855731670955712011595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 324570487780637141341063 486855731670955712011595)
          ·
            refine ⟨730283597506433568017393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 486855731670955712011595 730283597506433568017393)
            ·
              refine ⟨547712698129825176013045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 730283597506433568017393 547712698129825176013045)
              ·
                refine ⟨51348065449671110251223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 547712698129825176013045 51348065449671110251223)
                ·
                  rfl

theorem cell19_168750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 5].length) (baseStart_168750 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_168750 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_168750 prefixEnd_168750 := by exact prefixLift 168750
  have htrace : WordTrace (prefixWord ++ tailWord_168750) baseStart_168750 baseEnd_168750 := by
    simpa [prefixWord, tailWord_168750, baseEnd_168750] using wordTrace_append hprefix tailTrace_168750
  have hstable : (prefixWord ++ tailWord_168750).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168750).length < 2 ^ (prefixWord ++ tailWord_168750).sum := by decide
  have hdescent : baseEnd_168750 < baseStart_168750 := by decide
  rcases family_descends (prefixWord ++ tailWord_168750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168769 : List Nat := [1, 2, 5, 3, 1, 7]
def baseStart_168769 : Nat := 118140960795 + 168769 * 2 ^ 59
def prefixEnd_168769 : Nat := 4983230072969 + 3 ^ 40 * 168769 * 2
def baseEnd_168769 : Nat := 5705982984609410647661

theorem tailTrace_168769 : CollatzResearch.WordTrace tailWord_168769 prefixEnd_168769 5705982984609410647661 := by
  unfold tailWord_168769
  simp only [CollatzResearch.WordTrace]
  refine ⟨6155511125586211295557361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4103674083724140863704907 6155511125586211295557361)
  ·
    refine ⟨4616633344189658471668021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6155511125586211295557361 4616633344189658471668021)
    ·
      refine ⟨432809376017780481718877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4616633344189658471668021 432809376017780481718877)
      ·
        refine ⟨162303516006667680644579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 432809376017780481718877 162303516006667680644579)
        ·
          refine ⟨243455274010001520966869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162303516006667680644579 243455274010001520966869)
          ·
            refine ⟨5705982984609410647661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 243455274010001520966869 5705982984609410647661)
            ·
              rfl

theorem cell19_168769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 7].length) (baseStart_168769 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_168769 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_168769 prefixEnd_168769 := by exact prefixLift 168769
  have htrace : WordTrace (prefixWord ++ tailWord_168769) baseStart_168769 baseEnd_168769 := by
    simpa [prefixWord, tailWord_168769, baseEnd_168769] using wordTrace_append hprefix tailTrace_168769
  have hstable : (prefixWord ++ tailWord_168769).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168769).length < 2 ^ (prefixWord ++ tailWord_168769).sum := by decide
  have hdescent : baseEnd_168769 < baseStart_168769 := by decide
  rcases family_descends (prefixWord ++ tailWord_168769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168807 : List Nat := [1, 1, 5, 1, 2, 3, 3, 3]
def baseStart_168807 : Nat := 118140960795 + 168807 * 2 ^ 59
def prefixEnd_168807 : Nat := 4983230072969 + 3 ^ 40 * 168807 * 2
def baseEnd_168807 : Nat := 51365409685111866984401

theorem tailTrace_168807 : CollatzResearch.WordTrace tailWord_168807 prefixEnd_168807 51365409685111866984401 := by
  unfold tailWord_168807
  simp only [CollatzResearch.WordTrace]
  refine ⟨6156897099448543785440675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4104598066299029190293783 6156897099448543785440675)
  ·
    refine ⟨9235345649172815678161013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6156897099448543785440675 9235345649172815678161013)
    ·
      refine ⟨865813654609951469827595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9235345649172815678161013 865813654609951469827595)
      ·
        refine ⟨1298720481914927204741393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 865813654609951469827595 1298720481914927204741393)
        ·
          refine ⟨974040361436195403556045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1298720481914927204741393 974040361436195403556045)
          ·
            refine ⟨365265135538573276333517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 974040361436195403556045 365265135538573276333517)
            ·
              refine ⟨136974425826964978625069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 365265135538573276333517 136974425826964978625069)
              ·
                refine ⟨51365409685111866984401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 136974425826964978625069 51365409685111866984401)
                ·
                  rfl

theorem cell19_168807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 3, 3].length) (baseStart_168807 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_168807 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_168807 prefixEnd_168807 := by exact prefixLift 168807
  have htrace : WordTrace (prefixWord ++ tailWord_168807) baseStart_168807 baseEnd_168807 := by
    simpa [prefixWord, tailWord_168807, baseEnd_168807] using wordTrace_append hprefix tailTrace_168807
  have hstable : (prefixWord ++ tailWord_168807).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168807).length < 2 ^ (prefixWord ++ tailWord_168807).sum := by decide
  have hdescent : baseEnd_168807 < baseStart_168807 := by decide
  rcases family_descends (prefixWord ++ tailWord_168807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168811 : List Nat := [1, 1, 1, 1, 2, 2, 4, 7]
def baseStart_168811 : Nat := 118140960795 + 168811 * 2 ^ 59
def prefixEnd_168811 : Nat := 4983230072969 + 3 ^ 40 * 168811 * 2
def baseEnd_168811 : Nat := 51366626824441042895501

theorem tailTrace_168811 : CollatzResearch.WordTrace tailWord_168811 prefixEnd_168811 51366626824441042895501 := by
  unfold tailWord_168811
  simp only [CollatzResearch.WordTrace]
  refine ⟨6157042991434052468586287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4104695327622701645724191 6157042991434052468586287)
  ·
    refine ⟨9235564487151078702879431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6157042991434052468586287 9235564487151078702879431)
    ·
      refine ⟨13853346730726618054319147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9235564487151078702879431 13853346730726618054319147)
      ·
        refine ⟨20780020096089927081478721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13853346730726618054319147 20780020096089927081478721)
        ·
          refine ⟨15585015072067445311109041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20780020096089927081478721 15585015072067445311109041)
          ·
            refine ⟨11688761304050583983331781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15585015072067445311109041 11688761304050583983331781)
            ·
              refine ⟨2191642744509484496874709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11688761304050583983331781 2191642744509484496874709)
              ·
                refine ⟨51366626824441042895501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2191642744509484496874709 51366626824441042895501)
                ·
                  rfl

theorem cell19_168811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 7].length) (baseStart_168811 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_168811 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_168811 prefixEnd_168811 := by exact prefixLift 168811
  have htrace : WordTrace (prefixWord ++ tailWord_168811) baseStart_168811 baseEnd_168811 := by
    simpa [prefixWord, tailWord_168811, baseEnd_168811] using wordTrace_append hprefix tailTrace_168811
  have hstable : (prefixWord ++ tailWord_168811).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168811).length < 2 ^ (prefixWord ++ tailWord_168811).sum := by decide
  have hdescent : baseEnd_168811 < baseStart_168811 := by decide
  rcases family_descends (prefixWord ++ tailWord_168811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168849 : List Nat := [1, 2, 2, 1, 1, 1, 3, 8]
def baseStart_168849 : Nat := 118140960795 + 168849 * 2 ^ 59
def prefixEnd_168849 : Nat := 4983230072969 + 3 ^ 40 * 168849 * 2
def baseEnd_168849 : Nat := 51378189648068214050953

theorem tailTrace_168849 : CollatzResearch.WordTrace tailWord_168849 prefixEnd_168849 51378189648068214050953 := by
  unfold tailWord_168849
  simp only [CollatzResearch.WordTrace]
  refine ⟨6158428965296384958469601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4105619310197589972313067 6158428965296384958469601)
  ·
    refine ⟨4618821723972288718852201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6158428965296384958469601 4618821723972288718852201)
    ·
      refine ⟨3464116292979216539139151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4618821723972288718852201 3464116292979216539139151)
      ·
        refine ⟨5196174439468824808708727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3464116292979216539139151 5196174439468824808708727)
        ·
          refine ⟨7794261659203237213063091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5196174439468824808708727 7794261659203237213063091)
          ·
            refine ⟨11691392488804855819594637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7794261659203237213063091 11691392488804855819594637)
            ·
              refine ⟨4384272183301820932347989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11691392488804855819594637 4384272183301820932347989)
              ·
                refine ⟨51378189648068214050953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4384272183301820932347989 51378189648068214050953)
                ·
                  rfl

theorem cell19_168849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 8].length) (baseStart_168849 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_168849 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_168849 prefixEnd_168849 := by exact prefixLift 168849
  have htrace : WordTrace (prefixWord ++ tailWord_168849) baseStart_168849 baseEnd_168849 := by
    simpa [prefixWord, tailWord_168849, baseEnd_168849] using wordTrace_append hprefix tailTrace_168849
  have hstable : (prefixWord ++ tailWord_168849).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168849).length < 2 ^ (prefixWord ++ tailWord_168849).sum := by decide
  have hdescent : baseEnd_168849 < baseStart_168849 := by decide
  rcases family_descends (prefixWord ++ tailWord_168849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168860 : List Nat := [2, 2, 3, 3, 3, 1, 2, 3]
def baseStart_168860 : Nat := 118140960795 + 168860 * 2 ^ 59
def prefixEnd_168860 : Nat := 4983230072969 + 3 ^ 40 * 168860 * 2
def baseEnd_168860 : Nat := 51381536781223447806479

theorem tailTrace_168860 : CollatzResearch.WordTrace tailWord_168860 prefixEnd_168860 51381536781223447806479 := by
  unfold tailWord_168860
  simp only [CollatzResearch.WordTrace]
  refine ⟨3079415084128266918560017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4105886778837689224746689 3079415084128266918560017)
  ·
    refine ⟨2309561313096200188920013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3079415084128266918560017 2309561313096200188920013)
    ·
      refine ⟨866085492411075070845005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2309561313096200188920013 866085492411075070845005)
      ·
        refine ⟨324782059654153151566877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 866085492411075070845005 324782059654153151566877)
        ·
          refine ⟨121793272370307431837579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 324782059654153151566877 121793272370307431837579)
          ·
            refine ⟨182689908555461147756369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121793272370307431837579 182689908555461147756369)
            ·
              refine ⟨137017431416595860817277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 182689908555461147756369 137017431416595860817277)
              ·
                refine ⟨51381536781223447806479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 137017431416595860817277 51381536781223447806479)
                ·
                  rfl

theorem cell19_168860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 2, 3].length) (baseStart_168860 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_168860 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_168860 prefixEnd_168860 := by exact prefixLift 168860
  have htrace : WordTrace (prefixWord ++ tailWord_168860) baseStart_168860 baseEnd_168860 := by
    simpa [prefixWord, tailWord_168860, baseEnd_168860] using wordTrace_append hprefix tailTrace_168860
  have hstable : (prefixWord ++ tailWord_168860).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168860).length < 2 ^ (prefixWord ++ tailWord_168860).sum := by decide
  have hdescent : baseEnd_168860 < baseStart_168860 := by decide
  rcases family_descends (prefixWord ++ tailWord_168860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168887 : List Nat := [1, 1, 3, 1, 3, 1, 9]
def baseStart_168887 : Nat := 118140960795 + 168887 * 2 ^ 59
def prefixEnd_168887 : Nat := 4983230072969 + 3 ^ 40 * 168887 * 2
def baseEnd_168887 : Nat := 17129917490565128402135

theorem tailTrace_168887 : CollatzResearch.WordTrace tailWord_168887 prefixEnd_168887 17129917490565128402135 := by
  unfold tailWord_168887
  simp only [CollatzResearch.WordTrace]
  refine ⟨6159814939158717448352915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4106543292772478298901943 6159814939158717448352915)
  ·
    refine ⟨9239722408738076172529373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6159814939158717448352915 9239722408738076172529373)
    ·
      refine ⟨3464895903276778564698515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9239722408738076172529373 3464895903276778564698515)
      ·
        refine ⟨5197343854915167847047773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3464895903276778564698515 5197343854915167847047773)
        ·
          refine ⟨1949003945593187942642915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5197343854915167847047773 1949003945593187942642915)
          ·
            refine ⟨2923505918389781913964373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1949003945593187942642915 2923505918389781913964373)
            ·
              refine ⟨17129917490565128402135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2923505918389781913964373 17129917490565128402135)
              ·
                rfl

theorem cell19_168887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 9].length) (baseStart_168887 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_168887 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_168887 prefixEnd_168887 := by exact prefixLift 168887
  have htrace : WordTrace (prefixWord ++ tailWord_168887) baseStart_168887 baseEnd_168887 := by
    simpa [prefixWord, tailWord_168887, baseEnd_168887] using wordTrace_append hprefix tailTrace_168887
  have hstable : (prefixWord ++ tailWord_168887).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168887).length < 2 ^ (prefixWord ++ tailWord_168887).sum := by decide
  have hdescent : baseEnd_168887 < baseStart_168887 := by decide
  rcases family_descends (prefixWord ++ tailWord_168887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168900 : List Nat := [2, 3, 3, 3, 1, 1, 2, 4]
def baseStart_168900 : Nat := 118140960795 + 168900 * 2 ^ 59
def prefixEnd_168900 : Nat := 4983230072969 + 3 ^ 40 * 168900 * 2
def baseEnd_168900 : Nat := 51393708174515206917481

theorem tailTrace_168900 : CollatzResearch.WordTrace tailWord_168900 prefixEnd_168900 51393708174515206917481 := by
  unfold tailWord_168900
  simp only [CollatzResearch.WordTrace]
  refine ⟨3080144544055810334288077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4106859392074413779050769 3080144544055810334288077)
  ·
    refine ⟨1155054204020928875358029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3080144544055810334288077 1155054204020928875358029)
    ·
      refine ⟨433145326507848328259261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1155054204020928875358029 433145326507848328259261)
      ·
        refine ⟨162429497440443123097223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 433145326507848328259261 162429497440443123097223)
        ·
          refine ⟨243644246160664684645835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162429497440443123097223 243644246160664684645835)
          ·
            refine ⟨365466369240997026968753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 243644246160664684645835 365466369240997026968753)
            ·
              refine ⟨274099776930747770226565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 365466369240997026968753 274099776930747770226565)
              ·
                refine ⟨51393708174515206917481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 274099776930747770226565 51393708174515206917481)
                ·
                  rfl

theorem cell19_168900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 2, 4].length) (baseStart_168900 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_168900 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_168900 prefixEnd_168900 := by exact prefixLift 168900
  have htrace : WordTrace (prefixWord ++ tailWord_168900) baseStart_168900 baseEnd_168900 := by
    simpa [prefixWord, tailWord_168900, baseEnd_168900] using wordTrace_append hprefix tailTrace_168900
  have hstable : (prefixWord ++ tailWord_168900).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168900).length < 2 ^ (prefixWord ++ tailWord_168900).sum := by decide
  have hdescent : baseEnd_168900 < baseStart_168900 := by decide
  rcases family_descends (prefixWord ++ tailWord_168900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168942 : List Nat := [4, 1, 2, 1, 4, 7]
def baseStart_168942 : Nat := 118140960795 + 168942 * 2 ^ 59
def prefixEnd_168942 : Nat := 4983230072969 + 3 ^ 40 * 168942 * 2
def baseEnd_168942 : Nat := 5711832015274617109337

theorem tailTrace_168942 : CollatzResearch.WordTrace tailWord_168942 prefixEnd_168942 5711832015274617109337 := by
  unfold tailWord_168942
  simp only [CollatzResearch.WordTrace]
  refine ⟨770227619244932730200635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4107880635972974561070053 770227619244932730200635)
  ·
    refine ⟨1155341428867399095300953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 770227619244932730200635 1155341428867399095300953)
    ·
      refine ⟨866506071650549321475715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1155341428867399095300953 866506071650549321475715)
      ·
        refine ⟨1299759107475823982213573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 866506071650549321475715 1299759107475823982213573)
        ·
          refine ⟨243704832651716996665045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1299759107475823982213573 243704832651716996665045)
          ·
            refine ⟨5711832015274617109337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 243704832651716996665045 5711832015274617109337)
            ·
              rfl

theorem cell19_168942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 7].length) (baseStart_168942 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_168942 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_168942 prefixEnd_168942 := by exact prefixLift 168942
  have htrace : WordTrace (prefixWord ++ tailWord_168942) baseStart_168942 baseEnd_168942 := by
    simpa [prefixWord, tailWord_168942, baseEnd_168942] using wordTrace_append hprefix tailTrace_168942
  have hstable : (prefixWord ++ tailWord_168942).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168942).length < 2 ^ (prefixWord ++ tailWord_168942).sum := by decide
  have hdescent : baseEnd_168942 < baseStart_168942 := by decide
  rcases family_descends (prefixWord ++ tailWord_168942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168961 : List Nat := [1, 2, 4, 1, 2, 2, 3, 4]
def baseStart_168961 : Nat := 118140960795 + 168961 * 2 ^ 59
def prefixEnd_168961 : Nat := 4983230072969 + 3 ^ 40 * 168961 * 2
def baseEnd_168961 : Nat := 51412269549285139561759

theorem tailTrace_168961 : CollatzResearch.WordTrace tailWord_168961 prefixEnd_168961 51412269549285139561759 := by
  unfold tailWord_168961
  simp only [CollatzResearch.WordTrace]
  refine ⟨6162513940890628086546737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4108342627260418724364491 6162513940890628086546737)
  ·
    refine ⟨4621885455667971064910053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6162513940890628086546737 4621885455667971064910053)
    ·
      refine ⟨866603522937744574670635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4621885455667971064910053 866603522937744574670635)
      ·
        refine ⟨1299905284406616862005953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 866603522937744574670635 1299905284406616862005953)
        ·
          refine ⟨974928963304962646504465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1299905284406616862005953 974928963304962646504465)
          ·
            refine ⟨731196722478721984878349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 974928963304962646504465 731196722478721984878349)
            ·
              refine ⟨274198770929520744329381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 731196722478721984878349 274198770929520744329381)
              ·
                refine ⟨51412269549285139561759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 274198770929520744329381 51412269549285139561759)
                ·
                  rfl

theorem cell19_168961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 3, 4].length) (baseStart_168961 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_168961 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_168961 prefixEnd_168961 := by exact prefixLift 168961
  have htrace : WordTrace (prefixWord ++ tailWord_168961) baseStart_168961 baseEnd_168961 := by
    simpa [prefixWord, tailWord_168961, baseEnd_168961] using wordTrace_append hprefix tailTrace_168961
  have hstable : (prefixWord ++ tailWord_168961).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168961).length < 2 ^ (prefixWord ++ tailWord_168961).sum := by decide
  have hdescent : baseEnd_168961 < baseStart_168961 := by decide
  rcases family_descends (prefixWord ++ tailWord_168961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169130 : List Nat := [3, 1, 5, 1, 1, 1, 3, 4]
def baseStart_169130 : Nat := 118140960795 + 169130 * 2 ^ 59
def prefixEnd_169130 : Nat := 4983230072969 + 3 ^ 40 * 169130 * 2
def baseEnd_169130 : Nat := 51463693685942821805743

theorem tailTrace_169130 : CollatzResearch.WordTrace tailWord_169130 prefixEnd_169130 51463693685942821805743 := by
  unfold tailWord_169130
  simp only [CollatzResearch.WordTrace]
  refine ⟨1542169469319592487362211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4112451918185579966299229 1542169469319592487362211)
  ·
    refine ⟨2313254203979388731043317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1542169469319592487362211 2313254203979388731043317)
    ·
      refine ⟨216867581623067693535311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2313254203979388731043317 216867581623067693535311)
      ·
        refine ⟨325301372434601540302967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 216867581623067693535311 325301372434601540302967)
        ·
          refine ⟨487952058651902310454451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 325301372434601540302967 487952058651902310454451)
          ·
            refine ⟨731928087977853465681677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 487952058651902310454451 731928087977853465681677)
            ·
              refine ⟨274473032991695049630629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 731928087977853465681677 274473032991695049630629)
              ·
                refine ⟨51463693685942821805743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 274473032991695049630629 51463693685942821805743)
                ·
                  rfl

theorem cell19_169130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 3, 4].length) (baseStart_169130 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_169130 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_169130 prefixEnd_169130 := by exact prefixLift 169130
  have htrace : WordTrace (prefixWord ++ tailWord_169130) baseStart_169130 baseEnd_169130 := by
    simpa [prefixWord, tailWord_169130, baseEnd_169130] using wordTrace_append hprefix tailTrace_169130
  have hstable : (prefixWord ++ tailWord_169130).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169130).length < 2 ^ (prefixWord ++ tailWord_169130).sum := by decide
  have hdescent : baseEnd_169130 < baseStart_169130 := by decide
  rcases family_descends (prefixWord ++ tailWord_169130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169210 : List Nat := [3, 1, 1, 1, 1, 4, 3, 5]
def baseStart_169210 : Nat := 118140960795 + 169210 * 2 ^ 59
def prefixEnd_169210 : Nat := 4983230072969 + 3 ^ 40 * 169210 * 2
def baseEnd_169210 : Nat := 51488036472526340027747

theorem tailTrace_169210 : CollatzResearch.WordTrace tailWord_169210 prefixEnd_169210 51488036472526340027747 := by
  unfold tailWord_169210
  simp only [CollatzResearch.WordTrace]
  refine ⟨1542898929247135903090271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4114397144659029074907389 1542898929247135903090271)
  ·
    refine ⟨2314348393870703854635407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1542898929247135903090271 2314348393870703854635407)
    ·
      refine ⟨3471522590806055781953111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2314348393870703854635407 3471522590806055781953111)
      ·
        refine ⟨5207283886209083672929667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3471522590806055781953111 5207283886209083672929667)
        ·
          refine ⟨7810925829313625509394501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5207283886209083672929667 7810925829313625509394501)
          ·
            refine ⟨1464548592996304783011469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7810925829313625509394501 1464548592996304783011469)
            ·
              refine ⟨549205722373614293629301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1464548592996304783011469 549205722373614293629301)
              ·
                refine ⟨51488036472526340027747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 549205722373614293629301 51488036472526340027747)
                ·
                  rfl

theorem cell19_169210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 5].length) (baseStart_169210 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_169210 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_169210 prefixEnd_169210 := by exact prefixLift 169210
  have htrace : WordTrace (prefixWord ++ tailWord_169210) baseStart_169210 baseEnd_169210 := by
    simpa [prefixWord, tailWord_169210, baseEnd_169210] using wordTrace_append hprefix tailTrace_169210
  have hstable : (prefixWord ++ tailWord_169210).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169210).length < 2 ^ (prefixWord ++ tailWord_169210).sum := by decide
  have hdescent : baseEnd_169210 < baseStart_169210 := by decide
  rcases family_descends (prefixWord ++ tailWord_169210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169267 : List Nat := [1, 1, 1, 2, 5, 2, 2, 5]
def baseStart_169267 : Nat := 118140960795 + 169267 * 2 ^ 59
def prefixEnd_169267 : Nat := 4983230072969 + 3 ^ 40 * 169267 * 2
def baseEnd_169267 : Nat := 51505380707967096760925

theorem tailTrace_169267 : CollatzResearch.WordTrace tailWord_169267 prefixEnd_169267 51505380707967096760925 := by
  unfold tailWord_169267
  simp only [CollatzResearch.WordTrace]
  refine ⟨6173674677782042347186055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4115783118521361564790703 6173674677782042347186055)
  ·
    refine ⟨9260512016673063520779083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6173674677782042347186055 9260512016673063520779083)
    ·
      refine ⟨13890768025009595281168625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9260512016673063520779083 13890768025009595281168625)
      ·
        refine ⟨10418076018757196460876469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13890768025009595281168625 10418076018757196460876469)
        ·
          refine ⟨976694626758487168207169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10418076018757196460876469 976694626758487168207169)
          ·
            refine ⟨732520970068865376155377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 976694626758487168207169 732520970068865376155377)
            ·
              refine ⟨549390727551649032116533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 732520970068865376155377 549390727551649032116533)
              ·
                refine ⟨51505380707967096760925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 549390727551649032116533 51505380707967096760925)
                ·
                  rfl

theorem cell19_169267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 5].length) (baseStart_169267 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_169267 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_169267 prefixEnd_169267 := by exact prefixLift 169267
  have htrace : WordTrace (prefixWord ++ tailWord_169267) baseStart_169267 baseEnd_169267 := by
    simpa [prefixWord, tailWord_169267, baseEnd_169267] using wordTrace_append hprefix tailTrace_169267
  have hstable : (prefixWord ++ tailWord_169267).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169267).length < 2 ^ (prefixWord ++ tailWord_169267).sum := by decide
  have hdescent : baseEnd_169267 < baseStart_169267 := by decide
  rcases family_descends (prefixWord ++ tailWord_169267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169284 : List Nat := [2, 3, 4, 1, 1, 8]
def baseStart_169284 : Nat := 118140960795 + 169284 * 2 ^ 59
def prefixEnd_169284 : Nat := 4983230072969 + 3 ^ 40 * 169284 * 2
def baseEnd_169284 : Nat := 5723394838901788264789

theorem tailTrace_169284 : CollatzResearch.WordTrace tailWord_169284 prefixEnd_169284 5723394838901788264789 := by
  unfold tailWord_169284
  simp only [CollatzResearch.WordTrace]
  refine ⟨3087147359360227125277453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4116196479146969500369937 3087147359360227125277453)
  ·
    refine ⟨1157680259760085171979045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3087147359360227125277453 1157680259760085171979045)
    ·
      refine ⟨217065048705015969746071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1157680259760085171979045 217065048705015969746071)
      ·
        refine ⟨325597573057523954619107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217065048705015969746071 325597573057523954619107)
        ·
          refine ⟨488396359586285931928661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 325597573057523954619107 488396359586285931928661)
          ·
            refine ⟨5723394838901788264789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 488396359586285931928661 5723394838901788264789)
            ·
              rfl

theorem cell19_169284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 8].length) (baseStart_169284 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_169284 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_169284 prefixEnd_169284 := by exact prefixLift 169284
  have htrace : WordTrace (prefixWord ++ tailWord_169284) baseStart_169284 baseEnd_169284 := by
    simpa [prefixWord, tailWord_169284, baseEnd_169284] using wordTrace_append hprefix tailTrace_169284
  have hstable : (prefixWord ++ tailWord_169284).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169284).length < 2 ^ (prefixWord ++ tailWord_169284).sum := by decide
  have hdescent : baseEnd_169284 < baseStart_169284 := by decide
  rcases family_descends (prefixWord ++ tailWord_169284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169303 : List Nat := [1, 1, 3, 2, 3, 4, 1, 4]
def baseStart_169303 : Nat := 118140960795 + 169303 * 2 ^ 59
def prefixEnd_169303 : Nat := 4983230072969 + 3 ^ 40 * 169303 * 2
def baseEnd_169303 : Nat := 51516334961929679960827

theorem tailTrace_169303 : CollatzResearch.WordTrace tailWord_169303 prefixEnd_169303 51516334961929679960827 := by
  unfold tailWord_169303
  simp only [CollatzResearch.WordTrace]
  refine ⟨6174987705651620495496563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4116658470434413663664375 6174987705651620495496563)
  ·
    refine ⟨9262481558477430743244845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6174987705651620495496563 9262481558477430743244845)
    ·
      refine ⟨3473430584429036528716817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9262481558477430743244845 3473430584429036528716817)
      ·
        refine ⟨2605072938321777396537613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3473430584429036528716817 2605072938321777396537613)
        ·
          refine ⟨976902351870666523701605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2605072938321777396537613 976902351870666523701605)
          ·
            refine ⟨183169190975749973194051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 976902351870666523701605 183169190975749973194051)
            ·
              refine ⟨274753786463624959791077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 183169190975749973194051 274753786463624959791077)
              ·
                refine ⟨51516334961929679960827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 274753786463624959791077 51516334961929679960827)
                ·
                  rfl

theorem cell19_169303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 1, 4].length) (baseStart_169303 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_169303 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_169303 prefixEnd_169303 := by exact prefixLift 169303
  have htrace : WordTrace (prefixWord ++ tailWord_169303) baseStart_169303 baseEnd_169303 := by
    simpa [prefixWord, tailWord_169303, baseEnd_169303] using wordTrace_append hprefix tailTrace_169303
  have hstable : (prefixWord ++ tailWord_169303).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169303).length < 2 ^ (prefixWord ++ tailWord_169303).sum := by decide
  have hdescent : baseEnd_169303 < baseStart_169303 := by decide
  rcases family_descends (prefixWord ++ tailWord_169303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169305 : List Nat := [1, 2, 1, 2, 2, 2, 5, 4]
def baseStart_169305 : Nat := 118140960795 + 169305 * 2 ^ 59
def prefixEnd_169305 : Nat := 4983230072969 + 3 ^ 40 * 169305 * 2
def baseEnd_169305 : Nat := 51516943531594267916377

theorem tailTrace_169305 : CollatzResearch.WordTrace tailWord_169305 prefixEnd_169305 51516943531594267916377 := by
  unfold tailWord_169305
  simp only [CollatzResearch.WordTrace]
  refine ⟨6175060651644374837069369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4116707101096249891379579 6175060651644374837069369)
  ·
    refine ⟨4631295488733281127802027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6175060651644374837069369 4631295488733281127802027)
    ·
      refine ⟨6946943233099921691703041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4631295488733281127802027 6946943233099921691703041)
      ·
        refine ⟨5210207424824941268777281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6946943233099921691703041 5210207424824941268777281)
        ·
          refine ⟨3907655568618705951582961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5210207424824941268777281 3907655568618705951582961)
          ·
            refine ⟨2930741676464029463687221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3907655568618705951582961 2930741676464029463687221)
            ·
              refine ⟨274757032168502762220677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2930741676464029463687221 274757032168502762220677)
              ·
                refine ⟨51516943531594267916377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 274757032168502762220677 51516943531594267916377)
                ·
                  rfl

theorem cell19_169305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 5, 4].length) (baseStart_169305 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_169305 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_169305 prefixEnd_169305 := by exact prefixLift 169305
  have htrace : WordTrace (prefixWord ++ tailWord_169305) baseStart_169305 baseEnd_169305 := by
    simpa [prefixWord, tailWord_169305, baseEnd_169305] using wordTrace_append hprefix tailTrace_169305
  have hstable : (prefixWord ++ tailWord_169305).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169305).length < 2 ^ (prefixWord ++ tailWord_169305).sum := by decide
  have hdescent : baseEnd_169305 < baseStart_169305 := by decide
  rcases family_descends (prefixWord ++ tailWord_169305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169320 : List Nat := [2, 1, 4, 2, 3, 1, 3, 3]
def baseStart_169320 : Nat := 118140960795 + 169320 * 2 ^ 59
def prefixEnd_169320 : Nat := 4983230072969 + 3 ^ 40 * 169320 * 2
def baseEnd_169320 : Nat := 51521507804078677583003

theorem tailTrace_169320 : CollatzResearch.WordTrace tailWord_169320 prefixEnd_169320 51521507804078677583003 := by
  unfold tailWord_169320
  simp only [CollatzResearch.WordTrace]
  refine ⟨3087803873295016199432707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4117071831060021599243609 3087803873295016199432707)
  ·
    refine ⟨4631705809942524299149061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3087803873295016199432707 4631705809942524299149061)
    ·
      refine ⟨868444839364223306090449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4631705809942524299149061 868444839364223306090449)
      ·
        refine ⟨651333629523167479567837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 868444839364223306090449 651333629523167479567837)
        ·
          refine ⟨244250111071187804837939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 651333629523167479567837 244250111071187804837939)
          ·
            refine ⟨366375166606781707256909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 244250111071187804837939 366375166606781707256909)
            ·
              refine ⟨137390687477543140221341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 366375166606781707256909 137390687477543140221341)
              ·
                refine ⟨51521507804078677583003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 137390687477543140221341 51521507804078677583003)
                ·
                  rfl

theorem cell19_169320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 3, 3].length) (baseStart_169320 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_169320 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_169320 prefixEnd_169320 := by exact prefixLift 169320
  have htrace : WordTrace (prefixWord ++ tailWord_169320) baseStart_169320 baseEnd_169320 := by
    simpa [prefixWord, tailWord_169320, baseEnd_169320] using wordTrace_append hprefix tailTrace_169320
  have hstable : (prefixWord ++ tailWord_169320).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169320).length < 2 ^ (prefixWord ++ tailWord_169320).sum := by decide
  have hdescent : baseEnd_169320 < baseStart_169320 := by decide
  rcases family_descends (prefixWord ++ tailWord_169320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169470 : List Nat := [4, 2, 2, 3, 1, 2, 1, 4]
def baseStart_169470 : Nat := 118140960795 + 169470 * 2 ^ 59
def prefixEnd_169470 : Nat := 4983230072969 + 3 ^ 40 * 169470 * 2
def baseEnd_169470 : Nat := 51567150528922774249261

theorem tailTrace_169470 : CollatzResearch.WordTrace tailWord_169470 prefixEnd_169470 51567150528922774249261 := by
  unfold tailWord_169470
  simp only [CollatzResearch.WordTrace]
  refine ⟨772634837005826002103233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4120719130697738677883909 772634837005826002103233)
  ·
    refine ⟨579476127754369501577425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 772634837005826002103233 579476127754369501577425)
    ·
      refine ⟨434607095815777126183069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 579476127754369501577425 434607095815777126183069)
      ·
        refine ⟨162977660930916422318651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 434607095815777126183069 162977660930916422318651)
        ·
          refine ⟨244466491396374633477977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162977660930916422318651 244466491396374633477977)
          ·
            refine ⟨183349868547280975108483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 244466491396374633477977 183349868547280975108483)
            ·
              refine ⟨275024802820921462662725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 183349868547280975108483 275024802820921462662725)
              ·
                refine ⟨51567150528922774249261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 275024802820921462662725 51567150528922774249261)
                ·
                  rfl

theorem cell19_169470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 1, 4].length) (baseStart_169470 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_169470 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_169470 prefixEnd_169470 := by exact prefixLift 169470
  have htrace : WordTrace (prefixWord ++ tailWord_169470) baseStart_169470 baseEnd_169470 := by
    simpa [prefixWord, tailWord_169470, baseEnd_169470] using wordTrace_append hprefix tailTrace_169470
  have hstable : (prefixWord ++ tailWord_169470).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169470).length < 2 ^ (prefixWord ++ tailWord_169470).sum := by decide
  have hdescent : baseEnd_169470 < baseStart_169470 := by decide
  rcases family_descends (prefixWord ++ tailWord_169470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169493 : List Nat := [1, 3, 2, 1, 3, 3, 3, 3]
def baseStart_169493 : Nat := 118140960795 + 169493 * 2 ^ 59
def prefixEnd_169493 : Nat := 4983230072969 + 3 ^ 40 * 169493 * 2
def baseEnd_169493 : Nat := 51574149080065535738087

theorem tailTrace_169493 : CollatzResearch.WordTrace tailWord_169493 prefixEnd_169493 51574149080065535738087 := by
  unfold tailWord_169493
  simp only [CollatzResearch.WordTrace]
  refine ⟨6181917574963282944913133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4121278383308855296608755 6181917574963282944913133)
  ·
    refine ⟨2318219090611231104342425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6181917574963282944913133 2318219090611231104342425)
    ·
      refine ⟨1738664317958423328256819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2318219090611231104342425 1738664317958423328256819)
      ·
        refine ⟨2607996476937634992385229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1738664317958423328256819 2607996476937634992385229)
        ·
          refine ⟨977998678851613122144461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2607996476937634992385229 977998678851613122144461)
          ·
            refine ⟨366749504569354920804173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 977998678851613122144461 366749504569354920804173)
            ·
              refine ⟨137531064213508095301565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 366749504569354920804173 137531064213508095301565)
              ·
                refine ⟨51574149080065535738087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 137531064213508095301565 51574149080065535738087)
                ·
                  rfl

theorem cell19_169493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 3, 3].length) (baseStart_169493 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_169493 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_169493 prefixEnd_169493 := by exact prefixLift 169493
  have htrace : WordTrace (prefixWord ++ tailWord_169493) baseStart_169493 baseEnd_169493 := by
    simpa [prefixWord, tailWord_169493, baseEnd_169493] using wordTrace_append hprefix tailTrace_169493
  have hstable : (prefixWord ++ tailWord_169493).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169493).length < 2 ^ (prefixWord ++ tailWord_169493).sum := by decide
  have hdescent : baseEnd_169493 < baseStart_169493 := by decide
  rcases family_descends (prefixWord ++ tailWord_169493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169512 : List Nat := [2, 1, 5, 2, 2, 1, 6]
def baseStart_169512 : Nat := 118140960795 + 169512 * 2 ^ 59
def prefixEnd_169512 : Nat := 4983230072969 + 3 ^ 40 * 169512 * 2
def baseEnd_169512 : Nat := 17193310163959707105271

theorem tailTrace_169512 : CollatzResearch.WordTrace tailWord_169512 prefixEnd_169512 17193310163959707105271 := by
  unfold tailWord_169512
  simp only [CollatzResearch.WordTrace]
  refine ⟨3091305280947224594927395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4121740374596299459903193 3091305280947224594927395)
  ·
    refine ⟨4636957921420836892391093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3091305280947224594927395 4636957921420836892391093)
    ·
      refine ⟨434714805133203458661665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4636957921420836892391093 434714805133203458661665)
      ·
        refine ⟨326036103849902593996249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 434714805133203458661665 326036103849902593996249)
        ·
          refine ⟨244527077887426945497187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 326036103849902593996249 244527077887426945497187)
          ·
            refine ⟨366790616831140418245781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 244527077887426945497187 366790616831140418245781)
            ·
              refine ⟨17193310163959707105271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 366790616831140418245781 17193310163959707105271)
              ·
                rfl

theorem cell19_169512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 6].length) (baseStart_169512 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_169512 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_169512 prefixEnd_169512 := by exact prefixLift 169512
  have htrace : WordTrace (prefixWord ++ tailWord_169512) baseStart_169512 baseEnd_169512 := by
    simpa [prefixWord, tailWord_169512, baseEnd_169512] using wordTrace_append hprefix tailTrace_169512
  have hstable : (prefixWord ++ tailWord_169512).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169512).length < 2 ^ (prefixWord ++ tailWord_169512).sum := by decide
  have hdescent : baseEnd_169512 < baseStart_169512 := by decide
  rcases family_descends (prefixWord ++ tailWord_169512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169514 : List Nat := [3, 1, 4, 1, 1, 1, 8]
def baseStart_169514 : Nat := 118140960795 + 169514 * 2 ^ 59
def prefixEnd_169514 : Nat := 4983230072969 + 3 ^ 40 * 169514 * 2
def baseEnd_169514 : Nat := 17193513020514569757121

theorem tailTrace_169514 : CollatzResearch.WordTrace tailWord_169514 prefixEnd_169514 17193513020514569757121 := by
  unfold tailWord_169514
  simp only [CollatzResearch.WordTrace]
  refine ⟨1545670876971800882856899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4121789005258135687618397 1545670876971800882856899)
  ·
    refine ⟨2318506315457701324285349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1545670876971800882856899 2318506315457701324285349)
    ·
      refine ⟨434719934148318998303503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2318506315457701324285349 434719934148318998303503)
      ·
        refine ⟨652079901222478497455255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 434719934148318998303503 652079901222478497455255)
        ·
          refine ⟨978119851833717746182883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 652079901222478497455255 978119851833717746182883)
          ·
            refine ⟨1467179777750576619274325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 978119851833717746182883 1467179777750576619274325)
            ·
              refine ⟨17193513020514569757121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1467179777750576619274325 17193513020514569757121)
              ·
                rfl

theorem cell19_169514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 8].length) (baseStart_169514 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_169514 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_169514 prefixEnd_169514 := by exact prefixLift 169514
  have htrace : WordTrace (prefixWord ++ tailWord_169514) baseStart_169514 baseEnd_169514 := by
    simpa [prefixWord, tailWord_169514, baseEnd_169514] using wordTrace_append hprefix tailTrace_169514
  have hstable : (prefixWord ++ tailWord_169514).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169514).length < 2 ^ (prefixWord ++ tailWord_169514).sum := by decide
  have hdescent : baseEnd_169514 < baseStart_169514 := by decide
  rcases family_descends (prefixWord ++ tailWord_169514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169565 : List Nat := [1, 4, 4, 2, 2, 1, 5]
def baseStart_169565 : Nat := 118140960795 + 169565 * 2 ^ 59
def prefixEnd_169565 : Nat := 4983230072969 + 3 ^ 40 * 169565 * 2
def baseEnd_169565 : Nat := 17198685862663567379297

theorem tailTrace_169565 : CollatzResearch.WordTrace tailWord_169565 prefixEnd_169565 17198685862663567379297 := by
  unfold tailWord_169565
  simp only [CollatzResearch.WordTrace]
  refine ⟨6184543630702439241534149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4123029087134959494356099 6184543630702439241534149)
  ·
    refine ⟨1159601930756707357787653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6184543630702439241534149 1159601930756707357787653)
    ·
      refine ⟨217425362016882629585185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1159601930756707357787653 217425362016882629585185)
      ·
        refine ⟨163069021512661972188889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 217425362016882629585185 163069021512661972188889)
        ·
          refine ⟨122301766134496479141667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 163069021512661972188889 122301766134496479141667)
          ·
            refine ⟨183452649201744718712501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122301766134496479141667 183452649201744718712501)
            ·
              refine ⟨17198685862663567379297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 183452649201744718712501 17198685862663567379297)
              ·
                rfl

theorem cell19_169565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 5].length) (baseStart_169565 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_169565 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_169565 prefixEnd_169565 := by exact prefixLift 169565
  have htrace : WordTrace (prefixWord ++ tailWord_169565) baseStart_169565 baseEnd_169565 := by
    simpa [prefixWord, tailWord_169565, baseEnd_169565] using wordTrace_append hprefix tailTrace_169565
  have hstable : (prefixWord ++ tailWord_169565).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169565).length < 2 ^ (prefixWord ++ tailWord_169565).sum := by decide
  have hdescent : baseEnd_169565 < baseStart_169565 := by decide
  rcases family_descends (prefixWord ++ tailWord_169565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169571 : List Nat := [1, 1, 1, 5, 1, 5, 5]
def baseStart_169571 : Nat := 118140960795 + 169571 * 2 ^ 59
def prefixEnd_169571 : Nat := 4983230072969 + 3 ^ 40 * 169571 * 2
def baseEnd_169571 : Nat := 17199294432328155334847

theorem tailTrace_169571 : CollatzResearch.WordTrace tailWord_169571 prefixEnd_169571 17199294432328155334847 := by
  unfold tailWord_169571
  simp only [CollatzResearch.WordTrace]
  refine ⟨6184762468680702266252567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4123174979120468177501711 6184762468680702266252567)
  ·
    refine ⟨9277143703021053399378851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6184762468680702266252567 9277143703021053399378851)
    ·
      refine ⟨13915715554531580099068277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9277143703021053399378851 13915715554531580099068277)
      ·
        refine ⟨1304598333237335634287651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13915715554531580099068277 1304598333237335634287651)
        ·
          refine ⟨1956897499856003451431477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1304598333237335634287651 1956897499856003451431477)
          ·
            refine ⟨183459140611500323571701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1956897499856003451431477 183459140611500323571701)
            ·
              refine ⟨17199294432328155334847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 183459140611500323571701 17199294432328155334847)
              ·
                rfl

theorem cell19_169571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 5].length) (baseStart_169571 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_169571 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_169571 prefixEnd_169571 := by exact prefixLift 169571
  have htrace : WordTrace (prefixWord ++ tailWord_169571) baseStart_169571 baseEnd_169571 := by
    simpa [prefixWord, tailWord_169571, baseEnd_169571] using wordTrace_append hprefix tailTrace_169571
  have hstable : (prefixWord ++ tailWord_169571).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169571).length < 2 ^ (prefixWord ++ tailWord_169571).sum := by decide
  have hdescent : baseEnd_169571 < baseStart_169571 := by decide
  rcases family_descends (prefixWord ++ tailWord_169571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169611 : List Nat := [1, 1, 1, 1, 4, 1, 3, 7]
def baseStart_169611 : Nat := 118140960795 + 169611 * 2 ^ 59
def prefixEnd_169611 : Nat := 4983230072969 + 3 ^ 40 * 169611 * 2
def baseEnd_169611 : Nat := 51610054690276225115543

theorem tailTrace_169611 : CollatzResearch.WordTrace tailWord_169611 prefixEnd_169611 51610054690276225115543 := by
  unfold tailWord_169611
  simp only [CollatzResearch.WordTrace]
  refine ⟨6186221388535789097708687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4124147592357192731805791 6186221388535789097708687)
  ·
    refine ⟨9279332082803683646563031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6186221388535789097708687 9279332082803683646563031)
    ·
      refine ⟨13918998124205525469844547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9279332082803683646563031 13918998124205525469844547)
      ·
        refine ⟨20878497186308288204766821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13918998124205525469844547 20878497186308288204766821)
        ·
          refine ⟨3914718222432804038393779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20878497186308288204766821 3914718222432804038393779)
          ·
            refine ⟨5872077333649206057590669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3914718222432804038393779 5872077333649206057590669)
            ·
              refine ⟨2202029000118452271596501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5872077333649206057590669 2202029000118452271596501)
              ·
                refine ⟨51610054690276225115543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2202029000118452271596501 51610054690276225115543)
                ·
                  rfl

theorem cell19_169611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 7].length) (baseStart_169611 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_169611 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_169611 prefixEnd_169611 := by exact prefixLift 169611
  have htrace : WordTrace (prefixWord ++ tailWord_169611) baseStart_169611 baseEnd_169611 := by
    simpa [prefixWord, tailWord_169611, baseEnd_169611] using wordTrace_append hprefix tailTrace_169611
  have hstable : (prefixWord ++ tailWord_169611).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169611).length < 2 ^ (prefixWord ++ tailWord_169611).sum := by decide
  have hdescent : baseEnd_169611 < baseStart_169611 := by decide
  rcases family_descends (prefixWord ++ tailWord_169611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169628 : List Nat := [2, 2, 3, 2, 3, 7]
def baseStart_169628 : Nat := 118140960795 + 169628 * 2 ^ 59
def prefixEnd_169628 : Nat := 4983230072969 + 3 ^ 40 * 169628 * 2
def baseEnd_169628 : Nat := 5735025281380580304191

theorem tailTrace_169628 : CollatzResearch.WordTrace tailWord_169628 prefixEnd_169628 5735025281380580304191 := by
  unfold tailWord_169628
  simp only [CollatzResearch.WordTrace]
  refine ⟨3093420714737100500538769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4124560952982800667385025 3093420714737100500538769)
  ·
    refine ⟨2320065536052825375404077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3093420714737100500538769 2320065536052825375404077)
    ·
      refine ⟨870024576019809515776529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2320065536052825375404077 870024576019809515776529)
      ·
        refine ⟨652518432014857136832397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 870024576019809515776529 652518432014857136832397)
        ·
          refine ⟨244694412005571426312149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 652518432014857136832397 244694412005571426312149)
          ·
            refine ⟨5735025281380580304191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 244694412005571426312149 5735025281380580304191)
            ·
              rfl

theorem cell19_169628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 7].length) (baseStart_169628 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_169628 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_169628 prefixEnd_169628 := by exact prefixLift 169628
  have htrace : WordTrace (prefixWord ++ tailWord_169628) baseStart_169628 baseEnd_169628 := by
    simpa [prefixWord, tailWord_169628, baseEnd_169628] using wordTrace_append hprefix tailTrace_169628
  have hstable : (prefixWord ++ tailWord_169628).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169628).length < 2 ^ (prefixWord ++ tailWord_169628).sum := by decide
  have hdescent : baseEnd_169628 < baseStart_169628 := by decide
  rcases family_descends (prefixWord ++ tailWord_169628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169687 : List Nat := [1, 1, 3, 2, 1, 3, 8]
def baseStart_169687 : Nat := 118140960795 + 169687 * 2 ^ 59
def prefixEnd_169687 : Nat := 4983230072969 + 3 ^ 40 * 169687 * 2
def baseEnd_169687 : Nat := 17211060112510189142149

theorem tailTrace_169687 : CollatzResearch.WordTrace tailWord_169687 prefixEnd_169687 17211060112510189142149 := by
  unfold tailWord_169687
  simp only [CollatzResearch.WordTrace]
  refine ⟨6188993336260454077475315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4125995557506969384983543 6188993336260454077475315)
  ·
    refine ⟨9283490004390681116212973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6188993336260454077475315 9283490004390681116212973)
    ·
      refine ⟨3481308751646505418579865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9283490004390681116212973 3481308751646505418579865)
      ·
        refine ⟨2610981563734879063934899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3481308751646505418579865 2610981563734879063934899)
        ·
          refine ⟨3916472345602318595902349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2610981563734879063934899 3916472345602318595902349)
          ·
            refine ⟨1468677129600869473463381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3916472345602318595902349 1468677129600869473463381)
            ·
              refine ⟨17211060112510189142149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1468677129600869473463381 17211060112510189142149)
              ·
                rfl

theorem cell19_169687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 8].length) (baseStart_169687 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_169687 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_169687 prefixEnd_169687 := by exact prefixLift 169687
  have htrace : WordTrace (prefixWord ++ tailWord_169687) baseStart_169687 baseEnd_169687 := by
    simpa [prefixWord, tailWord_169687, baseEnd_169687] using wordTrace_append hprefix tailTrace_169687
  have hstable : (prefixWord ++ tailWord_169687).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169687).length < 2 ^ (prefixWord ++ tailWord_169687).sum := by decide
  have hdescent : baseEnd_169687 < baseStart_169687 := by decide
  rcases family_descends (prefixWord ++ tailWord_169687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169761 : List Nat := [1, 2, 3, 2, 1, 4, 2, 4]
def baseStart_169761 : Nat := 118140960795 + 169761 * 2 ^ 59
def prefixEnd_169761 : Nat := 4983230072969 + 3 ^ 40 * 169761 * 2
def baseEnd_169761 : Nat := 51655697415120321781801

theorem tailTrace_169761 : CollatzResearch.WordTrace tailWord_169761 prefixEnd_169761 51655697415120321781801 := by
  unfold tailWord_169761
  simp only [CollatzResearch.WordTrace]
  refine ⟨6191692337992364715669137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4127794891994909810446091 6191692337992364715669137)
  ·
    refine ⟨4643769253494273536751853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6191692337992364715669137 4643769253494273536751853)
    ·
      refine ⟨1741413470060352576281945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4643769253494273536751853 1741413470060352576281945)
      ·
        refine ⟨1306060102545264432211459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1741413470060352576281945 1306060102545264432211459)
        ·
          refine ⟨1959090153817896648317189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1306060102545264432211459 1959090153817896648317189)
          ·
            refine ⟨367329403840855621559473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1959090153817896648317189 367329403840855621559473)
            ·
              refine ⟨275497052880641716169605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 367329403840855621559473 275497052880641716169605)
              ·
                refine ⟨51655697415120321781801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 275497052880641716169605 51655697415120321781801)
                ·
                  rfl

theorem cell19_169761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 2, 4].length) (baseStart_169761 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_169761 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_169761 prefixEnd_169761 := by exact prefixLift 169761
  have htrace : WordTrace (prefixWord ++ tailWord_169761) baseStart_169761 baseEnd_169761 := by
    simpa [prefixWord, tailWord_169761, baseEnd_169761] using wordTrace_append hprefix tailTrace_169761
  have hstable : (prefixWord ++ tailWord_169761).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169761).length < 2 ^ (prefixWord ++ tailWord_169761).sum := by decide
  have hdescent : baseEnd_169761 < baseStart_169761 := by decide
  rcases family_descends (prefixWord ++ tailWord_169761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169763 : List Nat := [1, 1, 1, 4, 2, 1, 3, 6]
def baseStart_169763 : Nat := 118140960795 + 169763 * 2 ^ 59
def prefixEnd_169763 : Nat := 4983230072969 + 3 ^ 40 * 169763 * 2
def baseEnd_169763 : Nat := 51656305984784909737351

theorem tailTrace_169763 : CollatzResearch.WordTrace tailWord_169763 prefixEnd_169763 51656305984784909737351 := by
  unfold tailWord_169763
  simp only [CollatzResearch.WordTrace]
  refine ⟨6191765283985119057241943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4127843522656746038161295 6191765283985119057241943)
  ·
    refine ⟨9287647925977678585862915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6191765283985119057241943 9287647925977678585862915)
    ·
      refine ⟨13931471888966517878794373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9287647925977678585862915 13931471888966517878794373)
      ·
        refine ⟨2612150979181222102273945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13931471888966517878794373 2612150979181222102273945)
        ·
          refine ⟨1959113234385916576705459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2612150979181222102273945 1959113234385916576705459)
          ·
            refine ⟨2938669851578874865058189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1959113234385916576705459 2938669851578874865058189)
            ·
              refine ⟨1102001194342078074396821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2938669851578874865058189 1102001194342078074396821)
              ·
                refine ⟨51656305984784909737351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1102001194342078074396821 51656305984784909737351)
                ·
                  rfl

theorem cell19_169763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 6].length) (baseStart_169763 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_169763 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_169763 prefixEnd_169763 := by exact prefixLift 169763
  have htrace : WordTrace (prefixWord ++ tailWord_169763) baseStart_169763 baseEnd_169763 := by
    simpa [prefixWord, tailWord_169763, baseEnd_169763] using wordTrace_append hprefix tailTrace_169763
  have hstable : (prefixWord ++ tailWord_169763).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169763).length < 2 ^ (prefixWord ++ tailWord_169763).sum := by decide
  have hdescent : baseEnd_169763 < baseStart_169763 := by decide
  rcases family_descends (prefixWord ++ tailWord_169763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169854 : List Nat := [4, 2, 3, 1, 1, 2, 6]
def baseStart_169854 : Nat := 118140960795 + 169854 * 2 ^ 59
def prefixEnd_169854 : Nat := 4983230072969 + 3 ^ 40 * 169854 * 2
def baseEnd_169854 : Nat := 17227998634841220571627

theorem tailTrace_169854 : CollatzResearch.WordTrace tailWord_169854 prefixEnd_169854 17227998634841220571627 := by
  unfold tailWord_169854
  simp only [CollatzResearch.WordTrace]
  refine ⟨774385540831930199850577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4130056217770294399203077 774385540831930199850577)
  ·
    refine ⟨580789155623947649887933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 774385540831930199850577 580789155623947649887933)
    ·
      refine ⟨217795933358980368707975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 580789155623947649887933 217795933358980368707975)
      ·
        refine ⟨326693900038470553061963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217795933358980368707975 326693900038470553061963)
        ·
          refine ⟨490040850057705829592945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 326693900038470553061963 490040850057705829592945)
          ·
            refine ⟨367530637543279372194709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 490040850057705829592945 367530637543279372194709)
            ·
              refine ⟨17227998634841220571627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 367530637543279372194709 17227998634841220571627)
              ·
                rfl

theorem cell19_169854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 6].length) (baseStart_169854 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_169854 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_169854 prefixEnd_169854 := by exact prefixLift 169854
  have htrace : WordTrace (prefixWord ++ tailWord_169854) baseStart_169854 baseEnd_169854 := by
    simpa [prefixWord, tailWord_169854, baseEnd_169854] using wordTrace_append hprefix tailTrace_169854
  have hstable : (prefixWord ++ tailWord_169854).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169854).length < 2 ^ (prefixWord ++ tailWord_169854).sum := by decide
  have hdescent : baseEnd_169854 < baseStart_169854 := by decide
  rcases family_descends (prefixWord ++ tailWord_169854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169877 : List Nat := [1, 3, 2, 1, 1, 3, 2, 6]
def baseStart_169877 : Nat := 118140960795 + 169877 * 2 ^ 59
def prefixEnd_169877 : Nat := 4983230072969 + 3 ^ 40 * 169877 * 2
def baseEnd_169877 : Nat := 51690994455666423203707

theorem tailTrace_169877 : CollatzResearch.WordTrace tailWord_169877 prefixEnd_169877 51690994455666423203707 := by
  unfold tailWord_169877
  simp only [CollatzResearch.WordTrace]
  refine ⟨6195923205572116526891885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4130615470381411017927923 6195923205572116526891885)
  ·
    refine ⟨2323471202089543697584457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6195923205572116526891885 2323471202089543697584457)
    ·
      refine ⟨1742603401567157773188343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2323471202089543697584457 1742603401567157773188343)
      ·
        refine ⟨2613905102350736659782515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1742603401567157773188343 2613905102350736659782515)
        ·
          refine ⟨3920857653526104989673773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2613905102350736659782515 3920857653526104989673773)
          ·
            refine ⟨1470321620072289371127665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3920857653526104989673773 1470321620072289371127665)
            ·
              refine ⟨1102741215054217028345749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1470321620072289371127665 1102741215054217028345749)
              ·
                refine ⟨51690994455666423203707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1102741215054217028345749 51690994455666423203707)
                ·
                  rfl

theorem cell19_169877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 6].length) (baseStart_169877 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_169877 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_169877 prefixEnd_169877 := by exact prefixLift 169877
  have htrace : WordTrace (prefixWord ++ tailWord_169877) baseStart_169877 baseEnd_169877 := by
    simpa [prefixWord, tailWord_169877, baseEnd_169877] using wordTrace_append hprefix tailTrace_169877
  have hstable : (prefixWord ++ tailWord_169877).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169877).length < 2 ^ (prefixWord ++ tailWord_169877).sum := by decide
  have hdescent : baseEnd_169877 < baseStart_169877 := by decide
  rcases family_descends (prefixWord ++ tailWord_169877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169886 : List Nat := [4, 3, 1, 3, 2, 1, 2, 3]
def baseStart_169886 : Nat := 118140960795 + 169886 * 2 ^ 59
def prefixEnd_169886 : Nat := 4983230072969 + 3 ^ 40 * 169886 * 2
def baseEnd_169886 : Nat := 51693733019157069003683

theorem tailTrace_169886 : CollatzResearch.WordTrace tailWord_169886 prefixEnd_169886 51693733019157069003683 := by
  unfold tailWord_169886
  simp only [CollatzResearch.WordTrace]
  refine ⟨774531432817438882996189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4130834308359674042646341 774531432817438882996189)
  ·
    refine ⟨290449287306539581123571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 774531432817438882996189 290449287306539581123571)
    ·
      refine ⟨435673930959809371685357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 290449287306539581123571 435673930959809371685357)
      ·
        refine ⟨163377724109928514382009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 435673930959809371685357 163377724109928514382009)
        ·
          refine ⟨122533293082446385786507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 163377724109928514382009 122533293082446385786507)
          ·
            refine ⟨183799939623669578679761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122533293082446385786507 183799939623669578679761)
            ·
              refine ⟨137849954717752184009821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 183799939623669578679761 137849954717752184009821)
              ·
                refine ⟨51693733019157069003683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 137849954717752184009821 51693733019157069003683)
                ·
                  rfl

theorem cell19_169886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 2, 3].length) (baseStart_169886 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_169886 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_169886 prefixEnd_169886 := by exact prefixLift 169886
  have htrace : WordTrace (prefixWord ++ tailWord_169886) baseStart_169886 baseEnd_169886 := by
    simpa [prefixWord, tailWord_169886, baseEnd_169886] using wordTrace_append hprefix tailTrace_169886
  have hstable : (prefixWord ++ tailWord_169886).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169886).length < 2 ^ (prefixWord ++ tailWord_169886).sum := by decide
  have hdescent : baseEnd_169886 < baseStart_169886 := by decide
  rcases family_descends (prefixWord ++ tailWord_169886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169890 : List Nat := [3, 3, 1, 2, 3, 2, 2, 3]
def baseStart_169890 : Nat := 118140960795 + 169890 * 2 ^ 59
def prefixEnd_169890 : Nat := 4983230072969 + 3 ^ 40 * 169890 * 2
def baseEnd_169890 : Nat := 51694950158486244914783

theorem tailTrace_169890 : CollatzResearch.WordTrace tailWord_169890 prefixEnd_169890 51694950158486244914783 := by
  unfold tailWord_169890
  simp only [CollatzResearch.WordTrace]
  refine ⟨1549099338631254936778781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4130931569683346498076749 1549099338631254936778781)
  ·
    refine ⟨580912251986720601292043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1549099338631254936778781 580912251986720601292043)
    ·
      refine ⟨871368377980080901938065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 580912251986720601292043 871368377980080901938065)
      ·
        refine ⟨653526283485060676453549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 871368377980080901938065 653526283485060676453549)
        ·
          refine ⟨245072356306897753670081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 653526283485060676453549 245072356306897753670081)
          ·
            refine ⟨183804267230173315252561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 245072356306897753670081 183804267230173315252561)
            ·
              refine ⟨137853200422629986439421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 183804267230173315252561 137853200422629986439421)
              ·
                refine ⟨51694950158486244914783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 137853200422629986439421 51694950158486244914783)
                ·
                  rfl

theorem cell19_169890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 2, 3].length) (baseStart_169890 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_169890 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_169890 prefixEnd_169890 := by exact prefixLift 169890
  have htrace : WordTrace (prefixWord ++ tailWord_169890) baseStart_169890 baseEnd_169890 := by
    simpa [prefixWord, tailWord_169890, baseEnd_169890] using wordTrace_append hprefix tailTrace_169890
  have hstable : (prefixWord ++ tailWord_169890).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169890).length < 2 ^ (prefixWord ++ tailWord_169890).sum := by decide
  have hdescent : baseEnd_169890 < baseStart_169890 := by decide
  rcases family_descends (prefixWord ++ tailWord_169890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169892 : List Nat := [2, 3, 1, 2, 1, 5, 2, 3]
def baseStart_169892 : Nat := 118140960795 + 169892 * 2 ^ 59
def prefixEnd_169892 : Nat := 4983230072969 + 3 ^ 40 * 169892 * 2
def baseEnd_169892 : Nat := 51695558728150832870333

theorem tailTrace_169892 : CollatzResearch.WordTrace tailWord_169892 prefixEnd_169892 51695558728150832870333 := by
  unfold tailWord_169892
  simp only [CollatzResearch.WordTrace]
  refine ⟨3098235150258887044343965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4130980200345182725791953 3098235150258887044343965)
  ·
    refine ⟨1161838181347082641628987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3098235150258887044343965 1161838181347082641628987)
    ·
      refine ⟨1742757272020623962443481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1161838181347082641628987 1742757272020623962443481)
      ·
        refine ⟨1307067954015467971832611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1742757272020623962443481 1307067954015467971832611)
        ·
          refine ⟨1960601931023201957748917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1307067954015467971832611 1960601931023201957748917)
          ·
            refine ⟨183806431033425183538961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1960601931023201957748917 183806431033425183538961)
            ·
              refine ⟨137854823275068887654221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 183806431033425183538961 137854823275068887654221)
              ·
                refine ⟨51695558728150832870333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 137854823275068887654221 51695558728150832870333)
                ·
                  rfl

theorem cell19_169892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 2, 3].length) (baseStart_169892 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_169892 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_169892 prefixEnd_169892 := by exact prefixLift 169892
  have htrace : WordTrace (prefixWord ++ tailWord_169892) baseStart_169892 baseEnd_169892 := by
    simpa [prefixWord, tailWord_169892, baseEnd_169892] using wordTrace_append hprefix tailTrace_169892
  have hstable : (prefixWord ++ tailWord_169892).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169892).length < 2 ^ (prefixWord ++ tailWord_169892).sum := by decide
  have hdescent : baseEnd_169892 < baseStart_169892 := by decide
  rcases family_descends (prefixWord ++ tailWord_169892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169932 : List Nat := [2, 2, 1, 4, 1, 3, 2, 4]
def baseStart_169932 : Nat := 118140960795 + 169932 * 2 ^ 59
def prefixEnd_169932 : Nat := 4983230072969 + 3 ^ 40 * 169932 * 2
def baseEnd_169932 : Nat := 51707730121442591981335

theorem tailTrace_169932 : CollatzResearch.WordTrace tailWord_169932 prefixEnd_169932 51707730121442591981335 := by
  unfold tailWord_169932
  simp only [CollatzResearch.WordTrace]
  refine ⟨3098964610186430460072025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4131952813581907280096033 3098964610186430460072025)
  ·
    refine ⟨2324223457639822845054019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3098964610186430460072025 2324223457639822845054019)
    ·
      refine ⟨3486335186459734267581029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2324223457639822845054019 3486335186459734267581029)
      ·
        refine ⟨653687847461200175171443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3486335186459734267581029 653687847461200175171443)
        ·
          refine ⟨980531771191800262757165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 653687847461200175171443 980531771191800262757165)
          ·
            refine ⟨367699414196925098533937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 980531771191800262757165 367699414196925098533937)
            ·
              refine ⟨275774560647693823900453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 367699414196925098533937 275774560647693823900453)
              ·
                refine ⟨51707730121442591981335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 275774560647693823900453 51707730121442591981335)
                ·
                  rfl

theorem cell19_169932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 2, 4].length) (baseStart_169932 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_169932 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_169932 prefixEnd_169932 := by exact prefixLift 169932
  have htrace : WordTrace (prefixWord ++ tailWord_169932) baseStart_169932 baseEnd_169932 := by
    simpa [prefixWord, tailWord_169932, baseEnd_169932] using wordTrace_append hprefix tailTrace_169932
  have hstable : (prefixWord ++ tailWord_169932).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169932).length < 2 ^ (prefixWord ++ tailWord_169932).sum := by decide
  have hdescent : baseEnd_169932 < baseStart_169932 := by decide
  rcases family_descends (prefixWord ++ tailWord_169932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169953 : List Nat := [1, 2, 3, 1, 2, 1, 4, 5]
def baseStart_169953 : Nat := 118140960795 + 169953 * 2 ^ 59
def prefixEnd_169953 : Nat := 4983230072969 + 3 ^ 40 * 169953 * 2
def baseEnd_169953 : Nat := 51714120102920765514611

theorem tailTrace_169953 : CollatzResearch.WordTrace tailWord_169953 prefixEnd_169953 51714120102920765514611 := by
  unfold tailWord_169953
  simp only [CollatzResearch.WordTrace]
  refine ⟨6198695153296781506658513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4132463435531187671105675 6198695153296781506658513)
  ·
    refine ⟨4649021364972586129993885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6198695153296781506658513 4649021364972586129993885)
    ·
      refine ⟨1743383011864719798747707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4649021364972586129993885 1743383011864719798747707)
      ·
        refine ⟨2615074517797079698121561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1743383011864719798747707 2615074517797079698121561)
        ·
          refine ⟨1961305888347809773591171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2615074517797079698121561 1961305888347809773591171)
          ·
            refine ⟨2941958832521714660386757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1961305888347809773591171 2941958832521714660386757)
            ·
              refine ⟨551617281097821498822517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2941958832521714660386757 551617281097821498822517)
              ·
                refine ⟨51714120102920765514611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 551617281097821498822517 51714120102920765514611)
                ·
                  rfl

theorem cell19_169953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 5].length) (baseStart_169953 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_169953 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_169953 prefixEnd_169953 := by exact prefixLift 169953
  have htrace : WordTrace (prefixWord ++ tailWord_169953) baseStart_169953 baseEnd_169953 := by
    simpa [prefixWord, tailWord_169953, baseEnd_169953] using wordTrace_append hprefix tailTrace_169953
  have hstable : (prefixWord ++ tailWord_169953).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169953).length < 2 ^ (prefixWord ++ tailWord_169953).sum := by decide
  have hdescent : baseEnd_169953 < baseStart_169953 := by decide
  rcases family_descends (prefixWord ++ tailWord_169953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169989 : List Nat := [1, 3, 1, 1, 2, 6, 1, 4]
def baseStart_169989 : Nat := 118140960795 + 169989 * 2 ^ 59
def prefixEnd_169989 : Nat := 4983230072969 + 3 ^ 40 * 169989 * 2
def baseEnd_169989 : Nat := 51725074356883348714513

theorem tailTrace_169989 : CollatzResearch.WordTrace tailWord_169989 prefixEnd_169989 51725074356883348714513 := by
  unfold tailWord_169989
  simp only [CollatzResearch.WordTrace]
  refine ⟨6200008181166359654969021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4133338787444239769979347 6200008181166359654969021)
  ·
    refine ⟨2325003067937384870613383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6200008181166359654969021 2325003067937384870613383)
    ·
      refine ⟨3487504601906077305920075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2325003067937384870613383 3487504601906077305920075)
      ·
        refine ⟨5231256902859115958880113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3487504601906077305920075 5231256902859115958880113)
        ·
          refine ⟨3923442677144336969160085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5231256902859115958880113 3923442677144336969160085)
          ·
            refine ⟨183911375491140795429379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 3923442677144336969160085 183911375491140795429379)
            ·
              refine ⟨275867063236711193144069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 183911375491140795429379 275867063236711193144069)
              ·
                refine ⟨51725074356883348714513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 275867063236711193144069 51725074356883348714513)
                ·
                  rfl

theorem cell19_169989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 1, 4].length) (baseStart_169989 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_169989 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_169989 prefixEnd_169989 := by exact prefixLift 169989
  have htrace : WordTrace (prefixWord ++ tailWord_169989) baseStart_169989 baseEnd_169989 := by
    simpa [prefixWord, tailWord_169989, baseEnd_169989] using wordTrace_append hprefix tailTrace_169989
  have hstable : (prefixWord ++ tailWord_169989).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169989).length < 2 ^ (prefixWord ++ tailWord_169989).sum := by decide
  have hdescent : baseEnd_169989 < baseStart_169989 := by decide
  rcases family_descends (prefixWord ++ tailWord_169989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170008 : List Nat := [2, 1, 2, 3, 2, 1, 5, 3]
def baseStart_170008 : Nat := 118140960795 + 170008 * 2 ^ 59
def prefixEnd_170008 : Nat := 4983230072969 + 3 ^ 40 * 170008 * 2
def baseEnd_170008 : Nat := 51730855768696934292239

theorem tailTrace_170008 : CollatzResearch.WordTrace tailWord_170008 prefixEnd_170008 51730855768696934292239 := by
  unfold tailWord_170008
  simp only [CollatzResearch.WordTrace]
  refine ⟨3100350584048762949955339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4133800778731683933273785 3100350584048762949955339)
  ·
    refine ⟨4650525876073144424933009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3100350584048762949955339 4650525876073144424933009)
    ·
      refine ⟨3487894407054858318699757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4650525876073144424933009 3487894407054858318699757)
      ·
        refine ⟨1307960402645571869512409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3487894407054858318699757 1307960402645571869512409)
        ·
          refine ⟨980970301984178902134307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1307960402645571869512409 980970301984178902134307)
          ·
            refine ⟨1471455452976268353201461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 980970301984178902134307 1471455452976268353201461)
            ·
              refine ⟨137948948716525158112637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1471455452976268353201461 137948948716525158112637)
              ·
                refine ⟨51730855768696934292239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 137948948716525158112637 51730855768696934292239)
                ·
                  rfl

theorem cell19_170008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 5, 3].length) (baseStart_170008 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_170008 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_170008 prefixEnd_170008 := by exact prefixLift 170008
  have htrace : WordTrace (prefixWord ++ tailWord_170008) baseStart_170008 baseEnd_170008 := by
    simpa [prefixWord, tailWord_170008, baseEnd_170008] using wordTrace_append hprefix tailTrace_170008
  have hstable : (prefixWord ++ tailWord_170008).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170008).length < 2 ^ (prefixWord ++ tailWord_170008).sum := by decide
  have hdescent : baseEnd_170008 < baseStart_170008 := by decide
  rcases family_descends (prefixWord ++ tailWord_170008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170078 : List Nat := [4, 4, 1, 1, 3, 1, 5]
def baseStart_170078 : Nat := 118140960795 + 170078 * 2 ^ 59
def prefixEnd_170078 : Nat := 4983230072969 + 3 ^ 40 * 170078 * 2
def baseEnd_170078 : Nat := 17250718568985837578831

theorem tailTrace_170078 : CollatzResearch.WordTrace tailWord_170078 prefixEnd_170078 17250718568985837578831 := by
  unfold tailWord_170078
  simp only [CollatzResearch.WordTrace]
  refine ⟨775406784730490981869861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4135502851895951903305925 775406784730490981869861)
  ·
    refine ⟨145388772136967059100599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 775406784730490981869861 145388772136967059100599)
    ·
      refine ⟨218083158205450588650899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145388772136967059100599 218083158205450588650899)
      ·
        refine ⟨327124737308175882976349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218083158205450588650899 327124737308175882976349)
        ·
          refine ⟨122671776490565956116131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 327124737308175882976349 122671776490565956116131)
          ·
            refine ⟨184007664735848934174197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122671776490565956116131 184007664735848934174197)
            ·
              refine ⟨17250718568985837578831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 184007664735848934174197 17250718568985837578831)
              ·
                rfl

theorem cell19_170078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 5].length) (baseStart_170078 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_170078 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_170078 prefixEnd_170078 := by exact prefixLift 170078
  have htrace : WordTrace (prefixWord ++ tailWord_170078) baseStart_170078 baseEnd_170078 := by
    simpa [prefixWord, tailWord_170078, baseEnd_170078] using wordTrace_append hprefix tailTrace_170078
  have hstable : (prefixWord ++ tailWord_170078).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170078).length < 2 ^ (prefixWord ++ tailWord_170078).sum := by decide
  have hdescent : baseEnd_170078 < baseStart_170078 := by decide
  rcases family_descends (prefixWord ++ tailWord_170078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170082 : List Nat := [3, 3, 2, 2, 2, 2, 5]
def baseStart_170082 : Nat := 118140960795 + 170082 * 2 ^ 59
def prefixEnd_170082 : Nat := 4983230072969 + 3 ^ 40 * 170082 * 2
def baseEnd_170082 : Nat := 17251124282095562882531

theorem tailTrace_170082 : CollatzResearch.WordTrace tailWord_170082 prefixEnd_170082 17251124282095562882531 := by
  unfold tailWord_170082
  simp only [CollatzResearch.WordTrace]
  refine ⟨1550850042457359134526125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4135600113219624358736333 1550850042457359134526125)
  ·
    refine ⟨581568765921509675447297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1550850042457359134526125 581568765921509675447297)
    ·
      refine ⟨436176574441132256585473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 581568765921509675447297 436176574441132256585473)
      ·
        refine ⟨327132430830849192439105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 436176574441132256585473 327132430830849192439105)
        ·
          refine ⟨245349323123136894329329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 327132430830849192439105 245349323123136894329329)
          ·
            refine ⟨184011992342352670746997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 245349323123136894329329 184011992342352670746997)
            ·
              refine ⟨17251124282095562882531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 184011992342352670746997 17251124282095562882531)
              ·
                rfl

theorem cell19_170082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 5].length) (baseStart_170082 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_170082 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_170082 prefixEnd_170082 := by exact prefixLift 170082
  have htrace : WordTrace (prefixWord ++ tailWord_170082) baseStart_170082 baseEnd_170082 := by
    simpa [prefixWord, tailWord_170082, baseEnd_170082] using wordTrace_append hprefix tailTrace_170082
  have hstable : (prefixWord ++ tailWord_170082).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170082).length < 2 ^ (prefixWord ++ tailWord_170082).sum := by decide
  have hdescent : baseEnd_170082 < baseStart_170082 := by decide
  rcases family_descends (prefixWord ++ tailWord_170082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170105 : List Nat := [1, 2, 1, 3, 4, 1, 1, 6]
def baseStart_170105 : Nat := 118140960795 + 170105 * 2 ^ 59
def prefixEnd_170105 : Nat := 4983230072969 + 3 ^ 40 * 170105 * 2
def baseEnd_170105 : Nat := 51760371397429450136419

theorem tailTrace_170105 : CollatzResearch.WordTrace tailWord_170105 prefixEnd_170105 51760371397429450136419 := by
  unfold tailWord_170105
  simp only [CollatzResearch.WordTrace]
  refine ⟨6204239048746111466191769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4136159365830740977461179 6204239048746111466191769)
  ·
    refine ⟨4653179286559583599643827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6204239048746111466191769 4653179286559583599643827)
    ·
      refine ⟨6979768929839375399465741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4653179286559583599643827 6979768929839375399465741)
      ·
        refine ⟨2617413348689765774799653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6979768929839375399465741 2617413348689765774799653)
        ·
          refine ⟨490765002879331082774935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2617413348689765774799653 490765002879331082774935)
          ·
            refine ⟨736147504318996624162403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 490765002879331082774935 736147504318996624162403)
            ·
              refine ⟨1104221256478494936243605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 736147504318996624162403 1104221256478494936243605)
              ·
                refine ⟨51760371397429450136419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1104221256478494936243605 51760371397429450136419)
                ·
                  rfl

theorem cell19_170105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 6].length) (baseStart_170105 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_170105 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_170105 prefixEnd_170105 := by exact prefixLift 170105
  have htrace : WordTrace (prefixWord ++ tailWord_170105) baseStart_170105 baseEnd_170105 := by
    simpa [prefixWord, tailWord_170105, baseEnd_170105] using wordTrace_append hprefix tailTrace_170105
  have hstable : (prefixWord ++ tailWord_170105).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170105).length < 2 ^ (prefixWord ++ tailWord_170105).sum := by decide
  have hdescent : baseEnd_170105 < baseStart_170105 := by decide
  rcases family_descends (prefixWord ++ tailWord_170105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170143 : List Nat := [1, 1, 2, 6, 1, 8]
def baseStart_170143 : Nat := 118140960795 + 170143 * 2 ^ 59
def prefixEnd_170143 : Nat := 4983230072969 + 3 ^ 40 * 170143 * 2
def baseEnd_170143 : Nat := 5752437135672957921319

theorem tailTrace_170143 : CollatzResearch.WordTrace tailWord_170143 prefixEnd_170143 5752437135672957921319 := by
  unfold tailWord_170143
  simp only [CollatzResearch.WordTrace]
  refine ⟨6205625022608443956075083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4137083348405629304050055 6205625022608443956075083)
  ·
    refine ⟨9308437533912665934112625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6205625022608443956075083 9308437533912665934112625)
    ·
      refine ⟨6981328150434499450584469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9308437533912665934112625 6981328150434499450584469)
      ·
        refine ⟨327249757051617161746147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 6981328150434499450584469 327249757051617161746147)
        ·
          refine ⟨490874635577425742619221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 327249757051617161746147 490874635577425742619221)
          ·
            refine ⟨5752437135672957921319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 490874635577425742619221 5752437135672957921319)
            ·
              rfl

theorem cell19_170143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 8].length) (baseStart_170143 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_170143 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_170143 prefixEnd_170143 := by exact prefixLift 170143
  have htrace : WordTrace (prefixWord ++ tailWord_170143) baseStart_170143 baseEnd_170143 := by
    simpa [prefixWord, tailWord_170143, baseEnd_170143] using wordTrace_append hprefix tailTrace_170143
  have hstable : (prefixWord ++ tailWord_170143).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170143).length < 2 ^ (prefixWord ++ tailWord_170143).sum := by decide
  have hdescent : baseEnd_170143 < baseStart_170143 := by decide
  rcases family_descends (prefixWord ++ tailWord_170143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170200 : List Nat := [2, 1, 2, 2, 4, 2, 6]
def baseStart_170200 : Nat := 118140960795 + 170200 * 2 ^ 59
def prefixEnd_170200 : Nat := 4983230072969 + 3 ^ 40 * 170200 * 2
def baseEnd_170200 : Nat := 17263092818832459341683

theorem tailTrace_170200 : CollatzResearch.WordTrace tailWord_170200 prefixEnd_170200 17263092818832459341683 := by
  unfold tailWord_170200
  simp only [CollatzResearch.WordTrace]
  refine ⟨3103851991700971345450027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4138469322267961793933369 3103851991700971345450027)
  ·
    refine ⟨4655777987551457018175041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3103851991700971345450027 4655777987551457018175041)
    ·
      refine ⟨3491833490663592763631281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4655777987551457018175041 3491833490663592763631281)
      ·
        refine ⟨2618875117997694572723461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3491833490663592763631281 2618875117997694572723461)
        ·
          refine ⟨491039084624567732385649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2618875117997694572723461 491039084624567732385649)
          ·
            refine ⟨368279313468425799289237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 491039084624567732385649 368279313468425799289237)
            ·
              refine ⟨17263092818832459341683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 368279313468425799289237 17263092818832459341683)
              ·
                rfl

theorem cell19_170200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 6].length) (baseStart_170200 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_170200 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_170200 prefixEnd_170200 := by exact prefixLift 170200
  have htrace : WordTrace (prefixWord ++ tailWord_170200) baseStart_170200 baseEnd_170200 := by
    simpa [prefixWord, tailWord_170200, baseEnd_170200] using wordTrace_append hprefix tailTrace_170200
  have hstable : (prefixWord ++ tailWord_170200).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170200).length < 2 ^ (prefixWord ++ tailWord_170200).sum := by decide
  have hdescent : baseEnd_170200 < baseStart_170200 := by decide
  rcases family_descends (prefixWord ++ tailWord_170200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170236 : List Nat := [2, 2, 2, 1, 4, 1, 4, 3]
def baseStart_170236 : Nat := 118140960795 + 170236 * 2 ^ 59
def prefixEnd_170236 : Nat := 4983230072969 + 3 ^ 40 * 170236 * 2
def baseEnd_170236 : Nat := 51800232710459961224951

theorem tailTrace_170236 : CollatzResearch.WordTrace tailWord_170236 prefixEnd_170236 51800232710459961224951 := by
  unfold tailWord_170236
  simp only [CollatzResearch.WordTrace]
  refine ⟨3104508505635760419605281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4139344674181013892807041 3104508505635760419605281)
  ·
    refine ⟨2328381379226820314703961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3104508505635760419605281 2328381379226820314703961)
    ·
      refine ⟨1746286034420115236027971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2328381379226820314703961 1746286034420115236027971)
      ·
        refine ⟨2619429051630172854041957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1746286034420115236027971 2619429051630172854041957)
        ·
          refine ⟨491142947180657410132867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2619429051630172854041957 491142947180657410132867)
          ·
            refine ⟨736714420770986115199301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 491142947180657410132867 736714420770986115199301)
            ·
              refine ⟨138133953894559896599869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 736714420770986115199301 138133953894559896599869)
              ·
                refine ⟨51800232710459961224951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 138133953894559896599869 51800232710459961224951)
                ·
                  rfl

theorem cell19_170236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 4, 3].length) (baseStart_170236 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_170236 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_170236 prefixEnd_170236 := by exact prefixLift 170236
  have htrace : WordTrace (prefixWord ++ tailWord_170236) baseStart_170236 baseEnd_170236 := by
    simpa [prefixWord, tailWord_170236, baseEnd_170236] using wordTrace_append hprefix tailTrace_170236
  have hstable : (prefixWord ++ tailWord_170236).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170236).length < 2 ^ (prefixWord ++ tailWord_170236).sum := by decide
  have hdescent : baseEnd_170236 < baseStart_170236 := by decide
  rcases family_descends (prefixWord ++ tailWord_170236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170257 : List Nat := [1, 2, 2, 1, 1, 7, 5]
def baseStart_170257 : Nat := 118140960795 + 170257 * 2 ^ 59
def prefixEnd_170257 : Nat := 4983230072969 + 3 ^ 40 * 170257 * 2
def baseEnd_170257 : Nat := 17268874230646044919409

theorem tailTrace_170257 : CollatzResearch.WordTrace tailWord_170257 prefixEnd_170257 17268874230646044919409 := by
  unfold tailWord_170257
  simp only [CollatzResearch.WordTrace]
  refine ⟨6209782944195441425725025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4139855296130294283816683 6209782944195441425725025)
  ·
    refine ⟨4657337208146581069293769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6209782944195441425725025 4657337208146581069293769)
    ·
      refine ⟨3493002906109935801970327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4657337208146581069293769 3493002906109935801970327)
      ·
        refine ⟨5239504359164903702955491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3493002906109935801970327 5239504359164903702955491)
        ·
          refine ⟨7859256538747355554433237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5239504359164903702955491 7859256538747355554433237)
          ·
            refine ⟨184201325126891145807029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 7859256538747355554433237 184201325126891145807029)
            ·
              refine ⟨17268874230646044919409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 184201325126891145807029 17268874230646044919409)
              ·
                rfl

theorem cell19_170257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 5].length) (baseStart_170257 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_170257 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_170257 prefixEnd_170257 := by exact prefixLift 170257
  have htrace : WordTrace (prefixWord ++ tailWord_170257) baseStart_170257 baseEnd_170257 := by
    simpa [prefixWord, tailWord_170257, baseEnd_170257] using wordTrace_append hprefix tailTrace_170257
  have hstable : (prefixWord ++ tailWord_170257).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170257).length < 2 ^ (prefixWord ++ tailWord_170257).sum := by decide
  have hdescent : baseEnd_170257 < baseStart_170257 := by decide
  rcases family_descends (prefixWord ++ tailWord_170257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170274 : List Nat := [3, 3, 1, 1, 3, 2, 2, 4]
def baseStart_170274 : Nat := 118140960795 + 170274 * 2 ^ 59
def prefixEnd_170274 : Nat := 4983230072969 + 3 ^ 40 * 170274 * 2
def baseEnd_170274 : Nat := 51811795534087132380403

theorem tailTrace_170274 : CollatzResearch.WordTrace tailWord_170274 prefixEnd_170274 51811795534087132380403 := by
  unfold tailWord_170274
  simp only [CollatzResearch.WordTrace]
  refine ⟨1552600746283463332273469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4140268656755902219395917 1552600746283463332273469)
  ·
    refine ⟨582225279856298749602551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1552600746283463332273469 582225279856298749602551)
    ·
      refine ⟨873337919784448124403827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 582225279856298749602551 873337919784448124403827)
      ·
        refine ⟨1310006879676672186605741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 873337919784448124403827 1310006879676672186605741)
        ·
          refine ⟨491252579878752069977153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1310006879676672186605741 491252579878752069977153)
          ·
            refine ⟨368439434909064052482865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 491252579878752069977153 368439434909064052482865)
            ·
              refine ⟨276329576181798039362149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 368439434909064052482865 276329576181798039362149)
              ·
                refine ⟨51811795534087132380403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 276329576181798039362149 51811795534087132380403)
                ·
                  rfl

theorem cell19_170274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 2, 4].length) (baseStart_170274 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_170274 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_170274 prefixEnd_170274 := by exact prefixLift 170274
  have htrace : WordTrace (prefixWord ++ tailWord_170274) baseStart_170274 baseEnd_170274 := by
    simpa [prefixWord, tailWord_170274, baseEnd_170274] using wordTrace_append hprefix tailTrace_170274
  have hstable : (prefixWord ++ tailWord_170274).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170274).length < 2 ^ (prefixWord ++ tailWord_170274).sum := by decide
  have hdescent : baseEnd_170274 < baseStart_170274 := by decide
  rcases family_descends (prefixWord ++ tailWord_170274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170276 : List Nat := [2, 3, 1, 3, 1, 2, 1, 6]
def baseStart_170276 : Nat := 118140960795 + 170276 * 2 ^ 59
def prefixEnd_170276 : Nat := 4983230072969 + 3 ^ 40 * 170276 * 2
def baseEnd_170276 : Nat := 51812404103751720335953

theorem tailTrace_170276 : CollatzResearch.WordTrace tailWord_170276 prefixEnd_170276 51812404103751720335953 := by
  unfold tailWord_170276
  simp only [CollatzResearch.WordTrace]
  refine ⟨3105237965563303835333341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4140317287417738447111121 3105237965563303835333341)
  ·
    refine ⟨1164464237086238938250003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3105237965563303835333341 1164464237086238938250003)
    ·
      refine ⟨1746696355629358407375005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1164464237086238938250003 1746696355629358407375005)
      ·
        refine ⟨655011133361009402765627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1746696355629358407375005 655011133361009402765627)
        ·
          refine ⟨982516700041514104148441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 655011133361009402765627 982516700041514104148441)
          ·
            refine ⟨736887525031135578111331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 982516700041514104148441 736887525031135578111331)
            ·
              refine ⟨1105331287546703367166997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 736887525031135578111331 1105331287546703367166997)
              ·
                refine ⟨51812404103751720335953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1105331287546703367166997 51812404103751720335953)
                ·
                  rfl

theorem cell19_170276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 6].length) (baseStart_170276 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_170276 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_170276 prefixEnd_170276 := by exact prefixLift 170276
  have htrace : WordTrace (prefixWord ++ tailWord_170276) baseStart_170276 baseEnd_170276 := by
    simpa [prefixWord, tailWord_170276, baseEnd_170276] using wordTrace_append hprefix tailTrace_170276
  have hstable : (prefixWord ++ tailWord_170276).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170276).length < 2 ^ (prefixWord ++ tailWord_170276).sum := by decide
  have hdescent : baseEnd_170276 < baseStart_170276 := by decide
  rcases family_descends (prefixWord ++ tailWord_170276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170371 : List Nat := [1, 1, 1, 3, 6, 1, 6]
def baseStart_170371 : Nat := 118140960795 + 170371 * 2 ^ 59
def prefixEnd_170371 : Nat := 4983230072969 + 3 ^ 40 * 170371 * 2
def baseEnd_170371 : Nat := 17280437054273216074861

theorem tailTrace_170371 : CollatzResearch.WordTrace tailWord_170371 prefixEnd_170371 17280437054273216074861 := by
  unfold tailWord_170371
  simp only [CollatzResearch.WordTrace]
  refine ⟨6213940865782438895374967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4142627243854959263583311 6213940865782438895374967)
  ·
    refine ⟨9320911298673658343062451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6213940865782438895374967 9320911298673658343062451)
    ·
      refine ⟨13981366948010487514593677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9320911298673658343062451 13981366948010487514593677)
      ·
        refine ⟨5243012605503932817972629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13981366948010487514593677 5243012605503932817972629)
        ·
          refine ⟨245766215882996850842467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 5243012605503932817972629 245766215882996850842467)
          ·
            refine ⟨368649323824495276263701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 245766215882996850842467 368649323824495276263701)
            ·
              refine ⟨17280437054273216074861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 368649323824495276263701 17280437054273216074861)
              ·
                rfl

theorem cell19_170371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 6].length) (baseStart_170371 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_170371 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_170371 prefixEnd_170371 := by exact prefixLift 170371
  have htrace : WordTrace (prefixWord ++ tailWord_170371) baseStart_170371 baseEnd_170371 := by
    simpa [prefixWord, tailWord_170371, baseEnd_170371] using wordTrace_append hprefix tailTrace_170371
  have hstable : (prefixWord ++ tailWord_170371).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170371).length < 2 ^ (prefixWord ++ tailWord_170371).sum := by decide
  have hdescent : baseEnd_170371 < baseStart_170371 := by decide
  rcases family_descends (prefixWord ++ tailWord_170371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170407 : List Nat := [1, 1, 6, 1, 1, 2, 4, 3]
def baseStart_170407 : Nat := 118140960795 + 170407 * 2 ^ 59
def prefixEnd_170407 : Nat := 4983230072969 + 3 ^ 40 * 170407 * 2
def baseEnd_170407 : Nat := 51852265416782231424485

theorem tailTrace_170407 : CollatzResearch.WordTrace tailWord_170407 prefixEnd_170407 51852265416782231424485 := by
  unfold tailWord_170407
  simp only [CollatzResearch.WordTrace]
  refine ⟨6215253893652017043685475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4143502595768011362456983 6215253893652017043685475)
  ·
    refine ⟨9322880840478025565528213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6215253893652017043685475 9322880840478025565528213)
    ·
      refine ⟨437010039397407448384135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 9322880840478025565528213 437010039397407448384135)
      ·
        refine ⟨655515059096111172576203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 437010039397407448384135 655515059096111172576203)
        ·
          refine ⟨983272588644166758864305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 655515059096111172576203 983272588644166758864305)
          ·
            refine ⟨737454441483125069148229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 983272588644166758864305 737454441483125069148229)
            ·
              refine ⟨138272707778085950465293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 737454441483125069148229 138272707778085950465293)
              ·
                refine ⟨51852265416782231424485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 138272707778085950465293 51852265416782231424485)
                ·
                  rfl

theorem cell19_170407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 4, 3].length) (baseStart_170407 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_170407 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_170407 prefixEnd_170407 := by exact prefixLift 170407
  have htrace : WordTrace (prefixWord ++ tailWord_170407) baseStart_170407 baseEnd_170407 := by
    simpa [prefixWord, tailWord_170407, baseEnd_170407] using wordTrace_append hprefix tailTrace_170407
  have hstable : (prefixWord ++ tailWord_170407).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170407).length < 2 ^ (prefixWord ++ tailWord_170407).sum := by decide
  have hdescent : baseEnd_170407 < baseStart_170407 := by decide
  rcases family_descends (prefixWord ++ tailWord_170407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170428 : List Nat := [2, 2, 2, 4, 1, 1, 7]
def baseStart_170428 : Nat := 118140960795 + 170428 * 2 ^ 59
def prefixEnd_170428 : Nat := 4983230072969 + 3 ^ 40 * 170428 * 2
def baseEnd_170428 : Nat := 17286218466086801652587

theorem tailTrace_170428 : CollatzResearch.WordTrace tailWord_170428 prefixEnd_170428 17286218466086801652587 := by
  unfold tailWord_170428
  simp only [CollatzResearch.WordTrace]
  refine ⟨3108009913287968815099969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4144013217717291753466625 3108009913287968815099969)
  ·
    refine ⟨2331007434965976611324977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3108009913287968815099969 2331007434965976611324977)
    ·
      refine ⟨1748255576224482458493733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2331007434965976611324977 1748255576224482458493733)
      ·
        refine ⟨327797920542090460967575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1748255576224482458493733 327797920542090460967575)
        ·
          refine ⟨491696880813135691451363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 327797920542090460967575 491696880813135691451363)
          ·
            refine ⟨737545321219703537177045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 491696880813135691451363 737545321219703537177045)
            ·
              refine ⟨17286218466086801652587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 737545321219703537177045 17286218466086801652587)
              ·
                rfl

theorem cell19_170428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 7].length) (baseStart_170428 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_170428 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_170428 prefixEnd_170428 := by exact prefixLift 170428
  have htrace : WordTrace (prefixWord ++ tailWord_170428) baseStart_170428 baseEnd_170428 := by
    simpa [prefixWord, tailWord_170428, baseEnd_170428] using wordTrace_append hprefix tailTrace_170428
  have hstable : (prefixWord ++ tailWord_170428).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170428).length < 2 ^ (prefixWord ++ tailWord_170428).sum := by decide
  have hdescent : baseEnd_170428 < baseStart_170428 := by decide
  rcases family_descends (prefixWord ++ tailWord_170428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170485 : List Nat := [1, 3, 5, 1, 9]
def baseStart_170485 : Nat := 118140960795 + 170485 * 2 ^ 59
def prefixEnd_170485 : Nat := 4983230072969 + 3 ^ 40 * 170485 * 2
def baseEnd_170485 : Nat := 1921333319766709692257

theorem tailTrace_170485 : CollatzResearch.WordTrace tailWord_170485 prefixEnd_170485 1921333319766709692257 := by
  unfold tailWord_170485
  simp only [CollatzResearch.WordTrace]
  refine ⟨6218098787369436365024909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4145399191579624243349939 6218098787369436365024909)
  ·
    refine ⟨2331787045263538636884341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6218098787369436365024909 2331787045263538636884341)
    ·
      refine ⟨218605035493456747207907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2331787045263538636884341 218605035493456747207907)
      ·
        refine ⟨327907553240185120811861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218605035493456747207907 327907553240185120811861)
        ·
          refine ⟨1921333319766709692257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 327907553240185120811861 1921333319766709692257)
          ·
            rfl

theorem cell19_170485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 9].length) (baseStart_170485 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_170485 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_170485 prefixEnd_170485 := by exact prefixLift 170485
  have htrace : WordTrace (prefixWord ++ tailWord_170485) baseStart_170485 baseEnd_170485 := by
    simpa [prefixWord, tailWord_170485, baseEnd_170485] using wordTrace_append hprefix tailTrace_170485
  have hstable : (prefixWord ++ tailWord_170485).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170485).length < 2 ^ (prefixWord ++ tailWord_170485).sum := by decide
  have hdescent : baseEnd_170485 < baseStart_170485 := by decide
  rcases family_descends (prefixWord ++ tailWord_170485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170498 : List Nat := [3, 4, 1, 2, 3, 1, 1, 4]
def baseStart_170498 : Nat := 118140960795 + 170498 * 2 ^ 59
def prefixEnd_170498 : Nat := 4983230072969 + 3 ^ 40 * 170498 * 2
def baseEnd_170498 : Nat := 51879955336520983402015

theorem tailTrace_170498 : CollatzResearch.WordTrace tailWord_170498 prefixEnd_170498 51879955336520983402015 := by
  unfold tailWord_170498
  simp only [CollatzResearch.WordTrace]
  refine ⟨1554643234080584896312037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4145715290881559723498765 1554643234080584896312037)
  ·
    refine ⟨291495606390109668058507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1554643234080584896312037 291495606390109668058507)
    ·
      refine ⟨437243409585164502087761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 291495606390109668058507 437243409585164502087761)
      ·
        refine ⟨327932557188873376565821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 437243409585164502087761 327932557188873376565821)
        ·
          refine ⟨122974708945827516212183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 327932557188873376565821 122974708945827516212183)
          ·
            refine ⟨184462063418741274318275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122974708945827516212183 184462063418741274318275)
            ·
              refine ⟨276693095128111911477413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 184462063418741274318275 276693095128111911477413)
              ·
                refine ⟨51879955336520983402015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 276693095128111911477413 51879955336520983402015)
                ·
                  rfl

theorem cell19_170498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 1, 4].length) (baseStart_170498 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_170498 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_170498 prefixEnd_170498 := by exact prefixLift 170498
  have htrace : WordTrace (prefixWord ++ tailWord_170498) baseStart_170498 baseEnd_170498 := by
    simpa [prefixWord, tailWord_170498, baseEnd_170498] using wordTrace_append hprefix tailTrace_170498
  have hstable : (prefixWord ++ tailWord_170498).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170498).length < 2 ^ (prefixWord ++ tailWord_170498).sum := by decide
  have hdescent : baseEnd_170498 < baseStart_170498 := by decide
  rcases family_descends (prefixWord ++ tailWord_170498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170519 : List Nat := [1, 1, 3, 6, 1, 1, 3, 3]
def baseStart_170519 : Nat := 118140960795 + 170519 * 2 ^ 59
def prefixEnd_170519 : Nat := 4983230072969 + 3 ^ 40 * 170519 * 2
def baseEnd_170519 : Nat := 51886345317999156935291

theorem tailTrace_170519 : CollatzResearch.WordTrace tailWord_170519 prefixEnd_170519 51886345317999156935291 := by
  unfold tailWord_170519
  simp only [CollatzResearch.WordTrace]
  refine ⟨6219338869246260171762611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4146225912830840114508407 6219338869246260171762611)
  ·
    refine ⟨9329008303869390257643917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6219338869246260171762611 9329008303869390257643917)
    ·
      refine ⟨3498378113951021346616469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9329008303869390257643917 3498378113951021346616469)
      ·
        refine ⟨163986474091454125622647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 3498378113951021346616469 163986474091454125622647)
        ·
          refine ⟨245979711137181188433971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163986474091454125622647 245979711137181188433971)
          ·
            refine ⟨368969566705771782650957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 245979711137181188433971 368969566705771782650957)
            ·
              refine ⟨138363587514664418494109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 368969566705771782650957 138363587514664418494109)
              ·
                refine ⟨51886345317999156935291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 138363587514664418494109 51886345317999156935291)
                ·
                  rfl

theorem cell19_170519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 3, 3].length) (baseStart_170519 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_170519 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_170519 prefixEnd_170519 := by exact prefixLift 170519
  have htrace : WordTrace (prefixWord ++ tailWord_170519) baseStart_170519 baseEnd_170519 := by
    simpa [prefixWord, tailWord_170519, baseEnd_170519] using wordTrace_append hprefix tailTrace_170519
  have hstable : (prefixWord ++ tailWord_170519).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170519).length < 2 ^ (prefixWord ++ tailWord_170519).sum := by decide
  have hdescent : baseEnd_170519 < baseStart_170519 := by decide
  rcases family_descends (prefixWord ++ tailWord_170519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170580 : List Nat := [2, 4, 1, 1, 1, 4, 1, 5]
def baseStart_170580 : Nat := 118140960795 + 170580 * 2 ^ 59
def prefixEnd_170580 : Nat := 4983230072969 + 3 ^ 40 * 170580 * 2
def baseEnd_170580 : Nat := 51904906692769089579569

theorem tailTrace_170580 : CollatzResearch.WordTrace tailWord_170580 prefixEnd_170580 51904906692769089579569 := by
  unfold tailWord_170580
  simp only [CollatzResearch.WordTrace]
  refine ⟨3110781861012633794866597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4147709148016845059822129 3110781861012633794866597)
  ·
    refine ⟨583271598939868836537487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3110781861012633794866597 583271598939868836537487)
    ·
      refine ⟨874907398409803254806231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 583271598939868836537487 874907398409803254806231)
      ·
        refine ⟨1312361097614704882209347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 874907398409803254806231 1312361097614704882209347)
        ·
          refine ⟨1968541646422057323314021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1312361097614704882209347 1968541646422057323314021)
          ·
            refine ⟨369101558704135748121379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1968541646422057323314021 369101558704135748121379)
            ·
              refine ⟨553652338056203622182069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 369101558704135748121379 553652338056203622182069)
              ·
                refine ⟨51904906692769089579569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 553652338056203622182069 51904906692769089579569)
                ·
                  rfl

theorem cell19_170580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 5].length) (baseStart_170580 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_170580 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_170580 prefixEnd_170580 := by exact prefixLift 170580
  have htrace : WordTrace (prefixWord ++ tailWord_170580) baseStart_170580 baseEnd_170580 := by
    simpa [prefixWord, tailWord_170580, baseEnd_170580] using wordTrace_append hprefix tailTrace_170580
  have hstable : (prefixWord ++ tailWord_170580).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170580).length < 2 ^ (prefixWord ++ tailWord_170580).sum := by decide
  have hdescent : baseEnd_170580 < baseStart_170580 := by decide
  rcases family_descends (prefixWord ++ tailWord_170580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170597 : List Nat := [1, 3, 1, 3, 5, 1, 5]
def baseStart_170597 : Nat := 118140960795 + 170597 * 2 ^ 59
def prefixEnd_170597 : Nat := 4983230072969 + 3 ^ 40 * 170597 * 2
def baseEnd_170597 : Nat := 17303359844972695733915

theorem tailTrace_170597 : CollatzResearch.WordTrace tailWord_170597 prefixEnd_170597 17303359844972695733915 := by
  unfold tailWord_170597
  simp only [CollatzResearch.WordTrace]
  refine ⟨6222183762963679493102045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4148122508642452995401363 6222183762963679493102045)
  ·
    refine ⟨2333318911111379809913267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6222183762963679493102045 2333318911111379809913267)
    ·
      refine ⟨3499978366667069714869901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2333318911111379809913267 3499978366667069714869901)
      ·
        refine ⟨1312491887500151143076213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3499978366667069714869901 1312491887500151143076213)
        ·
          refine ⟨123046114453139169663395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1312491887500151143076213 123046114453139169663395)
          ·
            refine ⟨184569171679708754495093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123046114453139169663395 184569171679708754495093)
            ·
              refine ⟨17303359844972695733915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 184569171679708754495093 17303359844972695733915)
              ·
                rfl

theorem cell19_170597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 5].length) (baseStart_170597 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_170597 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_170597 prefixEnd_170597 := by exact prefixLift 170597
  have htrace : WordTrace (prefixWord ++ tailWord_170597) baseStart_170597 baseEnd_170597 := by
    simpa [prefixWord, tailWord_170597, baseEnd_170597] using wordTrace_append hprefix tailTrace_170597
  have hstable : (prefixWord ++ tailWord_170597).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170597).length < 2 ^ (prefixWord ++ tailWord_170597).sum := by decide
  have hdescent : baseEnd_170597 < baseStart_170597 := by decide
  rcases family_descends (prefixWord ++ tailWord_170597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170620 : List Nat := [2, 2, 2, 1, 1, 2, 3, 6]
def baseStart_170620 : Nat := 118140960795 + 170620 * 2 ^ 59
def prefixEnd_170620 : Nat := 4983230072969 + 3 ^ 40 * 170620 * 2
def baseEnd_170620 : Nat := 51917078086060848690571

theorem tailTrace_170620 : CollatzResearch.WordTrace tailWord_170620 prefixEnd_170620 51917078086060848690571 := by
  unfold tailWord_170620
  simp only [CollatzResearch.WordTrace]
  refine ⟨3111511320940177210594657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4148681761253569614126209 3111511320940177210594657)
  ·
    refine ⟨2333633490705132907945993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3111511320940177210594657 2333633490705132907945993)
    ·
      refine ⟨1750225118028849680959495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2333633490705132907945993 1750225118028849680959495)
      ·
        refine ⟨2625337677043274521439243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1750225118028849680959495 2625337677043274521439243)
        ·
          refine ⟨3938006515564911782158865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2625337677043274521439243 3938006515564911782158865)
          ·
            refine ⟨2953504886673683836619149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3938006515564911782158865 2953504886673683836619149)
            ·
              refine ⟨1107564332502631438732181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2953504886673683836619149 1107564332502631438732181)
              ·
                refine ⟨51917078086060848690571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1107564332502631438732181 51917078086060848690571)
                ·
                  rfl

theorem cell19_170620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 6].length) (baseStart_170620 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_170620 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_170620 prefixEnd_170620 := by exact prefixLift 170620
  have htrace : WordTrace (prefixWord ++ tailWord_170620) baseStart_170620 baseEnd_170620 := by
    simpa [prefixWord, tailWord_170620, baseEnd_170620] using wordTrace_append hprefix tailTrace_170620
  have hstable : (prefixWord ++ tailWord_170620).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170620).length < 2 ^ (prefixWord ++ tailWord_170620).sum := by decide
  have hdescent : baseEnd_170620 < baseStart_170620 := by decide
  rcases family_descends (prefixWord ++ tailWord_170620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170656 : List Nat := [2, 1, 1, 4, 5, 6]
def baseStart_170656 : Nat := 118140960795 + 170656 * 2 ^ 59
def prefixEnd_170656 : Nat := 4983230072969 + 3 ^ 40 * 170656 * 2
def baseEnd_170656 : Nat := 5769781371113714654497

theorem tailTrace_170656 : CollatzResearch.WordTrace tailWord_170656 prefixEnd_170656 5769781371113714654497 := by
  unfold tailWord_170656
  simp only [CollatzResearch.WordTrace]
  refine ⟨3112167834874966284749911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4149557113166621712999881 3112167834874966284749911)
  ·
    refine ⟨4668251752312449427124867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3112167834874966284749911 4668251752312449427124867)
    ·
      refine ⟨7002377628468674140687301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4668251752312449427124867 7002377628468674140687301)
      ·
        refine ⟨1312945805337876401378869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7002377628468674140687301 1312945805337876401378869)
        ·
          refine ⟨123088669250425912629269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1312945805337876401378869 123088669250425912629269)
          ·
            refine ⟨5769781371113714654497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 123088669250425912629269 5769781371113714654497)
            ·
              rfl

theorem cell19_170656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 6].length) (baseStart_170656 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_170656 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_170656 prefixEnd_170656 := by exact prefixLift 170656
  have htrace : WordTrace (prefixWord ++ tailWord_170656) baseStart_170656 baseEnd_170656 := by
    simpa [prefixWord, tailWord_170656, baseEnd_170656] using wordTrace_append hprefix tailTrace_170656
  have hstable : (prefixWord ++ tailWord_170656).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170656).length < 2 ^ (prefixWord ++ tailWord_170656).sum := by decide
  have hdescent : baseEnd_170656 < baseStart_170656 := by decide
  rcases family_descends (prefixWord ++ tailWord_170656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170658 : List Nat := [3, 3, 1, 12]
def baseStart_170658 : Nat := 118140960795 + 170658 * 2 ^ 59
def prefixEnd_170658 : Nat := 4983230072969 + 3 ^ 40 * 170658 * 2
def baseEnd_170658 : Nat := 641094332218370615383

theorem tailTrace_170658 : CollatzResearch.WordTrace tailWord_170658 prefixEnd_170658 641094332218370615383 := by
  unfold tailWord_170658
  simp only [CollatzResearch.WordTrace]
  refine ⟨1556102153935671727768157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4149605743828457940715085 1556102153935671727768157)
  ·
    refine ⟨583538307725876897913059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1556102153935671727768157 583538307725876897913059)
    ·
      refine ⟨875307461588815346869589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 583538307725876897913059 875307461588815346869589)
      ·
        refine ⟨641094332218370615383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 12 875307461588815346869589 641094332218370615383)
        ·
          rfl

theorem cell19_170658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 12].length) (baseStart_170658 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_170658 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_170658 prefixEnd_170658 := by exact prefixLift 170658
  have htrace : WordTrace (prefixWord ++ tailWord_170658) baseStart_170658 baseEnd_170658 := by
    simpa [prefixWord, tailWord_170658, baseEnd_170658] using wordTrace_append hprefix tailTrace_170658
  have hstable : (prefixWord ++ tailWord_170658).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170658).length < 2 ^ (prefixWord ++ tailWord_170658).sum := by decide
  have hdescent : baseEnd_170658 < baseStart_170658 := by decide
  rcases family_descends (prefixWord ++ tailWord_170658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170675 : List Nat := [1, 1, 1, 2, 3, 6, 1, 4]
def baseStart_170675 : Nat := 118140960795 + 170675 * 2 ^ 59
def prefixEnd_170675 : Nat := 4983230072969 + 3 ^ 40 * 170675 * 2
def baseEnd_170675 : Nat := 51933813751837017468199

theorem tailTrace_170675 : CollatzResearch.WordTrace tailWord_170675 prefixEnd_170675 51933813751837017468199 := by
  unfold tailWord_170675
  simp only [CollatzResearch.WordTrace]
  refine ⟨6225028656681098814441479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4150019104454065876294319 6225028656681098814441479)
  ·
    refine ⟨9337542985021648221662219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6225028656681098814441479 9337542985021648221662219)
    ·
      refine ⟨14006314477532472332493329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9337542985021648221662219 14006314477532472332493329)
      ·
        refine ⟨10504735858149354249369997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14006314477532472332493329 10504735858149354249369997)
        ·
          refine ⟨3939275946806007843513749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10504735858149354249369997 3939275946806007843513749)
          ·
            refine ⟨184653560006531617664707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 3939275946806007843513749 184653560006531617664707)
            ·
              refine ⟨276980340009797426497061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 184653560006531617664707 276980340009797426497061)
              ·
                refine ⟨51933813751837017468199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 276980340009797426497061 51933813751837017468199)
                ·
                  rfl

theorem cell19_170675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 1, 4].length) (baseStart_170675 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_170675 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_170675 prefixEnd_170675 := by exact prefixLift 170675
  have htrace : WordTrace (prefixWord ++ tailWord_170675) baseStart_170675 baseEnd_170675 := by
    simpa [prefixWord, tailWord_170675, baseEnd_170675] using wordTrace_append hprefix tailTrace_170675
  have hstable : (prefixWord ++ tailWord_170675).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170675).length < 2 ^ (prefixWord ++ tailWord_170675).sum := by decide
  have hdescent : baseEnd_170675 < baseStart_170675 := by decide
  rcases family_descends (prefixWord ++ tailWord_170675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170692 : List Nat := [2, 3, 3, 1, 1, 3, 3, 3]
def baseStart_170692 : Nat := 118140960795 + 170692 * 2 ^ 59
def prefixEnd_170692 : Nat := 4983230072969 + 3 ^ 40 * 170692 * 2
def baseEnd_170692 : Nat := 51938986593986015090375

theorem tailTrace_170692 : CollatzResearch.WordTrace tailWord_170692 prefixEnd_170692 51938986593986015090375 := by
  unfold tailWord_170692
  simp only [CollatzResearch.WordTrace]
  refine ⟨3112824348809755358905165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4150432465079673811873553 3112824348809755358905165)
  ·
    refine ⟨1167309130803658259589437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3112824348809755358905165 1167309130803658259589437)
    ·
      refine ⟨437740924051371847346039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1167309130803658259589437 437740924051371847346039)
      ·
        refine ⟨656611386077057771019059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 437740924051371847346039 656611386077057771019059)
        ·
          refine ⟨984917079115586656528589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 656611386077057771019059 984917079115586656528589)
          ·
            refine ⟨369343904668344996198221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 984917079115586656528589 369343904668344996198221)
            ·
              refine ⟨138503964250629373574333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 369343904668344996198221 138503964250629373574333)
              ·
                refine ⟨51938986593986015090375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 138503964250629373574333 51938986593986015090375)
                ·
                  rfl

theorem cell19_170692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 3, 3].length) (baseStart_170692 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_170692 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_170692 prefixEnd_170692 := by exact prefixLift 170692
  have htrace : WordTrace (prefixWord ++ tailWord_170692) baseStart_170692 baseEnd_170692 := by
    simpa [prefixWord, tailWord_170692, baseEnd_170692] using wordTrace_append hprefix tailTrace_170692
  have hstable : (prefixWord ++ tailWord_170692).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170692).length < 2 ^ (prefixWord ++ tailWord_170692).sum := by decide
  have hdescent : baseEnd_170692 < baseStart_170692 := by decide
  rcases family_descends (prefixWord ++ tailWord_170692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170844 : List Nat := [2, 2, 4, 2, 1, 3, 1, 4]
def baseStart_170844 : Nat := 118140960795 + 170844 * 2 ^ 59
def prefixEnd_170844 : Nat := 4983230072969 + 3 ^ 40 * 170844 * 2
def baseEnd_170844 : Nat := 51985237888494699712183

theorem tailTrace_170844 : CollatzResearch.WordTrace tailWord_170844 prefixEnd_170844 51985237888494699712183 := by
  unfold tailWord_170844
  simp only [CollatzResearch.WordTrace]
  refine ⟨3115596296534420338671793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4154128395379227118229057 3115596296534420338671793)
  ·
    refine ⟨2336697222400815254003845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3115596296534420338671793 2336697222400815254003845)
    ·
      refine ⟨438130729200152860125721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2336697222400815254003845 438130729200152860125721)
      ·
        refine ⟨328598046900114645094291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 438130729200152860125721 328598046900114645094291)
        ·
          refine ⟨492897070350171967641437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 328598046900114645094291 492897070350171967641437)
          ·
            refine ⟨184836401381314487865539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 492897070350171967641437 184836401381314487865539)
            ·
              refine ⟨277254602071971731798309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 184836401381314487865539 277254602071971731798309)
              ·
                refine ⟨51985237888494699712183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 277254602071971731798309 51985237888494699712183)
                ·
                  rfl

theorem cell19_170844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 1, 4].length) (baseStart_170844 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_170844 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_170844 prefixEnd_170844 := by exact prefixLift 170844
  have htrace : WordTrace (prefixWord ++ tailWord_170844) baseStart_170844 baseEnd_170844 := by
    simpa [prefixWord, tailWord_170844, baseEnd_170844] using wordTrace_append hprefix tailTrace_170844
  have hstable : (prefixWord ++ tailWord_170844).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170844).length < 2 ^ (prefixWord ++ tailWord_170844).sum := by decide
  have hdescent : baseEnd_170844 < baseStart_170844 := by decide
  rcases family_descends (prefixWord ++ tailWord_170844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170865 : List Nat := [1, 2, 2, 2, 1, 5, 3, 3]
def baseStart_170865 : Nat := 118140960795 + 170865 * 2 ^ 59
def prefixEnd_170865 : Nat := 4983230072969 + 3 ^ 40 * 170865 * 2
def baseEnd_170865 : Nat := 51991627869972873245459

theorem tailTrace_170865 : CollatzResearch.WordTrace tailWord_170865 prefixEnd_170865 51991627869972873245459 := by
  unfold tailWord_170865
  simp only [CollatzResearch.WordTrace]
  refine ⟨6231958525992761263858049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4154639017328507509238699 6231958525992761263858049)
  ·
    refine ⟨4673968894494570947893537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6231958525992761263858049 4673968894494570947893537)
    ·
      refine ⟨3505476670870928210920153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4673968894494570947893537 3505476670870928210920153)
      ·
        refine ⟨2629107503153196158190115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3505476670870928210920153 2629107503153196158190115)
        ·
          refine ⟨3943661254729794237285173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2629107503153196158190115 3943661254729794237285173)
          ·
            refine ⟨369718242630918209745485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3943661254729794237285173 369718242630918209745485)
            ·
              refine ⟨138644340986594328654557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 369718242630918209745485 138644340986594328654557)
              ·
                refine ⟨51991627869972873245459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 138644340986594328654557 51991627869972873245459)
                ·
                  rfl

theorem cell19_170865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 3, 3].length) (baseStart_170865 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_170865 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_170865 prefixEnd_170865 := by exact prefixLift 170865
  have htrace : WordTrace (prefixWord ++ tailWord_170865) baseStart_170865 baseEnd_170865 := by
    simpa [prefixWord, tailWord_170865, baseEnd_170865] using wordTrace_append hprefix tailTrace_170865
  have hstable : (prefixWord ++ tailWord_170865).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170865).length < 2 ^ (prefixWord ++ tailWord_170865).sum := by decide
  have hdescent : baseEnd_170865 < baseStart_170865 := by decide
  rcases family_descends (prefixWord ++ tailWord_170865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170941 : List Nat := [1, 4, 1, 2, 4, 2, 5]
def baseStart_170941 : Nat := 118140960795 + 170941 * 2 ^ 59
def prefixEnd_170941 : Nat := 4983230072969 + 3 ^ 40 * 170941 * 2
def baseEnd_170941 : Nat := 17338251172409071852121

theorem tailTrace_170941 : CollatzResearch.WordTrace tailWord_170941 prefixEnd_170941 17338251172409071852121 := by
  unfold tailWord_170941
  simp only [CollatzResearch.WordTrace]
  refine ⟨6234730473717426243624677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4156486982478284162416451 6234730473717426243624677)
  ·
    refine ⟨1169011963822017420679627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6234730473717426243624677 1169011963822017420679627)
    ·
      refine ⟨1753517945733026131019441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1169011963822017420679627 1753517945733026131019441)
      ·
        refine ⟨1315138459299769598264581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1753517945733026131019441 1315138459299769598264581)
        ·
          refine ⟨246588461118706799674609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1315138459299769598264581 246588461118706799674609)
          ·
            refine ⟨184941345839030099755957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 246588461118706799674609 184941345839030099755957)
            ·
              refine ⟨17338251172409071852121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 184941345839030099755957 17338251172409071852121)
              ·
                rfl

theorem cell19_170941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 5].length) (baseStart_170941 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_170941 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_170941 prefixEnd_170941 := by exact prefixLift 170941
  have htrace : WordTrace (prefixWord ++ tailWord_170941) baseStart_170941 baseEnd_170941 := by
    simpa [prefixWord, tailWord_170941, baseEnd_170941] using wordTrace_append hprefix tailTrace_170941
  have hstable : (prefixWord ++ tailWord_170941).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170941).length < 2 ^ (prefixWord ++ tailWord_170941).sum := by decide
  have hdescent : baseEnd_170941 < baseStart_170941 := by decide
  rcases family_descends (prefixWord ++ tailWord_170941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171019 : List Nat := [1, 1, 1, 1, 6, 2, 3, 4]
def baseStart_171019 : Nat := 118140960795 + 171019 * 2 ^ 59
def prefixEnd_171019 : Nat := 4983230072969 + 3 ^ 40 * 171019 * 2
def baseEnd_171019 : Nat := 52038487734146145822817

theorem tailTrace_171019 : CollatzResearch.WordTrace tailWord_171019 prefixEnd_171019 52038487734146145822817 := by
  unfold tailWord_171019
  simp only [CollatzResearch.WordTrace]
  refine ⟨6237575367434845564964111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4158383578289897043309407 6237575367434845564964111)
  ·
    refine ⟨9356363051152268347446167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6237575367434845564964111 9356363051152268347446167)
    ·
      refine ⟨14034544576728402521169251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9356363051152268347446167 14034544576728402521169251)
      ·
        refine ⟨21051816865092603781753877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14034544576728402521169251 21051816865092603781753877)
        ·
          refine ⟨986803915551215802269713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 21051816865092603781753877 986803915551215802269713)
          ·
            refine ⟨740102936663411851702285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 986803915551215802269713 740102936663411851702285)
            ·
              refine ⟨277538601248779444388357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 740102936663411851702285 277538601248779444388357)
              ·
                refine ⟨52038487734146145822817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 277538601248779444388357 52038487734146145822817)
                ·
                  rfl

theorem cell19_171019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 3, 4].length) (baseStart_171019 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_171019 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_171019 prefixEnd_171019 := by exact prefixLift 171019
  have htrace : WordTrace (prefixWord ++ tailWord_171019) baseStart_171019 baseEnd_171019 := by
    simpa [prefixWord, tailWord_171019, baseEnd_171019] using wordTrace_append hprefix tailTrace_171019
  have hstable : (prefixWord ++ tailWord_171019).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171019).length < 2 ^ (prefixWord ++ tailWord_171019).sum := by decide
  have hdescent : baseEnd_171019 < baseStart_171019 := by decide
  rcases family_descends (prefixWord ++ tailWord_171019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171114 : List Nat := [3, 1, 3, 2, 2, 1, 7]
def baseStart_171114 : Nat := 118140960795 + 171114 * 2 ^ 59
def prefixEnd_171114 : Nat := 4983230072969 + 3 ^ 40 * 171114 * 2
def baseEnd_171114 : Nat := 17355798264404691237149

theorem tailTrace_171114 : CollatzResearch.WordTrace tailWord_171114 prefixEnd_171114 17355798264404691237149 := by
  unfold tailWord_171114
  simp only [CollatzResearch.WordTrace]
  refine ⟨1560260075522669197418099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4160693534727117859781597 1560260075522669197418099)
  ·
    refine ⟨2340390113284003796127149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1560260075522669197418099 2340390113284003796127149)
    ·
      refine ⟨877646292481501423547681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2340390113284003796127149 877646292481501423547681)
      ·
        refine ⟨658234719361126067660761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 877646292481501423547681 658234719361126067660761)
        ·
          refine ⟨493676039520844550745571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 658234719361126067660761 493676039520844550745571)
          ·
            refine ⟨740514059281266826118357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 493676039520844550745571 740514059281266826118357)
            ·
              refine ⟨17355798264404691237149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 740514059281266826118357 17355798264404691237149)
              ·
                rfl

theorem cell19_171114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 7].length) (baseStart_171114 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_171114 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_171114 prefixEnd_171114 := by exact prefixLift 171114
  have htrace : WordTrace (prefixWord ++ tailWord_171114) baseStart_171114 baseEnd_171114 := by
    simpa [prefixWord, tailWord_171114, baseEnd_171114] using wordTrace_append hprefix tailTrace_171114
  have hstable : (prefixWord ++ tailWord_171114).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171114).length < 2 ^ (prefixWord ++ tailWord_171114).sum := by decide
  have hdescent : baseEnd_171114 < baseStart_171114 := by decide
  rcases family_descends (prefixWord ++ tailWord_171114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171133 : List Nat := [1, 4, 1, 1, 3, 1, 4, 4]
def baseStart_171133 : Nat := 118140960795 + 171133 * 2 ^ 59
def prefixEnd_171133 : Nat := 4983230072969 + 3 ^ 40 * 171133 * 2
def baseEnd_171133 : Nat := 52073176205027659289173

theorem tailTrace_171133 : CollatzResearch.WordTrace tailWord_171133 prefixEnd_171133 52073176205027659289173 := by
  unfold tailWord_171133
  simp only [CollatzResearch.WordTrace]
  refine ⟨6241733289021843034614053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4161155526014562023076035 6241733289021843034614053)
  ·
    refine ⟨1170324991691595568990135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6241733289021843034614053 1170324991691595568990135)
    ·
      refine ⟨1755487487537393353485203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1170324991691595568990135 1755487487537393353485203)
      ·
        refine ⟨2633231231306090030227805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1755487487537393353485203 2633231231306090030227805)
        ·
          refine ⟨987461711739783761335427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2633231231306090030227805 987461711739783761335427)
          ·
            refine ⟨1481192567609675642003141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 987461711739783761335427 1481192567609675642003141)
            ·
              refine ⟨277723606426814182875589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1481192567609675642003141 277723606426814182875589)
              ·
                refine ⟨52073176205027659289173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 277723606426814182875589 52073176205027659289173)
                ·
                  rfl

theorem cell19_171133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 4, 4].length) (baseStart_171133 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_171133 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_171133 prefixEnd_171133 := by exact prefixLift 171133
  have htrace : WordTrace (prefixWord ++ tailWord_171133) baseStart_171133 baseEnd_171133 := by
    simpa [prefixWord, tailWord_171133, baseEnd_171133] using wordTrace_append hprefix tailTrace_171133
  have hstable : (prefixWord ++ tailWord_171133).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171133).length < 2 ^ (prefixWord ++ tailWord_171133).sum := by decide
  have hdescent : baseEnd_171133 < baseStart_171133 := by decide
  rcases family_descends (prefixWord ++ tailWord_171133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171173 : List Nat := [1, 3, 1, 2, 1, 11]
def baseStart_171173 : Nat := 118140960795 + 171173 * 2 ^ 59
def prefixEnd_171173 : Nat := 4983230072969 + 3 ^ 40 * 171173 * 2
def baseEnd_171173 : Nat := 5787260844257713155575

theorem tailTrace_171173 : CollatzResearch.WordTrace tailWord_171173 prefixEnd_171173 5787260844257713155575 := by
  unfold tailWord_171173
  simp only [CollatzResearch.WordTrace]
  refine ⟨6243192208876929866070173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4162128139251286577380115 6243192208876929866070173)
  ·
    refine ⟨2341197078328848699776315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6243192208876929866070173 2341197078328848699776315)
    ·
      refine ⟨3511795617493273049664473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2341197078328848699776315 3511795617493273049664473)
      ·
        refine ⟨2633846713119954787248355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3511795617493273049664473 2633846713119954787248355)
        ·
          refine ⟨3950770069679932180872533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2633846713119954787248355 3950770069679932180872533)
          ·
            refine ⟨5787260844257713155575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 3950770069679932180872533 5787260844257713155575)
            ·
              rfl

theorem cell19_171173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 11].length) (baseStart_171173 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_171173 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_171173 prefixEnd_171173 := by exact prefixLift 171173
  have htrace : WordTrace (prefixWord ++ tailWord_171173) baseStart_171173 baseEnd_171173 := by
    simpa [prefixWord, tailWord_171173, baseEnd_171173] using wordTrace_append hprefix tailTrace_171173
  have hstable : (prefixWord ++ tailWord_171173).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171173).length < 2 ^ (prefixWord ++ tailWord_171173).sum := by decide
  have hdescent : baseEnd_171173 < baseStart_171173 := by decide
  rcases family_descends (prefixWord ++ tailWord_171173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171192 : List Nat := [2, 1, 2, 1, 2, 1, 2, 8]
def baseStart_171192 : Nat := 118140960795 + 171192 * 2 ^ 59
def prefixEnd_171192 : Nat := 4983230072969 + 3 ^ 40 * 171192 * 2
def baseEnd_171192 : Nat := 52091129010133003977901

theorem tailTrace_171192 : CollatzResearch.WordTrace tailWord_171192 prefixEnd_171192 52091129010133003977901 := by
  unfold tailWord_171192
  simp only [CollatzResearch.WordTrace]
  refine ⟨3121942597904048055505915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4162590130538730740674553 3121942597904048055505915)
  ·
    refine ⟨4682913896856072083258873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3121942597904048055505915 4682913896856072083258873)
    ·
      refine ⟨3512185422642054062444155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4682913896856072083258873 3512185422642054062444155)
      ·
        refine ⟨5268278133963081093666233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3512185422642054062444155 5268278133963081093666233)
        ·
          refine ⟨3951208600472310820249675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5268278133963081093666233 3951208600472310820249675)
          ·
            refine ⟨5926812900708466230374513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3951208600472310820249675 5926812900708466230374513)
            ·
              refine ⟨4445109675531349672780885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5926812900708466230374513 4445109675531349672780885)
              ·
                refine ⟨52091129010133003977901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4445109675531349672780885 52091129010133003977901)
                ·
                  rfl

theorem cell19_171192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 8].length) (baseStart_171192 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_171192 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_171192 prefixEnd_171192 := by exact prefixLift 171192
  have htrace : WordTrace (prefixWord ++ tailWord_171192) baseStart_171192 baseEnd_171192 := by
    simpa [prefixWord, tailWord_171192, baseEnd_171192] using wordTrace_append hprefix tailTrace_171192
  have hstable : (prefixWord ++ tailWord_171192).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171192).length < 2 ^ (prefixWord ++ tailWord_171192).sum := by decide
  have hdescent : baseEnd_171192 < baseStart_171192 := by decide
  rcases family_descends (prefixWord ++ tailWord_171192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171249 : List Nat := [1, 2, 2, 2, 2, 1, 1, 8]
def baseStart_171249 : Nat := 118140960795 + 171249 * 2 ^ 59
def prefixEnd_171249 : Nat := 4983230072969 + 3 ^ 40 * 171249 * 2
def baseEnd_171249 : Nat := 52108473245573760711079

theorem tailTrace_171249 : CollatzResearch.WordTrace tailWord_171249 prefixEnd_171249 52108473245573760711079 := by
  unfold tailWord_171249
  simp only [CollatzResearch.WordTrace]
  refine ⟨6245964156601594845836801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4163976104401063230557867 6245964156601594845836801)
  ·
    refine ⟨4684473117451196134377601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6245964156601594845836801 4684473117451196134377601)
    ·
      refine ⟨3513354838088397100783201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4684473117451196134377601 3513354838088397100783201)
      ·
        refine ⟨2635016128566297825587401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3513354838088397100783201 2635016128566297825587401)
        ·
          refine ⟨1976262096424723369190551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2635016128566297825587401 1976262096424723369190551)
          ·
            refine ⟨2964393144637085053785827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1976262096424723369190551 2964393144637085053785827)
            ·
              refine ⟨4446589716955627580678741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2964393144637085053785827 4446589716955627580678741)
              ·
                refine ⟨52108473245573760711079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4446589716955627580678741 52108473245573760711079)
                ·
                  rfl

theorem cell19_171249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 8].length) (baseStart_171249 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_171249 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_171249 prefixEnd_171249 := by exact prefixLift 171249
  have htrace : WordTrace (prefixWord ++ tailWord_171249) baseStart_171249 baseEnd_171249 := by
    simpa [prefixWord, tailWord_171249, baseEnd_171249] using wordTrace_append hprefix tailTrace_171249
  have hstable : (prefixWord ++ tailWord_171249).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171249).length < 2 ^ (prefixWord ++ tailWord_171249).sum := by decide
  have hdescent : baseEnd_171249 < baseStart_171249 := by decide
  rcases family_descends (prefixWord ++ tailWord_171249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171262 : List Nat := [4, 2, 2, 1, 1, 4, 2, 3]
def baseStart_171262 : Nat := 118140960795 + 171262 * 2 ^ 59
def prefixEnd_171262 : Nat := 4983230072969 + 3 ^ 40 * 171262 * 2
def baseEnd_171262 : Nat := 52112428948393582422155

theorem tailTrace_171262 : CollatzResearch.WordTrace tailWord_171262 prefixEnd_171262 52112428948393582422155 := by
  unfold tailWord_171262
  simp only [CollatzResearch.WordTrace]
  refine ⟨780804788194312258257505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4164292203702998710706693 780804788194312258257505)
  ·
    refine ⟨585603591145734193693129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 780804788194312258257505 585603591145734193693129)
    ·
      refine ⟨439202693359300645269847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 585603591145734193693129 439202693359300645269847)
      ·
        refine ⟨658804040038950967904771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 439202693359300645269847 658804040038950967904771)
        ·
          refine ⟨988206060058426451857157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 658804040038950967904771 988206060058426451857157)
          ·
            refine ⟨185288636260954959723217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 988206060058426451857157 185288636260954959723217)
            ·
              refine ⟨138966477195716219792413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 185288636260954959723217 138966477195716219792413)
              ·
                refine ⟨52112428948393582422155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 138966477195716219792413 52112428948393582422155)
                ·
                  rfl

theorem cell19_171262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 2, 3].length) (baseStart_171262 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_171262 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_171262 prefixEnd_171262 := by exact prefixLift 171262
  have htrace : WordTrace (prefixWord ++ tailWord_171262) baseStart_171262 baseEnd_171262 := by
    simpa [prefixWord, tailWord_171262, baseEnd_171262] using wordTrace_append hprefix tailTrace_171262
  have hstable : (prefixWord ++ tailWord_171262).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171262).length < 2 ^ (prefixWord ++ tailWord_171262).sum := by decide
  have hdescent : baseEnd_171262 < baseStart_171262 := by decide
  rcases family_descends (prefixWord ++ tailWord_171262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan19Incremental
