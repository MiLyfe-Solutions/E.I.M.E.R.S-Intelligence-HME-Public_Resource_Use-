import V185TrunkScan23Chunk1340

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7942200 : List Nat := [2, 1, 2, 1, 6, 1, 1, 1, 3, 5]
def baseStart_7942200 : Nat := 118140960795 + 7942200 * 2 ^ 59
def prefixEnd_7942200 : Nat := 4983230072969 + 3 ^ 40 * 7942200 * 2
def baseEnd_7942200 : Nat := 1359388684712977113224831

theorem tailTrace_7942200 : CollatzResearch.WordTrace tailWord_7942200 prefixEnd_7942200 1359388684712977113224831 := by
  unfold tailWord_7942200
  simp only [CollatzResearch.WordTrace]
  refine ⟨144837915913386647307508027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193117221217848863076677369 144837915913386647307508027)
  ·
    refine ⟨217256873870079970961262041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144837915913386647307508027 217256873870079970961262041)
    ·
      refine ⟨162942655402559978220946531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217256873870079970961262041 162942655402559978220946531)
      ·
        refine ⟨244413983103839967331419797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162942655402559978220946531 244413983103839967331419797)
        ·
          refine ⟨11456905457992498468660303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 244413983103839967331419797 11456905457992498468660303)
          ·
            refine ⟨17185358186988747702990455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11456905457992498468660303 17185358186988747702990455)
            ·
              refine ⟨25778037280483121554485683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17185358186988747702990455 25778037280483121554485683)
              ·
                refine ⟨38667055920724682331728525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25778037280483121554485683 38667055920724682331728525)
                ·
                  refine ⟨14500145970271755874398197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38667055920724682331728525 14500145970271755874398197)
                  ·
                    refine ⟨1359388684712977113224831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14500145970271755874398197 1359388684712977113224831)
                    ·
                      rfl

theorem cell23_7942200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 1, 3, 5].length) (baseStart_7942200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7942200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7942200 prefixEnd_7942200 := by exact prefixLift 7942200
  have htrace : WordTrace (prefixWord ++ tailWord_7942200) baseStart_7942200 baseEnd_7942200 := by
    simpa [prefixWord, tailWord_7942200, baseEnd_7942200] using wordTrace_append hprefix tailTrace_7942200
  have hstable : (prefixWord ++ tailWord_7942200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7942200).length < 2 ^ (prefixWord ++ tailWord_7942200).sum := by decide
  have hdescent : baseEnd_7942200 < baseStart_7942200 := by decide
  rcases family_descends (prefixWord ++ tailWord_7942200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7942203 : List Nat := [1, 1, 1, 1, 1, 2, 1, 7, 3, 1, 4]
def baseStart_7942203 : Nat := 118140960795 + 7942203 * 2 ^ 59
def prefixEnd_7942203 : Nat := 4983230072969 + 3 ^ 40 * 7942203 * 2
def baseEnd_7942203 : Nat := 4078167594580894827936979

theorem tailTrace_7942203 : CollatzResearch.WordTrace tailWord_7942203 prefixEnd_7942203 4078167594580894827936979 := by
  unfold tailWord_7942203
  simp only [CollatzResearch.WordTrace]
  refine ⟨289675941245762426127375263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193117294163841617418250175 289675941245762426127375263)
  ·
    refine ⟨434513911868643639191062895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289675941245762426127375263 434513911868643639191062895)
    ·
      refine ⟨651770867802965458786594343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 434513911868643639191062895 651770867802965458786594343)
      ·
        refine ⟨977656301704448188179891515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 651770867802965458786594343 977656301704448188179891515)
        ·
          refine ⟨1466484452556672282269837273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 977656301704448188179891515 1466484452556672282269837273)
          ·
            refine ⟨1099863339417504211702377955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1466484452556672282269837273 1099863339417504211702377955)
            ·
              refine ⟨1649795009126256317553566933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1099863339417504211702377955 1649795009126256317553566933)
              ·
                refine ⟨38667070526396632442661725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1649795009126256317553566933 38667070526396632442661725)
                ·
                  refine ⟨14500151447398737165998147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38667070526396632442661725 14500151447398737165998147)
                  ·
                    refine ⟨21750227171098105748997221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14500151447398737165998147 21750227171098105748997221)
                    ·
                      refine ⟨4078167594580894827936979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21750227171098105748997221 4078167594580894827936979)
                      ·
                        rfl

theorem cell23_7942203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 7, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 7, 3, 1, 4].length) (baseStart_7942203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7942203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7942203 prefixEnd_7942203 := by exact prefixLift 7942203
  have htrace : WordTrace (prefixWord ++ tailWord_7942203) baseStart_7942203 baseEnd_7942203 := by
    simpa [prefixWord, tailWord_7942203, baseEnd_7942203] using wordTrace_append hprefix tailTrace_7942203
  have hstable : (prefixWord ++ tailWord_7942203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7942203).length < 2 ^ (prefixWord ++ tailWord_7942203).sum := by decide
  have hdescent : baseEnd_7942203 < baseStart_7942203 := by decide
  rcases family_descends (prefixWord ++ tailWord_7942203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7942220 : List Nat := [2, 2, 1, 3, 1, 1, 2, 5, 1, 1, 4]
def baseStart_7942220 : Nat := 118140960795 + 7942220 * 2 ^ 59
def prefixEnd_7942220 : Nat := 4983230072969 + 3 ^ 40 * 7942220 * 2
def baseEnd_7942220 : Nat := 4078176323752021261424401

theorem tailTrace_7942220 : CollatzResearch.WordTrace tailWord_7942220 prefixEnd_7942220 4078176323752021261424401 := by
  unfold tailWord_7942220
  simp only [CollatzResearch.WordTrace]
  refine ⟨144838280643350419015372057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193117707524467225353829409 144838280643350419015372057)
  ·
    refine ⟨108628710482512814261529043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144838280643350419015372057 108628710482512814261529043)
    ·
      refine ⟨162943065723769221392293565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108628710482512814261529043 162943065723769221392293565)
      ·
        refine ⟨61103649646413458022110087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162943065723769221392293565 61103649646413458022110087)
        ·
          refine ⟨91655474469620187033165131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61103649646413458022110087 91655474469620187033165131)
          ·
            refine ⟨137483211704430280549747697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91655474469620187033165131 137483211704430280549747697)
            ·
              refine ⟨103112408778322710412310773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137483211704430280549747697 103112408778322710412310773)
              ·
                refine ⟨9666788322967754101154135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 103112408778322710412310773 9666788322967754101154135)
                ·
                  refine ⟨14500182484451631151731203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9666788322967754101154135 14500182484451631151731203)
                  ·
                    refine ⟨21750273726677446727596805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14500182484451631151731203 21750273726677446727596805)
                    ·
                      refine ⟨4078176323752021261424401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21750273726677446727596805 4078176323752021261424401)
                      ·
                        rfl

theorem cell23_7942220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 5, 1, 1, 4].length) (baseStart_7942220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7942220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7942220 prefixEnd_7942220 := by exact prefixLift 7942220
  have htrace : WordTrace (prefixWord ++ tailWord_7942220) baseStart_7942220 baseEnd_7942220 := by
    simpa [prefixWord, tailWord_7942220, baseEnd_7942220] using wordTrace_append hprefix tailTrace_7942220
  have hstable : (prefixWord ++ tailWord_7942220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7942220).length < 2 ^ (prefixWord ++ tailWord_7942220).sum := by decide
  have hdescent : baseEnd_7942220 < baseStart_7942220 := by decide
  rcases family_descends (prefixWord ++ tailWord_7942220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7942233 : List Nat := [1, 2, 1, 2, 2, 1, 3, 2, 3, 2, 4]
def baseStart_7942233 : Nat := 118140960795 + 7942233 * 2 ^ 59
def prefixEnd_7942233 : Nat := 4983230072969 + 3 ^ 40 * 7942233 * 2
def baseEnd_7942233 : Nat := 4078182999000529710561841

theorem tailTrace_7942233 : CollatzResearch.WordTrace tailWord_7942233 prefixEnd_7942233 4078182999000529710561841 := by
  unfold tailWord_7942233
  simp only [CollatzResearch.WordTrace]
  refine ⟨289677035435653741250967353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193118023623769160833978235 289677035435653741250967353)
  ·
    refine ⟨217257776576740305938225515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289677035435653741250967353 217257776576740305938225515)
    ·
      refine ⟨325886664865110458907338273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217257776576740305938225515 325886664865110458907338273)
      ·
        refine ⟨244414998648832844180503705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 325886664865110458907338273 244414998648832844180503705)
        ·
          refine ⟨183311248986624633135377779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 244414998648832844180503705 183311248986624633135377779)
          ·
            refine ⟨274966873479936949703066669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183311248986624633135377779 274966873479936949703066669)
            ·
              refine ⟨103112577554976356138650001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 274966873479936949703066669 103112577554976356138650001)
              ·
                refine ⟨77334433166232267103987501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103112577554976356138650001 77334433166232267103987501)
                ·
                  refine ⟨29000412437337100163995313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77334433166232267103987501 29000412437337100163995313)
                  ·
                    refine ⟨21750309328002825122996485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29000412437337100163995313 21750309328002825122996485)
                    ·
                      refine ⟨4078182999000529710561841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21750309328002825122996485 4078182999000529710561841)
                      ·
                        rfl

theorem cell23_7942233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 2, 3, 2, 4].length) (baseStart_7942233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7942233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7942233 prefixEnd_7942233 := by exact prefixLift 7942233
  have htrace : WordTrace (prefixWord ++ tailWord_7942233) baseStart_7942233 baseEnd_7942233 := by
    simpa [prefixWord, tailWord_7942233, baseEnd_7942233] using wordTrace_append hprefix tailTrace_7942233
  have hstable : (prefixWord ++ tailWord_7942233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7942233).length < 2 ^ (prefixWord ++ tailWord_7942233).sum := by decide
  have hdescent : baseEnd_7942233 < baseStart_7942233 := by decide
  rcases family_descends (prefixWord ++ tailWord_7942233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7942237 : List Nat := [1, 4, 4, 1, 1, 1, 1, 2, 3, 1, 4]
def baseStart_7942237 : Nat := 118140960795 + 7942237 * 2 ^ 59
def prefixEnd_7942237 : Nat := 4983230072969 + 3 ^ 40 * 7942237 * 2
def baseEnd_7942237 : Nat := 4078185052923147694911823

theorem tailTrace_7942237 : CollatzResearch.WordTrace tailWord_7942237 prefixEnd_7942237 4078185052923147694911823 := by
  unfold tailWord_7942237
  simp only [CollatzResearch.WordTrace]
  refine ⟨289677181327639249934112965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193118120885092833289408643 289677181327639249934112965)
  ·
    refine ⟨54314471498932359362646181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 289677181327639249934112965 54314471498932359362646181)
    ·
      refine ⟨10183963406049817380496159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54314471498932359362646181 10183963406049817380496159)
      ·
        refine ⟨15275945109074726070744239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10183963406049817380496159 15275945109074726070744239)
        ·
          refine ⟨22913917663612089106116359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15275945109074726070744239 22913917663612089106116359)
          ·
            refine ⟨34370876495418133659174539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22913917663612089106116359 34370876495418133659174539)
            ·
              refine ⟨51556314743127200488761809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34370876495418133659174539 51556314743127200488761809)
              ·
                refine ⟨38667236057345400366571357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51556314743127200488761809 38667236057345400366571357)
                ·
                  refine ⟨14500213521504525137464259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38667236057345400366571357 14500213521504525137464259)
                  ·
                    refine ⟨21750320282256787706196389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14500213521504525137464259 21750320282256787706196389)
                    ·
                      refine ⟨4078185052923147694911823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21750320282256787706196389 4078185052923147694911823)
                      ·
                        rfl

theorem cell23_7942237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_7942237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7942237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7942237 prefixEnd_7942237 := by exact prefixLift 7942237
  have htrace : WordTrace (prefixWord ++ tailWord_7942237) baseStart_7942237 baseEnd_7942237 := by
    simpa [prefixWord, tailWord_7942237, baseEnd_7942237] using wordTrace_append hprefix tailTrace_7942237
  have hstable : (prefixWord ++ tailWord_7942237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7942237).length < 2 ^ (prefixWord ++ tailWord_7942237).sum := by decide
  have hdescent : baseEnd_7942237 < baseStart_7942237 := by decide
  rcases family_descends (prefixWord ++ tailWord_7942237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7942240 : List Nat := [2, 1, 1, 3, 2, 3, 1, 2, 3, 2, 3]
def baseStart_7942240 : Nat := 118140960795 + 7942240 * 2 ^ 59
def prefixEnd_7942240 : Nat := 4983230072969 + 3 ^ 40 * 7942240 * 2
def baseEnd_7942240 : Nat := 4078186593365111183174309

theorem tailTrace_7942240 : CollatzResearch.WordTrace tailWord_7942240 prefixEnd_7942240 4078186593365111183174309 := by
  unfold tailWord_7942240
  simp only [CollatzResearch.WordTrace]
  refine ⟨144838645373314190723236087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193118193831085587630981449 144838645373314190723236087)
  ·
    refine ⟨217257968059971286084854131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144838645373314190723236087 217257968059971286084854131)
    ·
      refine ⟨325886952089956929127281197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217257968059971286084854131 325886952089956929127281197)
      ·
        refine ⟨122207607033733848422730449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 325886952089956929127281197 122207607033733848422730449)
        ·
          refine ⟨91655705275300386317047837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122207607033733848422730449 91655705275300386317047837)
          ·
            refine ⟨34370889478237644868892939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91655705275300386317047837 34370889478237644868892939)
            ·
              refine ⟨51556334217356467303339409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34370889478237644868892939 51556334217356467303339409)
              ·
                refine ⟨38667250663017350477504557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51556334217356467303339409 38667250663017350477504557)
                ·
                  refine ⟨14500218998631506429064209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38667250663017350477504557 14500218998631506429064209)
                  ·
                    refine ⟨10875164248973629821798157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14500218998631506429064209 10875164248973629821798157)
                    ·
                      refine ⟨4078186593365111183174309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10875164248973629821798157 4078186593365111183174309)
                      ·
                        rfl

theorem cell23_7942240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 2, 3, 2, 3].length) (baseStart_7942240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7942240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7942240 prefixEnd_7942240 := by exact prefixLift 7942240
  have htrace : WordTrace (prefixWord ++ tailWord_7942240) baseStart_7942240 baseEnd_7942240 := by
    simpa [prefixWord, tailWord_7942240, baseEnd_7942240] using wordTrace_append hprefix tailTrace_7942240
  have hstable : (prefixWord ++ tailWord_7942240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7942240).length < 2 ^ (prefixWord ++ tailWord_7942240).sum := by decide
  have hdescent : baseEnd_7942240 < baseStart_7942240 := by decide
  rcases family_descends (prefixWord ++ tailWord_7942240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7942243 : List Nat := [1, 1, 1, 5, 1, 1, 5, 8]
def baseStart_7942243 : Nat := 118140960795 + 7942243 * 2 ^ 59
def prefixEnd_7942243 : Nat := 4983230072969 + 3 ^ 40 * 7942243 * 2
def baseEnd_7942243 : Nat := 151044004955817580423585

theorem tailTrace_7942243 : CollatzResearch.WordTrace tailWord_7942243 prefixEnd_7942243 151044004955817580423585 := by
  unfold tailWord_7942243
  simp only [CollatzResearch.WordTrace]
  refine ⟨289677400165617512958831383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193118266777078341972554255 289677400165617512958831383)
  ·
    refine ⟨434516100248426269438247075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289677400165617512958831383 434516100248426269438247075)
    ·
      refine ⟨651774150372639404157370613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 434516100248426269438247075 651774150372639404157370613)
      ·
        refine ⟨61103826597434944139753495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 651774150372639404157370613 61103826597434944139753495)
        ·
          refine ⟨91655739896152416209630243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61103826597434944139753495 91655739896152416209630243)
          ·
            refine ⟨137483609844228624314445365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91655739896152416209630243 137483609844228624314445365)
            ·
              refine ⟨12889088422896433529479253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 137483609844228624314445365 12889088422896433529479253)
              ·
                refine ⟨151044004955817580423585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12889088422896433529479253 151044004955817580423585)
                ·
                  rfl

theorem cell23_7942243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 5, 8].length) (baseStart_7942243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7942243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7942243 prefixEnd_7942243 := by exact prefixLift 7942243
  have htrace : WordTrace (prefixWord ++ tailWord_7942243) baseStart_7942243 baseEnd_7942243 := by
    simpa [prefixWord, tailWord_7942243, baseEnd_7942243] using wordTrace_append hprefix tailTrace_7942243
  have hstable : (prefixWord ++ tailWord_7942243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7942243).length < 2 ^ (prefixWord ++ tailWord_7942243).sum := by decide
  have hdescent : baseEnd_7942243 < baseStart_7942243 := by decide
  rcases family_descends (prefixWord ++ tailWord_7942243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7942254 : List Nat := [4, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2]
def baseStart_7942254 : Nat := 118140960795 + 7942254 * 2 ^ 59
def prefixEnd_7942254 : Nat := 4983230072969 + 3 ^ 40 * 7942254 * 2
def baseEnd_7942254 : Nat := 4078193782094274128399245

theorem tailTrace_7942254 : CollatzResearch.WordTrace tailWord_7942254 prefixEnd_7942254 4078193782094274128399245 := by
  unfold tailWord_7942254
  simp only [CollatzResearch.WordTrace]
  refine ⟨36209725171072207729685227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 193118534245718441224987877 36209725171072207729685227)
  ·
    refine ⟨54314587756608311594527841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36209725171072207729685227 54314587756608311594527841)
    ·
      refine ⟨40735940817456233695895881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54314587756608311594527841 40735940817456233695895881)
      ·
        refine ⟨30551955613092175271921911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40735940817456233695895881 30551955613092175271921911)
        ·
          refine ⟨45827933419638262907882867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30551955613092175271921911 45827933419638262907882867)
          ·
            refine ⟨68741900129457394361824301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45827933419638262907882867 68741900129457394361824301)
            ·
              refine ⟨25778212548546522885684113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68741900129457394361824301 25778212548546522885684113)
              ·
                refine ⟨19333659411409892164263085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25778212548546522885684113 19333659411409892164263085)
                ·
                  refine ⟨7250122279278709561598657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19333659411409892164263085 7250122279278709561598657)
                  ·
                    refine ⟨5437591709459032171198993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7250122279278709561598657 5437591709459032171198993)
                    ·
                      refine ⟨4078193782094274128399245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5437591709459032171198993 4078193782094274128399245)
                      ·
                        rfl

theorem cell23_7942254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2].length) (baseStart_7942254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7942254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7942254 prefixEnd_7942254 := by exact prefixLift 7942254
  have htrace : WordTrace (prefixWord ++ tailWord_7942254) baseStart_7942254 baseEnd_7942254 := by
    simpa [prefixWord, tailWord_7942254, baseEnd_7942254] using wordTrace_append hprefix tailTrace_7942254
  have hstable : (prefixWord ++ tailWord_7942254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7942254).length < 2 ^ (prefixWord ++ tailWord_7942254).sum := by decide
  have hdescent : baseEnd_7942254 < baseStart_7942254 := by decide
  rcases family_descends (prefixWord ++ tailWord_7942254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7942344 : List Nat := [2, 1, 3, 1, 2, 1, 1, 6, 2, 2, 2]
def baseStart_7942344 : Nat := 118140960795 + 7942344 * 2 ^ 59
def prefixEnd_7942344 : Nat := 4983230072969 + 3 ^ 40 * 7942344 * 2
def baseEnd_7942344 : Nat := 4078239995353178776273831

theorem tailTrace_7942344 : CollatzResearch.WordTrace tailWord_7942344 prefixEnd_7942344 4078239995353178776273831 := by
  unfold tailWord_7942344
  simp only [CollatzResearch.WordTrace]
  refine ⟨144840541969125803604129043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193120722625501071472172057 144840541969125803604129043)
  ·
    refine ⟨217260812953688705406193565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144840541969125803604129043 217260812953688705406193565)
    ·
      refine ⟨81472804857633264527322587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 217260812953688705406193565 81472804857633264527322587)
      ·
        refine ⟨122209207286449896790983881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81472804857633264527322587 122209207286449896790983881)
        ·
          refine ⟨91656905464837422593237911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122209207286449896790983881 91656905464837422593237911)
          ·
            refine ⟨137485358197256133889856867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91656905464837422593237911 137485358197256133889856867)
            ·
              refine ⟨206228037295884200834785301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137485358197256133889856867 206228037295884200834785301)
              ·
                refine ⟨9666939248244571914130561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 206228037295884200834785301 9666939248244571914130561)
                ·
                  refine ⟨7250204436183428935597921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9666939248244571914130561 7250204436183428935597921)
                  ·
                    refine ⟨5437653327137571701698441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7250204436183428935597921 5437653327137571701698441)
                    ·
                      refine ⟨4078239995353178776273831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5437653327137571701698441 4078239995353178776273831)
                      ·
                        rfl

theorem cell23_7942344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 6, 2, 2, 2].length) (baseStart_7942344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7942344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7942344 prefixEnd_7942344 := by exact prefixLift 7942344
  have htrace : WordTrace (prefixWord ++ tailWord_7942344) baseStart_7942344 baseEnd_7942344 := by
    simpa [prefixWord, tailWord_7942344, baseEnd_7942344] using wordTrace_append hprefix tailTrace_7942344
  have hstable : (prefixWord ++ tailWord_7942344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7942344).length < 2 ^ (prefixWord ++ tailWord_7942344).sum := by decide
  have hdescent : baseEnd_7942344 < baseStart_7942344 := by decide
  rcases family_descends (prefixWord ++ tailWord_7942344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7942361 : List Nat := [1, 2, 1, 2, 3, 1, 6, 1, 2, 2, 2]
def baseStart_7942361 : Nat := 118140960795 + 7942361 * 2 ^ 59
def prefixEnd_7942361 : Nat := 4983230072969 + 3 ^ 40 * 7942361 * 2
def baseEnd_7942361 : Nat := 4078248724524305209761253

theorem tailTrace_7942361 : CollatzResearch.WordTrace tailWord_7942361 prefixEnd_7942361 4078248724524305209761253 := by
  unfold tailWord_7942361
  simp only [CollatzResearch.WordTrace]
  refine ⟨289681703979190019111626937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193121135986126679407751291 289681703979190019111626937)
  ·
    refine ⟨217261277984392514333720203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289681703979190019111626937 217261277984392514333720203)
    ·
      refine ⟨325891916976588771500580305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217261277984392514333720203 325891916976588771500580305)
      ·
        refine ⟨244418937732441578625435229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 325891916976588771500580305 244418937732441578625435229)
        ·
          refine ⟨91657101649665591984538211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 244418937732441578625435229 91657101649665591984538211)
          ·
            refine ⟨137485652474498387976807317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91657101649665591984538211 137485652474498387976807317)
            ·
              refine ⟨6444639959742111936412843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 137485652474498387976807317 6444639959742111936412843)
              ·
                refine ⟨9666959939613167904619265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6444639959742111936412843 9666959939613167904619265)
                ·
                  refine ⟨7250219954709875928464449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9666959939613167904619265 7250219954709875928464449)
                  ·
                    refine ⟨5437664966032406946348337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7250219954709875928464449 5437664966032406946348337)
                    ·
                      refine ⟨4078248724524305209761253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5437664966032406946348337 4078248724524305209761253)
                      ·
                        rfl

theorem cell23_7942361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 6, 1, 2, 2, 2].length) (baseStart_7942361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7942361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7942361 prefixEnd_7942361 := by exact prefixLift 7942361
  have htrace : WordTrace (prefixWord ++ tailWord_7942361) baseStart_7942361 baseEnd_7942361 := by
    simpa [prefixWord, tailWord_7942361, baseEnd_7942361] using wordTrace_append hprefix tailTrace_7942361
  have hstable : (prefixWord ++ tailWord_7942361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7942361).length < 2 ^ (prefixWord ++ tailWord_7942361).sum := by decide
  have hdescent : baseEnd_7942361 < baseStart_7942361 := by decide
  rcases family_descends (prefixWord ++ tailWord_7942361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7942417 : List Nat := [1, 2, 2, 1, 1, 5, 1, 1, 1, 6, 2]
def baseStart_7942417 : Nat := 118140960795 + 7942417 * 2 ^ 59
def prefixEnd_7942417 : Nat := 4983230072969 + 3 ^ 40 * 7942417 * 2
def baseEnd_7942417 : Nat := 4078277479440956990660995

theorem tailTrace_7942417 : CollatzResearch.WordTrace tailWord_7942417 prefixEnd_7942417 4078277479440956990660995 := by
  unfold tailWord_7942417
  simp only [CollatzResearch.WordTrace]
  refine ⟨289683746466987140675665505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193122497644658093783777003 289683746466987140675665505)
  ·
    refine ⟨217262809850240355506749129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289683746466987140675665505 217262809850240355506749129)
    ·
      refine ⟨162947107387680266630061847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217262809850240355506749129 162947107387680266630061847)
      ·
        refine ⟨244420661081520399945092771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162947107387680266630061847 244420661081520399945092771)
        ·
          refine ⟨366630991622280599917639157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244420661081520399945092771 366630991622280599917639157)
          ·
            refine ⟨34371655464588806242278671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 366630991622280599917639157 34371655464588806242278671)
            ·
              refine ⟨51557483196883209363418007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34371655464588806242278671 51557483196883209363418007)
              ·
                refine ⟨77336224795324814045127011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51557483196883209363418007 77336224795324814045127011)
                ·
                  refine ⟨116004337192987221067690517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77336224795324814045127011 116004337192987221067690517)
                  ·
                    refine ⟨5437703305921275987547993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 116004337192987221067690517 5437703305921275987547993)
                    ·
                      refine ⟨4078277479440956990660995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5437703305921275987547993 4078277479440956990660995)
                      ·
                        rfl

theorem cell23_7942417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 6, 2].length) (baseStart_7942417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7942417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7942417 prefixEnd_7942417 := by exact prefixLift 7942417
  have htrace : WordTrace (prefixWord ++ tailWord_7942417) baseStart_7942417 baseEnd_7942417 := by
    simpa [prefixWord, tailWord_7942417, baseEnd_7942417] using wordTrace_append hprefix tailTrace_7942417
  have hstable : (prefixWord ++ tailWord_7942417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7942417).length < 2 ^ (prefixWord ++ tailWord_7942417).sum := by decide
  have hdescent : baseEnd_7942417 < baseStart_7942417 := by decide
  rcases family_descends (prefixWord ++ tailWord_7942417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7942434 : List Nat := [3, 3, 1, 1, 3, 1, 3, 1, 2, 1, 4]
def baseStart_7942434 : Nat := 118140960795 + 7942434 * 2 ^ 59
def prefixEnd_7942434 : Nat := 4983230072969 + 3 ^ 40 * 7942434 * 2
def baseEnd_7942434 : Nat := 4078286208612083424148417

theorem tailTrace_7942434 : CollatzResearch.WordTrace tailWord_7942434 prefixEnd_7942434 4078286208612083424148417 := by
  unfold tailWord_7942434
  simp only [CollatzResearch.WordTrace]
  refine ⟨72421091626981388144758589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193122911005283701719356237 72421091626981388144758589)
  ·
    refine ⟨27157909360118020554284471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72421091626981388144758589 27157909360118020554284471)
    ·
      refine ⟨40736864040177030831426707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27157909360118020554284471 40736864040177030831426707)
      ·
        refine ⟨61105296060265546247140061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40736864040177030831426707 61105296060265546247140061)
        ·
          refine ⟨22914486022599579842677523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61105296060265546247140061 22914486022599579842677523)
          ·
            refine ⟨34371729033899369764016285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22914486022599579842677523 34371729033899369764016285)
            ·
              refine ⟨12889398387712263661506107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34371729033899369764016285 12889398387712263661506107)
              ·
                refine ⟨19334097581568395492259161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12889398387712263661506107 19334097581568395492259161)
                ·
                  refine ⟨14500573186176296619194371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19334097581568395492259161 14500573186176296619194371)
                  ·
                    refine ⟨21750859779264444928791557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14500573186176296619194371 21750859779264444928791557)
                    ·
                      refine ⟨4078286208612083424148417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21750859779264444928791557 4078286208612083424148417)
                      ·
                        rfl

theorem cell23_7942434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 3, 1, 2, 1, 4].length) (baseStart_7942434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7942434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7942434 prefixEnd_7942434 := by exact prefixLift 7942434
  have htrace : WordTrace (prefixWord ++ tailWord_7942434) baseStart_7942434 baseEnd_7942434 := by
    simpa [prefixWord, tailWord_7942434, baseEnd_7942434] using wordTrace_append hprefix tailTrace_7942434
  have hstable : (prefixWord ++ tailWord_7942434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7942434).length < 2 ^ (prefixWord ++ tailWord_7942434).sum := by decide
  have hdescent : baseEnd_7942434 < baseStart_7942434 := by decide
  rcases family_descends (prefixWord ++ tailWord_7942434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7942444 : List Nat := [2, 2, 1, 1, 1, 3, 3, 5, 1, 4]
def baseStart_7942444 : Nat := 118140960795 + 7942444 * 2 ^ 59
def prefixEnd_7942444 : Nat := 4983230072969 + 3 ^ 40 * 7942444 * 2
def baseEnd_7942444 : Nat := 1359430447806209461674457

theorem tailTrace_7942444 : CollatzResearch.WordTrace tailWord_7942444 prefixEnd_7942444 1359430447806209461674457 := by
  unfold tailWord_7942444
  simp only [CollatzResearch.WordTrace]
  refine ⟨144842365618944662143449193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193123154158592882857932257 144842365618944662143449193)
  ·
    refine ⟨108631774214208496607586895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144842365618944662143449193 108631774214208496607586895)
    ·
      refine ⟨162947661321312744911380343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108631774214208496607586895 162947661321312744911380343)
      ·
        refine ⟨244421491981969117367070515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162947661321312744911380343 244421491981969117367070515)
        ·
          refine ⟨366632237972953676050605773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244421491981969117367070515 366632237972953676050605773)
          ·
            refine ⟨137487089239857628518977165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 366632237972953676050605773 137487089239857628518977165)
            ·
              refine ⟨51557658464946610694616437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 137487089239857628518977165 51557658464946610694616437)
              ·
                refine ⟨4833530481088744752620291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51557658464946610694616437 4833530481088744752620291)
                ·
                  refine ⟨7250295721633117128930437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4833530481088744752620291 7250295721633117128930437)
                  ·
                    refine ⟨1359430447806209461674457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7250295721633117128930437 1359430447806209461674457)
                    ·
                      rfl

theorem cell23_7942444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 5, 1, 4].length) (baseStart_7942444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7942444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7942444 prefixEnd_7942444 := by exact prefixLift 7942444
  have htrace : WordTrace (prefixWord ++ tailWord_7942444) baseStart_7942444 baseEnd_7942444 := by
    simpa [prefixWord, tailWord_7942444, baseEnd_7942444] using wordTrace_append hprefix tailTrace_7942444
  have hstable : (prefixWord ++ tailWord_7942444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7942444).length < 2 ^ (prefixWord ++ tailWord_7942444).sum := by decide
  have hdescent : baseEnd_7942444 < baseStart_7942444 := by decide
  rcases family_descends (prefixWord ++ tailWord_7942444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7942457 : List Nat := [1, 2, 1, 6, 1, 2, 1, 1, 8]
def baseStart_7942457 : Nat := 118140960795 + 7942457 * 2 ^ 59
def prefixEnd_7942457 : Nat := 4983230072969 + 3 ^ 40 * 7942457 * 2
def baseEnd_7942457 : Nat := 453144224296348537128979

theorem tailTrace_7942457 : CollatzResearch.WordTrace tailWord_7942457 prefixEnd_7942457 453144224296348537128979 := by
  unfold tailWord_7942457
  simp only [CollatzResearch.WordTrace]
  refine ⟨289685205386842227507121625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193123470257894818338081083 289685205386842227507121625)
  ·
    refine ⟨217263904040131670630341219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289685205386842227507121625 217263904040131670630341219)
    ·
      refine ⟨325895856060197505945511829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217263904040131670630341219 325895856060197505945511829)
      ·
        refine ⟨15276368252821758091195867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 325895856060197505945511829 15276368252821758091195867)
        ·
          refine ⟨22914552379232637136793801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15276368252821758091195867 22914552379232637136793801)
          ·
            refine ⟨17185914284424477852595351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22914552379232637136793801 17185914284424477852595351)
            ·
              refine ⟨25778871426636716778893027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17185914284424477852595351 25778871426636716778893027)
              ·
                refine ⟨38668307139955075168339541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25778871426636716778893027 38668307139955075168339541)
                ·
                  refine ⟨453144224296348537128979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38668307139955075168339541 453144224296348537128979)
                  ·
                    rfl

theorem cell23_7942457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 1, 8].length) (baseStart_7942457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7942457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7942457 prefixEnd_7942457 := by exact prefixLift 7942457
  have htrace : WordTrace (prefixWord ++ tailWord_7942457) baseStart_7942457 baseEnd_7942457 := by
    simpa [prefixWord, tailWord_7942457, baseEnd_7942457] using wordTrace_append hprefix tailTrace_7942457
  have hstable : (prefixWord ++ tailWord_7942457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7942457).length < 2 ^ (prefixWord ++ tailWord_7942457).sum := by decide
  have hdescent : baseEnd_7942457 < baseStart_7942457 := by decide
  rcases family_descends (prefixWord ++ tailWord_7942457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7942460 : List Nat := [2, 2, 2, 2, 1, 2, 1, 1, 1, 1, 8]
def baseStart_7942460 : Nat := 118140960795 + 7942460 * 2 ^ 59
def prefixEnd_7942460 : Nat := 4983230072969 + 3 ^ 40 * 7942460 * 2
def baseEnd_7942460 : Nat := 4078299559109100322423297

theorem tailTrace_7942460 : CollatzResearch.WordTrace tailWord_7942460 prefixEnd_7942460 4078299559109100322423297 := by
  unfold tailWord_7942460
  simp only [CollatzResearch.WordTrace]
  refine ⟨144842657402915679509740417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193123543203887572679653889 144842657402915679509740417)
  ·
    refine ⟨108631993052186759632305313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144842657402915679509740417 108631993052186759632305313)
    ·
      refine ⟨81473994789140069724228985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108631993052186759632305313 81473994789140069724228985)
      ·
        refine ⟨61105496091855052293171739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81473994789140069724228985 61105496091855052293171739)
        ·
          refine ⟨91658244137782578439757609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61105496091855052293171739 91658244137782578439757609)
          ·
            refine ⟨68743683103336933829818207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91658244137782578439757609 68743683103336933829818207)
            ·
              refine ⟨103115524655005400744727311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68743683103336933829818207 103115524655005400744727311)
              ·
                refine ⟨154673286982508101117090967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103115524655005400744727311 154673286982508101117090967)
                ·
                  refine ⟨232009930473762151675636451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 154673286982508101117090967 232009930473762151675636451)
                  ·
                    refine ⟨348014895710643227513454677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 232009930473762151675636451 348014895710643227513454677)
                    ·
                      refine ⟨4078299559109100322423297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 348014895710643227513454677 4078299559109100322423297)
                      ·
                        rfl

theorem cell23_7942460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 1, 1, 1, 8].length) (baseStart_7942460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7942460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7942460 prefixEnd_7942460 := by exact prefixLift 7942460
  have htrace : WordTrace (prefixWord ++ tailWord_7942460) baseStart_7942460 baseEnd_7942460 := by
    simpa [prefixWord, tailWord_7942460, baseEnd_7942460] using wordTrace_append hprefix tailTrace_7942460
  have hstable : (prefixWord ++ tailWord_7942460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7942460).length < 2 ^ (prefixWord ++ tailWord_7942460).sum := by decide
  have hdescent : baseEnd_7942460 < baseStart_7942460 := by decide
  rcases family_descends (prefixWord ++ tailWord_7942460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7942504 : List Nat := [2, 1, 4, 2, 2, 1, 2, 3, 1, 5]
def baseStart_7942504 : Nat := 118140960795 + 7942504 * 2 ^ 59
def prefixEnd_7942504 : Nat := 4983230072969 + 3 ^ 40 * 7942504 * 2
def baseEnd_7942504 : Nat := 1359440717419299383424365

theorem tailTrace_7942504 : CollatzResearch.WordTrace tailWord_7942504 prefixEnd_7942504 1359440717419299383424365 := by
  unfold tailWord_7942504
  simp only [CollatzResearch.WordTrace]
  refine ⟨144843459808835977267041283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193124613078447969689388377 144843459808835977267041283)
  ·
    refine ⟨217265189713253965900561925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144843459808835977267041283 217265189713253965900561925)
    ·
      refine ⟨40737223071235118606355361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 217265189713253965900561925 40737223071235118606355361)
      ·
        refine ⟨30552917303426338954766521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40737223071235118606355361 30552917303426338954766521)
        ·
          refine ⟨22914687977569754216074891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30552917303426338954766521 22914687977569754216074891)
          ·
            refine ⟨34372031966354631324112337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22914687977569754216074891 34372031966354631324112337)
            ·
              refine ⟨25779023974765973493084253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34372031966354631324112337 25779023974765973493084253)
              ·
                refine ⟨9667133990537240059906595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25779023974765973493084253 9667133990537240059906595)
                ·
                  refine ⟨14500700985805860089859893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9667133990537240059906595 14500700985805860089859893)
                  ·
                    refine ⟨1359440717419299383424365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14500700985805860089859893 1359440717419299383424365)
                    ·
                      rfl

theorem cell23_7942504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 3, 1, 5].length) (baseStart_7942504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7942504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7942504 prefixEnd_7942504 := by exact prefixLift 7942504
  have htrace : WordTrace (prefixWord ++ tailWord_7942504) baseStart_7942504 baseEnd_7942504 := by
    simpa [prefixWord, tailWord_7942504, baseEnd_7942504] using wordTrace_append hprefix tailTrace_7942504
  have hstable : (prefixWord ++ tailWord_7942504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7942504).length < 2 ^ (prefixWord ++ tailWord_7942504).sum := by decide
  have hdescent : baseEnd_7942504 < baseStart_7942504 := by decide
  rcases family_descends (prefixWord ++ tailWord_7942504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7942507 : List Nat := [1, 1, 1, 1, 2, 2, 2, 2, 1, 8, 2]
def baseStart_7942507 : Nat := 118140960795 + 7942507 * 2 ^ 59
def prefixEnd_7942507 : Nat := 4983230072969 + 3 ^ 40 * 7942507 * 2
def baseEnd_7942507 : Nat := 4078323692699861638535581

theorem tailTrace_7942507 : CollatzResearch.WordTrace tailWord_7942507 prefixEnd_7942507 4078323692699861638535581 := by
  unfold tailWord_7942507
  simp only [CollatzResearch.WordTrace]
  refine ⟨289687029036661086046441775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193124686024440724030961183 289687029036661086046441775)
  ·
    refine ⟨434530543554991629069662663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289687029036661086046441775 434530543554991629069662663)
    ·
      refine ⟨651795815332487443604493995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 434530543554991629069662663 651795815332487443604493995)
      ·
        refine ⟨977693722998731165406740993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 651795815332487443604493995 977693722998731165406740993)
        ·
          refine ⟨733270292249048374055055745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 977693722998731165406740993 733270292249048374055055745)
          ·
            refine ⟨549952719186786280541291809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 733270292249048374055055745 549952719186786280541291809)
            ·
              refine ⟨412464539390089710405968857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 549952719186786280541291809 412464539390089710405968857)
              ·
                refine ⟨309348404542567282804476643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 412464539390089710405968857 309348404542567282804476643)
                ·
                  refine ⟨464022606813850924206714965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 309348404542567282804476643 464022606813850924206714965)
                  ·
                    refine ⟨5437764923599815518047441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 464022606813850924206714965 5437764923599815518047441)
                    ·
                      refine ⟨4078323692699861638535581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5437764923599815518047441 4078323692699861638535581)
                      ·
                        rfl

theorem cell23_7942507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 8, 2].length) (baseStart_7942507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7942507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7942507 prefixEnd_7942507 := by exact prefixLift 7942507
  have htrace : WordTrace (prefixWord ++ tailWord_7942507) baseStart_7942507 baseEnd_7942507 := by
    simpa [prefixWord, tailWord_7942507, baseEnd_7942507] using wordTrace_append hprefix tailTrace_7942507
  have hstable : (prefixWord ++ tailWord_7942507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7942507).length < 2 ^ (prefixWord ++ tailWord_7942507).sum := by decide
  have hdescent : baseEnd_7942507 < baseStart_7942507 := by decide
  rcases family_descends (prefixWord ++ tailWord_7942507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7942527 : List Nat := [1, 1, 2, 2, 1, 1, 2, 3, 5, 2, 3]
def baseStart_7942527 : Nat := 118140960795 + 7942527 * 2 ^ 59
def prefixEnd_7942527 : Nat := 4983230072969 + 3 ^ 40 * 7942527 * 2
def baseEnd_7942527 : Nat := 4078333962312951560285489

theorem tailTrace_7942527 : CollatzResearch.WordTrace tailWord_7942527 prefixEnd_7942527 4078333962312951560285489 := by
  unfold tailWord_7942527
  simp only [CollatzResearch.WordTrace]
  refine ⟨289687758496588629462169835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193125172331059086308113223 289687758496588629462169835)
  ·
    refine ⟨434531637744882944193254753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289687758496588629462169835 434531637744882944193254753)
    ·
      refine ⟨325898728308662208144941065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 434531637744882944193254753 325898728308662208144941065)
      ·
        refine ⟨244424046231496656108705799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 325898728308662208144941065 244424046231496656108705799)
        ·
          refine ⟨366636069347244984163058699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244424046231496656108705799 366636069347244984163058699)
          ·
            refine ⟨549954104020867476244588049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 366636069347244984163058699 549954104020867476244588049)
            ·
              refine ⟨412465578015650607183441037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 549954104020867476244588049 412465578015650607183441037)
              ·
                refine ⟨154674591755868977693790389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 412465578015650607183441037 154674591755868977693790389)
                ·
                  refine ⟨14500742977112716658792849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 154674591755868977693790389 14500742977112716658792849)
                  ·
                    refine ⟨10875557232834537494094637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14500742977112716658792849 10875557232834537494094637)
                    ·
                      refine ⟨4078333962312951560285489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10875557232834537494094637 4078333962312951560285489)
                      ·
                        rfl

theorem cell23_7942527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 3, 5, 2, 3].length) (baseStart_7942527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7942527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7942527 prefixEnd_7942527 := by exact prefixLift 7942527
  have htrace : WordTrace (prefixWord ++ tailWord_7942527) baseStart_7942527 baseEnd_7942527 := by
    simpa [prefixWord, tailWord_7942527, baseEnd_7942527] using wordTrace_append hprefix tailTrace_7942527
  have hstable : (prefixWord ++ tailWord_7942527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7942527).length < 2 ^ (prefixWord ++ tailWord_7942527).sum := by decide
  have hdescent : baseEnd_7942527 < baseStart_7942527 := by decide
  rcases family_descends (prefixWord ++ tailWord_7942527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7942537 : List Nat := [1, 2, 1, 1, 6, 1, 2, 1, 1, 1, 6]
def baseStart_7942537 : Nat := 118140960795 + 7942537 * 2 ^ 59
def prefixEnd_7942537 : Nat := 4983230072969 + 3 ^ 40 * 7942537 * 2
def baseEnd_7942537 : Nat := 4078339097119496521160443

theorem tailTrace_7942537 : CollatzResearch.WordTrace tailWord_7942537 prefixEnd_7942537 4078339097119496521160443 := by
  unfold tailWord_7942537
  simp only [CollatzResearch.WordTrace]
  refine ⟨289688123226552401170033865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193125415484368267446689243 289688123226552401170033865)
  ·
    refine ⟨217266092419914300877525399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289688123226552401170033865 217266092419914300877525399)
    ·
      refine ⟨325899138629871451316288099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217266092419914300877525399 325899138629871451316288099)
      ·
        refine ⟨488848707944807176974432149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 325899138629871451316288099 488848707944807176974432149)
        ·
          refine ⟨22914783184912836420676507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 488848707944807176974432149 22914783184912836420676507)
          ·
            refine ⟨34372174777369254631014761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22914783184912836420676507 34372174777369254631014761)
            ·
              refine ⟨25779131083026940973261071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34372174777369254631014761 25779131083026940973261071)
              ·
                refine ⟨38668696624540411459891607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25779131083026940973261071 38668696624540411459891607)
                ·
                  refine ⟨58003044936810617189837411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38668696624540411459891607 58003044936810617189837411)
                  ·
                    refine ⟨87004567405215925784756117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58003044936810617189837411 87004567405215925784756117)
                    ·
                      refine ⟨4078339097119496521160443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 87004567405215925784756117 4078339097119496521160443)
                      ·
                        rfl

theorem cell23_7942537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 1, 1, 1, 6].length) (baseStart_7942537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7942537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7942537 prefixEnd_7942537 := by exact prefixLift 7942537
  have htrace : WordTrace (prefixWord ++ tailWord_7942537) baseStart_7942537 baseEnd_7942537 := by
    simpa [prefixWord, tailWord_7942537, baseEnd_7942537] using wordTrace_append hprefix tailTrace_7942537
  have hstable : (prefixWord ++ tailWord_7942537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7942537).length < 2 ^ (prefixWord ++ tailWord_7942537).sum := by decide
  have hdescent : baseEnd_7942537 < baseStart_7942537 := by decide
  rcases family_descends (prefixWord ++ tailWord_7942537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7942538 : List Nat := [3, 1, 2, 5, 1, 2, 1, 2, 1, 5]
def baseStart_7942538 : Nat := 118140960795 + 7942538 * 2 ^ 59
def prefixEnd_7942538 : Nat := 4983230072969 + 3 ^ 40 * 7942538 * 2
def baseEnd_7942538 : Nat := 1359446536866717005749313

theorem tailTrace_7942538 : CollatzResearch.WordTrace tailWord_7942538 prefixEnd_7942538 1359446536866717005749313 := by
  unfold tailWord_7942538
  simp only [CollatzResearch.WordTrace]
  refine ⟨72422039924887194585205067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193125439799699185560546845 72422039924887194585205067)
  ·
    refine ⟨108633059887330791877807601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72422039924887194585205067 108633059887330791877807601)
    ·
      refine ⟨81474794915498093908355701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108633059887330791877807601 81474794915498093908355701)
      ·
        refine ⟨7638262023327946303908347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 81474794915498093908355701 7638262023327946303908347)
        ·
          refine ⟨11457393034991919455862521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7638262023327946303908347 11457393034991919455862521)
          ·
            refine ⟨8593044776243939591896891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11457393034991919455862521 8593044776243939591896891)
            ·
              refine ⟨12889567164365909387845337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8593044776243939591896891 12889567164365909387845337)
              ·
                refine ⟨9667175373274432040884003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12889567164365909387845337 9667175373274432040884003)
                ·
                  refine ⟨14500763059911648061326005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9667175373274432040884003 14500763059911648061326005)
                  ·
                    refine ⟨1359446536866717005749313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14500763059911648061326005 1359446536866717005749313)
                    ·
                      rfl

theorem cell23_7942538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 1, 2, 1, 5].length) (baseStart_7942538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7942538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7942538 prefixEnd_7942538 := by exact prefixLift 7942538
  have htrace : WordTrace (prefixWord ++ tailWord_7942538) baseStart_7942538 baseEnd_7942538 := by
    simpa [prefixWord, tailWord_7942538, baseEnd_7942538] using wordTrace_append hprefix tailTrace_7942538
  have hstable : (prefixWord ++ tailWord_7942538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7942538).length < 2 ^ (prefixWord ++ tailWord_7942538).sum := by decide
  have hdescent : baseEnd_7942538 < baseStart_7942538 := by decide
  rcases family_descends (prefixWord ++ tailWord_7942538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7942554 : List Nat := [3, 1, 1, 4, 1, 3, 1, 2, 1, 2, 4]
def baseStart_7942554 : Nat := 118140960795 + 7942554 * 2 ^ 59
def prefixEnd_7942554 : Nat := 4983230072969 + 3 ^ 40 * 7942554 * 2
def baseEnd_7942554 : Nat := 4078347826290622954647865

theorem tailTrace_7942554 : CollatzResearch.WordTrace tailWord_7942554 prefixEnd_7942554 4078347826290622954647865 := by
  unfold tailWord_7942554
  simp only [CollatzResearch.WordTrace]
  refine ⟨72422185816872703268350679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193125828844993875382268477 72422185816872703268350679)
  ·
    refine ⟨108633278725309054902526019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72422185816872703268350679 108633278725309054902526019)
    ·
      refine ⟨162949918087963582353789029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108633278725309054902526019 162949918087963582353789029)
      ·
        refine ⟨30553109641493171691335443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 162949918087963582353789029 30553109641493171691335443)
        ·
          refine ⟨45829664462239757537003165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30553109641493171691335443 45829664462239757537003165)
          ·
            refine ⟨17186124173339909076376187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45829664462239757537003165 17186124173339909076376187)
            ·
              refine ⟨25779186260009863614564281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17186124173339909076376187 25779186260009863614564281)
              ·
                refine ⟨19334389695007397710923211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25779186260009863614564281 19334389695007397710923211)
                ·
                  refine ⟨29001584542511096566384817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19334389695007397710923211 29001584542511096566384817)
                  ·
                    refine ⟨21751188406883322424788613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29001584542511096566384817 21751188406883322424788613)
                    ·
                      refine ⟨4078347826290622954647865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21751188406883322424788613 4078347826290622954647865)
                      ·
                        rfl

theorem cell23_7942554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 2, 1, 2, 4].length) (baseStart_7942554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7942554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7942554 prefixEnd_7942554 := by exact prefixLift 7942554
  have htrace : WordTrace (prefixWord ++ tailWord_7942554) baseStart_7942554 baseEnd_7942554 := by
    simpa [prefixWord, tailWord_7942554, baseEnd_7942554] using wordTrace_append hprefix tailTrace_7942554
  have hstable : (prefixWord ++ tailWord_7942554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7942554).length < 2 ^ (prefixWord ++ tailWord_7942554).sum := by decide
  have hdescent : baseEnd_7942554 < baseStart_7942554 := by decide
  rcases family_descends (prefixWord ++ tailWord_7942554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7942568 : List Nat := [2, 1, 6, 1, 1, 2, 2, 2, 2, 4]
def baseStart_7942568 : Nat := 118140960795 + 7942568 * 2 ^ 59
def prefixEnd_7942568 : Nat := 4983230072969 + 3 ^ 40 * 7942568 * 2
def baseEnd_7942568 : Nat := 1359451671673261966624267

theorem tailTrace_7942568 : CollatzResearch.WordTrace tailWord_7942568 prefixEnd_7942568 1359451671673261966624267 := by
  unfold tailWord_7942568
  simp only [CollatzResearch.WordTrace]
  refine ⟨144844626944720046732206179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193126169259626728976274905 144844626944720046732206179)
  ·
    refine ⟨217266940417080070098309269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144844626944720046732206179 217266940417080070098309269)
    ·
      refine ⟨10184387832050628285858247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 217266940417080070098309269 10184387832050628285858247)
      ·
        refine ⟨15276581748075942428787371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10184387832050628285858247 15276581748075942428787371)
        ·
          refine ⟨22914872622113913643181057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15276581748075942428787371 22914872622113913643181057)
          ·
            refine ⟨17186154466585435232385793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22914872622113913643181057 17186154466585435232385793)
            ·
              refine ⟨12889615849939076424289345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17186154466585435232385793 12889615849939076424289345)
              ·
                refine ⟨9667211887454307318217009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12889615849939076424289345 9667211887454307318217009)
                ·
                  refine ⟨7250408915590730488662757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9667211887454307318217009 7250408915590730488662757)
                  ·
                    refine ⟨1359451671673261966624267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7250408915590730488662757 1359451671673261966624267)
                    ·
                      rfl

theorem cell23_7942568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 2, 2, 2, 4].length) (baseStart_7942568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7942568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7942568 prefixEnd_7942568 := by exact prefixLift 7942568
  have htrace : WordTrace (prefixWord ++ tailWord_7942568) baseStart_7942568 baseEnd_7942568 := by
    simpa [prefixWord, tailWord_7942568, baseEnd_7942568] using wordTrace_append hprefix tailTrace_7942568
  have hstable : (prefixWord ++ tailWord_7942568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7942568).length < 2 ^ (prefixWord ++ tailWord_7942568).sum := by decide
  have hdescent : baseEnd_7942568 < baseStart_7942568 := by decide
  rcases family_descends (prefixWord ++ tailWord_7942568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7942577 : List Nat := [1, 2, 2, 4, 1, 2, 1, 1, 2, 7]
def baseStart_7942577 : Nat := 118140960795 + 7942577 * 2 ^ 59
def prefixEnd_7942577 : Nat := 4983230072969 + 3 ^ 40 * 7942577 * 2
def baseEnd_7942577 : Nat := 1359453212115225454886753

theorem tailTrace_7942577 : CollatzResearch.WordTrace tailWord_7942577 prefixEnd_7942577 1359453212115225454886753 := by
  unfold tailWord_7942577
  simp only [CollatzResearch.WordTrace]
  refine ⟨289689582146407488001489985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193126388097604992000993323 289689582146407488001489985)
  ·
    refine ⟨217267186609805616001117489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289689582146407488001489985 217267186609805616001117489)
    ·
      refine ⟨162950389957354212000838117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217267186609805616001117489 162950389957354212000838117)
      ·
        refine ⟨30553198117003914750157147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 162950389957354212000838117 30553198117003914750157147)
        ·
          refine ⟨45829797175505872125235721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30553198117003914750157147 45829797175505872125235721)
          ·
            refine ⟨34372347881629404093926791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45829797175505872125235721 34372347881629404093926791)
            ·
              refine ⟨51558521822444106140890187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34372347881629404093926791 51558521822444106140890187)
              ·
                refine ⟨77337782733666159211335281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51558521822444106140890187 77337782733666159211335281)
                ·
                  refine ⟨58003337050249619408501461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77337782733666159211335281 58003337050249619408501461)
                  ·
                    refine ⟨1359453212115225454886753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58003337050249619408501461 1359453212115225454886753)
                    ·
                      rfl

theorem cell23_7942577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 1, 2, 7].length) (baseStart_7942577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7942577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7942577 prefixEnd_7942577 := by exact prefixLift 7942577
  have htrace : WordTrace (prefixWord ++ tailWord_7942577) baseStart_7942577 baseEnd_7942577 := by
    simpa [prefixWord, tailWord_7942577, baseEnd_7942577] using wordTrace_append hprefix tailTrace_7942577
  have hstable : (prefixWord ++ tailWord_7942577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7942577).length < 2 ^ (prefixWord ++ tailWord_7942577).sum := by decide
  have hdescent : baseEnd_7942577 < baseStart_7942577 := by decide
  rcases family_descends (prefixWord ++ tailWord_7942577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7942581 : List Nat := [1, 3, 3, 2, 4, 1, 1, 8]
def baseStart_7942581 : Nat := 118140960795 + 7942581 * 2 ^ 59
def prefixEnd_7942581 : Nat := 4983230072969 + 3 ^ 40 * 7942581 * 2
def baseEnd_7942581 : Nat := 151050432972899790704083

theorem tailTrace_7942581 : CollatzResearch.WordTrace tailWord_7942581 prefixEnd_7942581 151050432972899790704083 := by
  unfold tailWord_7942581
  simp only [CollatzResearch.WordTrace]
  refine ⟨289689728038392996684635597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193126485358928664456423731 289689728038392996684635597)
  ·
    refine ⟨108633648014397373756738349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 289689728038392996684635597 108633648014397373756738349)
    ·
      refine ⟨40737618005399015158776881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108633648014397373756738349 40737618005399015158776881)
      ·
        refine ⟨30553213504049261369082661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40737618005399015158776881 30553213504049261369082661)
        ·
          refine ⟨5728727532009236506702999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30553213504049261369082661 5728727532009236506702999)
          ·
            refine ⟨8593091298013854760054499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5728727532009236506702999 8593091298013854760054499)
            ·
              refine ⟨12889636947020782140081749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8593091298013854760054499 12889636947020782140081749)
              ·
                refine ⟨151050432972899790704083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12889636947020782140081749 151050432972899790704083)
                ·
                  rfl

theorem cell23_7942581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 1, 8].length) (baseStart_7942581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7942581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7942581 prefixEnd_7942581 := by exact prefixLift 7942581
  have htrace : WordTrace (prefixWord ++ tailWord_7942581) baseStart_7942581 baseEnd_7942581 := by
    simpa [prefixWord, tailWord_7942581, baseEnd_7942581] using wordTrace_append hprefix tailTrace_7942581
  have hstable : (prefixWord ++ tailWord_7942581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7942581).length < 2 ^ (prefixWord ++ tailWord_7942581).sum := by decide
  have hdescent : baseEnd_7942581 < baseStart_7942581 := by decide
  rcases family_descends (prefixWord ++ tailWord_7942581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7942617 : List Nat := [1, 2, 1, 2, 4, 1, 2, 1, 1, 3, 5]
def baseStart_7942617 : Nat := 118140960795 + 7942617 * 2 ^ 59
def prefixEnd_7942617 : Nat := 4983230072969 + 3 ^ 40 * 7942617 * 2
def baseEnd_7942617 : Nat := 4078380175571856208160075

theorem tailTrace_7942617 : CollatzResearch.WordTrace tailWord_7942617 prefixEnd_7942617 4078380175571856208160075 := by
  unfold tailWord_7942617
  simp only [CollatzResearch.WordTrace]
  refine ⟨289691041066262574832946105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193127360710841716555297403 289691041066262574832946105)
  ·
    refine ⟨217268280799696931124709579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289691041066262574832946105 217268280799696931124709579)
    ·
      refine ⟨325902421199545396687064369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217268280799696931124709579 325902421199545396687064369)
      ·
        refine ⟨244426815899659047515298277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 325902421199545396687064369 244426815899659047515298277)
        ·
          refine ⟨45830027981186071409118427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 244426815899659047515298277 45830027981186071409118427)
          ·
            refine ⟨68745041971779107113677641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45830027981186071409118427 68745041971779107113677641)
            ·
              refine ⟨51558781478834330335258231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68745041971779107113677641 51558781478834330335258231)
              ·
                refine ⟨77338172218251495502887347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51558781478834330335258231 77338172218251495502887347)
                ·
                  refine ⟨116007258327377243254331021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77338172218251495502887347 116007258327377243254331021)
                  ·
                    refine ⟨43502721872766466220374133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 116007258327377243254331021 43502721872766466220374133)
                    ·
                      refine ⟨4078380175571856208160075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43502721872766466220374133 4078380175571856208160075)
                      ·
                        rfl

theorem cell23_7942617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 1, 1, 3, 5].length) (baseStart_7942617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7942617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7942617 prefixEnd_7942617 := by exact prefixLift 7942617
  have htrace : WordTrace (prefixWord ++ tailWord_7942617) baseStart_7942617 baseEnd_7942617 := by
    simpa [prefixWord, tailWord_7942617, baseEnd_7942617] using wordTrace_append hprefix tailTrace_7942617
  have hstable : (prefixWord ++ tailWord_7942617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7942617).length < 2 ^ (prefixWord ++ tailWord_7942617).sum := by decide
  have hdescent : baseEnd_7942617 < baseStart_7942617 := by decide
  rcases family_descends (prefixWord ++ tailWord_7942617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7942684 : List Nat := [2, 2, 3, 1, 2, 2, 1, 1, 4, 5]
def baseStart_7942684 : Nat := 118140960795 + 7942684 * 2 ^ 59
def prefixEnd_7942684 : Nat := 4983230072969 + 3 ^ 40 * 7942684 * 2
def baseEnd_7942684 : Nat := 1359471526258569148674089

theorem tailTrace_7942684 : CollatzResearch.WordTrace tailWord_7942684 prefixEnd_7942684 1359471526258569148674089 := by
  unfold tailWord_7942684
  simp only [CollatzResearch.WordTrace]
  refine ⟨144846742378509922637817553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193128989838013230183756737 144846742378509922637817553)
  ·
    refine ⟨108635056783882441978363165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144846742378509922637817553 108635056783882441978363165)
    ·
      refine ⟨40738146293955915741886187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108635056783882441978363165 40738146293955915741886187)
      ·
        refine ⟨61107219440933873612829281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40738146293955915741886187 61107219440933873612829281)
        ·
          refine ⟨45830414580700405209621961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61107219440933873612829281 45830414580700405209621961)
          ·
            refine ⟨34372810935525303907216471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45830414580700405209621961 34372810935525303907216471)
            ·
              refine ⟨51559216403287955860824707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34372810935525303907216471 51559216403287955860824707)
              ·
                refine ⟨77338824604931933791237061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51559216403287955860824707 77338824604931933791237061)
                ·
                  refine ⟨14501029613424737585856949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77338824604931933791237061 14501029613424737585856949)
                  ·
                    refine ⟨1359471526258569148674089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14501029613424737585856949 1359471526258569148674089)
                    ·
                      rfl

theorem cell23_7942684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 1, 4, 5].length) (baseStart_7942684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7942684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7942684 prefixEnd_7942684 := by exact prefixLift 7942684
  have htrace : WordTrace (prefixWord ++ tailWord_7942684) baseStart_7942684 baseEnd_7942684 := by
    simpa [prefixWord, tailWord_7942684, baseEnd_7942684] using wordTrace_append hprefix tailTrace_7942684
  have hstable : (prefixWord ++ tailWord_7942684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7942684).length < 2 ^ (prefixWord ++ tailWord_7942684).sum := by decide
  have hdescent : baseEnd_7942684 < baseStart_7942684 := by decide
  rcases family_descends (prefixWord ++ tailWord_7942684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7942688 : List Nat := [2, 1, 1, 6, 3, 1, 1, 1, 7]
def baseStart_7942688 : Nat := 118140960795 + 7942688 * 2 ^ 59
def prefixEnd_7942688 : Nat := 4983230072969 + 3 ^ 40 * 7942688 * 2
def baseEnd_7942688 : Nat := 453157403633147270041361

theorem tailTrace_7942688 : CollatzResearch.WordTrace tailWord_7942688 prefixEnd_7942688 453157403633147270041361 := by
  unfold tailWord_7942688
  simp only [CollatzResearch.WordTrace]
  refine ⟨144846815324502676979390359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193129087099336902639187145 144846815324502676979390359)
  ·
    refine ⟨217270222986754015469085539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144846815324502676979390359 217270222986754015469085539)
    ·
      refine ⟨325905334480131023203628309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217270222986754015469085539 325905334480131023203628309)
      ·
        refine ⟨15276812553756141712670077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 325905334480131023203628309 15276812553756141712670077)
        ·
          refine ⟨5728804707658553142251279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15276812553756141712670077 5728804707658553142251279)
          ·
            refine ⟨8593207061487829713376919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5728804707658553142251279 8593207061487829713376919)
            ·
              refine ⟨12889810592231744570065379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8593207061487829713376919 12889810592231744570065379)
              ·
                refine ⟨19334715888347616855098069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12889810592231744570065379 19334715888347616855098069)
                ·
                  refine ⟨453157403633147270041361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19334715888347616855098069 453157403633147270041361)
                  ·
                    rfl

theorem cell23_7942688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 1, 1, 7].length) (baseStart_7942688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7942688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7942688 prefixEnd_7942688 := by exact prefixLift 7942688
  have htrace : WordTrace (prefixWord ++ tailWord_7942688) baseStart_7942688 baseEnd_7942688 := by
    simpa [prefixWord, tailWord_7942688, baseEnd_7942688] using wordTrace_append hprefix tailTrace_7942688
  have hstable : (prefixWord ++ tailWord_7942688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7942688).length < 2 ^ (prefixWord ++ tailWord_7942688).sum := by decide
  have hdescent : baseEnd_7942688 < baseStart_7942688 := by decide
  rcases family_descends (prefixWord ++ tailWord_7942688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7942721 : List Nat := [1, 2, 5, 1, 1, 2, 1, 3, 2, 1, 4]
def baseStart_7942721 : Nat := 118140960795 + 7942721 * 2 ^ 59
def prefixEnd_7942721 : Nat := 4983230072969 + 3 ^ 40 * 7942721 * 2
def baseEnd_7942721 : Nat := 4078433577559923801259597

theorem tailTrace_7942721 : CollatzResearch.WordTrace tailWord_7942721 prefixEnd_7942721 4078433577559923801259597 := by
  unfold tailWord_7942721
  simp only [CollatzResearch.WordTrace]
  refine ⟨289694834257885800594732017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193129889505257200396488011 289694834257885800594732017)
  ·
    refine ⟨217271125693414350446049013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289694834257885800594732017 217271125693414350446049013)
    ·
      refine ⟨20369168033757595354317095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 217271125693414350446049013 20369168033757595354317095)
      ·
        refine ⟨30553752050636393031475643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20369168033757595354317095 30553752050636393031475643)
        ·
          refine ⟨45830628075954589547213465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30553752050636393031475643 45830628075954589547213465)
          ·
            refine ⟨34372971056965942160410099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45830628075954589547213465 34372971056965942160410099)
            ·
              refine ⟨51559456585448913240615149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34372971056965942160410099 51559456585448913240615149)
              ·
                refine ⟨19334796219543342465230681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51559456585448913240615149 19334796219543342465230681)
                ·
                  refine ⟨14501097164657506848923011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19334796219543342465230681 14501097164657506848923011)
                  ·
                    refine ⟨21751645746986260273384517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14501097164657506848923011 21751645746986260273384517)
                    ·
                      refine ⟨4078433577559923801259597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21751645746986260273384517 4078433577559923801259597)
                      ·
                        rfl

theorem cell23_7942721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 3, 2, 1, 4].length) (baseStart_7942721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7942721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7942721 prefixEnd_7942721 := by exact prefixLift 7942721
  have htrace : WordTrace (prefixWord ++ tailWord_7942721) baseStart_7942721 baseEnd_7942721 := by
    simpa [prefixWord, tailWord_7942721, baseEnd_7942721] using wordTrace_append hprefix tailTrace_7942721
  have hstable : (prefixWord ++ tailWord_7942721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7942721).length < 2 ^ (prefixWord ++ tailWord_7942721).sum := by decide
  have hdescent : baseEnd_7942721 < baseStart_7942721 := by decide
  rcases family_descends (prefixWord ++ tailWord_7942721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7942741 : List Nat := [1, 3, 2, 2, 1, 1, 4, 2, 2, 2, 3]
def baseStart_7942741 : Nat := 118140960795 + 7942741 * 2 ^ 59
def prefixEnd_7942741 : Nat := 4983230072969 + 3 ^ 40 * 7942741 * 2
def baseEnd_7942741 : Nat := 4078443847173013723009505

theorem tailTrace_7942741 : CollatzResearch.WordTrace tailWord_7942741 prefixEnd_7942741 4078443847173013723009505 := by
  unfold tailWord_7942741
  simp only [CollatzResearch.WordTrace]
  refine ⟨289695563717813344010460077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193130375811875562673640051 289695563717813344010460077)
  ·
    refine ⟨108635836394180004003922529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 289695563717813344010460077 108635836394180004003922529)
    ·
      refine ⟨81476877295635003002941897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108635836394180004003922529 81476877295635003002941897)
      ·
        refine ⟨61107657971726252252206423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81476877295635003002941897 61107657971726252252206423)
        ·
          refine ⟨91661486957589378378309635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61107657971726252252206423 91661486957589378378309635)
          ·
            refine ⟨137492230436384067567464453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91661486957589378378309635 137492230436384067567464453)
            ·
              refine ⟨25779793206822012668899585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 137492230436384067567464453 25779793206822012668899585)
              ·
                refine ⟨19334844905116509501674689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25779793206822012668899585 19334844905116509501674689)
                ·
                  refine ⟨14501133678837382126256017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19334844905116509501674689 14501133678837382126256017)
                  ·
                    refine ⟨10875850259128036594692013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14501133678837382126256017 10875850259128036594692013)
                    ·
                      refine ⟨4078443847173013723009505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10875850259128036594692013 4078443847173013723009505)
                      ·
                        rfl

theorem cell23_7942741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 2, 2, 2, 3].length) (baseStart_7942741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7942741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7942741 prefixEnd_7942741 := by exact prefixLift 7942741
  have htrace : WordTrace (prefixWord ++ tailWord_7942741) baseStart_7942741 baseEnd_7942741 := by
    simpa [prefixWord, tailWord_7942741, baseEnd_7942741] using wordTrace_append hprefix tailTrace_7942741
  have hstable : (prefixWord ++ tailWord_7942741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7942741).length < 2 ^ (prefixWord ++ tailWord_7942741).sum := by decide
  have hdescent : baseEnd_7942741 < baseStart_7942741 := by decide
  rcases family_descends (prefixWord ++ tailWord_7942741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7942744 : List Nat := [2, 1, 2, 2, 1, 2, 3, 4, 6]
def baseStart_7942744 : Nat := 118140960795 + 7942744 * 2 ^ 59
def prefixEnd_7942744 : Nat := 4983230072969 + 3 ^ 40 * 7942744 * 2
def baseEnd_7942744 : Nat := 453160598623886356807999

theorem tailTrace_7942744 : CollatzResearch.WordTrace tailWord_7942744 prefixEnd_7942744 453160598623886356807999 := by
  unfold tailWord_7942744
  simp only [CollatzResearch.WordTrace]
  refine ⟨144847836568401237761409643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193130448757868317015212857 144847836568401237761409643)
  ·
    refine ⟨217271754852601856642114465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144847836568401237761409643 217271754852601856642114465)
    ·
      refine ⟨162953816139451392481585849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217271754852601856642114465 162953816139451392481585849)
      ·
        refine ⟨122215362104588544361189387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162953816139451392481585849 122215362104588544361189387)
        ·
          refine ⟨183323043156882816541784081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122215362104588544361189387 183323043156882816541784081)
          ·
            refine ⟨137492282367662112406338061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183323043156882816541784081 137492282367662112406338061)
            ·
              refine ⟨51559605887873292152376773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 137492282367662112406338061 51559605887873292152376773)
              ·
                refine ⟨9667426103976242278570645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51559605887873292152376773 9667426103976242278570645)
                ·
                  refine ⟨453160598623886356807999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9667426103976242278570645 453160598623886356807999)
                  ·
                    rfl

theorem cell23_7942744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 4, 6].length) (baseStart_7942744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7942744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7942744 prefixEnd_7942744 := by exact prefixLift 7942744
  have htrace : WordTrace (prefixWord ++ tailWord_7942744) baseStart_7942744 baseEnd_7942744 := by
    simpa [prefixWord, tailWord_7942744, baseEnd_7942744] using wordTrace_append hprefix tailTrace_7942744
  have hstable : (prefixWord ++ tailWord_7942744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7942744).length < 2 ^ (prefixWord ++ tailWord_7942744).sum := by decide
  have hdescent : baseEnd_7942744 < baseStart_7942744 := by decide
  rcases family_descends (prefixWord ++ tailWord_7942744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7942791 : List Nat := [1, 1, 4, 2, 1, 2, 3, 3, 1, 5]
def baseStart_7942791 : Nat := 118140960795 + 7942791 * 2 ^ 59
def prefixEnd_7942791 : Nat := 4983230072969 + 3 ^ 40 * 7942791 * 2
def baseEnd_7942791 : Nat := 1359489840401912842461425

theorem tailTrace_7942791 : CollatzResearch.WordTrace tailWord_7942791 prefixEnd_7942791 1359489840401912842461425 := by
  unfold tailWord_7942791
  simp only [CollatzResearch.WordTrace]
  refine ⟨289697387367632202549780227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193131591578421468366520151 289697387367632202549780227)
  ·
    refine ⟨434546081051448303824670341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289697387367632202549780227 434546081051448303824670341)
    ·
      refine ⟨81477390197146556967125689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 434546081051448303824670341 81477390197146556967125689)
      ·
        refine ⟨61108042647859917725344267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81477390197146556967125689 61108042647859917725344267)
        ·
          refine ⟨91662063971789876588016401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61108042647859917725344267 91662063971789876588016401)
          ·
            refine ⟨68746547978842407441012301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91662063971789876588016401 68746547978842407441012301)
            ·
              refine ⟨25779955492065902790379613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68746547978842407441012301 25779955492065902790379613)
              ·
                refine ⟨9667483309524713546392355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25779955492065902790379613 9667483309524713546392355)
                ·
                  refine ⟨14501224964287070319588533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9667483309524713546392355 14501224964287070319588533)
                  ·
                    refine ⟨1359489840401912842461425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14501224964287070319588533 1359489840401912842461425)
                    ·
                      rfl

theorem cell23_7942791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 3, 1, 5].length) (baseStart_7942791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7942791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7942791 prefixEnd_7942791 := by exact prefixLift 7942791
  have htrace : WordTrace (prefixWord ++ tailWord_7942791) baseStart_7942791 baseEnd_7942791 := by
    simpa [prefixWord, tailWord_7942791, baseEnd_7942791] using wordTrace_append hprefix tailTrace_7942791
  have hstable : (prefixWord ++ tailWord_7942791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7942791).length < 2 ^ (prefixWord ++ tailWord_7942791).sum := by decide
  have hdescent : baseEnd_7942791 < baseStart_7942791 := by decide
  rcases family_descends (prefixWord ++ tailWord_7942791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7942798 : List Nat := [4, 1, 1, 3, 1, 1, 2, 1, 4, 3, 2]
def baseStart_7942798 : Nat := 118140960795 + 7942798 * 2 ^ 59
def prefixEnd_7942798 : Nat := 4983230072969 + 3 ^ 40 * 7942798 * 2
def baseEnd_7942798 : Nat := 4078473115570319999996743

theorem tailTrace_7942798 : CollatzResearch.WordTrace tailWord_7942798 prefixEnd_7942798 4078473115570319999996743 := by
  unfold tailWord_7942798
  simp only [CollatzResearch.WordTrace]
  refine ⟨36212205334825855343160631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 193131761785737895163523365 36212205334825855343160631)
  ·
    refine ⟨54318308002238783014740947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36212205334825855343160631 54318308002238783014740947)
    ·
      refine ⟨81477462003358174522111421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54318308002238783014740947 81477462003358174522111421)
      ·
        refine ⟨30554048251259315445791783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81477462003358174522111421 30554048251259315445791783)
        ·
          refine ⟨45831072376888973168687675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30554048251259315445791783 45831072376888973168687675)
          ·
            refine ⟨68746608565333459753031513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45831072376888973168687675 68746608565333459753031513)
            ·
              refine ⟨51559956424000094814773635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68746608565333459753031513 51559956424000094814773635)
              ·
                refine ⟨77339934636000142222160453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51559956424000094814773635 77339934636000142222160453)
                ·
                  refine ⟨14501237744250026666655085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77339934636000142222160453 14501237744250026666655085)
                  ·
                    refine ⟨5437964154093759999995657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14501237744250026666655085 5437964154093759999995657)
                    ·
                      refine ⟨4078473115570319999996743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5437964154093759999995657 4078473115570319999996743)
                      ·
                        rfl

theorem cell23_7942798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 1, 4, 3, 2].length) (baseStart_7942798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7942798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7942798 prefixEnd_7942798 := by exact prefixLift 7942798
  have htrace : WordTrace (prefixWord ++ tailWord_7942798) baseStart_7942798 baseEnd_7942798 := by
    simpa [prefixWord, tailWord_7942798, baseEnd_7942798] using wordTrace_append hprefix tailTrace_7942798
  have hstable : (prefixWord ++ tailWord_7942798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7942798).length < 2 ^ (prefixWord ++ tailWord_7942798).sum := by decide
  have hdescent : baseEnd_7942798 < baseStart_7942798 := by decide
  rcases family_descends (prefixWord ++ tailWord_7942798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7942839 : List Nat := [1, 1, 3, 1, 7, 1, 1, 3, 1, 1, 3]
def baseStart_7942839 : Nat := 118140960795 + 7942839 * 2 ^ 59
def prefixEnd_7942839 : Nat := 4983230072969 + 3 ^ 40 * 7942839 * 2
def baseEnd_7942839 : Nat := 4078494168277154339584055

theorem tailTrace_7942839 : CollatzResearch.WordTrace tailWord_7942839 prefixEnd_7942839 4078494168277154339584055 := by
  unfold tailWord_7942839
  simp only [CollatzResearch.WordTrace]
  refine ⟨289699138071458306747527571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193132758714305537831685047 289699138071458306747527571)
  ·
    refine ⟨434548707107187460121291357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289699138071458306747527571 434548707107187460121291357)
    ·
      refine ⟨162955765165195297545484259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 434548707107187460121291357 162955765165195297545484259)
      ·
        refine ⟨244433647747792946318226389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162955765165195297545484259 244433647747792946318226389)
        ·
          refine ⟨5728913619088897179333431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 244433647747792946318226389 5728913619088897179333431)
          ·
            refine ⟨8593370428633345769000147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5728913619088897179333431 8593370428633345769000147)
            ·
              refine ⟨12890055642950018653500221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8593370428633345769000147 12890055642950018653500221)
              ·
                refine ⟨4833770866106256995062583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12890055642950018653500221 4833770866106256995062583)
                ·
                  refine ⟨7250656299159385492593875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4833770866106256995062583 7250656299159385492593875)
                  ·
                    refine ⟨10875984448739078238890813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7250656299159385492593875 10875984448739078238890813)
                    ·
                      refine ⟨4078494168277154339584055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10875984448739078238890813 4078494168277154339584055)
                      ·
                        rfl

theorem cell23_7942839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 1, 3, 1, 1, 3].length) (baseStart_7942839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7942839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7942839 prefixEnd_7942839 := by exact prefixLift 7942839
  have htrace : WordTrace (prefixWord ++ tailWord_7942839) baseStart_7942839 baseEnd_7942839 := by
    simpa [prefixWord, tailWord_7942839, baseEnd_7942839] using wordTrace_append hprefix tailTrace_7942839
  have hstable : (prefixWord ++ tailWord_7942839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7942839).length < 2 ^ (prefixWord ++ tailWord_7942839).sum := by decide
  have hdescent : baseEnd_7942839 < baseStart_7942839 := by decide
  rcases family_descends (prefixWord ++ tailWord_7942839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7942848 : List Nat := [2, 1, 1, 2, 4, 2, 2, 3, 1, 2, 3]
def baseStart_7942848 : Nat := 118140960795 + 7942848 * 2 ^ 59
def prefixEnd_7942848 : Nat := 4983230072969 + 3 ^ 40 * 7942848 * 2
def baseEnd_7942848 : Nat := 4078498789603044804371513

theorem tailTrace_7942848 : CollatzResearch.WordTrace tailWord_7942848 prefixEnd_7942848 4078498789603044804371513 := by
  unfold tailWord_7942848
  simp only [CollatzResearch.WordTrace]
  refine ⟨144849733164212850642302599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193132977552283800856403465 144849733164212850642302599)
  ·
    refine ⟨217274599746319275963453899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144849733164212850642302599 217274599746319275963453899)
    ·
      refine ⟨325911899619478913945180849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217274599746319275963453899 325911899619478913945180849)
      ·
        refine ⟨244433924714609185458885637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 325911899619478913945180849 244433924714609185458885637)
        ·
          refine ⟨45831360883989222273541057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 244433924714609185458885637 45831360883989222273541057)
          ·
            refine ⟨34373520662991916705155793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45831360883989222273541057 34373520662991916705155793)
            ·
              refine ⟨25780140497243937528866845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34373520662991916705155793 25780140497243937528866845)
              ·
                refine ⟨9667552686466476573325067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25780140497243937528866845 9667552686466476573325067)
                ·
                  refine ⟨14501329029699714859987601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9667552686466476573325067 14501329029699714859987601)
                  ·
                    refine ⟨10875996772274786144990701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14501329029699714859987601 10875996772274786144990701)
                    ·
                      refine ⟨4078498789603044804371513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10875996772274786144990701 4078498789603044804371513)
                      ·
                        rfl

theorem cell23_7942848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 3, 1, 2, 3].length) (baseStart_7942848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7942848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7942848 prefixEnd_7942848 := by exact prefixLift 7942848
  have htrace : WordTrace (prefixWord ++ tailWord_7942848) baseStart_7942848 baseEnd_7942848 := by
    simpa [prefixWord, tailWord_7942848, baseEnd_7942848] using wordTrace_append hprefix tailTrace_7942848
  have hstable : (prefixWord ++ tailWord_7942848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7942848).length < 2 ^ (prefixWord ++ tailWord_7942848).sum := by decide
  have hdescent : baseEnd_7942848 < baseStart_7942848 := by decide
  rcases family_descends (prefixWord ++ tailWord_7942848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7942862 : List Nat := [4, 1, 1, 1, 3, 4, 1, 1, 3, 2, 2]
def baseStart_7942862 : Nat := 118140960795 + 7942862 * 2 ^ 59
def prefixEnd_7942862 : Nat := 4983230072969 + 3 ^ 40 * 7942862 * 2
def baseEnd_7942862 : Nat := 4078505978332207749596449

theorem tailTrace_7942862 : CollatzResearch.WordTrace tailWord_7942862 prefixEnd_7942862 4078505978332207749596449 := by
  unfold tailWord_7942862
  simp only [CollatzResearch.WordTrace]
  refine ⟨36212497118796872709451855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 193133317966916654450409893 36212497118796872709451855)
  ·
    refine ⟨54318745678195309064177783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36212497118796872709451855 54318745678195309064177783)
    ·
      refine ⟨81478118517292963596266675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54318745678195309064177783 81478118517292963596266675)
      ·
        refine ⟨122217177775939445394400013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81478118517292963596266675 122217177775939445394400013)
        ·
          refine ⟨45831441665977292022900005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122217177775939445394400013 45831441665977292022900005)
          ·
            refine ⟨8593395312370742254293751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45831441665977292022900005 8593395312370742254293751)
            ·
              refine ⟨12890092968556113381440627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8593395312370742254293751 12890092968556113381440627)
              ·
                refine ⟨19335139452834170072160941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12890092968556113381440627 19335139452834170072160941)
                ·
                  refine ⟨7250677294812813777060353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19335139452834170072160941 7250677294812813777060353)
                  ·
                    refine ⟨5438007971109610332795265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7250677294812813777060353 5438007971109610332795265)
                    ·
                      refine ⟨4078505978332207749596449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5438007971109610332795265 4078505978332207749596449)
                      ·
                        rfl

theorem cell23_7942862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 1, 1, 3, 2, 2].length) (baseStart_7942862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7942862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7942862 prefixEnd_7942862 := by exact prefixLift 7942862
  have htrace : WordTrace (prefixWord ++ tailWord_7942862) baseStart_7942862 baseEnd_7942862 := by
    simpa [prefixWord, tailWord_7942862, baseEnd_7942862] using wordTrace_append hprefix tailTrace_7942862
  have hstable : (prefixWord ++ tailWord_7942862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7942862).length < 2 ^ (prefixWord ++ tailWord_7942862).sum := by decide
  have hdescent : baseEnd_7942862 < baseStart_7942862 := by decide
  rcases family_descends (prefixWord ++ tailWord_7942862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7942868 : List Nat := [2, 4, 1, 3, 2, 1, 2, 8]
def baseStart_7942868 : Nat := 118140960795 + 7942868 * 2 ^ 59
def prefixEnd_7942868 : Nat := 4983230072969 + 3 ^ 40 * 7942868 * 2
def baseEnd_7942868 : Nat := 151055891082079063930423

theorem tailTrace_7942868 : CollatzResearch.WordTrace tailWord_7942868 prefixEnd_7942868 151055891082079063930423 := by
  unfold tailWord_7942868
  simp only [CollatzResearch.WordTrace]
  refine ⟨144850097894176622350166629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193133463858902163133555505 144850097894176622350166629)
  ·
    refine ⟨27159393355158116690656243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 144850097894176622350166629 27159393355158116690656243)
    ·
      refine ⟨40739090032737175035984365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27159393355158116690656243 40739090032737175035984365)
      ·
        refine ⟨15277158762276440638494137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40739090032737175035984365 15277158762276440638494137)
        ·
          refine ⟨11457869071707330478870603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15277158762276440638494137 11457869071707330478870603)
          ·
            refine ⟨17186803607560995718305905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11457869071707330478870603 17186803607560995718305905)
            ·
              refine ⟨12890102705670746788729429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17186803607560995718305905 12890102705670746788729429)
              ·
                refine ⟨151055891082079063930423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12890102705670746788729429 151055891082079063930423)
                ·
                  rfl

theorem cell23_7942868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 2, 8].length) (baseStart_7942868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7942868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7942868 prefixEnd_7942868 := by exact prefixLift 7942868
  have htrace : WordTrace (prefixWord ++ tailWord_7942868) baseStart_7942868 baseEnd_7942868 := by
    simpa [prefixWord, tailWord_7942868, baseEnd_7942868] using wordTrace_append hprefix tailTrace_7942868
  have hstable : (prefixWord ++ tailWord_7942868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7942868).length < 2 ^ (prefixWord ++ tailWord_7942868).sum := by decide
  have hdescent : baseEnd_7942868 < baseStart_7942868 := by decide
  rcases family_descends (prefixWord ++ tailWord_7942868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7942921 : List Nat := [1, 2, 1, 1, 3, 2, 3, 1, 2, 4, 3]
def baseStart_7942921 : Nat := 118140960795 + 7942921 * 2 ^ 59
def prefixEnd_7942921 : Nat := 4983230072969 + 3 ^ 40 * 7942921 * 2
def baseEnd_7942921 : Nat := 4078536273690823018758677

theorem tailTrace_7942921 : CollatzResearch.WordTrace tailWord_7942921 prefixEnd_7942921 4078536273690823018758677 := by
  unfold tailWord_7942921
  simp only [CollatzResearch.WordTrace]
  refine ⟨289702128857161234752012617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193134752571440823168008411 289702128857161234752012617)
  ·
    refine ⟨217276596642870926064009463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289702128857161234752012617 217276596642870926064009463)
    ·
      refine ⟨325914894964306389096014195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217276596642870926064009463 325914894964306389096014195)
      ·
        refine ⟨488872342446459583644021293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 325914894964306389096014195 488872342446459583644021293)
        ·
          refine ⟨183327128417422343866507985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 488872342446459583644021293 183327128417422343866507985)
          ·
            refine ⟨137495346313066757899880989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183327128417422343866507985 137495346313066757899880989)
            ·
              refine ⟨51560754867400034212455371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 137495346313066757899880989 51560754867400034212455371)
              ·
                refine ⟨77341132301100051318683057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51560754867400034212455371 77341132301100051318683057)
                ·
                  refine ⟨58005849225825038489012293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77341132301100051318683057 58005849225825038489012293)
                  ·
                    refine ⟨10876096729842194716689805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58005849225825038489012293 10876096729842194716689805)
                    ·
                      refine ⟨4078536273690823018758677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10876096729842194716689805 4078536273690823018758677)
                      ·
                        rfl

theorem cell23_7942921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 1, 2, 4, 3].length) (baseStart_7942921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7942921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7942921 prefixEnd_7942921 := by exact prefixLift 7942921
  have htrace : WordTrace (prefixWord ++ tailWord_7942921) baseStart_7942921 baseEnd_7942921 := by
    simpa [prefixWord, tailWord_7942921, baseEnd_7942921] using wordTrace_append hprefix tailTrace_7942921
  have hstable : (prefixWord ++ tailWord_7942921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7942921).length < 2 ^ (prefixWord ++ tailWord_7942921).sum := by decide
  have hdescent : baseEnd_7942921 < baseStart_7942921 := by decide
  rcases family_descends (prefixWord ++ tailWord_7942921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7942931 : List Nat := [1, 1, 1, 2, 1, 3, 5, 1, 2, 2, 4]
def baseStart_7942931 : Nat := 118140960795 + 7942931 * 2 ^ 59
def prefixEnd_7942931 : Nat := 4983230072969 + 3 ^ 40 * 7942931 * 2
def baseEnd_7942931 : Nat := 4078541408497367979633631

theorem tailTrace_7942931 : CollatzResearch.WordTrace tailWord_7942931 prefixEnd_7942931 4078541408497367979633631 := by
  unfold tailWord_7942931
  simp only [CollatzResearch.WordTrace]
  refine ⟨289702493587125006459876647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193134995724750004306584431 289702493587125006459876647)
  ·
    refine ⟨434553740380687509689814971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289702493587125006459876647 434553740380687509689814971)
    ·
      refine ⟨651830610571031264534722457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 434553740380687509689814971 651830610571031264534722457)
      ·
        refine ⟨488872957928273448401041843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 651830610571031264534722457 488872957928273448401041843)
        ·
          refine ⟨733309436892410172601562765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 488872957928273448401041843 733309436892410172601562765)
          ·
            refine ⟨274991038834653814725586037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 733309436892410172601562765 274991038834653814725586037)
            ·
              refine ⟨25780409890748795130523691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 274991038834653814725586037 25780409890748795130523691)
              ·
                refine ⟨38670614836123192695785537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25780409890748795130523691 38670614836123192695785537)
                ·
                  refine ⟨29002961127092394521839153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38670614836123192695785537 29002961127092394521839153)
                  ·
                    refine ⟨21752220845319295891379365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29002961127092394521839153 21752220845319295891379365)
                    ·
                      refine ⟨4078541408497367979633631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21752220845319295891379365 4078541408497367979633631)
                      ·
                        rfl

theorem cell23_7942931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 1, 2, 2, 4].length) (baseStart_7942931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7942931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7942931 prefixEnd_7942931 := by exact prefixLift 7942931
  have htrace : WordTrace (prefixWord ++ tailWord_7942931) baseStart_7942931 baseEnd_7942931 := by
    simpa [prefixWord, tailWord_7942931, baseEnd_7942931] using wordTrace_append hprefix tailTrace_7942931
  have hstable : (prefixWord ++ tailWord_7942931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7942931).length < 2 ^ (prefixWord ++ tailWord_7942931).sum := by decide
  have hdescent : baseEnd_7942931 < baseStart_7942931 := by decide
  rcases family_descends (prefixWord ++ tailWord_7942931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7943008 : List Nat := [2, 1, 1, 3, 3, 1, 2, 3, 2, 1, 4]
def baseStart_7943008 : Nat := 118140960795 + 7943008 * 2 ^ 59
def prefixEnd_7943008 : Nat := 4983230072969 + 3 ^ 40 * 7943008 * 2
def baseEnd_7943008 : Nat := 4078580946507764178370777

theorem tailTrace_7943008 : CollatzResearch.WordTrace tailWord_7943008 prefixEnd_7943008 4078580946507764178370777 := by
  unfold tailWord_7943008
  simp only [CollatzResearch.WordTrace]
  refine ⟨144852651003923024305214839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193136868005230699073619785 144852651003923024305214839)
  ·
    refine ⟨217278976505884536457822259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144852651003923024305214839 217278976505884536457822259)
    ·
      refine ⟨325918464758826804686733389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217278976505884536457822259 325918464758826804686733389)
      ·
        refine ⟨122219424284560051757525021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 325918464758826804686733389 122219424284560051757525021)
        ·
          refine ⟨45832284106710019409071883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122219424284560051757525021 45832284106710019409071883)
          ·
            refine ⟨68748426160065029113607825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45832284106710019409071883 68748426160065029113607825)
            ·
              refine ⟨51561319620048771835205869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68748426160065029113607825 51561319620048771835205869)
              ·
                refine ⟨19335494857518289438202201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51561319620048771835205869 19335494857518289438202201)
                ·
                  refine ⟨14501621143138717078651651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19335494857518289438202201 14501621143138717078651651)
                  ·
                    refine ⟨21752431714708075617977477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14501621143138717078651651 21752431714708075617977477)
                    ·
                      refine ⟨4078580946507764178370777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21752431714708075617977477 4078580946507764178370777)
                      ·
                        rfl

theorem cell23_7943008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 3, 2, 1, 4].length) (baseStart_7943008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7943008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7943008 prefixEnd_7943008 := by exact prefixLift 7943008
  have htrace : WordTrace (prefixWord ++ tailWord_7943008) baseStart_7943008 baseEnd_7943008 := by
    simpa [prefixWord, tailWord_7943008, baseEnd_7943008] using wordTrace_append hprefix tailTrace_7943008
  have hstable : (prefixWord ++ tailWord_7943008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7943008).length < 2 ^ (prefixWord ++ tailWord_7943008).sum := by decide
  have hdescent : baseEnd_7943008 < baseStart_7943008 := by decide
  rcases family_descends (prefixWord ++ tailWord_7943008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7943035 : List Nat := [1, 1, 1, 1, 1, 5, 2, 6, 1, 4]
def baseStart_7943035 : Nat := 118140960795 + 7943035 * 2 ^ 59
def prefixEnd_7943035 : Nat := 4983230072969 + 3 ^ 40 * 7943035 * 2
def baseEnd_7943035 : Nat := 1359531603495145190911051

theorem tailTrace_7943035 : CollatzResearch.WordTrace tailWord_7943035 prefixEnd_7943035 1359531603495145190911051 := by
  unfold tailWord_7943035
  simp only [CollatzResearch.WordTrace]
  refine ⟨289706286778748232221662559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193137524519165488147775039 289706286778748232221662559)
  ·
    refine ⟨434559430168122348332493839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289706286778748232221662559 434559430168122348332493839)
    ·
      refine ⟨651839145252183522498740759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 434559430168122348332493839 651839145252183522498740759)
      ·
        refine ⟨977758717878275283748111139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 651839145252183522498740759 977758717878275283748111139)
        ·
          refine ⟨1466638076817412925622166709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 977758717878275283748111139 1466638076817412925622166709)
          ·
            refine ⟨137497319701632461777078129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1466638076817412925622166709 137497319701632461777078129)
            ·
              refine ⟨103122989776224346332808597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137497319701632461777078129 103122989776224346332808597)
              ·
                refine ⟨4833890145760516234350403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 103122989776224346332808597 4833890145760516234350403)
                ·
                  refine ⟨7250835218640774351525605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4833890145760516234350403 7250835218640774351525605)
                  ·
                    refine ⟨1359531603495145190911051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7250835218640774351525605 1359531603495145190911051)
                    ·
                      rfl

theorem cell23_7943035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 6, 1, 4].length) (baseStart_7943035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7943035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7943035 prefixEnd_7943035 := by exact prefixLift 7943035
  have htrace : WordTrace (prefixWord ++ tailWord_7943035) baseStart_7943035 baseEnd_7943035 := by
    simpa [prefixWord, tailWord_7943035, baseEnd_7943035] using wordTrace_append hprefix tailTrace_7943035
  have hstable : (prefixWord ++ tailWord_7943035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7943035).length < 2 ^ (prefixWord ++ tailWord_7943035).sum := by decide
  have hdescent : baseEnd_7943035 < baseStart_7943035 := by decide
  rcases family_descends (prefixWord ++ tailWord_7943035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7943051 : List Nat := [1, 1, 1, 1, 4, 2, 2, 2, 1, 2, 6]
def baseStart_7943051 : Nat := 118140960795 + 7943051 * 2 ^ 59
def prefixEnd_7943051 : Nat := 4983230072969 + 3 ^ 40 * 7943051 * 2
def baseEnd_7943051 : Nat := 4078603026175907510133079

theorem tailTrace_7943051 : CollatzResearch.WordTrace tailWord_7943051 prefixEnd_7943051 4078603026175907510133079 := by
  unfold tailWord_7943051
  simp only [CollatzResearch.WordTrace]
  refine ⟨289706870346690266954245007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193137913564460177969496671 289706870346690266954245007)
  ·
    refine ⟨434560305520035400431367511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289706870346690266954245007 434560305520035400431367511)
    ·
      refine ⟨651840458280053100647051267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 434560305520035400431367511 651840458280053100647051267)
      ·
        refine ⟨977760687420079650970576901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 651840458280053100647051267 977760687420079650970576901)
        ·
          refine ⟨183330128891264934556983169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 977760687420079650970576901 183330128891264934556983169)
          ·
            refine ⟨137497596668448700917737377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183330128891264934556983169 137497596668448700917737377)
            ·
              refine ⟨103123197501336525688303033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137497596668448700917737377 103123197501336525688303033)
              ·
                refine ⟨77342398126002394266227275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103123197501336525688303033 77342398126002394266227275)
                ·
                  refine ⟨116013597189003591399340913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77342398126002394266227275 116013597189003591399340913)
                  ·
                    refine ⟨87010197891752693549505685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 116013597189003591399340913 87010197891752693549505685)
                    ·
                      refine ⟨4078603026175907510133079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 87010197891752693549505685 4078603026175907510133079)
                      ·
                        rfl

theorem cell23_7943051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 2, 1, 2, 6].length) (baseStart_7943051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7943051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7943051 prefixEnd_7943051 := by exact prefixLift 7943051
  have htrace : WordTrace (prefixWord ++ tailWord_7943051) baseStart_7943051 baseEnd_7943051 := by
    simpa [prefixWord, tailWord_7943051, baseEnd_7943051] using wordTrace_append hprefix tailTrace_7943051
  have hstable : (prefixWord ++ tailWord_7943051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7943051).length < 2 ^ (prefixWord ++ tailWord_7943051).sum := by decide
  have hdescent : baseEnd_7943051 < baseStart_7943051 := by decide
  rcases family_descends (prefixWord ++ tailWord_7943051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7943098 : List Nat := [3, 1, 1, 1, 2, 1, 3, 1, 5, 1, 4]
def baseStart_7943098 : Nat := 118140960795 + 7943098 * 2 ^ 59
def prefixEnd_7943098 : Nat := 4983230072969 + 3 ^ 40 * 7943098 * 2
def baseEnd_7943098 : Nat := 4078627159766668826245363

theorem tailTrace_7943098 : CollatzResearch.WordTrace tailWord_7943098 prefixEnd_7943098 4078627159766668826245363 := by
  unfold tailWord_7943098
  simp only [CollatzResearch.WordTrace]
  refine ⟨72427146144379998495301487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193139056385013329320803965 72427146144379998495301487)
  ·
    refine ⟨108640719216569997742952231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72427146144379998495301487 108640719216569997742952231)
    ·
      refine ⟨162961078824854996614428347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108640719216569997742952231 162961078824854996614428347)
      ·
        refine ⟨244441618237282494921642521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162961078824854996614428347 244441618237282494921642521)
        ·
          refine ⟨183331213677961871191231891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 244441618237282494921642521 183331213677961871191231891)
          ·
            refine ⟨274996820516942806786847837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183331213677961871191231891 274996820516942806786847837)
            ·
              refine ⟨103123807693853552545067939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 274996820516942806786847837 103123807693853552545067939)
              ·
                refine ⟨154685711540780328817601909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103123807693853552545067939 154685711540780328817601909)
                ·
                  refine ⟨14501785456948155826650179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 154685711540780328817601909 14501785456948155826650179)
                  ·
                    refine ⟨21752678185422233739975269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14501785456948155826650179 21752678185422233739975269)
                    ·
                      refine ⟨4078627159766668826245363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21752678185422233739975269 4078627159766668826245363)
                      ·
                        rfl

theorem cell23_7943098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 1, 5, 1, 4].length) (baseStart_7943098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7943098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7943098 prefixEnd_7943098 := by exact prefixLift 7943098
  have htrace : WordTrace (prefixWord ++ tailWord_7943098) baseStart_7943098 baseEnd_7943098 := by
    simpa [prefixWord, tailWord_7943098, baseEnd_7943098] using wordTrace_append hprefix tailTrace_7943098
  have hstable : (prefixWord ++ tailWord_7943098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7943098).length < 2 ^ (prefixWord ++ tailWord_7943098).sum := by decide
  have hdescent : baseEnd_7943098 < baseStart_7943098 := by decide
  rcases family_descends (prefixWord ++ tailWord_7943098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7943110 : List Nat := [6, 1, 3, 1, 2, 1, 1, 1, 2, 1, 4]
def baseStart_7943110 : Nat := 118140960795 + 7943110 * 2 ^ 59
def prefixEnd_7943110 : Nat := 4983230072969 + 3 ^ 40 * 7943110 * 2
def baseEnd_7943110 : Nat := 4078633321534522779295309

theorem tailTrace_7943110 : CollatzResearch.WordTrace tailWord_7943110 prefixEnd_7943110 4078633321534522779295309 := by
  unfold tailWord_7943110
  simp only [CollatzResearch.WordTrace]
  refine ⟨9053406945421141250957587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 193139348168984346687095189 9053406945421141250957587)
  ·
    refine ⟨13580110418131711876436381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9053406945421141250957587 13580110418131711876436381)
    ·
      refine ⟨5092541406799391953663643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13580110418131711876436381 5092541406799391953663643)
      ·
        refine ⟨7638812110199087930495465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5092541406799391953663643 7638812110199087930495465)
        ·
          refine ⟨5729109082649315947871599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7638812110199087930495465 5729109082649315947871599)
          ·
            refine ⟨8593663623973973921807399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5729109082649315947871599 8593663623973973921807399)
            ·
              refine ⟨12890495435960960882711099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8593663623973973921807399 12890495435960960882711099)
              ·
                refine ⟨19335743153941441324066649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12890495435960960882711099 19335743153941441324066649)
                ·
                  refine ⟨14501807365456080993049987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19335743153941441324066649 14501807365456080993049987)
                  ·
                    refine ⟨21752711048184121489574981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14501807365456080993049987 21752711048184121489574981)
                    ·
                      refine ⟨4078633321534522779295309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21752711048184121489574981 4078633321534522779295309)
                      ·
                        rfl

theorem cell23_7943110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 1, 1, 2, 1, 4].length) (baseStart_7943110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7943110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7943110 prefixEnd_7943110 := by exact prefixLift 7943110
  have htrace : WordTrace (prefixWord ++ tailWord_7943110) baseStart_7943110 baseEnd_7943110 := by
    simpa [prefixWord, tailWord_7943110, baseEnd_7943110] using wordTrace_append hprefix tailTrace_7943110
  have hstable : (prefixWord ++ tailWord_7943110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7943110).length < 2 ^ (prefixWord ++ tailWord_7943110).sum := by decide
  have hdescent : baseEnd_7943110 < baseStart_7943110 := by decide
  rcases family_descends (prefixWord ++ tailWord_7943110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7943126 : List Nat := [5, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3]
def baseStart_7943126 : Nat := 118140960795 + 7943126 * 2 ^ 59
def prefixEnd_7943126 : Nat := 4983230072969 + 3 ^ 40 * 7943126 * 2
def baseEnd_7943126 : Nat := 4078641537224994716695235

theorem tailTrace_7943126 : CollatzResearch.WordTrace tailWord_7943126 prefixEnd_7943126 4078641537224994716695235 := by
  unfold tailWord_7943126
  simp only [CollatzResearch.WordTrace]
  refine ⟨18106850363838659672701577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 193139737214279036508816821 18106850363838659672701577)
  ·
    refine ⟨13580137772878994754526183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18106850363838659672701577 13580137772878994754526183)
    ·
      refine ⟨20370206659318492131789275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13580137772878994754526183 20370206659318492131789275)
      ·
        refine ⟨30555309988977738197683913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20370206659318492131789275 30555309988977738197683913)
        ·
          refine ⟨22916482491733303648262935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30555309988977738197683913 22916482491733303648262935)
          ·
            refine ⟨34374723737599955472394403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22916482491733303648262935 34374723737599955472394403)
            ·
              refine ⟨51562085606399933208591605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34374723737599955472394403 51562085606399933208591605)
              ·
                refine ⟨4833945525599993738305463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51562085606399933208591605 4833945525599993738305463)
                ·
                  refine ⟨7250918288399990607458195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4833945525599993738305463 7250918288399990607458195)
                  ·
                    refine ⟨10876377432599985911187293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7250918288399990607458195 10876377432599985911187293)
                    ·
                      refine ⟨4078641537224994716695235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10876377432599985911187293 4078641537224994716695235)
                      ·
                        rfl

theorem cell23_7943126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3].length) (baseStart_7943126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7943126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7943126 prefixEnd_7943126 := by exact prefixLift 7943126
  have htrace : WordTrace (prefixWord ++ tailWord_7943126) baseStart_7943126 baseEnd_7943126 := by
    simpa [prefixWord, tailWord_7943126, baseEnd_7943126] using wordTrace_append hprefix tailTrace_7943126
  have hstable : (prefixWord ++ tailWord_7943126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7943126).length < 2 ^ (prefixWord ++ tailWord_7943126).sum := by decide
  have hdescent : baseEnd_7943126 < baseStart_7943126 := by decide
  rcases family_descends (prefixWord ++ tailWord_7943126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7943148 : List Nat := [2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 3]
def baseStart_7943148 : Nat := 118140960795 + 7943148 * 2 ^ 59
def prefixEnd_7943148 : Nat := 4983230072969 + 3 ^ 40 * 7943148 * 2
def baseEnd_7943148 : Nat := 4078652833799393630620133

theorem tailTrace_7943148 : CollatzResearch.WordTrace tailWord_7943148 prefixEnd_7943148 4078652833799393630620133 := by
  unfold tailWord_7943148
  simp only [CollatzResearch.WordTrace]
  refine ⟨144855204113669426260263049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193140272151559235013684065 144855204113669426260263049)
  ·
    refine ⟨108641403085252069695197287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144855204113669426260263049 108641403085252069695197287)
    ·
      refine ⟨162962104627878104542795931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108641403085252069695197287 162962104627878104542795931)
      ·
        refine ⟨244443156941817156814193897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162962104627878104542795931 244443156941817156814193897)
        ·
          refine ⟨183332367706362867610645423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 244443156941817156814193897 183332367706362867610645423)
          ·
            refine ⟨274998551559544301415968135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183332367706362867610645423 274998551559544301415968135)
            ·
              refine ⟨412497827339316452123952203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 274998551559544301415968135 412497827339316452123952203)
              ·
                refine ⟨618746741008974678185928305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 412497827339316452123952203 618746741008974678185928305)
                ·
                  refine ⟨464060055756731008639446229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 618746741008974678185928305 464060055756731008639446229)
                  ·
                    refine ⟨10876407556798383014987021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 464060055756731008639446229 10876407556798383014987021)
                    ·
                      refine ⟨4078652833799393630620133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10876407556798383014987021 4078652833799393630620133)
                      ·
                        rfl

theorem cell23_7943148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 3].length) (baseStart_7943148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7943148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7943148 prefixEnd_7943148 := by exact prefixLift 7943148
  have htrace : WordTrace (prefixWord ++ tailWord_7943148) baseStart_7943148 baseEnd_7943148 := by
    simpa [prefixWord, tailWord_7943148, baseEnd_7943148] using wordTrace_append hprefix tailTrace_7943148
  have hstable : (prefixWord ++ tailWord_7943148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7943148).length < 2 ^ (prefixWord ++ tailWord_7943148).sum := by decide
  have hdescent : baseEnd_7943148 < baseStart_7943148 := by decide
  rcases family_descends (prefixWord ++ tailWord_7943148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7943182 : List Nat := [4, 1, 1, 2, 2, 2, 1, 2, 4, 1, 3]
def baseStart_7943182 : Nat := 118140960795 + 7943182 * 2 ^ 59
def prefixEnd_7943182 : Nat := 4983230072969 + 3 ^ 40 * 7943182 * 2
def baseEnd_7943182 : Nat := 4078670292141646497594977

theorem tailTrace_7943182 : CollatzResearch.WordTrace tailWord_7943182 prefixEnd_7943182 4078670292141646497594977 := by
  unfold tailWord_7943182
  simp only [CollatzResearch.WordTrace]
  refine ⟨36213956038651959540907975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 193141098872810450884842533 36213956038651959540907975)
  ·
    refine ⟨54320934057977939311361963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36213956038651959540907975 54320934057977939311361963)
    ·
      refine ⟨81481401086966908967042945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54320934057977939311361963 81481401086966908967042945)
      ·
        refine ⟨61111050815225181725282209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81481401086966908967042945 61111050815225181725282209)
        ·
          refine ⟨45833288111418886293961657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61111050815225181725282209 45833288111418886293961657)
          ·
            refine ⟨34374966083564164720471243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45833288111418886293961657 34374966083564164720471243)
            ·
              refine ⟨51562449125346247080706865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34374966083564164720471243 51562449125346247080706865)
              ·
                refine ⟨38671836844009685310530149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51562449125346247080706865 38671836844009685310530149)
                ·
                  refine ⟨7250969408251815995724403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38671836844009685310530149 7250969408251815995724403)
                  ·
                    refine ⟨10876454112377723993586605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7250969408251815995724403 10876454112377723993586605)
                    ·
                      refine ⟨4078670292141646497594977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10876454112377723993586605 4078670292141646497594977)
                      ·
                        rfl

theorem cell23_7943182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 2, 4, 1, 3].length) (baseStart_7943182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7943182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7943182 prefixEnd_7943182 := by exact prefixLift 7943182
  have htrace : WordTrace (prefixWord ++ tailWord_7943182) baseStart_7943182 baseEnd_7943182 := by
    simpa [prefixWord, tailWord_7943182, baseEnd_7943182] using wordTrace_append hprefix tailTrace_7943182
  have hstable : (prefixWord ++ tailWord_7943182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7943182).length < 2 ^ (prefixWord ++ tailWord_7943182).sum := by decide
  have hdescent : baseEnd_7943182 < baseStart_7943182 := by decide
  rcases family_descends (prefixWord ++ tailWord_7943182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7943186 : List Nat := [3, 2, 5, 1, 1, 1, 2, 1, 1, 1, 5]
def baseStart_7943186 : Nat := 118140960795 + 7943186 * 2 ^ 59
def prefixEnd_7943186 : Nat := 4983230072969 + 3 ^ 40 * 7943186 * 2
def baseEnd_7943186 : Nat := 4078672346064264481944959

theorem tailTrace_7943186 : CollatzResearch.WordTrace tailWord_7943186 prefixEnd_7943186 4078672346064264481944959 := by
  unfold tailWord_7943186
  simp only [CollatzResearch.WordTrace]
  refine ⟨72427948550300296252602353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193141196134134123340272941 72427948550300296252602353)
  ·
    refine ⟨54320961412725222189451765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72427948550300296252602353 54320961412725222189451765)
    ·
      refine ⟨5092590132442989580261103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 54320961412725222189451765 5092590132442989580261103)
      ·
        refine ⟨7638885198664484370391655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5092590132442989580261103 7638885198664484370391655)
        ·
          refine ⟨11458327797996726555587483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7638885198664484370391655 11458327797996726555587483)
          ·
            refine ⟨17187491696995089833381225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11458327797996726555587483 17187491696995089833381225)
            ·
              refine ⟨12890618772746317375035919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17187491696995089833381225 12890618772746317375035919)
              ·
                refine ⟨19335928159119476062553879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12890618772746317375035919 19335928159119476062553879)
                ·
                  refine ⟨29003892238679214093830819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19335928159119476062553879 29003892238679214093830819)
                  ·
                    refine ⟨43505838358018821140746229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29003892238679214093830819 43505838358018821140746229)
                    ·
                      refine ⟨4078672346064264481944959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43505838358018821140746229 4078672346064264481944959)
                      ·
                        rfl

theorem cell23_7943186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_7943186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7943186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7943186 prefixEnd_7943186 := by exact prefixLift 7943186
  have htrace : WordTrace (prefixWord ++ tailWord_7943186) baseStart_7943186 baseEnd_7943186 := by
    simpa [prefixWord, tailWord_7943186, baseEnd_7943186] using wordTrace_append hprefix tailTrace_7943186
  have hstable : (prefixWord ++ tailWord_7943186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7943186).length < 2 ^ (prefixWord ++ tailWord_7943186).sum := by decide
  have hdescent : baseEnd_7943186 < baseStart_7943186 := by decide
  rcases family_descends (prefixWord ++ tailWord_7943186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7943200 : List Nat := [2, 1, 1, 7, 1, 1, 3, 2, 1, 2, 2]
def baseStart_7943200 : Nat := 118140960795 + 7943200 * 2 ^ 59
def prefixEnd_7943200 : Nat := 4983230072969 + 3 ^ 40 * 7943200 * 2
def baseEnd_7943200 : Nat := 4078679534793427427169895

theorem tailTrace_7943200 : CollatzResearch.WordTrace tailWord_7943200 prefixEnd_7943200 4078679534793427427169895 := by
  unfold tailWord_7943200
  simp only [CollatzResearch.WordTrace]
  refine ⟨144856152411575232700709527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193141536548766976934279369 144856152411575232700709527)
  ·
    refine ⟨217284228617362849051064291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144856152411575232700709527 217284228617362849051064291)
    ·
      refine ⟨325926342926044273576596437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217284228617362849051064291 325926342926044273576596437)
      ·
        refine ⟨7638898662329162661951479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 325926342926044273576596437 7638898662329162661951479)
        ·
          refine ⟨11458347993493743992927219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7638898662329162661951479 11458347993493743992927219)
          ·
            refine ⟨17187521990240615989390829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11458347993493743992927219 17187521990240615989390829)
            ·
              refine ⟨6445320746340230996021561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17187521990240615989390829 6445320746340230996021561)
              ·
                refine ⟨4833990559755173247016171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6445320746340230996021561 4833990559755173247016171)
                ·
                  refine ⟨7250985839632759870524257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4833990559755173247016171 7250985839632759870524257)
                  ·
                    refine ⟨5438239379724569902893193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7250985839632759870524257 5438239379724569902893193)
                    ·
                      refine ⟨4078679534793427427169895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5438239379724569902893193 4078679534793427427169895)
                      ·
                        rfl

theorem cell23_7943200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 3, 2, 1, 2, 2].length) (baseStart_7943200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7943200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7943200 prefixEnd_7943200 := by exact prefixLift 7943200
  have htrace : WordTrace (prefixWord ++ tailWord_7943200) baseStart_7943200 baseEnd_7943200 := by
    simpa [prefixWord, tailWord_7943200, baseEnd_7943200] using wordTrace_append hprefix tailTrace_7943200
  have hstable : (prefixWord ++ tailWord_7943200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7943200).length < 2 ^ (prefixWord ++ tailWord_7943200).sum := by decide
  have hdescent : baseEnd_7943200 < baseStart_7943200 := by decide
  rcases family_descends (prefixWord ++ tailWord_7943200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7943225 : List Nat := [1, 2, 1, 5, 2, 1, 1, 2, 2, 1, 5]
def baseStart_7943225 : Nat := 118140960795 + 7943225 * 2 ^ 59
def prefixEnd_7943225 : Nat := 4983230072969 + 3 ^ 40 * 7943225 * 2
def baseEnd_7943225 : Nat := 4078692371809789829357279

theorem tailTrace_7943225 : CollatzResearch.WordTrace tailWord_7943225 prefixEnd_7943225 4078692371809789829357279 := by
  unfold tailWord_7943225
  simp only [CollatzResearch.WordTrace]
  refine ⟨289713216648059894671079129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193142144432039929780719419 289713216648059894671079129)
  ·
    refine ⟨217284912486044921003309347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289713216648059894671079129 217284912486044921003309347)
    ·
      refine ⟨325927368729067381504964021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217284912486044921003309347 325927368729067381504964021)
      ·
        refine ⟨30555690818350067016090377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 325927368729067381504964021 30555690818350067016090377)
        ·
          refine ⟨22916768113762550262067783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30555690818350067016090377 22916768113762550262067783)
          ·
            refine ⟨34375152170643825393101675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22916768113762550262067783 34375152170643825393101675)
            ·
              refine ⟨51562728255965738089652513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34375152170643825393101675 51562728255965738089652513)
              ·
                refine ⟨38672046191974303567239385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51562728255965738089652513 38672046191974303567239385)
                ·
                  refine ⟨29004034643980727675429539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38672046191974303567239385 29004034643980727675429539)
                  ·
                    refine ⟨43506051965971091513144309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29004034643980727675429539 43506051965971091513144309)
                    ·
                      refine ⟨4078692371809789829357279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43506051965971091513144309 4078692371809789829357279)
                      ·
                        rfl

theorem cell23_7943225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 2, 2, 1, 5].length) (baseStart_7943225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7943225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7943225 prefixEnd_7943225 := by exact prefixLift 7943225
  have htrace : WordTrace (prefixWord ++ tailWord_7943225) baseStart_7943225 baseEnd_7943225 := by
    simpa [prefixWord, tailWord_7943225, baseEnd_7943225] using wordTrace_append hprefix tailTrace_7943225
  have hstable : (prefixWord ++ tailWord_7943225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7943225).length < 2 ^ (prefixWord ++ tailWord_7943225).sum := by decide
  have hdescent : baseEnd_7943225 < baseStart_7943225 := by decide
  rcases family_descends (prefixWord ++ tailWord_7943225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7943255 : List Nat := [1, 1, 3, 2, 2, 1, 1, 4, 2, 3, 3]
def baseStart_7943255 : Nat := 118140960795 + 7943255 * 2 ^ 59
def prefixEnd_7943255 : Nat := 4983230072969 + 3 ^ 40 * 7943255 * 2
def baseEnd_7943255 : Nat := 4078707776229424711982141

theorem tailTrace_7943255 : CollatzResearch.WordTrace tailWord_7943255 prefixEnd_7943255 4078707776229424711982141 := by
  unfold tailWord_7943255
  simp only [CollatzResearch.WordTrace]
  refine ⟨289714310837951209794671219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193142873891967473196447479 289714310837951209794671219)
  ·
    refine ⟨434571466256926814692006829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289714310837951209794671219 434571466256926814692006829)
    ·
      refine ⟨162964299846347555509502561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 434571466256926814692006829 162964299846347555509502561)
      ·
        refine ⟨122223224884760666632126921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162964299846347555509502561 122223224884760666632126921)
        ·
          refine ⟨91667418663570499974095191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122223224884760666632126921 91667418663570499974095191)
          ·
            refine ⟨137501127995355749961142787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91667418663570499974095191 137501127995355749961142787)
            ·
              refine ⟨206251691993033624941714181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137501127995355749961142787 206251691993033624941714181)
              ·
                refine ⟨38672192248693804676571409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 206251691993033624941714181 38672192248693804676571409)
                ·
                  refine ⟨29004144186520353507428557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38672192248693804676571409 29004144186520353507428557)
                  ·
                    refine ⟨10876554069945132565285709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29004144186520353507428557 10876554069945132565285709)
                    ·
                      refine ⟨4078707776229424711982141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10876554069945132565285709 4078707776229424711982141)
                      ·
                        rfl

theorem cell23_7943255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 4, 2, 3, 3].length) (baseStart_7943255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7943255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7943255 prefixEnd_7943255 := by exact prefixLift 7943255
  have htrace : WordTrace (prefixWord ++ tailWord_7943255) baseStart_7943255 baseEnd_7943255 := by
    simpa [prefixWord, tailWord_7943255, baseEnd_7943255] using wordTrace_append hprefix tailTrace_7943255
  have hstable : (prefixWord ++ tailWord_7943255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7943255).length < 2 ^ (prefixWord ++ tailWord_7943255).sum := by decide
  have hdescent : baseEnd_7943255 < baseStart_7943255 := by decide
  rcases family_descends (prefixWord ++ tailWord_7943255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7943282 : List Nat := [3, 2, 1, 2, 2, 1, 1, 2, 2, 5, 2]
def baseStart_7943282 : Nat := 118140960795 + 7943282 * 2 ^ 59
def prefixEnd_7943282 : Nat := 4983230072969 + 3 ^ 40 * 7943282 * 2
def baseEnd_7943282 : Nat := 4078721640207096106344517

theorem tailTrace_7943282 : CollatzResearch.WordTrace tailWord_7943282 prefixEnd_7943282 4078721640207096106344517 := by
  unfold tailWord_7943282
  simp only [CollatzResearch.WordTrace]
  refine ⟨72428823902213348351476025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193143530405902262270602733 72428823902213348351476025)
  ·
    refine ⟨54321617926660011263607019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72428823902213348351476025 54321617926660011263607019)
    ·
      refine ⟨81482426889990016895410529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54321617926660011263607019 81482426889990016895410529)
      ·
        refine ⟨61111820167492512671557897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81482426889990016895410529 61111820167492512671557897)
        ·
          refine ⟨45833865125619384503668423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61111820167492512671557897 45833865125619384503668423)
          ·
            refine ⟨68750797688429076755502635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45833865125619384503668423 68750797688429076755502635)
            ·
              refine ⟨103126196532643615133253953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68750797688429076755502635 103126196532643615133253953)
              ·
                refine ⟨77344647399482711349940465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103126196532643615133253953 77344647399482711349940465)
                ·
                  refine ⟨58008485549612033512455349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77344647399482711349940465 58008485549612033512455349)
                  ·
                    refine ⟨5438295520276128141792689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 58008485549612033512455349 5438295520276128141792689)
                    ·
                      refine ⟨4078721640207096106344517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5438295520276128141792689 4078721640207096106344517)
                      ·
                        rfl

theorem cell23_7943282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 2, 2, 5, 2].length) (baseStart_7943282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7943282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7943282 prefixEnd_7943282 := by exact prefixLift 7943282
  have htrace : WordTrace (prefixWord ++ tailWord_7943282) baseStart_7943282 baseEnd_7943282 := by
    simpa [prefixWord, tailWord_7943282, baseEnd_7943282] using wordTrace_append hprefix tailTrace_7943282
  have hstable : (prefixWord ++ tailWord_7943282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7943282).length < 2 ^ (prefixWord ++ tailWord_7943282).sum := by decide
  have hdescent : baseEnd_7943282 < baseStart_7943282 := by decide
  rcases family_descends (prefixWord ++ tailWord_7943282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7943294 : List Nat := [4, 2, 4, 1, 2, 1, 2, 1, 1, 3, 2]
def baseStart_7943294 : Nat := 118140960795 + 7943294 * 2 ^ 59
def prefixEnd_7943294 : Nat := 4983230072969 + 3 ^ 40 * 7943294 * 2
def baseEnd_7943294 : Nat := 4078727801974950059394463

theorem tailTrace_7943294 : CollatzResearch.WordTrace tailWord_7943294 prefixEnd_7943294 4078727801974950059394463 := by
  unfold tailWord_7943294
  simp only [CollatzResearch.WordTrace]
  refine ⟨36214466660601239931917617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 193143822189873279636893957 36214466660601239931917617)
  ·
    refine ⟨27160849995450929948938213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36214466660601239931917617 27160849995450929948938213)
    ·
      refine ⟨5092659374147049365425915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27160849995450929948938213 5092659374147049365425915)
      ·
        refine ⟨7638989061220574048138873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5092659374147049365425915 7638989061220574048138873)
        ·
          refine ⟨5729241795915430536104155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7638989061220574048138873 5729241795915430536104155)
          ·
            refine ⟨8593862693873145804156233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5729241795915430536104155 8593862693873145804156233)
            ·
              refine ⟨6445397020404859353117175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8593862693873145804156233 6445397020404859353117175)
              ·
                refine ⟨9668095530607289029675763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6445397020404859353117175 9668095530607289029675763)
                ·
                  refine ⟨14502143295910933544513645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9668095530607289029675763 14502143295910933544513645)
                  ·
                    refine ⟨5438303735966600079192617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14502143295910933544513645 5438303735966600079192617)
                    ·
                      refine ⟨4078727801974950059394463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5438303735966600079192617 4078727801974950059394463)
                      ·
                        rfl

theorem cell23_7943294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 2, 1, 1, 3, 2].length) (baseStart_7943294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7943294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7943294 prefixEnd_7943294 := by exact prefixLift 7943294
  have htrace : WordTrace (prefixWord ++ tailWord_7943294) baseStart_7943294 baseEnd_7943294 := by
    simpa [prefixWord, tailWord_7943294, baseEnd_7943294] using wordTrace_append hprefix tailTrace_7943294
  have hstable : (prefixWord ++ tailWord_7943294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7943294).length < 2 ^ (prefixWord ++ tailWord_7943294).sum := by decide
  have hdescent : baseEnd_7943294 < baseStart_7943294 := by decide
  rcases family_descends (prefixWord ++ tailWord_7943294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7943325 : List Nat := [1, 4, 2, 1, 1, 2, 1, 2, 2, 1, 6]
def baseStart_7943325 : Nat := 118140960795 + 7943325 * 2 ^ 59
def prefixEnd_7943325 : Nat := 4983230072969 + 3 ^ 40 * 7943325 * 2
def baseEnd_7943325 : Nat := 4078743719875239438106819

theorem tailTrace_7943325 : CollatzResearch.WordTrace tailWord_7943325 prefixEnd_7943325 4078743719875239438106819 := by
  unfold tailWord_7943325
  simp only [CollatzResearch.WordTrace]
  refine ⟨289716863947697611749719429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193144575965131741166479619 289716863947697611749719429)
  ·
    refine ⟨54321911990193302203072393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 289716863947697611749719429 54321911990193302203072393)
    ·
      refine ⟨40741433992644976652304295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54321911990193302203072393 40741433992644976652304295)
      ·
        refine ⟨61112150988967464978456443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40741433992644976652304295 61112150988967464978456443)
        ·
          refine ⟨91668226483451197467684665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61112150988967464978456443 91668226483451197467684665)
          ·
            refine ⟨68751169862588398100763499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91668226483451197467684665 68751169862588398100763499)
            ·
              refine ⟨103126754793882597151145249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68751169862588398100763499 103126754793882597151145249)
              ·
                refine ⟨77345066095411947863358937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103126754793882597151145249 77345066095411947863358937)
                ·
                  refine ⟨58008799571558960897519203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77345066095411947863358937 58008799571558960897519203)
                  ·
                    refine ⟨87013199357338441346278805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58008799571558960897519203 87013199357338441346278805)
                    ·
                      refine ⟨4078743719875239438106819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 87013199357338441346278805 4078743719875239438106819)
                      ·
                        rfl

theorem cell23_7943325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 2, 2, 1, 6].length) (baseStart_7943325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7943325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7943325 prefixEnd_7943325 := by exact prefixLift 7943325
  have htrace : WordTrace (prefixWord ++ tailWord_7943325) baseStart_7943325 baseEnd_7943325 := by
    simpa [prefixWord, tailWord_7943325, baseEnd_7943325] using wordTrace_append hprefix tailTrace_7943325
  have hstable : (prefixWord ++ tailWord_7943325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7943325).length < 2 ^ (prefixWord ++ tailWord_7943325).sum := by decide
  have hdescent : baseEnd_7943325 < baseStart_7943325 := by decide
  rcases family_descends (prefixWord ++ tailWord_7943325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7943332 : List Nat := [2, 3, 1, 2, 3, 1, 1, 2, 1, 4, 3]
def baseStart_7943332 : Nat := 118140960795 + 7943332 * 2 ^ 59
def prefixEnd_7943332 : Nat := 4983230072969 + 3 ^ 40 * 7943332 * 2
def baseEnd_7943332 : Nat := 4078747314239820910719287

theorem tailTrace_7943332 : CollatzResearch.WordTrace tailWord_7943332 prefixEnd_7943332 4078747314239820910719287 := by
  unfold tailWord_7943332
  simp only [CollatzResearch.WordTrace]
  refine ⟨144858559629336125972612125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193144746172448167963482833 144858559629336125972612125)
  ·
    refine ⟨54321959861001047239729547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144858559629336125972612125 54321959861001047239729547)
    ·
      refine ⟨81482939791501570859594321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54321959861001047239729547 81482939791501570859594321)
      ·
        refine ⟨61112204843626178144695741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81482939791501570859594321 61112204843626178144695741)
        ·
          refine ⟨22917076816359816804260903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61112204843626178144695741 22917076816359816804260903)
          ·
            refine ⟨34375615224539725206391355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22917076816359816804260903 34375615224539725206391355)
            ·
              refine ⟨51563422836809587809587033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34375615224539725206391355 51563422836809587809587033)
              ·
                refine ⟨38672567127607190857190275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51563422836809587809587033 38672567127607190857190275)
                ·
                  refine ⟨58008850691410786285785413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38672567127607190857190275 58008850691410786285785413)
                  ·
                    refine ⟨10876659504639522428584765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58008850691410786285785413 10876659504639522428584765)
                    ·
                      refine ⟨4078747314239820910719287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10876659504639522428584765 4078747314239820910719287)
                      ·
                        rfl

theorem cell23_7943332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 2, 1, 4, 3].length) (baseStart_7943332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7943332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7943332 prefixEnd_7943332 := by exact prefixLift 7943332
  have htrace : WordTrace (prefixWord ++ tailWord_7943332) baseStart_7943332 baseEnd_7943332 := by
    simpa [prefixWord, tailWord_7943332, baseEnd_7943332] using wordTrace_append hprefix tailTrace_7943332
  have hstable : (prefixWord ++ tailWord_7943332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7943332).length < 2 ^ (prefixWord ++ tailWord_7943332).sum := by decide
  have hdescent : baseEnd_7943332 < baseStart_7943332 := by decide
  rcases family_descends (prefixWord ++ tailWord_7943332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7943356 : List Nat := [2, 2, 2, 3, 2, 1, 3, 3, 1, 4]
def baseStart_7943356 : Nat := 118140960795 + 7943356 * 2 ^ 59
def prefixEnd_7943356 : Nat := 4983230072969 + 3 ^ 40 * 7943356 * 2
def baseEnd_7943356 : Nat := 1359586545925176272273059

theorem tailTrace_7943356 : CollatzResearch.WordTrace tailWord_7943356 prefixEnd_7943356 1359586545925176272273059 := by
  unfold tailWord_7943356
  simp only [CollatzResearch.WordTrace]
  refine ⟨144858997305292652022048961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193145329740390202696065281 144858997305292652022048961)
  ·
    refine ⟨108644247978969489016536721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144858997305292652022048961 108644247978969489016536721)
    ·
      refine ⟨81483185984227116762402541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108644247978969489016536721 81483185984227116762402541)
      ·
        refine ⟨30556194744085168785900953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81483185984227116762402541 30556194744085168785900953)
        ·
          refine ⟨22917146058063876589425715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30556194744085168785900953 22917146058063876589425715)
          ·
            refine ⟨34375719087095814884138573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22917146058063876589425715 34375719087095814884138573)
            ·
              refine ⟨12890894657660930581551965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34375719087095814884138573 12890894657660930581551965)
              ·
                refine ⟨4834085496622848968081987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12890894657660930581551965 4834085496622848968081987)
                ·
                  refine ⟨7251128244934273452122981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4834085496622848968081987 7251128244934273452122981)
                  ·
                    refine ⟨1359586545925176272273059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7251128244934273452122981 1359586545925176272273059)
                    ·
                      rfl

theorem cell23_7943356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 3, 3, 1, 4].length) (baseStart_7943356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7943356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7943356 prefixEnd_7943356 := by exact prefixLift 7943356
  have htrace : WordTrace (prefixWord ++ tailWord_7943356) baseStart_7943356 baseEnd_7943356 := by
    simpa [prefixWord, tailWord_7943356, baseEnd_7943356] using wordTrace_append hprefix tailTrace_7943356
  have hstable : (prefixWord ++ tailWord_7943356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7943356).length < 2 ^ (prefixWord ++ tailWord_7943356).sum := by decide
  have hdescent : baseEnd_7943356 < baseStart_7943356 := by decide
  rcases family_descends (prefixWord ++ tailWord_7943356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7943365 : List Nat := [1, 3, 1, 1, 1, 1, 3, 2, 5, 5]
def baseStart_7943365 : Nat := 118140960795 + 7943365 * 2 ^ 59
def prefixEnd_7943365 : Nat := 4983230072969 + 3 ^ 40 * 7943365 * 2
def baseEnd_7943365 : Nat := 1359588086367139760535545

theorem tailTrace_7943365 : CollatzResearch.WordTrace tailWord_7943365 prefixEnd_7943365 1359588086367139760535545 := by
  unfold tailWord_7943365
  simp only [CollatzResearch.WordTrace]
  refine ⟨289718322867552698581175549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193145548578368465720783699 289718322867552698581175549)
  ·
    refine ⟨108644371075332261967940831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 289718322867552698581175549 108644371075332261967940831)
    ·
      refine ⟨162966556612998392951911247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108644371075332261967940831 162966556612998392951911247)
      ·
        refine ⟨244449834919497589427866871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162966556612998392951911247 244449834919497589427866871)
        ·
          refine ⟨366674752379246384141800307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244449834919497589427866871 366674752379246384141800307)
          ·
            refine ⟨550012128568869576212700461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 366674752379246384141800307 550012128568869576212700461)
            ·
              refine ⟨206254548213326091079762673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 550012128568869576212700461 206254548213326091079762673)
              ·
                refine ⟨154690911159994568309822005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 206254548213326091079762673 154690911159994568309822005)
                ·
                  refine ⟨14502272921249490779045813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 154690911159994568309822005 14502272921249490779045813)
                  ·
                    refine ⟨1359588086367139760535545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14502272921249490779045813 1359588086367139760535545)
                    ·
                      rfl

theorem cell23_7943365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 2, 5, 5].length) (baseStart_7943365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7943365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7943365 prefixEnd_7943365 := by exact prefixLift 7943365
  have htrace : WordTrace (prefixWord ++ tailWord_7943365) baseStart_7943365 baseEnd_7943365 := by
    simpa [prefixWord, tailWord_7943365, baseEnd_7943365] using wordTrace_append hprefix tailTrace_7943365
  have hstable : (prefixWord ++ tailWord_7943365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7943365).length < 2 ^ (prefixWord ++ tailWord_7943365).sum := by decide
  have hdescent : baseEnd_7943365 < baseStart_7943365 := by decide
  rcases family_descends (prefixWord ++ tailWord_7943365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7943385 : List Nat := [1, 2, 1, 2, 3, 1, 1, 1, 2, 5, 4]
def baseStart_7943385 : Nat := 118140960795 + 7943385 * 2 ^ 59
def prefixEnd_7943385 : Nat := 4983230072969 + 3 ^ 40 * 7943385 * 2
def baseEnd_7943385 : Nat := 4078774528714509203356543

theorem tailTrace_7943385 : CollatzResearch.WordTrace tailWord_7943385 prefixEnd_7943385 4078774528714509203356543 := by
  unfold tailWord_7943385
  simp only [CollatzResearch.WordTrace]
  refine ⟨289719052327480241996903609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193146034884986827997935739 289719052327480241996903609)
  ·
    refine ⟨217289289245610181497677707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289719052327480241996903609 217289289245610181497677707)
    ·
      refine ⟨325933933868415272246516561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217289289245610181497677707 325933933868415272246516561)
      ·
        refine ⟨244450450401311454184887421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 325933933868415272246516561 244450450401311454184887421)
        ·
          refine ⟨91668918900491795319332783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 244450450401311454184887421 91668918900491795319332783)
          ·
            refine ⟨137503378350737692978999175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91668918900491795319332783 137503378350737692978999175)
            ·
              refine ⟨206255067526106539468498763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137503378350737692978999175 206255067526106539468498763)
              ·
                refine ⟨309382601289159809202748145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 206255067526106539468498763 309382601289159809202748145)
                ·
                  refine ⟨232036950966869856902061109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 309382601289159809202748145 232036950966869856902061109)
                  ·
                    refine ⟨21753464153144049084568229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 232036950966869856902061109 21753464153144049084568229)
                    ·
                      refine ⟨4078774528714509203356543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21753464153144049084568229 4078774528714509203356543)
                      ·
                        rfl

theorem cell23_7943385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 1, 2, 5, 4].length) (baseStart_7943385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7943385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7943385 prefixEnd_7943385 := by exact prefixLift 7943385
  have htrace : WordTrace (prefixWord ++ tailWord_7943385) baseStart_7943385 baseEnd_7943385 := by
    simpa [prefixWord, tailWord_7943385, baseEnd_7943385] using wordTrace_append hprefix tailTrace_7943385
  have hstable : (prefixWord ++ tailWord_7943385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7943385).length < 2 ^ (prefixWord ++ tailWord_7943385).sum := by decide
  have hdescent : baseEnd_7943385 < baseStart_7943385 := by decide
  rcases family_descends (prefixWord ++ tailWord_7943385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7943399 : List Nat := [1, 1, 5, 3, 2, 1, 1, 1, 3, 5]
def baseStart_7943399 : Nat := 118140960795 + 7943399 * 2 ^ 59
def prefixEnd_7943399 : Nat := 4983230072969 + 3 ^ 40 * 7943399 * 2
def baseEnd_7943399 : Nat := 1359593905814557382860493

theorem tailTrace_7943399 : CollatzResearch.WordTrace tailWord_7943399 prefixEnd_7943399 1359593905814557382860493 := by
  unfold tailWord_7943399
  simp only [CollatzResearch.WordTrace]
  refine ⟨289719562949429522387913251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193146375299619681591942167 289719562949429522387913251)
  ·
    refine ⟨434579344424144283581869877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289719562949429522387913251 434579344424144283581869877)
    ·
      refine ⟨40741813539763526585800301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 434579344424144283581869877 40741813539763526585800301)
      ·
        refine ⟨15278180077411322469675113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40741813539763526585800301 15278180077411322469675113)
        ·
          refine ⟨11458635058058491852256335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15278180077411322469675113 11458635058058491852256335)
          ·
            refine ⟨17187952587087737778384503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11458635058058491852256335 17187952587087737778384503)
            ·
              refine ⟨25781928880631606667576755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17187952587087737778384503 25781928880631606667576755)
              ·
                refine ⟨38672893320947410001365133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25781928880631606667576755 38672893320947410001365133)
                ·
                  refine ⟨14502334995355278750511925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38672893320947410001365133 14502334995355278750511925)
                  ·
                    refine ⟨1359593905814557382860493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14502334995355278750511925 1359593905814557382860493)
                    ·
                      rfl

theorem cell23_7943399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 1, 3, 5].length) (baseStart_7943399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7943399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7943399 prefixEnd_7943399 := by exact prefixLift 7943399
  have htrace : WordTrace (prefixWord ++ tailWord_7943399) baseStart_7943399 baseEnd_7943399 := by
    simpa [prefixWord, tailWord_7943399, baseEnd_7943399] using wordTrace_append hprefix tailTrace_7943399
  have hstable : (prefixWord ++ tailWord_7943399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7943399).length < 2 ^ (prefixWord ++ tailWord_7943399).sum := by decide
  have hdescent : baseEnd_7943399 < baseStart_7943399 := by decide
  rcases family_descends (prefixWord ++ tailWord_7943399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7943425 : List Nat := [1, 2, 4, 1, 1, 14]
def baseStart_7943425 : Nat := 118140960795 + 7943425 * 2 ^ 59
def prefixEnd_7943425 : Nat := 4983230072969 + 3 ^ 40 * 7943425 * 2
def baseEnd_7943425 : Nat := 16785164888644810892413

theorem tailTrace_7943425 : CollatzResearch.WordTrace tailWord_7943425 prefixEnd_7943425 16785164888644810892413 := by
  unfold tailWord_7943425
  simp only [CollatzResearch.WordTrace]
  refine ⟨289720511247335328828359729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193147007498223552552239819 289720511247335328828359729)
  ·
    refine ⟨217290383435501496621269797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289720511247335328828359729 217290383435501496621269797)
    ·
      refine ⟨40741946894156530616488087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 217290383435501496621269797 40741946894156530616488087)
      ·
        refine ⟨61112920341234795924732131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40741946894156530616488087 61112920341234795924732131)
        ·
          refine ⟨91669380511852193887098197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61112920341234795924732131 91669380511852193887098197)
          ·
            refine ⟨16785164888644810892413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 14 91669380511852193887098197 16785164888644810892413)
            ·
              rfl

theorem cell23_7943425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 14].length) (baseStart_7943425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7943425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7943425 prefixEnd_7943425 := by exact prefixLift 7943425
  have htrace : WordTrace (prefixWord ++ tailWord_7943425) baseStart_7943425 baseEnd_7943425 := by
    simpa [prefixWord, tailWord_7943425, baseEnd_7943425] using wordTrace_append hprefix tailTrace_7943425
  have hstable : (prefixWord ++ tailWord_7943425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7943425).length < 2 ^ (prefixWord ++ tailWord_7943425).sum := by decide
  have hdescent : baseEnd_7943425 < baseStart_7943425 := by decide
  rcases family_descends (prefixWord ++ tailWord_7943425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7943429 : List Nat := [1, 3, 1, 1, 2, 1, 6, 2, 2, 4]
def baseStart_7943429 : Nat := 118140960795 + 7943429 * 2 ^ 59
def prefixEnd_7943429 : Nat := 4983230072969 + 3 ^ 40 * 7943429 * 2
def baseEnd_7943429 : Nat := 1359599040621102343735447

theorem tailTrace_7943429 : CollatzResearch.WordTrace tailWord_7943429 prefixEnd_7943429 1359599040621102343735447 := by
  unfold tailWord_7943429
  simp only [CollatzResearch.WordTrace]
  refine ⟨289720657139320837511505341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193147104759547225007670227 289720657139320837511505341)
  ·
    refine ⟨108645246427245314066814503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 289720657139320837511505341 108645246427245314066814503)
    ·
      refine ⟨162967869640867971100221755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108645246427245314066814503 162967869640867971100221755)
      ·
        refine ⟨244451804461301956650332633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162967869640867971100221755 244451804461301956650332633)
        ·
          refine ⟨183338853345976467487749475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 244451804461301956650332633 183338853345976467487749475)
          ·
            refine ⟨275008280018964701231624213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183338853345976467487749475 275008280018964701231624213)
            ·
              refine ⟨12891013125888970370232385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 275008280018964701231624213 12891013125888970370232385)
              ·
                refine ⟨9668259844416727777674289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12891013125888970370232385 9668259844416727777674289)
                ·
                  refine ⟨7251194883312545833255717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9668259844416727777674289 7251194883312545833255717)
                  ·
                    refine ⟨1359599040621102343735447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7251194883312545833255717 1359599040621102343735447)
                    ·
                      rfl

theorem cell23_7943429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 6, 2, 2, 4].length) (baseStart_7943429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7943429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7943429 prefixEnd_7943429 := by exact prefixLift 7943429
  have htrace : WordTrace (prefixWord ++ tailWord_7943429) baseStart_7943429 baseEnd_7943429 := by
    simpa [prefixWord, tailWord_7943429, baseEnd_7943429] using wordTrace_append hprefix tailTrace_7943429
  have hstable : (prefixWord ++ tailWord_7943429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7943429).length < 2 ^ (prefixWord ++ tailWord_7943429).sum := by decide
  have hdescent : baseEnd_7943429 < baseStart_7943429 := by decide
  rcases family_descends (prefixWord ++ tailWord_7943429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7943453 : List Nat := [1, 4, 2, 3, 1, 2, 1, 2, 3, 2, 2]
def baseStart_7943453 : Nat := 118140960795 + 7943453 * 2 ^ 59
def prefixEnd_7943453 : Nat := 4983230072969 + 3 ^ 40 * 7943453 * 2
def baseEnd_7943453 : Nat := 4078809445399014937306231

theorem tailTrace_7943453 : CollatzResearch.WordTrace tailWord_7943453 prefixEnd_7943453 4078809445399014937306231 := by
  unfold tailWord_7943453
  simp only [CollatzResearch.WordTrace]
  refine ⟨289721532491233889610379013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193147688327489259740252675 289721532491233889610379013)
  ·
    refine ⟨54322787342106354301946065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 289721532491233889610379013 54322787342106354301946065)
    ·
      refine ⟨40742090506579765726459549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54322787342106354301946065 40742090506579765726459549)
      ·
        refine ⟨15278283939967412147422331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40742090506579765726459549 15278283939967412147422331)
        ·
          refine ⟨22917425909951118221133497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15278283939967412147422331 22917425909951118221133497)
          ·
            refine ⟨17188069432463338665850123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22917425909951118221133497 17188069432463338665850123)
            ·
              refine ⟨25782104148695007998775185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17188069432463338665850123 25782104148695007998775185)
              ·
                refine ⟨19336578111521255999081389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25782104148695007998775185 19336578111521255999081389)
                ·
                  refine ⟨7251216791820470999655521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19336578111521255999081389 7251216791820470999655521)
                  ·
                    refine ⟨5438412593865353249741641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7251216791820470999655521 5438412593865353249741641)
                    ·
                      refine ⟨4078809445399014937306231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5438412593865353249741641 4078809445399014937306231)
                      ·
                        rfl

theorem cell23_7943453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 2, 3, 2, 2].length) (baseStart_7943453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7943453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7943453 prefixEnd_7943453 := by exact prefixLift 7943453
  have htrace : WordTrace (prefixWord ++ tailWord_7943453) baseStart_7943453 baseEnd_7943453 := by
    simpa [prefixWord, tailWord_7943453, baseEnd_7943453] using wordTrace_append hprefix tailTrace_7943453
  have hstable : (prefixWord ++ tailWord_7943453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7943453).length < 2 ^ (prefixWord ++ tailWord_7943453).sum := by decide
  have hdescent : baseEnd_7943453 < baseStart_7943453 := by decide
  rcases family_descends (prefixWord ++ tailWord_7943453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7943473 : List Nat := [1, 2, 2, 3, 3, 3, 2, 1, 1, 2, 3]
def baseStart_7943473 : Nat := 118140960795 + 7943473 * 2 ^ 59
def prefixEnd_7943473 : Nat := 4983230072969 + 3 ^ 40 * 7943473 * 2
def baseEnd_7943473 : Nat := 4078819715012104859056139

theorem tailTrace_7943473 : CollatzResearch.WordTrace tailWord_7943473 prefixEnd_7943473 4078819715012104859056139 := by
  unfold tailWord_7943473
  simp only [CollatzResearch.WordTrace]
  refine ⟨289722261951161433026107073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193148174634107622017404715 289722261951161433026107073)
  ·
    refine ⟨217291696463371074769580305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289722261951161433026107073 217291696463371074769580305)
    ·
      refine ⟨162968772347528306077185229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217291696463371074769580305 162968772347528306077185229)
      ·
        refine ⟨61113289630323114778944461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162968772347528306077185229 61113289630323114778944461)
        ·
          refine ⟨22917483611371168042104173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61113289630323114778944461 22917483611371168042104173)
          ·
            refine ⟨8594056354264188015789065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22917483611371168042104173 8594056354264188015789065)
            ·
              refine ⟨6445542265698141011841799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8594056354264188015789065 6445542265698141011841799)
              ·
                refine ⟨9668313398547211517762699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6445542265698141011841799 9668313398547211517762699)
                ·
                  refine ⟨14502470097820817276644049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9668313398547211517762699 14502470097820817276644049)
                  ·
                    refine ⟨10876852573365612957483037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14502470097820817276644049 10876852573365612957483037)
                    ·
                      refine ⟨4078819715012104859056139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10876852573365612957483037 4078819715012104859056139)
                      ·
                        rfl

theorem cell23_7943473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 2, 1, 1, 2, 3].length) (baseStart_7943473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7943473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7943473 prefixEnd_7943473 := by exact prefixLift 7943473
  have htrace : WordTrace (prefixWord ++ tailWord_7943473) baseStart_7943473 baseEnd_7943473 := by
    simpa [prefixWord, tailWord_7943473, baseEnd_7943473] using wordTrace_append hprefix tailTrace_7943473
  have hstable : (prefixWord ++ tailWord_7943473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7943473).length < 2 ^ (prefixWord ++ tailWord_7943473).sum := by decide
  have hdescent : baseEnd_7943473 < baseStart_7943473 := by decide
  rcases family_descends (prefixWord ++ tailWord_7943473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7943486 : List Nat := [4, 2, 1, 2, 1, 1, 3, 1, 4, 1, 3]
def baseStart_7943486 : Nat := 118140960795 + 7943486 * 2 ^ 59
def prefixEnd_7943486 : Nat := 4983230072969 + 3 ^ 40 * 7943486 * 2
def baseEnd_7943486 : Nat := 4078826390260613308193579

theorem tailTrace_7943486 : CollatzResearch.WordTrace tailWord_7943486 prefixEnd_7943486 4078826390260613308193579 := by
  unfold tailWord_7943486
  simp only [CollatzResearch.WordTrace]
  refine ⟨36215342012514292030791289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 193148490733409557497553541 36215342012514292030791289)
  ·
    refine ⟨27161506509385719023093467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36215342012514292030791289 27161506509385719023093467)
    ·
      refine ⟨40742259764078578534640201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27161506509385719023093467 40742259764078578534640201)
      ·
        refine ⟨30556694823058933900980151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40742259764078578534640201 30556694823058933900980151)
        ·
          refine ⟨45835042234588400851470227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30556694823058933900980151 45835042234588400851470227)
          ·
            refine ⟨68752563351882601277205341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45835042234588400851470227 68752563351882601277205341)
            ·
              refine ⟨25782211256955975478952003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68752563351882601277205341 25782211256955975478952003)
              ·
                refine ⟨38673316885433963218428005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25782211256955975478952003 38673316885433963218428005)
                ·
                  refine ⟨7251246916018868103455251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38673316885433963218428005 7251246916018868103455251)
                  ·
                    refine ⟨10876870374028302155182877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7251246916018868103455251 10876870374028302155182877)
                    ·
                      refine ⟨4078826390260613308193579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10876870374028302155182877 4078826390260613308193579)
                      ·
                        rfl

theorem cell23_7943486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 1, 4, 1, 3].length) (baseStart_7943486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7943486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7943486 prefixEnd_7943486 := by exact prefixLift 7943486
  have htrace : WordTrace (prefixWord ++ tailWord_7943486) baseStart_7943486 baseEnd_7943486 := by
    simpa [prefixWord, tailWord_7943486, baseEnd_7943486] using wordTrace_append hprefix tailTrace_7943486
  have hstable : (prefixWord ++ tailWord_7943486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7943486).length < 2 ^ (prefixWord ++ tailWord_7943486).sum := by decide
  have hdescent : baseEnd_7943486 < baseStart_7943486 := by decide
  rcases family_descends (prefixWord ++ tailWord_7943486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7943502 : List Nat := [4, 1, 1, 1, 1, 1, 3, 3, 2, 6]
def baseStart_7943502 : Nat := 118140960795 + 7943502 * 2 ^ 59
def prefixEnd_7943502 : Nat := 4983230072969 + 3 ^ 40 * 7943502 * 2
def baseEnd_7943502 : Nat := 1359611535317028415197835

theorem tailTrace_7943502 : CollatzResearch.WordTrace tailWord_7943502 prefixEnd_7943502 1359611535317028415197835 := by
  unfold tailWord_7943502
  simp only [CollatzResearch.WordTrace]
  refine ⟨36215414958507046372364095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 193148879778704247319275173 36215414958507046372364095)
  ·
    refine ⟨54323122437760569558546143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36215414958507046372364095 54323122437760569558546143)
    ·
      refine ⟨81484683656640854337819215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54323122437760569558546143 81484683656640854337819215)
      ·
        refine ⟨122227025484961281506728823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81484683656640854337819215 122227025484961281506728823)
        ·
          refine ⟨183340538227441922260093235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122227025484961281506728823 183340538227441922260093235)
          ·
            refine ⟨275010807341162883390139853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183340538227441922260093235 275010807341162883390139853)
            ·
              refine ⟨103129052752936081271302445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 275010807341162883390139853 103129052752936081271302445)
              ·
                refine ⟨38673394782351030476738417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103129052752936081271302445 38673394782351030476738417)
                ·
                  refine ⟨29005046086763272857553813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38673394782351030476738417 29005046086763272857553813)
                  ·
                    refine ⟨1359611535317028415197835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29005046086763272857553813 1359611535317028415197835)
                    ·
                      rfl

theorem cell23_7943502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 3, 2, 6].length) (baseStart_7943502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7943502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7943502 prefixEnd_7943502 := by exact prefixLift 7943502
  have htrace : WordTrace (prefixWord ++ tailWord_7943502) baseStart_7943502 baseEnd_7943502 := by
    simpa [prefixWord, tailWord_7943502, baseEnd_7943502] using wordTrace_append hprefix tailTrace_7943502
  have hstable : (prefixWord ++ tailWord_7943502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7943502).length < 2 ^ (prefixWord ++ tailWord_7943502).sum := by decide
  have hdescent : baseEnd_7943502 < baseStart_7943502 := by decide
  rcases family_descends (prefixWord ++ tailWord_7943502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7943512 : List Nat := [2, 1, 2, 2, 1, 1, 4, 2, 2, 1, 5]
def baseStart_7943512 : Nat := 118140960795 + 7943512 * 2 ^ 59
def prefixEnd_7943512 : Nat := 4983230072969 + 3 ^ 40 * 7943512 * 2
def baseEnd_7943512 : Nat := 4078839740757630206468459

theorem tailTrace_7943512 : CollatzResearch.WordTrace tailWord_7943512 prefixEnd_7943512 4078839740757630206468459 := by
  unfold tailWord_7943512
  simp only [CollatzResearch.WordTrace]
  refine ⟨144861842199010071343388395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193149122932013428457851193 144861842199010071343388395)
  ·
    refine ⟨217292763298515107015082593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144861842199010071343388395 217292763298515107015082593)
    ·
      refine ⟨162969572473886330261311945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217292763298515107015082593 162969572473886330261311945)
      ·
        refine ⟨122227179355414747695983959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162969572473886330261311945 122227179355414747695983959)
        ·
          refine ⟨183340769033122121543975939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122227179355414747695983959 183340769033122121543975939)
          ·
            refine ⟨275011153549683182315963909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183340769033122121543975939 275011153549683182315963909)
            ·
              refine ⟨51564591290565596684243233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 275011153549683182315963909 51564591290565596684243233)
              ·
                refine ⟨38673443467924197513182425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51564591290565596684243233 38673443467924197513182425)
                ·
                  refine ⟨29005082600943148134886819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38673443467924197513182425 29005082600943148134886819)
                  ·
                    refine ⟨43507623901414722202330229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29005082600943148134886819 43507623901414722202330229)
                    ·
                      refine ⟨4078839740757630206468459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43507623901414722202330229 4078839740757630206468459)
                      ·
                        rfl

theorem cell23_7943512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 2, 2, 1, 5].length) (baseStart_7943512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7943512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7943512 prefixEnd_7943512 := by exact prefixLift 7943512
  have htrace : WordTrace (prefixWord ++ tailWord_7943512) baseStart_7943512 baseEnd_7943512 := by
    simpa [prefixWord, tailWord_7943512, baseEnd_7943512] using wordTrace_append hprefix tailTrace_7943512
  have hstable : (prefixWord ++ tailWord_7943512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7943512).length < 2 ^ (prefixWord ++ tailWord_7943512).sum := by decide
  have hdescent : baseEnd_7943512 < baseStart_7943512 := by decide
  rcases family_descends (prefixWord ++ tailWord_7943512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7943560 : List Nat := [2, 1, 3, 3, 1, 2, 4, 1, 2, 2, 2]
def baseStart_7943560 : Nat := 118140960795 + 7943560 * 2 ^ 59
def prefixEnd_7943560 : Nat := 4983230072969 + 3 ^ 40 * 7943560 * 2
def baseEnd_7943560 : Nat := 4078864387829046018668239

theorem tailTrace_7943560 : CollatzResearch.WordTrace tailWord_7943560 prefixEnd_7943560 4078864387829046018668239 := by
  unfold tailWord_7943560
  simp only [CollatzResearch.WordTrace]
  refine ⟨144862717550923123442262067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193150290067897497923016089 144862717550923123442262067)
  ·
    refine ⟨217294076326384685163393101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144862717550923123442262067 217294076326384685163393101)
    ·
      refine ⟨81485278622394256936272413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 217294076326384685163393101 81485278622394256936272413)
      ·
        refine ⟨30556979483397846351102155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81485278622394256936272413 30556979483397846351102155)
        ·
          refine ⟨45835469225096769526653233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30556979483397846351102155 45835469225096769526653233)
          ·
            refine ⟨34376601918822577144989925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45835469225096769526653233 34376601918822577144989925)
            ·
              refine ⟨6445612859779233214685611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34376601918822577144989925 6445612859779233214685611)
              ·
                refine ⟨9668419289668849822028417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6445612859779233214685611 9668419289668849822028417)
                ·
                  refine ⟨7251314467251637366521313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9668419289668849822028417 7251314467251637366521313)
                  ·
                    refine ⟨5438485850438728024890985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7251314467251637366521313 5438485850438728024890985)
                    ·
                      refine ⟨4078864387829046018668239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5438485850438728024890985 4078864387829046018668239)
                      ·
                        rfl

theorem cell23_7943560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 4, 1, 2, 2, 2].length) (baseStart_7943560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7943560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7943560 prefixEnd_7943560 := by exact prefixLift 7943560
  have htrace : WordTrace (prefixWord ++ tailWord_7943560) baseStart_7943560 baseEnd_7943560 := by
    simpa [prefixWord, tailWord_7943560, baseEnd_7943560] using wordTrace_append hprefix tailTrace_7943560
  have hstable : (prefixWord ++ tailWord_7943560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7943560).length < 2 ^ (prefixWord ++ tailWord_7943560).sum := by decide
  have hdescent : baseEnd_7943560 < baseStart_7943560 := by decide
  rcases family_descends (prefixWord ++ tailWord_7943560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7943569 : List Nat := [1, 2, 2, 1, 1, 1, 2, 4, 2, 5, 2]
def baseStart_7943569 : Nat := 118140960795 + 7943569 * 2 ^ 59
def prefixEnd_7943569 : Nat := 4983230072969 + 3 ^ 40 * 7943569 * 2
def baseEnd_7943569 : Nat := 4078869009154936483455697

theorem tailTrace_7943569 : CollatzResearch.WordTrace tailWord_7943569 prefixEnd_7943569 4078869009154936483455697 := by
  unfold tailWord_7943569
  simp only [CollatzResearch.WordTrace]
  refine ⟨289725763358813641421601761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193150508905875760947734507 289725763358813641421601761)
  ·
    refine ⟨217294322519110231066201321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289725763358813641421601761 217294322519110231066201321)
    ·
      refine ⟨162970741889332673299650991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217294322519110231066201321 162970741889332673299650991)
      ·
        refine ⟨244456112833999009949476487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162970741889332673299650991 244456112833999009949476487)
        ·
          refine ⟨366684169250998514924214731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244456112833999009949476487 366684169250998514924214731)
          ·
            refine ⟨550026253876497772386322097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 366684169250998514924214731 550026253876497772386322097)
            ·
              refine ⟨412519690407373329289741573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 550026253876497772386322097 412519690407373329289741573)
              ·
                refine ⟨77347441951382499241826545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 412519690407373329289741573 77347441951382499241826545)
                ·
                  refine ⟨58010581463536874431369909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77347441951382499241826545 58010581463536874431369909)
                  ·
                    refine ⟨5438492012206581977940929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 58010581463536874431369909 5438492012206581977940929)
                    ·
                      refine ⟨4078869009154936483455697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5438492012206581977940929 4078869009154936483455697)
                      ·
                        rfl

theorem cell23_7943569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 5, 2].length) (baseStart_7943569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7943569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7943569 prefixEnd_7943569 := by exact prefixLift 7943569
  have htrace : WordTrace (prefixWord ++ tailWord_7943569) baseStart_7943569 baseEnd_7943569 := by
    simpa [prefixWord, tailWord_7943569, baseEnd_7943569] using wordTrace_append hprefix tailTrace_7943569
  have hstable : (prefixWord ++ tailWord_7943569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7943569).length < 2 ^ (prefixWord ++ tailWord_7943569).sum := by decide
  have hdescent : baseEnd_7943569 < baseStart_7943569 := by decide
  rcases family_descends (prefixWord ++ tailWord_7943569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7943599 : List Nat := [1, 1, 2, 1, 2, 2, 1, 2, 3, 6, 2]
def baseStart_7943599 : Nat := 118140960795 + 7943599 * 2 ^ 59
def prefixEnd_7943599 : Nat := 4983230072969 + 3 ^ 40 * 7943599 * 2
def baseEnd_7943599 : Nat := 4078884413574571366080559

theorem tailTrace_7943599 : CollatzResearch.WordTrace tailWord_7943599 prefixEnd_7943599 4078884413574571366080559 := by
  unfold tailWord_7943599
  simp only [CollatzResearch.WordTrace]
  refine ⟨289726857548704956545193851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193151238365803304363462567 289726857548704956545193851)
  ·
    refine ⟨434590286323057434817790777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289726857548704956545193851 434590286323057434817790777)
    ·
      refine ⟨325942714742293076113343083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 434590286323057434817790777 325942714742293076113343083)
      ·
        refine ⟨488914072113439614170014625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 325942714742293076113343083 488914072113439614170014625)
        ·
          refine ⟨366685554085079710627510969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 488914072113439614170014625 366685554085079710627510969)
          ·
            refine ⟨275014165563809782970633227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 366685554085079710627510969 275014165563809782970633227)
            ·
              refine ⟨412521248345714674455949841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 275014165563809782970633227 412521248345714674455949841)
              ·
                refine ⟨309390936259286005841962381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 412521248345714674455949841 309390936259286005841962381)
                ·
                  refine ⟨116021601097232252190735893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 309390936259286005841962381 116021601097232252190735893)
                  ·
                    refine ⟨5438512551432761821440745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 116021601097232252190735893 5438512551432761821440745)
                    ·
                      refine ⟨4078884413574571366080559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5438512551432761821440745 4078884413574571366080559)
                      ·
                        rfl

theorem cell23_7943599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 3, 6, 2].length) (baseStart_7943599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7943599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7943599 prefixEnd_7943599 := by exact prefixLift 7943599
  have htrace : WordTrace (prefixWord ++ tailWord_7943599) baseStart_7943599 baseEnd_7943599 := by
    simpa [prefixWord, tailWord_7943599, baseEnd_7943599] using wordTrace_append hprefix tailTrace_7943599
  have hstable : (prefixWord ++ tailWord_7943599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7943599).length < 2 ^ (prefixWord ++ tailWord_7943599).sum := by decide
  have hdescent : baseEnd_7943599 < baseStart_7943599 := by decide
  rcases family_descends (prefixWord ++ tailWord_7943599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7943619 : List Nat := [1, 1, 1, 3, 1, 1, 4, 2, 4, 2, 3]
def baseStart_7943619 : Nat := 118140960795 + 7943619 * 2 ^ 59
def prefixEnd_7943619 : Nat := 4983230072969 + 3 ^ 40 * 7943619 * 2
def baseEnd_7943619 : Nat := 4078894683187661287830467

theorem tailTrace_7943619 : CollatzResearch.WordTrace tailWord_7943619 prefixEnd_7943619 4078894683187661287830467 := by
  unfold tailWord_7943619
  simp only [CollatzResearch.WordTrace]
  refine ⟨289727587008632499960921911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193151724672421666640614607 289727587008632499960921911)
  ·
    refine ⟨434591380512948749941382867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289727587008632499960921911 434591380512948749941382867)
    ·
      refine ⟨651887070769423124912074301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 434591380512948749941382867 651887070769423124912074301)
      ·
        refine ⟨244457651538533671842027863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 651887070769423124912074301 244457651538533671842027863)
        ·
          refine ⟨366686477307800507763041795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244457651538533671842027863 366686477307800507763041795)
          ·
            refine ⟨550029715961700761644562693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 366686477307800507763041795 550029715961700761644562693)
            ·
              refine ⟨103130571742818892808355505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 550029715961700761644562693 103130571742818892808355505)
              ·
                refine ⟨77347928807114169606266629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103130571742818892808355505 77347928807114169606266629)
                ·
                  refine ⟨14502736651333906801174993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77347928807114169606266629 14502736651333906801174993)
                  ·
                    refine ⟨10877052488500430100881245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14502736651333906801174993 10877052488500430100881245)
                    ·
                      refine ⟨4078894683187661287830467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10877052488500430100881245 4078894683187661287830467)
                      ·
                        rfl

theorem cell23_7943619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 2, 4, 2, 3].length) (baseStart_7943619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7943619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7943619 prefixEnd_7943619 := by exact prefixLift 7943619
  have htrace : WordTrace (prefixWord ++ tailWord_7943619) baseStart_7943619 baseEnd_7943619 := by
    simpa [prefixWord, tailWord_7943619, baseEnd_7943619] using wordTrace_append hprefix tailTrace_7943619
  have hstable : (prefixWord ++ tailWord_7943619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7943619).length < 2 ^ (prefixWord ++ tailWord_7943619).sum := by decide
  have hdescent : baseEnd_7943619 < baseStart_7943619 := by decide
  rcases family_descends (prefixWord ++ tailWord_7943619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7943626 : List Nat := [3, 1, 2, 1, 2, 4, 1, 2, 3, 4]
def baseStart_7943626 : Nat := 118140960795 + 7943626 * 2 ^ 59
def prefixEnd_7943626 : Nat := 4983230072969 + 3 ^ 40 * 7943626 * 2
def baseEnd_7943626 : Nat := 1359632759184080920147645

theorem tailTrace_7943626 : CollatzResearch.WordTrace tailWord_7943626 prefixEnd_7943626 1359632759184080920147645 := by
  unfold tailWord_7943626
  simp only [CollatzResearch.WordTrace]
  refine ⟨72431960579901785039106683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193151894879738093437617821 72431960579901785039106683)
  ·
    refine ⟨108647940869852677558660025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72431960579901785039106683 108647940869852677558660025)
    ·
      refine ⟨81485955652389508168995019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108647940869852677558660025 81485955652389508168995019)
      ·
        refine ⟨122228933478584262253492529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81485955652389508168995019 122228933478584262253492529)
        ·
          refine ⟨91671700108938196690119397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122228933478584262253492529 91671700108938196690119397)
          ·
            refine ⟨17188443770425911879397387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 91671700108938196690119397 17188443770425911879397387)
            ·
              refine ⟨25782665655638867819096081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17188443770425911879397387 25782665655638867819096081)
              ·
                refine ⟨19336999241729150864322061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25782665655638867819096081 19336999241729150864322061)
                ·
                  refine ⟨7251374715648431574120773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19336999241729150864322061 7251374715648431574120773)
                  ·
                    refine ⟨1359632759184080920147645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7251374715648431574120773 1359632759184080920147645)
                    ·
                      rfl

theorem cell23_7943626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 2, 3, 4].length) (baseStart_7943626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7943626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7943626 prefixEnd_7943626 := by exact prefixLift 7943626
  have htrace : WordTrace (prefixWord ++ tailWord_7943626) baseStart_7943626 baseEnd_7943626 := by
    simpa [prefixWord, tailWord_7943626, baseEnd_7943626] using wordTrace_append hprefix tailTrace_7943626
  have hstable : (prefixWord ++ tailWord_7943626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7943626).length < 2 ^ (prefixWord ++ tailWord_7943626).sum := by decide
  have hdescent : baseEnd_7943626 < baseStart_7943626 := by decide
  rcases family_descends (prefixWord ++ tailWord_7943626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7943676 : List Nat := [2, 2, 2, 1, 2, 1, 3, 2, 1, 5, 2]
def baseStart_7943676 : Nat := 118140960795 + 7943676 * 2 ^ 59
def prefixEnd_7943676 : Nat := 4983230072969 + 3 ^ 40 * 7943676 * 2
def baseEnd_7943676 : Nat := 4078923951584967564817705

theorem tailTrace_7943676 : CollatzResearch.WordTrace tailWord_7943676 prefixEnd_7943676 4078923951584967564817705 := by
  unfold tailWord_7943676
  simp only [CollatzResearch.WordTrace]
  refine ⟨144864832984712999347873441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193153110646283999130497921 144864832984712999347873441)
  ·
    refine ⟨108648624738534749510905081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144864832984712999347873441 108648624738534749510905081)
    ·
      refine ⟨81486468553901062133178811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108648624738534749510905081 81486468553901062133178811)
      ·
        refine ⟨122229702830851593199768217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81486468553901062133178811 122229702830851593199768217)
        ·
          refine ⟨91672277123138694899826163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122229702830851593199768217 91672277123138694899826163)
          ·
            refine ⟨137508415684708042349739245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91672277123138694899826163 137508415684708042349739245)
            ·
              refine ⟨51565655881765515881152217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 137508415684708042349739245 51565655881765515881152217)
              ·
                refine ⟨38674241911324136910864163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51565655881765515881152217 38674241911324136910864163)
                ·
                  refine ⟨58011362866986205366296245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38674241911324136910864163 58011362866986205366296245)
                  ·
                    refine ⟨5438565268779956753090273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 58011362866986205366296245 5438565268779956753090273)
                    ·
                      refine ⟨4078923951584967564817705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5438565268779956753090273 4078923951584967564817705)
                      ·
                        rfl

theorem cell23_7943676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 2, 1, 5, 2].length) (baseStart_7943676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7943676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7943676 prefixEnd_7943676 := by exact prefixLift 7943676
  have htrace : WordTrace (prefixWord ++ tailWord_7943676) baseStart_7943676 baseEnd_7943676 := by
    simpa [prefixWord, tailWord_7943676, baseEnd_7943676] using wordTrace_append hprefix tailTrace_7943676
  have hstable : (prefixWord ++ tailWord_7943676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7943676).length < 2 ^ (prefixWord ++ tailWord_7943676).sum := by decide
  have hdescent : baseEnd_7943676 < baseStart_7943676 := by decide
  rcases family_descends (prefixWord ++ tailWord_7943676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7943733 : List Nat := [1, 3, 3, 1, 1, 4, 1, 3, 2, 4]
def baseStart_7943733 : Nat := 118140960795 + 7943733 * 2 ^ 59
def prefixEnd_7943733 : Nat := 4983230072969 + 3 ^ 40 * 7943733 * 2
def baseEnd_7943733 : Nat := 1359651073327424613934981

theorem tailTrace_7943733 : CollatzResearch.WordTrace tailWord_7943733 prefixEnd_7943733 1359651073327424613934981 := by
  unfold tailWord_7943733
  simp only [CollatzResearch.WordTrace]
  refine ⟨289731744930219497430571853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193154496620146331620381235 289731744930219497430571853)
  ·
    refine ⟨108649404348832311536464445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 289731744930219497430571853 108649404348832311536464445)
    ·
      refine ⟨40743526630812116826174167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108649404348832311536464445 40743526630812116826174167)
      ·
        refine ⟨61115289946218175239261251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40743526630812116826174167 61115289946218175239261251)
        ·
          refine ⟨91672934919327262858891877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61115289946218175239261251 91672934919327262858891877)
          ·
            refine ⟨17188675297373861786042227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 91672934919327262858891877 17188675297373861786042227)
            ·
              refine ⟨25783012946060792679063341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17188675297373861786042227 25783012946060792679063341)
              ·
                refine ⟨9668629854772797254648753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25783012946060792679063341 9668629854772797254648753)
                ·
                  refine ⟨7251472391079597940986565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9668629854772797254648753 7251472391079597940986565)
                  ·
                    refine ⟨1359651073327424613934981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7251472391079597940986565 1359651073327424613934981)
                    ·
                      rfl

theorem cell23_7943733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 3, 2, 4].length) (baseStart_7943733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7943733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7943733 prefixEnd_7943733 := by exact prefixLift 7943733
  have htrace : WordTrace (prefixWord ++ tailWord_7943733) baseStart_7943733 baseEnd_7943733 := by
    simpa [prefixWord, tailWord_7943733, baseEnd_7943733] using wordTrace_append hprefix tailTrace_7943733
  have hstable : (prefixWord ++ tailWord_7943733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7943733).length < 2 ^ (prefixWord ++ tailWord_7943733).sum := by decide
  have hdescent : baseEnd_7943733 < baseStart_7943733 := by decide
  rcases family_descends (prefixWord ++ tailWord_7943733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7943739 : List Nat := [1, 1, 1, 1, 1, 2, 1, 2, 1, 9, 3]
def baseStart_7943739 : Nat := 118140960795 + 7943739 * 2 ^ 59
def prefixEnd_7943739 : Nat := 4983230072969 + 3 ^ 40 * 7943739 * 2
def baseEnd_7943739 : Nat := 4078956300866200818329915

theorem tailTrace_7943739 : CollatzResearch.WordTrace tailWord_7943739 prefixEnd_7943739 4078956300866200818329915 := by
  unfold tailWord_7943739
  simp only [CollatzResearch.WordTrace]
  refine ⟨289731963768197760455290271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193154642512131840303526847 289731963768197760455290271)
  ·
    refine ⟨434597945652296640682935407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289731963768197760455290271 434597945652296640682935407)
    ·
      refine ⟨651896918478444961024403111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 434597945652296640682935407 651896918478444961024403111)
      ·
        refine ⟨977845377717667441536604667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 651896918478444961024403111 977845377717667441536604667)
        ·
          refine ⟨1466768066576501162304907001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 977845377717667441536604667 1466768066576501162304907001)
          ·
            refine ⟨1100076049932375871728680251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1466768066576501162304907001 1100076049932375871728680251)
            ·
              refine ⟨1650114074898563807593020377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1100076049932375871728680251 1650114074898563807593020377)
              ·
                refine ⟨1237585556173922855694765283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1650114074898563807593020377 1237585556173922855694765283)
                ·
                  refine ⟨1856378334260884283542147925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1237585556173922855694765283 1856378334260884283542147925)
                  ·
                    refine ⟨10877216802309868848879773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 1856378334260884283542147925 10877216802309868848879773)
                    ·
                      refine ⟨4078956300866200818329915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10877216802309868848879773 4078956300866200818329915)
                      ·
                        rfl

theorem cell23_7943739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 9, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 9, 3].length) (baseStart_7943739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7943739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7943739 prefixEnd_7943739 := by exact prefixLift 7943739
  have htrace : WordTrace (prefixWord ++ tailWord_7943739) baseStart_7943739 baseEnd_7943739 := by
    simpa [prefixWord, tailWord_7943739, baseEnd_7943739] using wordTrace_append hprefix tailTrace_7943739
  have hstable : (prefixWord ++ tailWord_7943739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7943739).length < 2 ^ (prefixWord ++ tailWord_7943739).sum := by decide
  have hdescent : baseEnd_7943739 < baseStart_7943739 := by decide
  rcases family_descends (prefixWord ++ tailWord_7943739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7943740 : List Nat := [2, 2, 2, 2, 4, 2, 1, 2, 1, 1, 4]
def baseStart_7943740 : Nat := 118140960795 + 7943740 * 2 ^ 59
def prefixEnd_7943740 : Nat := 4983230072969 + 3 ^ 40 * 7943740 * 2
def baseEnd_7943740 : Nat := 4078956814346855314417411

theorem tailTrace_7943740 : CollatzResearch.WordTrace tailWord_7943740 prefixEnd_7943740 4078956814346855314417411 := by
  unfold tailWord_7943740
  simp only [CollatzResearch.WordTrace]
  refine ⟨144866000120597068813038337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193154666827462758417384449 144866000120597068813038337)
  ·
    refine ⟨108649500090447801609778753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144866000120597068813038337 108649500090447801609778753)
    ·
      refine ⟨81487125067835851207334065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108649500090447801609778753 81487125067835851207334065)
      ·
        refine ⟨61115343800876888405500549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81487125067835851207334065 61115343800876888405500549)
        ·
          refine ⟨11459126962664416576031353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61115343800876888405500549 11459126962664416576031353)
          ·
            refine ⟨8594345221998312432023515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11459126962664416576031353 8594345221998312432023515)
            ·
              refine ⟨12891517832997468648035273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8594345221998312432023515 12891517832997468648035273)
              ·
                refine ⟨9668638374748101486026455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12891517832997468648035273 9668638374748101486026455)
                ·
                  refine ⟨14502957562122152229039683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9668638374748101486026455 14502957562122152229039683)
                  ·
                    refine ⟨21754436343183228343559525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14502957562122152229039683 21754436343183228343559525)
                    ·
                      refine ⟨4078956814346855314417411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21754436343183228343559525 4078956814346855314417411)
                      ·
                        rfl

theorem cell23_7943740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 1, 2, 1, 1, 4].length) (baseStart_7943740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7943740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7943740 prefixEnd_7943740 := by exact prefixLift 7943740
  have htrace : WordTrace (prefixWord ++ tailWord_7943740) baseStart_7943740 baseEnd_7943740 := by
    simpa [prefixWord, tailWord_7943740, baseEnd_7943740] using wordTrace_append hprefix tailTrace_7943740
  have hstable : (prefixWord ++ tailWord_7943740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7943740).length < 2 ^ (prefixWord ++ tailWord_7943740).sum := by decide
  have hdescent : baseEnd_7943740 < baseStart_7943740 := by decide
  rcases family_descends (prefixWord ++ tailWord_7943740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7943743 : List Nat := [1, 1, 2, 2, 3, 3, 3, 2, 1, 2, 3]
def baseStart_7943743 : Nat := 118140960795 + 7943743 * 2 ^ 59
def prefixEnd_7943743 : Nat := 4983230072969 + 3 ^ 40 * 7943743 * 2
def baseEnd_7943743 : Nat := 4078958354788818802679897

theorem tailTrace_7943743 : CollatzResearch.WordTrace tailWord_7943743 prefixEnd_7943743 4078958354788818802679897 := by
  unfold tailWord_7943743
  simp only [CollatzResearch.WordTrace]
  refine ⟨289732109660183269138435883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193154739773455512758957255 289732109660183269138435883)
  ·
    refine ⟨434598164490274903707653825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289732109660183269138435883 434598164490274903707653825)
    ·
      refine ⟨325948623367706177780740369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 434598164490274903707653825 325948623367706177780740369)
      ·
        refine ⟨244461467525779633335555277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 325948623367706177780740369 244461467525779633335555277)
        ·
          refine ⟨91673050322167362500833229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 244461467525779633335555277 91673050322167362500833229)
          ·
            refine ⟨34377393870812760937812461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91673050322167362500833229 34377393870812760937812461)
            ·
              refine ⟨12891522701554785351679673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34377393870812760937812461 12891522701554785351679673)
              ·
                refine ⟨9668642026166089013759755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12891522701554785351679673 9668642026166089013759755)
                ·
                  refine ⟨14502963039249133520639633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9668642026166089013759755 14502963039249133520639633)
                  ·
                    refine ⟨10877222279436850140479725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14502963039249133520639633 10877222279436850140479725)
                    ·
                      refine ⟨4078958354788818802679897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10877222279436850140479725 4078958354788818802679897)
                      ·
                        rfl

theorem cell23_7943743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 3, 2, 1, 2, 3].length) (baseStart_7943743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7943743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7943743 prefixEnd_7943743 := by exact prefixLift 7943743
  have htrace : WordTrace (prefixWord ++ tailWord_7943743) baseStart_7943743 baseEnd_7943743 := by
    simpa [prefixWord, tailWord_7943743, baseEnd_7943743] using wordTrace_append hprefix tailTrace_7943743
  have hstable : (prefixWord ++ tailWord_7943743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7943743).length < 2 ^ (prefixWord ++ tailWord_7943743).sum := by decide
  have hdescent : baseEnd_7943743 < baseStart_7943743 := by decide
  rcases family_descends (prefixWord ++ tailWord_7943743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7943750 : List Nat := [6, 1, 1, 1, 3, 1, 1, 2, 1, 6]
def baseStart_7943750 : Nat := 118140960795 + 7943750 * 2 ^ 59
def prefixEnd_7943750 : Nat := 4983230072969 + 3 ^ 40 * 7943750 * 2
def baseEnd_7943750 : Nat := 1359653983051133425097455

theorem tailTrace_7943750 : CollatzResearch.WordTrace tailWord_7943750 prefixEnd_7943750 1359653983051133425097455 := by
  unfold tailWord_7943750
  simp only [CollatzResearch.WordTrace]
  refine ⟨9054136405348684666685647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 193154909980771939555960469 9054136405348684666685647)
  ·
    refine ⟨13581204608023027000028471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9054136405348684666685647 13581204608023027000028471)
    ·
      refine ⟨20371806912034540500042707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13581204608023027000028471 20371806912034540500042707)
      ·
        refine ⟨30557710368051810750064061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20371806912034540500042707 30557710368051810750064061)
        ·
          refine ⟨11459141388019429031274023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30557710368051810750064061 11459141388019429031274023)
          ·
            refine ⟨17188712082029143546911035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11459141388019429031274023 17188712082029143546911035)
            ·
              refine ⟨25783068123043715320366553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17188712082029143546911035 25783068123043715320366553)
              ·
                refine ⟨19337301092282786490274915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25783068123043715320366553 19337301092282786490274915)
                ·
                  refine ⟨29005951638424179735412373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19337301092282786490274915 29005951638424179735412373)
                  ·
                    refine ⟨1359653983051133425097455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29005951638424179735412373 1359653983051133425097455)
                    ·
                      rfl

theorem cell23_7943750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 2, 1, 6].length) (baseStart_7943750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7943750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7943750 prefixEnd_7943750 := by exact prefixLift 7943750
  have htrace : WordTrace (prefixWord ++ tailWord_7943750) baseStart_7943750 baseEnd_7943750 := by
    simpa [prefixWord, tailWord_7943750, baseEnd_7943750] using wordTrace_append hprefix tailTrace_7943750
  have hstable : (prefixWord ++ tailWord_7943750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7943750).length < 2 ^ (prefixWord ++ tailWord_7943750).sum := by decide
  have hdescent : baseEnd_7943750 < baseStart_7943750 := by decide
  rcases family_descends (prefixWord ++ tailWord_7943750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7943756 : List Nat := [2, 2, 1, 3, 1, 3, 1, 1, 3, 3, 3]
def baseStart_7943756 : Nat := 118140960795 + 7943756 * 2 ^ 59
def prefixEnd_7943756 : Nat := 4983230072969 + 3 ^ 40 * 7943756 * 2
def baseEnd_7943756 : Nat := 4078965030037327251817337

theorem tailTrace_7943756 : CollatzResearch.WordTrace tailWord_7943756 prefixEnd_7943756 4078965030037327251817337 := by
  unfold tailWord_7943756
  simp only [CollatzResearch.WordTrace]
  refine ⟨144866291904568086179329561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193155055872757448239106081 144866291904568086179329561)
  ·
    refine ⟨108649718928426064634497171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144866291904568086179329561 108649718928426064634497171)
    ·
      refine ⟨162974578392639096951745757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108649718928426064634497171 162974578392639096951745757)
      ·
        refine ⟨61115466897239661356904659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162974578392639096951745757 61115466897239661356904659)
        ·
          refine ⟨91673200345859492035356989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61115466897239661356904659 91673200345859492035356989)
          ·
            refine ⟨34377450129697309513258871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91673200345859492035356989 34377450129697309513258871)
            ·
              refine ⟨51566175194545964269888307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34377450129697309513258871 51566175194545964269888307)
              ·
                refine ⟨77349262791818946404832461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51566175194545964269888307 77349262791818946404832461)
                ·
                  refine ⟨29005973546932104901812173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77349262791818946404832461 29005973546932104901812173)
                  ·
                    refine ⟨10877240080099539338179565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29005973546932104901812173 10877240080099539338179565)
                    ·
                      refine ⟨4078965030037327251817337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10877240080099539338179565 4078965030037327251817337)
                      ·
                        rfl

theorem cell23_7943756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 1, 3, 3, 3].length) (baseStart_7943756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7943756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7943756 prefixEnd_7943756 := by exact prefixLift 7943756
  have htrace : WordTrace (prefixWord ++ tailWord_7943756) baseStart_7943756 baseEnd_7943756 := by
    simpa [prefixWord, tailWord_7943756, baseEnd_7943756] using wordTrace_append hprefix tailTrace_7943756
  have hstable : (prefixWord ++ tailWord_7943756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7943756).length < 2 ^ (prefixWord ++ tailWord_7943756).sum := by decide
  have hdescent : baseEnd_7943756 < baseStart_7943756 := by decide
  rcases family_descends (prefixWord ++ tailWord_7943756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7943757 : List Nat := [1, 6, 1, 1, 3, 1, 3, 1, 1, 1, 4]
def baseStart_7943757 : Nat := 118140960795 + 7943757 * 2 ^ 59
def prefixEnd_7943757 : Nat := 4983230072969 + 3 ^ 40 * 7943757 * 2
def baseEnd_7943757 : Nat := 4078965543517981747904833

theorem tailTrace_7943757 : CollatzResearch.WordTrace tailWord_7943757 prefixEnd_7943757 4078965543517981747904833 := by
  unfold tailWord_7943757
  simp only [CollatzResearch.WordTrace]
  refine ⟨289732620282132549529445525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193155080188088366352963683 289732620282132549529445525)
  ·
    refine ⟨13581216575724963259192759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 289732620282132549529445525 13581216575724963259192759)
    ·
      refine ⟨20371824863587444888789139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13581216575724963259192759 20371824863587444888789139)
      ·
        refine ⟨30557737295381167333183709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20371824863587444888789139 30557737295381167333183709)
        ·
          refine ⟨11459151485767937749943891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30557737295381167333183709 11459151485767937749943891)
          ·
            refine ⟨17188727228651906624915837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11459151485767937749943891 17188727228651906624915837)
            ·
              refine ⟨6445772710744464984343439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17188727228651906624915837 6445772710744464984343439)
              ·
                refine ⟨9668659066116697476515159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6445772710744464984343439 9668659066116697476515159)
                ·
                  refine ⟨14502988599175046214772739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9668659066116697476515159 14502988599175046214772739)
                  ·
                    refine ⟨21754482898762569322159109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14502988599175046214772739 21754482898762569322159109)
                    ·
                      refine ⟨4078965543517981747904833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21754482898762569322159109 4078965543517981747904833)
                      ·
                        rfl

theorem cell23_7943757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 3, 1, 1, 1, 4].length) (baseStart_7943757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7943757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7943757 prefixEnd_7943757 := by exact prefixLift 7943757
  have htrace : WordTrace (prefixWord ++ tailWord_7943757) baseStart_7943757 baseEnd_7943757 := by
    simpa [prefixWord, tailWord_7943757, baseEnd_7943757] using wordTrace_append hprefix tailTrace_7943757
  have hstable : (prefixWord ++ tailWord_7943757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7943757).length < 2 ^ (prefixWord ++ tailWord_7943757).sum := by decide
  have hdescent : baseEnd_7943757 < baseStart_7943757 := by decide
  rcases family_descends (prefixWord ++ tailWord_7943757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7943769 : List Nat := [1, 2, 1, 2, 2, 1, 1, 4, 2, 2, 5]
def baseStart_7943769 : Nat := 118140960795 + 7943769 * 2 ^ 59
def prefixEnd_7943769 : Nat := 4983230072969 + 3 ^ 40 * 7943769 * 2
def baseEnd_7943769 : Nat := 4078971705285835700954777

theorem tailTrace_7943769 : CollatzResearch.WordTrace tailWord_7943769 prefixEnd_7943769 4078971705285835700954777 := by
  unfold tailWord_7943769
  simp only [CollatzResearch.WordTrace]
  refine ⟨289733057958089075578882361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193155371972059383719254907 289733057958089075578882361)
  ·
    refine ⟨217299793468566806684161771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289733057958089075578882361 217299793468566806684161771)
    ·
      refine ⟨325949690202850210026242657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217299793468566806684161771 325949690202850210026242657)
      ·
        refine ⟨244462267652137657519681993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 325949690202850210026242657 244462267652137657519681993)
        ·
          refine ⟨183346700739103243139761495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 244462267652137657519681993 183346700739103243139761495)
          ·
            refine ⟨275020051108654864709642243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183346700739103243139761495 275020051108654864709642243)
            ·
              refine ⟨412530076662982297064463365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 275020051108654864709642243 412530076662982297064463365)
              ·
                refine ⟨77349389374309180699586881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 412530076662982297064463365 77349389374309180699586881)
                ·
                  refine ⟨58012042030731885524690161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77349389374309180699586881 58012042030731885524690161)
                  ·
                    refine ⟨43509031523048914143517621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58012042030731885524690161 43509031523048914143517621)
                    ·
                      refine ⟨4078971705285835700954777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43509031523048914143517621 4078971705285835700954777)
                      ·
                        rfl

theorem cell23_7943769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 4, 2, 2, 5].length) (baseStart_7943769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7943769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7943769 prefixEnd_7943769 := by exact prefixLift 7943769
  have htrace : WordTrace (prefixWord ++ tailWord_7943769) baseStart_7943769 baseEnd_7943769 := by
    simpa [prefixWord, tailWord_7943769, baseEnd_7943769] using wordTrace_append hprefix tailTrace_7943769
  have hstable : (prefixWord ++ tailWord_7943769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7943769).length < 2 ^ (prefixWord ++ tailWord_7943769).sum := by decide
  have hdescent : baseEnd_7943769 < baseStart_7943769 := by decide
  rcases family_descends (prefixWord ++ tailWord_7943769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7943783 : List Nat := [1, 1, 5, 1, 1, 1, 3, 2, 3, 3, 2]
def baseStart_7943783 : Nat := 118140960795 + 7943783 * 2 ^ 59
def prefixEnd_7943783 : Nat := 4983230072969 + 3 ^ 40 * 7943783 * 2
def baseEnd_7943783 : Nat := 4078978894014998646179713

theorem tailTrace_7943783 : CollatzResearch.WordTrace tailWord_7943783 prefixEnd_7943783 4078978894014998646179713 := by
  unfold tailWord_7943783
  simp only [CollatzResearch.WordTrace]
  refine ⟨289733568580038355969892003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193155712386692237313261335 289733568580038355969892003)
  ·
    refine ⟨434600352870057533954838005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289733568580038355969892003 434600352870057533954838005)
    ·
      refine ⟨40743783081567893808266063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 434600352870057533954838005 40743783081567893808266063)
      ·
        refine ⟨61115674622351840712399095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40743783081567893808266063 61115674622351840712399095)
        ·
          refine ⟨91673511933527761068598643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61115674622351840712399095 91673511933527761068598643)
          ·
            refine ⟨137510267900291641602897965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91673511933527761068598643 137510267900291641602897965)
            ·
              refine ⟨51566350462609365601086737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 137510267900291641602897965 51566350462609365601086737)
              ·
                refine ⟨38674762846957024200815053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51566350462609365601086737 38674762846957024200815053)
                ·
                  refine ⟨14503036067608884075305645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38674762846957024200815053 14503036067608884075305645)
                  ·
                    refine ⟨5438638525353331528239617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14503036067608884075305645 5438638525353331528239617)
                    ·
                      refine ⟨4078978894014998646179713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5438638525353331528239617 4078978894014998646179713)
                      ·
                        rfl

theorem cell23_7943783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 2, 3, 3, 2].length) (baseStart_7943783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7943783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7943783 prefixEnd_7943783 := by exact prefixLift 7943783
  have htrace : WordTrace (prefixWord ++ tailWord_7943783) baseStart_7943783 baseEnd_7943783 := by
    simpa [prefixWord, tailWord_7943783, baseEnd_7943783] using wordTrace_append hprefix tailTrace_7943783
  have hstable : (prefixWord ++ tailWord_7943783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7943783).length < 2 ^ (prefixWord ++ tailWord_7943783).sum := by decide
  have hdescent : baseEnd_7943783 < baseStart_7943783 := by decide
  rcases family_descends (prefixWord ++ tailWord_7943783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7943790 : List Nat := [4, 1, 2, 2, 3, 1, 2, 1, 1, 3, 3]
def baseStart_7943790 : Nat := 118140960795 + 7943790 * 2 ^ 59
def prefixEnd_7943790 : Nat := 4983230072969 + 3 ^ 40 * 7943790 * 2
def baseEnd_7943790 : Nat := 4078982488379580118792181

theorem tailTrace_7943790 : CollatzResearch.WordTrace tailWord_7943790 prefixEnd_7943790 4078982488379580118792181 := by
  unfold tailWord_7943790
  simp only [CollatzResearch.WordTrace]
  refine ⟨36216727986376624520674603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 193155882594008664110264549 36216727986376624520674603)
  ·
    refine ⟨54325091979564936781011905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36216727986376624520674603 54325091979564936781011905)
    ·
      refine ⟨40743818984673702585758929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54325091979564936781011905 40743818984673702585758929)
      ·
        refine ⟨30557864238505276939319197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40743818984673702585758929 30557864238505276939319197)
        ·
          refine ⟨11459199089439478852244699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30557864238505276939319197 11459199089439478852244699)
          ·
            refine ⟨17188798634159218278367049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11459199089439478852244699 17188798634159218278367049)
            ·
              refine ⟨12891598975619413708775287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17188798634159218278367049 12891598975619413708775287)
              ·
                refine ⟨19337398463429120563162931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12891598975619413708775287 19337398463429120563162931)
                ·
                  refine ⟨29006097695143680844744397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19337398463429120563162931 29006097695143680844744397)
                  ·
                    refine ⟨10877286635678880316779149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29006097695143680844744397 10877286635678880316779149)
                    ·
                      refine ⟨4078982488379580118792181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10877286635678880316779149 4078982488379580118792181)
                      ·
                        rfl

theorem cell23_7943790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 2, 1, 1, 3, 3].length) (baseStart_7943790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7943790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7943790 prefixEnd_7943790 := by exact prefixLift 7943790
  have htrace : WordTrace (prefixWord ++ tailWord_7943790) baseStart_7943790 baseEnd_7943790 := by
    simpa [prefixWord, tailWord_7943790, baseEnd_7943790] using wordTrace_append hprefix tailTrace_7943790
  have hstable : (prefixWord ++ tailWord_7943790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7943790).length < 2 ^ (prefixWord ++ tailWord_7943790).sum := by decide
  have hdescent : baseEnd_7943790 < baseStart_7943790 := by decide
  rcases family_descends (prefixWord ++ tailWord_7943790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7943813 : List Nat := [1, 3, 1, 1, 4, 1, 1, 4, 1, 4, 2]
def baseStart_7943813 : Nat := 118140960795 + 7943813 * 2 ^ 59
def prefixEnd_7943813 : Nat := 4983230072969 + 3 ^ 40 * 7943813 * 2
def baseEnd_7943813 : Nat := 4078994298434633528804575

theorem tailTrace_7943813 : CollatzResearch.WordTrace tailWord_7943813 prefixEnd_7943813 4078994298434633528804575 := by
  unfold tailWord_7943813
  simp only [CollatzResearch.WordTrace]
  refine ⟨289734662769929671093484093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193156441846619780728989395 289734662769929671093484093)
  ·
    refine ⟨108650498538723626660056535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 289734662769929671093484093 108650498538723626660056535)
    ·
      refine ⟨162975747808085439990084803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108650498538723626660056535 162975747808085439990084803)
      ·
        refine ⟨244463621712128159985127205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162975747808085439990084803 244463621712128159985127205)
        ·
          refine ⟨45836929071024029997211351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 244463621712128159985127205 45836929071024029997211351)
          ·
            refine ⟨68755393606536044995817027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45836929071024029997211351 68755393606536044995817027)
            ·
              refine ⟨103133090409804067493725541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68755393606536044995817027 103133090409804067493725541)
              ·
                refine ⟨19337454451838262655073539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 103133090409804067493725541 19337454451838262655073539)
                ·
                  refine ⟨29006181677757393982610309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19337454451838262655073539 29006181677757393982610309)
                  ·
                    refine ⟨5438659064579511371739433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29006181677757393982610309 5438659064579511371739433)
                    ·
                      refine ⟨4078994298434633528804575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5438659064579511371739433 4078994298434633528804575)
                      ·
                        rfl

theorem cell23_7943813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 4, 1, 4, 2].length) (baseStart_7943813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7943813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7943813 prefixEnd_7943813 := by exact prefixLift 7943813
  have htrace : WordTrace (prefixWord ++ tailWord_7943813) baseStart_7943813 baseEnd_7943813 := by
    simpa [prefixWord, tailWord_7943813, baseEnd_7943813] using wordTrace_append hprefix tailTrace_7943813
  have hstable : (prefixWord ++ tailWord_7943813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7943813).length < 2 ^ (prefixWord ++ tailWord_7943813).sum := by decide
  have hdescent : baseEnd_7943813 < baseStart_7943813 := by decide
  rcases family_descends (prefixWord ++ tailWord_7943813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7943819 : List Nat := [1, 1, 1, 1, 4, 1, 3, 2, 9]
def baseStart_7943819 : Nat := 118140960795 + 7943819 * 2 ^ 59
def prefixEnd_7943819 : Nat := 4983230072969 + 3 ^ 40 * 7943819 * 2
def baseEnd_7943819 : Nat := 453221931035395611703283

theorem tailTrace_7943819 : CollatzResearch.WordTrace tailWord_7943819 prefixEnd_7943819 453221931035395611703283 := by
  unfold tailWord_7943819
  simp only [CollatzResearch.WordTrace]
  refine ⟨289734881607907934118202511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193156587738605289412135007 289734881607907934118202511)
  ·
    refine ⟨434602322411861901177303767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289734881607907934118202511 434602322411861901177303767)
    ·
      refine ⟨651903483617792851765955651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 434602322411861901177303767 651903483617792851765955651)
      ·
        refine ⟨977855225426689277648933477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 651903483617792851765955651 977855225426689277648933477)
        ·
          refine ⟨183347854767504239559175027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 977855225426689277648933477 183347854767504239559175027)
          ·
            refine ⟨275021782151256359338762541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183347854767504239559175027 275021782151256359338762541)
            ·
              refine ⟨103133168306721134752035953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 275021782151256359338762541 103133168306721134752035953)
              ·
                refine ⟨77349876230040851064026965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103133168306721134752035953 77349876230040851064026965)
                ·
                  refine ⟨453221931035395611703283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 77349876230040851064026965 453221931035395611703283)
                  ·
                    rfl

theorem cell23_7943819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 2, 9].length) (baseStart_7943819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7943819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7943819 prefixEnd_7943819 := by exact prefixLift 7943819
  have htrace : WordTrace (prefixWord ++ tailWord_7943819) baseStart_7943819 baseEnd_7943819 := by
    simpa [prefixWord, tailWord_7943819, baseEnd_7943819] using wordTrace_append hprefix tailTrace_7943819
  have hstable : (prefixWord ++ tailWord_7943819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7943819).length < 2 ^ (prefixWord ++ tailWord_7943819).sum := by decide
  have hdescent : baseEnd_7943819 < baseStart_7943819 := by decide
  rcases family_descends (prefixWord ++ tailWord_7943819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7943866 : List Nat := [3, 1, 1, 1, 2, 4, 2, 1, 1, 7]
def baseStart_7943866 : Nat := 118140960795 + 7943866 * 2 ^ 59
def prefixEnd_7943866 : Nat := 4983230072969 + 3 ^ 40 * 7943866 * 2
def baseEnd_7943866 : Nat := 1359673837636440607147277

theorem tailTrace_7943866 : CollatzResearch.WordTrace tailWord_7943866 prefixEnd_7943866 1359673837636440607147277 := by
  unfold tailWord_7943866
  simp only [CollatzResearch.WordTrace]
  refine ⟨72434148959684415286290863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193157730559158440763442301 72434148959684415286290863)
  ·
    refine ⟨108651223439526622929436295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72434148959684415286290863 108651223439526622929436295)
    ·
      refine ⟨162976835159289934394154443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108651223439526622929436295 162976835159289934394154443)
      ·
        refine ⟨244465252738934901591231665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162976835159289934394154443 244465252738934901591231665)
        ·
          refine ⟨183348939554201176193423749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 244465252738934901591231665 183348939554201176193423749)
          ·
            refine ⟨34377926166412720536266953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 183348939554201176193423749 34377926166412720536266953)
            ·
              refine ⟨25783444624809540402200215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34377926166412720536266953 25783444624809540402200215)
              ·
                refine ⟨38675166937214310603300323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25783444624809540402200215 38675166937214310603300323)
                ·
                  refine ⟨58012750405821465904950485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38675166937214310603300323 58012750405821465904950485)
                  ·
                    refine ⟨1359673837636440607147277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58012750405821465904950485 1359673837636440607147277)
                    ·
                      rfl

theorem cell23_7943866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 1, 1, 7].length) (baseStart_7943866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7943866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7943866 prefixEnd_7943866 := by exact prefixLift 7943866
  have htrace : WordTrace (prefixWord ++ tailWord_7943866) baseStart_7943866 baseEnd_7943866 := by
    simpa [prefixWord, tailWord_7943866, baseEnd_7943866] using wordTrace_append hprefix tailTrace_7943866
  have hstable : (prefixWord ++ tailWord_7943866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7943866).length < 2 ^ (prefixWord ++ tailWord_7943866).sum := by decide
  have hdescent : baseEnd_7943866 < baseStart_7943866 := by decide
  rcases family_descends (prefixWord ++ tailWord_7943866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7943870 : List Nat := [4, 2, 1, 1, 2, 2, 3, 3, 5]
def baseStart_7943870 : Nat := 118140960795 + 7943870 * 2 ^ 59
def prefixEnd_7943870 : Nat := 4983230072969 + 3 ^ 40 * 7943870 * 2
def baseEnd_7943870 : Nat := 453224840759104422865757

theorem tailTrace_7943870 : CollatzResearch.WordTrace tailWord_7943870 prefixEnd_7943870 453224840759104422865757 := by
  unfold tailWord_7943870
  simp only [CollatzResearch.WordTrace]
  refine ⟨36217092716340396228538633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 193157827820482113218872709 36217092716340396228538633)
  ·
    refine ⟨27162819537255297171403975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36217092716340396228538633 27162819537255297171403975)
    ·
      refine ⟨40744229305882945757105963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27162819537255297171403975 40744229305882945757105963)
      ·
        refine ⟨61116343958824418635658945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40744229305882945757105963 61116343958824418635658945)
        ·
          refine ⟨45837257969118313976744209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61116343958824418635658945 45837257969118313976744209)
          ·
            refine ⟨34377943476838735482558157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45837257969118313976744209 34377943476838735482558157)
            ·
              refine ⟨12891728803814525805959309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34377943476838735482558157 12891728803814525805959309)
              ·
                refine ⟨4834398301430447177234741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12891728803814525805959309 4834398301430447177234741)
                ·
                  refine ⟨453224840759104422865757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4834398301430447177234741 453224840759104422865757)
                  ·
                    rfl

theorem cell23_7943870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 3, 3, 5].length) (baseStart_7943870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7943870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7943870 prefixEnd_7943870 := by exact prefixLift 7943870
  have htrace : WordTrace (prefixWord ++ tailWord_7943870) baseStart_7943870 baseEnd_7943870 := by
    simpa [prefixWord, tailWord_7943870, baseEnd_7943870] using wordTrace_append hprefix tailTrace_7943870
  have hstable : (prefixWord ++ tailWord_7943870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7943870).length < 2 ^ (prefixWord ++ tailWord_7943870).sum := by decide
  have hdescent : baseEnd_7943870 < baseStart_7943870 := by decide
  rcases family_descends (prefixWord ++ tailWord_7943870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7943903 : List Nat := [1, 1, 2, 3, 2, 2, 2, 1, 1, 6, 2]
def baseStart_7943903 : Nat := 118140960795 + 7943903 * 2 ^ 59
def prefixEnd_7943903 : Nat := 4983230072969 + 3 ^ 40 * 7943903 * 2
def baseEnd_7943903 : Nat := 4079040511693538176679161

theorem tailTrace_7943903 : CollatzResearch.WordTrace tailWord_7943903 prefixEnd_7943903 4079040511693538176679161 := by
  unfold tailWord_7943903
  simp only [CollatzResearch.WordTrace]
  refine ⟨289737945339603616464260363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193158630226402410976173575 289737945339603616464260363)
  ·
    refine ⟨434606918009405424696390545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289737945339603616464260363 434606918009405424696390545)
    ·
      refine ⟨325955188507054068522292909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 434606918009405424696390545 325955188507054068522292909)
      ·
        refine ⟨122233195690145275695859841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 325955188507054068522292909 122233195690145275695859841)
        ·
          refine ⟨91674896767608956771894881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122233195690145275695859841 91674896767608956771894881)
          ·
            refine ⟨68756172575706717578921161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91674896767608956771894881 68756172575706717578921161)
            ·
              refine ⟨51567129431780038184190871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68756172575706717578921161 51567129431780038184190871)
              ·
                refine ⟨77350694147670057276286307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51567129431780038184190871 77350694147670057276286307)
                ·
                  refine ⟨116026041221505085914429461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77350694147670057276286307 116026041221505085914429461)
                  ·
                    refine ⟨5438720682258050902238881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 116026041221505085914429461 5438720682258050902238881)
                    ·
                      refine ⟨4079040511693538176679161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5438720682258050902238881 4079040511693538176679161)
                      ·
                        rfl

theorem cell23_7943903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 1, 1, 6, 2].length) (baseStart_7943903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7943903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7943903 prefixEnd_7943903 := by exact prefixLift 7943903
  have htrace : WordTrace (prefixWord ++ tailWord_7943903) baseStart_7943903 baseEnd_7943903 := by
    simpa [prefixWord, tailWord_7943903, baseEnd_7943903] using wordTrace_append hprefix tailTrace_7943903
  have hstable : (prefixWord ++ tailWord_7943903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7943903).length < 2 ^ (prefixWord ++ tailWord_7943903).sum := by decide
  have hdescent : baseEnd_7943903 < baseStart_7943903 := by decide
  rcases family_descends (prefixWord ++ tailWord_7943903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7943916 : List Nat := [2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 4]
def baseStart_7943916 : Nat := 118140960795 + 7943916 * 2 ^ 59
def prefixEnd_7943916 : Nat := 4983230072969 + 3 ^ 40 * 7943916 * 2
def baseEnd_7943916 : Nat := 4079047186942046625816601

theorem tailTrace_7943916 : CollatzResearch.WordTrace tailWord_7943916 prefixEnd_7943916 4079047186942046625816601 := by
  unfold tailWord_7943916
  simp only [CollatzResearch.WordTrace]
  refine ⟨144869209744278259842241801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193158946325704346456322401 144869209744278259842241801)
  ·
    refine ⟨108651907308208694881681351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144869209744278259842241801 108651907308208694881681351)
    ·
      refine ⟨162977860962313042322522027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108651907308208694881681351 162977860962313042322522027)
      ·
        refine ⟨244466791443469563483783041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162977860962313042322522027 244466791443469563483783041)
        ·
          refine ⟨183350093582602172612837281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 244466791443469563483783041 183350093582602172612837281)
          ·
            refine ⟨137512570186951629459627961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183350093582602172612837281 137512570186951629459627961)
            ·
              refine ⟨103134427640213722094720971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137512570186951629459627961 103134427640213722094720971)
              ·
                refine ⟨154701641460320583142081457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103134427640213722094720971 154701641460320583142081457)
                ·
                  refine ⟨116026231095240437356561093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 154701641460320583142081457 116026231095240437356561093)
                  ·
                    refine ⟨21754918330357582004355205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 116026231095240437356561093 21754918330357582004355205)
                    ·
                      refine ⟨4079047186942046625816601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21754918330357582004355205 4079047186942046625816601)
                      ·
                        rfl

theorem cell23_7943916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 4].length) (baseStart_7943916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7943916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7943916 prefixEnd_7943916 := by exact prefixLift 7943916
  have htrace : WordTrace (prefixWord ++ tailWord_7943916) baseStart_7943916 baseEnd_7943916 := by
    simpa [prefixWord, tailWord_7943916, baseEnd_7943916] using wordTrace_append hprefix tailTrace_7943916
  have hstable : (prefixWord ++ tailWord_7943916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7943916).length < 2 ^ (prefixWord ++ tailWord_7943916).sum := by decide
  have hdescent : baseEnd_7943916 < baseStart_7943916 := by decide
  rcases family_descends (prefixWord ++ tailWord_7943916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7943923 : List Nat := [1, 1, 1, 2, 2, 3, 3, 3, 2, 2, 3]
def baseStart_7943923 : Nat := 118140960795 + 7943923 * 2 ^ 59
def prefixEnd_7943923 : Nat := 4983230072969 + 3 ^ 40 * 7943923 * 2
def baseEnd_7943923 : Nat := 4079050781306628098429069

theorem tailTrace_7943923 : CollatzResearch.WordTrace tailWord_7943923 prefixEnd_7943923 4079050781306628098429069 := by
  unfold tailWord_7943923
  simp only [CollatzResearch.WordTrace]
  refine ⟨289738674799531159879988423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193159116533020773253325615 289738674799531159879988423)
  ·
    refine ⟨434608012199296739819982635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289738674799531159879988423 434608012199296739819982635)
    ·
      refine ⟨651912018298945109729973953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 434608012199296739819982635 651912018298945109729973953)
      ·
        refine ⟨488934013724208832297480465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 651912018298945109729973953 488934013724208832297480465)
        ·
          refine ⟨366700510293156624223110349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 488934013724208832297480465 366700510293156624223110349)
          ·
            refine ⟨137512691359933734083666381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 366700510293156624223110349 137512691359933734083666381)
            ·
              refine ⟨51567259259975150281374893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 137512691359933734083666381 51567259259975150281374893)
              ·
                refine ⟨19337722222490681355515585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51567259259975150281374893 19337722222490681355515585)
                ·
                  refine ⟨14503291666868011016636689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19337722222490681355515585 14503291666868011016636689)
                  ·
                    refine ⟨10877468750151008262477517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14503291666868011016636689 10877468750151008262477517)
                    ·
                      refine ⟨4079050781306628098429069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10877468750151008262477517 4079050781306628098429069)
                      ·
                        rfl

theorem cell23_7943923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 3, 2, 2, 3].length) (baseStart_7943923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7943923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7943923 prefixEnd_7943923 := by exact prefixLift 7943923
  have htrace : WordTrace (prefixWord ++ tailWord_7943923) baseStart_7943923 baseEnd_7943923 := by
    simpa [prefixWord, tailWord_7943923, baseEnd_7943923] using wordTrace_append hprefix tailTrace_7943923
  have hstable : (prefixWord ++ tailWord_7943923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7943923).length < 2 ^ (prefixWord ++ tailWord_7943923).sum := by decide
  have hdescent : baseEnd_7943923 < baseStart_7943923 := by decide
  rcases family_descends (prefixWord ++ tailWord_7943923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7943930 : List Nat := [3, 1, 1, 1, 1, 3, 1, 7, 1, 4]
def baseStart_7943930 : Nat := 118140960795 + 7943930 * 2 ^ 59
def prefixEnd_7943930 : Nat := 4983230072969 + 3 ^ 40 * 7943930 * 2
def baseEnd_7943930 : Nat := 1359684791890403190347179

theorem tailTrace_7943930 : CollatzResearch.WordTrace tailWord_7943930 prefixEnd_7943930 1359684791890403190347179 := by
  unfold tailWord_7943930
  simp only [CollatzResearch.WordTrace]
  refine ⟨72434732527626450018873311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193159286740337200050328829 72434732527626450018873311)
  ·
    refine ⟨108652098791439675028309967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72434732527626450018873311 108652098791439675028309967)
    ·
      refine ⟨162978148187159512542464951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108652098791439675028309967 162978148187159512542464951)
      ·
        refine ⟨244467222280739268813697427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162978148187159512542464951 244467222280739268813697427)
        ·
          refine ⟨366700833421108903220546141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244467222280739268813697427 366700833421108903220546141)
          ·
            refine ⟨137512812532915838707704803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 366700833421108903220546141 137512812532915838707704803)
            ·
              refine ⟨206269218799373758061557205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137512812532915838707704803 206269218799373758061557205)
              ·
                refine ⟨4834434815610322454567747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 206269218799373758061557205 4834434815610322454567747)
                ·
                  refine ⟨7251652223415483681851621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4834434815610322454567747 7251652223415483681851621)
                  ·
                    refine ⟨1359684791890403190347179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7251652223415483681851621 1359684791890403190347179)
                    ·
                      rfl

theorem cell23_7943930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 7, 1, 4].length) (baseStart_7943930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7943930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7943930 prefixEnd_7943930 := by exact prefixLift 7943930
  have htrace : WordTrace (prefixWord ++ tailWord_7943930) baseStart_7943930 baseEnd_7943930 := by
    simpa [prefixWord, tailWord_7943930, baseEnd_7943930] using wordTrace_append hprefix tailTrace_7943930
  have hstable : (prefixWord ++ tailWord_7943930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7943930).length < 2 ^ (prefixWord ++ tailWord_7943930).sum := by decide
  have hdescent : baseEnd_7943930 < baseStart_7943930 := by decide
  rcases family_descends (prefixWord ++ tailWord_7943930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7943940 : List Nat := [2, 3, 2, 2, 1, 2, 2, 2, 2, 2, 3]
def baseStart_7943940 : Nat := 118140960795 + 7943940 * 2 ^ 59
def prefixEnd_7943940 : Nat := 4983230072969 + 3 ^ 40 * 7943940 * 2
def baseEnd_7943940 : Nat := 4079059510477754531916491

theorem tailTrace_7943940 : CollatzResearch.WordTrace tailWord_7943940 prefixEnd_7943940 4079059510477754531916491 := by
  unfold tailWord_7943940
  simp only [CollatzResearch.WordTrace]
  refine ⟨144869647420234785891678637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193159529893646381188904849 144869647420234785891678637)
  ·
    refine ⟨54326117782588044709379489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144869647420234785891678637 54326117782588044709379489)
    ·
      refine ⟨40744588336941033532034617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54326117782588044709379489 40744588336941033532034617)
      ·
        refine ⟨30558441252705775149025963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40744588336941033532034617 30558441252705775149025963)
        ·
          refine ⟨45837661879058662723538945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30558441252705775149025963 45837661879058662723538945)
          ·
            refine ⟨34378246409293997042654209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45837661879058662723538945 34378246409293997042654209)
            ·
              refine ⟨25783684806970497781990657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34378246409293997042654209 25783684806970497781990657)
              ·
                refine ⟨19337763605227873336492993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25783684806970497781990657 19337763605227873336492993)
                ·
                  refine ⟨14503322703920905002369745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19337763605227873336492993 14503322703920905002369745)
                  ·
                    refine ⟨10877492027940678751777309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14503322703920905002369745 10877492027940678751777309)
                    ·
                      refine ⟨4079059510477754531916491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10877492027940678751777309 4079059510477754531916491)
                      ·
                        rfl

theorem cell23_7943940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 2, 2, 2, 3].length) (baseStart_7943940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7943940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7943940 prefixEnd_7943940 := by exact prefixLift 7943940
  have htrace : WordTrace (prefixWord ++ tailWord_7943940) baseStart_7943940 baseEnd_7943940 := by
    simpa [prefixWord, tailWord_7943940, baseEnd_7943940] using wordTrace_append hprefix tailTrace_7943940
  have hstable : (prefixWord ++ tailWord_7943940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7943940).length < 2 ^ (prefixWord ++ tailWord_7943940).sum := by decide
  have hdescent : baseEnd_7943940 < baseStart_7943940 := by decide
  rcases family_descends (prefixWord ++ tailWord_7943940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7943947 : List Nat := [1, 1, 1, 1, 5, 1, 6, 2, 1, 4]
def baseStart_7943947 : Nat := 118140960795 + 7943947 * 2 ^ 59
def prefixEnd_7943947 : Nat := 4983230072969 + 3 ^ 40 * 7943947 * 2
def baseEnd_7943947 : Nat := 1359687701614112001509653

theorem tailTrace_7943947 : CollatzResearch.WordTrace tailWord_7943947 prefixEnd_7943947 1359687701614112001509653 := by
  unfold tailWord_7943947
  simp only [CollatzResearch.WordTrace]
  refine ⟨289739550151444211978862095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193159700100962807985908063 289739550151444211978862095)
  ·
    refine ⟨434609325227166317968293143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289739550151444211978862095 434609325227166317968293143)
    ·
      refine ⟨651913987840749476952439715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 434609325227166317968293143 651913987840749476952439715)
      ·
        refine ⟨977870981761124215428659573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 651913987840749476952439715 977870981761124215428659573)
        ·
          refine ⟨91675404540105395196436835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 977870981761124215428659573 91675404540105395196436835)
          ·
            refine ⟨137513106810158092794655253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91675404540105395196436835 137513106810158092794655253)
            ·
              refine ⟨6445926881726160599749465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 137513106810158092794655253 6445926881726160599749465)
              ·
                refine ⟨4834445161294620449812099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6445926881726160599749465 4834445161294620449812099)
                ·
                  refine ⟨7251667741941930674718149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4834445161294620449812099 7251667741941930674718149)
                  ·
                    refine ⟨1359687701614112001509653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7251667741941930674718149 1359687701614112001509653)
                    ·
                      rfl

theorem cell23_7943947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 6, 2, 1, 4].length) (baseStart_7943947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7943947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7943947 prefixEnd_7943947 := by exact prefixLift 7943947
  have htrace : WordTrace (prefixWord ++ tailWord_7943947) baseStart_7943947 baseEnd_7943947 := by
    simpa [prefixWord, tailWord_7943947, baseEnd_7943947] using wordTrace_append hprefix tailTrace_7943947
  have hstable : (prefixWord ++ tailWord_7943947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7943947).length < 2 ^ (prefixWord ++ tailWord_7943947).sum := by decide
  have hdescent : baseEnd_7943947 < baseStart_7943947 := by decide
  rcases family_descends (prefixWord ++ tailWord_7943947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7943963 : List Nat := [1, 1, 1, 1, 1, 1, 4, 3, 3, 5, 2]
def baseStart_7943963 : Nat := 118140960795 + 7943963 * 2 ^ 59
def prefixEnd_7943963 : Nat := 4983230072969 + 3 ^ 40 * 7943963 * 2
def baseEnd_7943963 : Nat := 4079071320532807941928885

theorem tailTrace_7943963 : CollatzResearch.WordTrace tailWord_7943963 prefixEnd_7943963 4079071320532807941928885 := by
  unfold tailWord_7943963
  simp only [CollatzResearch.WordTrace]
  refine ⟨289740133719386246711444543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193160089146257497807629695 289740133719386246711444543)
  ·
    refine ⟨434610200579079370067166815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289740133719386246711444543 434610200579079370067166815)
    ·
      refine ⟨651915300868619055100750223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 434610200579079370067166815 651915300868619055100750223)
      ·
        refine ⟨977872951302928582651125335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 651915300868619055100750223 977872951302928582651125335)
        ·
          refine ⟨1466809426954392873976688003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 977872951302928582651125335 1466809426954392873976688003)
          ·
            refine ⟨2200214140431589310965032005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1466809426954392873976688003 2200214140431589310965032005)
            ·
              refine ⟨412540151330922995805943501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2200214140431589310965032005 412540151330922995805943501)
              ·
                refine ⟨154702556749096123427228813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 412540151330922995805943501 154702556749096123427228813)
                ·
                  refine ⟨58013458780911046285210805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 154702556749096123427228813 58013458780911046285210805)
                  ·
                    refine ⟨5438761760710410589238513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 58013458780911046285210805 5438761760710410589238513)
                    ·
                      refine ⟨4079071320532807941928885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5438761760710410589238513 4079071320532807941928885)
                      ·
                        rfl

theorem cell23_7943963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 3, 5, 2].length) (baseStart_7943963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7943963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7943963 prefixEnd_7943963 := by exact prefixLift 7943963
  have htrace : WordTrace (prefixWord ++ tailWord_7943963) baseStart_7943963 baseEnd_7943963 := by
    simpa [prefixWord, tailWord_7943963, baseEnd_7943963] using wordTrace_append hprefix tailTrace_7943963
  have hstable : (prefixWord ++ tailWord_7943963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7943963).length < 2 ^ (prefixWord ++ tailWord_7943963).sum := by decide
  have hdescent : baseEnd_7943963 < baseStart_7943963 := by decide
  rcases family_descends (prefixWord ++ tailWord_7943963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7943973 : List Nat := [1, 3, 1, 2, 3, 2, 2, 1, 3, 5]
def baseStart_7943973 : Nat := 118140960795 + 7943973 * 2 ^ 59
def prefixEnd_7943973 : Nat := 4983230072969 + 3 ^ 40 * 7943973 * 2
def baseEnd_7943973 : Nat := 1359692151779784300934613

theorem tailTrace_7943973 : CollatzResearch.WordTrace tailWord_7943973 prefixEnd_7943973 1359692151779784300934613 := by
  unfold tailWord_7943973
  simp only [CollatzResearch.WordTrace]
  refine ⟨289740498449350018419308573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193160332299566678946205715 289740498449350018419308573)
  ·
    refine ⟨108652686918506256907240715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 289740498449350018419308573 108652686918506256907240715)
    ·
      refine ⟨162979030377759385360861073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108652686918506256907240715 162979030377759385360861073)
      ·
        refine ⟨122234272783319539020645805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162979030377759385360861073 122234272783319539020645805)
        ·
          refine ⟨45837852293744827132742177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122234272783319539020645805 45837852293744827132742177)
          ·
            refine ⟨34378389220308620349556633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45837852293744827132742177 34378389220308620349556633)
            ·
              refine ⟨25783791915231465262167475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34378389220308620349556633 25783791915231465262167475)
              ·
                refine ⟨38675687872847197893251213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25783791915231465262167475 38675687872847197893251213)
                ·
                  refine ⟨14503382952317699209969205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38675687872847197893251213 14503382952317699209969205)
                  ·
                    refine ⟨1359692151779784300934613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14503382952317699209969205 1359692151779784300934613)
                    ·
                      rfl

theorem cell23_7943973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 1, 3, 5].length) (baseStart_7943973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7943973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7943973 prefixEnd_7943973 := by exact prefixLift 7943973
  have htrace : WordTrace (prefixWord ++ tailWord_7943973) baseStart_7943973 baseEnd_7943973 := by
    simpa [prefixWord, tailWord_7943973, baseEnd_7943973] using wordTrace_append hprefix tailTrace_7943973
  have hstable : (prefixWord ++ tailWord_7943973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7943973).length < 2 ^ (prefixWord ++ tailWord_7943973).sum := by decide
  have hdescent : baseEnd_7943973 < baseStart_7943973 := by decide
  rcases family_descends (prefixWord ++ tailWord_7943973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7943980 : List Nat := [2, 2, 1, 1, 1, 6, 1, 1, 1, 5, 2]
def baseStart_7943980 : Nat := 118140960795 + 7943980 * 2 ^ 59
def prefixEnd_7943980 : Nat := 4983230072969 + 3 ^ 40 * 7943980 * 2
def baseEnd_7943980 : Nat := 4079080049703934375416307

theorem tailTrace_7943980 : CollatzResearch.WordTrace tailWord_7943980 prefixEnd_7943980 4079080049703934375416307 := by
  unfold tailWord_7943980
  simp only [CollatzResearch.WordTrace]
  refine ⟨144870376880162329307406697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193160502506883105743208929 144870376880162329307406697)
  ·
    refine ⟨108652782660121746980555023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144870376880162329307406697 108652782660121746980555023)
    ·
      refine ⟨162979173990182620470832535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108652782660121746980555023 162979173990182620470832535)
      ·
        refine ⟨244468760985273930706248803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162979173990182620470832535 244468760985273930706248803)
        ·
          refine ⟨366703141477910896059373205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244468760985273930706248803 366703141477910896059373205)
          ·
            refine ⟨17189209756777073252783119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 366703141477910896059373205 17189209756777073252783119)
            ·
              refine ⟨25783814635165609879174679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17189209756777073252783119 25783814635165609879174679)
              ·
                refine ⟨38675721952748414818762019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25783814635165609879174679 38675721952748414818762019)
                ·
                  refine ⟨58013582929122622228143029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38675721952748414818762019 58013582929122622228143029)
                  ·
                    refine ⟨5438773399605245833888409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 58013582929122622228143029 5438773399605245833888409)
                    ·
                      refine ⟨4079080049703934375416307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5438773399605245833888409 4079080049703934375416307)
                      ·
                        rfl

theorem cell23_7943980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 5, 2].length) (baseStart_7943980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7943980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7943980 prefixEnd_7943980 := by exact prefixLift 7943980
  have htrace : WordTrace (prefixWord ++ tailWord_7943980) baseStart_7943980 baseEnd_7943980 := by
    simpa [prefixWord, tailWord_7943980, baseEnd_7943980] using wordTrace_append hprefix tailTrace_7943980
  have hstable : (prefixWord ++ tailWord_7943980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7943980).length < 2 ^ (prefixWord ++ tailWord_7943980).sum := by decide
  have hdescent : baseEnd_7943980 < baseStart_7943980 := by decide
  rcases family_descends (prefixWord ++ tailWord_7943980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7944016 : List Nat := [2, 1, 1, 1, 1, 4, 1, 12]
def baseStart_7944016 : Nat := 118140960795 + 7944016 * 2 ^ 59
def prefixEnd_7944016 : Nat := 4983230072969 + 3 ^ 40 * 7944016 * 2
def baseEnd_7944016 : Nat := 151077723518796156835783

theorem tailTrace_7944016 : CollatzResearch.WordTrace tailWord_7944016 prefixEnd_7944016 151077723518796156835783 := by
  unfold tailWord_7944016
  simp only [CollatzResearch.WordTrace]
  refine ⟨144871033394097118381561951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193161377858796157842082601 144871033394097118381561951)
  ·
    refine ⟨217306550091145677572342927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144871033394097118381561951 217306550091145677572342927)
    ·
      refine ⟨325959825136718516358514391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217306550091145677572342927 325959825136718516358514391)
      ·
        refine ⟨488939737705077774537771587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 325959825136718516358514391 488939737705077774537771587)
        ·
          refine ⟨733409606557616661806657381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 488939737705077774537771587 733409606557616661806657381)
          ·
            refine ⟨137514301229553124088748259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 733409606557616661806657381 137514301229553124088748259)
            ·
              refine ⟨206271451844329686133122389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137514301229553124088748259 206271451844329686133122389)
              ·
                refine ⟨151077723518796156835783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 206271451844329686133122389 151077723518796156835783)
                ·
                  rfl

theorem cell23_7944016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 12].length) (baseStart_7944016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7944016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7944016 prefixEnd_7944016 := by exact prefixLift 7944016
  have htrace : WordTrace (prefixWord ++ tailWord_7944016) baseStart_7944016 baseEnd_7944016 := by
    simpa [prefixWord, tailWord_7944016, baseEnd_7944016] using wordTrace_append hprefix tailTrace_7944016
  have hstable : (prefixWord ++ tailWord_7944016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7944016).length < 2 ^ (prefixWord ++ tailWord_7944016).sum := by decide
  have hdescent : baseEnd_7944016 < baseStart_7944016 := by decide
  rcases family_descends (prefixWord ++ tailWord_7944016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7944020 : List Nat := [2, 4, 1, 1, 3, 1, 3, 1, 1, 6]
def baseStart_7944020 : Nat := 118140960795 + 7944020 * 2 ^ 59
def prefixEnd_7944020 : Nat := 4983230072969 + 3 ^ 40 * 7944020 * 2
def baseEnd_7944020 : Nat := 1359700196310038072972041

theorem tailTrace_7944020 : CollatzResearch.WordTrace tailWord_7944020 prefixEnd_7944020 1359700196310038072972041 := by
  unfold tailWord_7944020
  simp only [CollatzResearch.WordTrace]
  refine ⟨144871106340089872723134757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193161475120119830297513009 144871106340089872723134757)
  ·
    refine ⟨27163332438766851135587767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 144871106340089872723134757 27163332438766851135587767)
    ·
      refine ⟨40744998658150276703381651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27163332438766851135587767 40744998658150276703381651)
      ·
        refine ⟨61117497987225415055072477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40744998658150276703381651 61117497987225415055072477)
        ·
          refine ⟨22919061745209530645652179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61117497987225415055072477 22919061745209530645652179)
          ·
            refine ⟨34378592617814295968478269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22919061745209530645652179 34378592617814295968478269)
            ·
              refine ⟨12891972231680360988179351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34378592617814295968478269 12891972231680360988179351)
              ·
                refine ⟨19337958347520541482269027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12891972231680360988179351 19337958347520541482269027)
                ·
                  refine ⟨29006937521280812223403541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19337958347520541482269027 29006937521280812223403541)
                  ·
                    refine ⟨1359700196310038072972041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29006937521280812223403541 1359700196310038072972041)
                    ·
                      rfl

theorem cell23_7944020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 3, 1, 1, 6].length) (baseStart_7944020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7944020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7944020 prefixEnd_7944020 := by exact prefixLift 7944020
  have htrace : WordTrace (prefixWord ++ tailWord_7944020) baseStart_7944020 baseEnd_7944020 := by
    simpa [prefixWord, tailWord_7944020, baseEnd_7944020] using wordTrace_append hprefix tailTrace_7944020
  have hstable : (prefixWord ++ tailWord_7944020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7944020).length < 2 ^ (prefixWord ++ tailWord_7944020).sum := by decide
  have hdescent : baseEnd_7944020 < baseStart_7944020 := by decide
  rcases family_descends (prefixWord ++ tailWord_7944020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7944043 : List Nat := [1, 1, 1, 1, 2, 2, 3, 3, 3, 3, 3]
def baseStart_7944043 : Nat := 118140960795 + 7944043 * 2 ^ 59
def prefixEnd_7944043 : Nat := 4983230072969 + 3 ^ 40 * 7944043 * 2
def baseEnd_7944043 : Nat := 4079112398985167628928517

theorem tailTrace_7944043 : CollatzResearch.WordTrace tailWord_7944043 prefixEnd_7944043 4079112398985167628928517 := by
  unfold tailWord_7944043
  simp only [CollatzResearch.WordTrace]
  refine ⟨289743051559096420374356783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193162034372730946916237855 289743051559096420374356783)
  ·
    refine ⟨434614577338644630561535175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289743051559096420374356783 434614577338644630561535175)
    ·
      refine ⟨651921866007966945842302763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 434614577338644630561535175 651921866007966945842302763)
      ·
        refine ⟨977882799011950418763454145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 651921866007966945842302763 977882799011950418763454145)
        ·
          refine ⟨733412099258962814072590609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 977882799011950418763454145 733412099258962814072590609)
          ·
            refine ⟨550059074444222110554442957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 733412099258962814072590609 550059074444222110554442957)
            ·
              refine ⟨206272152916583291457916109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 550059074444222110554442957 206272152916583291457916109)
              ·
                refine ⟨77352057343718734296718541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 206272152916583291457916109 77352057343718734296718541)
                ·
                  refine ⟨29007021503894525361269453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77352057343718734296718541 29007021503894525361269453)
                  ·
                    refine ⟨10877633063960447010476045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29007021503894525361269453 10877633063960447010476045)
                    ·
                      refine ⟨4079112398985167628928517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10877633063960447010476045 4079112398985167628928517)
                      ·
                        rfl

theorem cell23_7944043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 3, 3, 3].length) (baseStart_7944043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7944043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7944043 prefixEnd_7944043 := by exact prefixLift 7944043
  have htrace : WordTrace (prefixWord ++ tailWord_7944043) baseStart_7944043 baseEnd_7944043 := by
    simpa [prefixWord, tailWord_7944043, baseEnd_7944043] using wordTrace_append hprefix tailTrace_7944043
  have hstable : (prefixWord ++ tailWord_7944043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7944043).length < 2 ^ (prefixWord ++ tailWord_7944043).sum := by decide
  have hdescent : baseEnd_7944043 < baseStart_7944043 := by decide
  rcases family_descends (prefixWord ++ tailWord_7944043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7944071 : List Nat := [1, 1, 4, 2, 5, 1, 2, 1, 2, 4]
def baseStart_7944071 : Nat := 118140960795 + 7944071 * 2 ^ 59
def prefixEnd_7944071 : Nat := 4983230072969 + 3 ^ 40 * 7944071 * 2
def baseEnd_7944071 : Nat := 1359708925481164506459463

theorem tailTrace_7944071 : CollatzResearch.WordTrace tailWord_7944071 prefixEnd_7944071 1359708925481164506459463 := by
  unfold tailWord_7944071
  simp only [CollatzResearch.WordTrace]
  refine ⟨289744072802994981156376067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193162715201996654104250711 289744072802994981156376067)
  ·
    refine ⟨434616109204492471734564101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289744072802994981156376067 434616109204492471734564101)
    ·
      refine ⟨81490520475842338450230769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 434616109204492471734564101 81490520475842338450230769)
      ·
        refine ⟨61117890356881753837673077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81490520475842338450230769 61117890356881753837673077)
        ·
          refine ⟨5729802220957664422281851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 61117890356881753837673077 5729802220957664422281851)
          ·
            refine ⟨8594703331436496633422777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5729802220957664422281851 8594703331436496633422777)
            ·
              refine ⟨6446027498577372475067083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8594703331436496633422777 6446027498577372475067083)
              ·
                refine ⟨9669041247866058712600625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6446027498577372475067083 9669041247866058712600625)
                ·
                  refine ⟨7251780935899544034450469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9669041247866058712600625 7251780935899544034450469)
                  ·
                    refine ⟨1359708925481164506459463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7251780935899544034450469 1359708925481164506459463)
                    ·
                      rfl

theorem cell23_7944071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 2, 1, 2, 4].length) (baseStart_7944071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7944071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7944071 prefixEnd_7944071 := by exact prefixLift 7944071
  have htrace : WordTrace (prefixWord ++ tailWord_7944071) baseStart_7944071 baseEnd_7944071 := by
    simpa [prefixWord, tailWord_7944071, baseEnd_7944071] using wordTrace_append hprefix tailTrace_7944071
  have hstable : (prefixWord ++ tailWord_7944071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7944071).length < 2 ^ (prefixWord ++ tailWord_7944071).sum := by decide
  have hdescent : baseEnd_7944071 < baseStart_7944071 := by decide
  rcases family_descends (prefixWord ++ tailWord_7944071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7944087 : List Nat := [1, 1, 3, 3, 1, 4, 1, 1, 3, 3, 2]
def baseStart_7944087 : Nat := 118140960795 + 7944087 * 2 ^ 59
def prefixEnd_7944087 : Nat := 4983230072969 + 3 ^ 40 * 7944087 * 2
def baseEnd_7944087 : Nat := 4079134992133965456778315

theorem tailTrace_7944087 : CollatzResearch.WordTrace tailWord_7944087 prefixEnd_7944087 4079134992133965456778315 := by
  unfold tailWord_7944087
  simp only [CollatzResearch.WordTrace]
  refine ⟨289744656370937015888958515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193163104247291343925972343 289744656370937015888958515)
  ·
    refine ⟨434616984556405523833437773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289744656370937015888958515 434616984556405523833437773)
    ·
      refine ⟨162981369208652071437539165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 434616984556405523833437773 162981369208652071437539165)
      ·
        refine ⟨61118013453244526789077187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162981369208652071437539165 61118013453244526789077187)
        ·
          refine ⟨91677020179866790183615781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61118013453244526789077187 91677020179866790183615781)
          ·
            refine ⟨17189441283725023159427959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 91677020179866790183615781 17189441283725023159427959)
            ·
              refine ⟨25784161925587534739141939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17189441283725023159427959 25784161925587534739141939)
              ·
                refine ⟨38676242888381302108712909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25784161925587534739141939 38676242888381302108712909)
                ·
                  refine ⟨14503591083142988290767341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38676242888381302108712909 14503591083142988290767341)
                  ·
                    refine ⟨5438846656178620609037753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14503591083142988290767341 5438846656178620609037753)
                    ·
                      refine ⟨4079134992133965456778315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5438846656178620609037753 4079134992133965456778315)
                      ·
                        rfl

theorem cell23_7944087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 1, 3, 3, 2].length) (baseStart_7944087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7944087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7944087 prefixEnd_7944087 := by exact prefixLift 7944087
  have htrace : WordTrace (prefixWord ++ tailWord_7944087) baseStart_7944087 baseEnd_7944087 := by
    simpa [prefixWord, tailWord_7944087, baseEnd_7944087] using wordTrace_append hprefix tailTrace_7944087
  have hstable : (prefixWord ++ tailWord_7944087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7944087).length < 2 ^ (prefixWord ++ tailWord_7944087).sum := by decide
  have hdescent : baseEnd_7944087 < baseStart_7944087 := by decide
  rcases family_descends (prefixWord ++ tailWord_7944087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7944140 : List Nat := [2, 2, 1, 4, 1, 3, 1, 2, 7]
def baseStart_7944140 : Nat := 118140960795 + 7944140 * 2 ^ 59
def prefixEnd_7944140 : Nat := 4983230072969 + 3 ^ 40 * 7944140 * 2
def baseEnd_7944140 : Nat := 453240245178739305490619

theorem tailTrace_7944140 : CollatzResearch.WordTrace tailWord_7944140 prefixEnd_7944140 453240245178739305490619 := by
  unfold tailWord_7944140
  simp only [CollatzResearch.WordTrace]
  refine ⟨144873294719872502970318937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193164392959830003960425249 144873294719872502970318937)
  ·
    refine ⟨108654971039904377227739203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144873294719872502970318937 108654971039904377227739203)
    ·
      refine ⟨162982456559856565841608805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108654971039904377227739203 162982456559856565841608805)
      ·
        refine ⟨30559210604973106095301651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 162982456559856565841608805 30559210604973106095301651)
        ·
          refine ⟨45838815907459659142952477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30559210604973106095301651 45838815907459659142952477)
          ·
            refine ⟨17189555965297372178607179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45838815907459659142952477 17189555965297372178607179)
            ·
              refine ⟨25784333947946058267910769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17189555965297372178607179 25784333947946058267910769)
              ·
                refine ⟨19338250460959543700933077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25784333947946058267910769 19338250460959543700933077)
                ·
                  refine ⟨453240245178739305490619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19338250460959543700933077 453240245178739305490619)
                  ·
                    rfl

theorem cell23_7944140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 2, 7].length) (baseStart_7944140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7944140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7944140 prefixEnd_7944140 := by exact prefixLift 7944140
  have htrace : WordTrace (prefixWord ++ tailWord_7944140) baseStart_7944140 baseEnd_7944140 := by
    simpa [prefixWord, tailWord_7944140, baseEnd_7944140] using wordTrace_append hprefix tailTrace_7944140
  have hstable : (prefixWord ++ tailWord_7944140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7944140).length < 2 ^ (prefixWord ++ tailWord_7944140).sum := by decide
  have hdescent : baseEnd_7944140 < baseStart_7944140 := by decide
  rcases family_descends (prefixWord ++ tailWord_7944140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7944170 : List Nat := [3, 1, 3, 1, 2, 1, 2, 1, 4, 5]
def baseStart_7944170 : Nat := 118140960795 + 7944170 * 2 ^ 59
def prefixEnd_7944170 : Nat := 4983230072969 + 3 ^ 40 * 7944170 * 2
def baseEnd_7944170 : Nat := 1359725870342762877346811

theorem tailTrace_7944170 : CollatzResearch.WordTrace tailWord_7944170 prefixEnd_7944170 1359725870342762877346811 := by
  unfold tailWord_7944170
  simp only [CollatzResearch.WordTrace]
  refine ⟨72436920907409080266057491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193165122419757547376153309 72436920907409080266057491)
  ·
    refine ⟨108655381361113620399086237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72436920907409080266057491 108655381361113620399086237)
    ·
      refine ⟨40745768010417607649657339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108655381361113620399086237 40745768010417607649657339)
      ·
        refine ⟨61118652015626411474486009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40745768010417607649657339 61118652015626411474486009)
        ·
          refine ⟨45838989011719808605864507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61118652015626411474486009 45838989011719808605864507)
          ·
            refine ⟨68758483517579712908796761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45838989011719808605864507 68758483517579712908796761)
            ·
              refine ⟨51568862638184784681597571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68758483517579712908796761 51568862638184784681597571)
              ·
                refine ⟨77353293957277177022396357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51568862638184784681597571 77353293957277177022396357)
                ·
                  refine ⟨14503742616989470691699317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77353293957277177022396357 14503742616989470691699317)
                  ·
                    refine ⟨1359725870342762877346811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14503742616989470691699317 1359725870342762877346811)
                    ·
                      rfl

theorem cell23_7944170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 1, 4, 5].length) (baseStart_7944170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7944170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7944170 prefixEnd_7944170 := by exact prefixLift 7944170
  have htrace : WordTrace (prefixWord ++ tailWord_7944170) baseStart_7944170 baseEnd_7944170 := by
    simpa [prefixWord, tailWord_7944170, baseEnd_7944170] using wordTrace_append hprefix tailTrace_7944170
  have hstable : (prefixWord ++ tailWord_7944170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7944170).length < 2 ^ (prefixWord ++ tailWord_7944170).sum := by decide
  have hdescent : baseEnd_7944170 < baseStart_7944170 := by decide
  rcases family_descends (prefixWord ++ tailWord_7944170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7944227 : List Nat := [1, 1, 1, 4, 3, 1, 3, 2, 2, 2, 3]
def baseStart_7944227 : Nat := 118140960795 + 7944227 * 2 ^ 59
def prefixEnd_7944227 : Nat := 4983230072969 + 3 ^ 40 * 7944227 * 2
def baseEnd_7944227 : Nat := 4079206879425594909027671

theorem tailTrace_7944227 : CollatzResearch.WordTrace tailWord_7944227 prefixEnd_7944227 4079206879425594909027671 := by
  unfold tailWord_7944227
  simp only [CollatzResearch.WordTrace]
  refine ⟨289749762590429819799054935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193166508393619879866036623 289749762590429819799054935)
  ·
    refine ⟨434624643885644729698582403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289749762590429819799054935 434624643885644729698582403)
    ·
      refine ⟨651936965828467094547873605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 434624643885644729698582403 651936965828467094547873605)
      ·
        refine ⟨122238181092837580227726301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 651936965828467094547873605 122238181092837580227726301)
        ·
          refine ⟨45839317909814092585397363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122238181092837580227726301 45839317909814092585397363)
          ·
            refine ⟨68758976864721138878096045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45839317909814092585397363 68758976864721138878096045)
            ·
              refine ⟨25784616324270427079286017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68758976864721138878096045 25784616324270427079286017)
              ·
                refine ⟨19338462243202820309464513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25784616324270427079286017 19338462243202820309464513)
                ·
                  refine ⟨14503846682402115232098385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19338462243202820309464513 14503846682402115232098385)
                  ·
                    refine ⟨10877885011801586424073789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14503846682402115232098385 10877885011801586424073789)
                    ·
                      refine ⟨4079206879425594909027671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10877885011801586424073789 4079206879425594909027671)
                      ·
                        rfl

theorem cell23_7944227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 2, 2, 2, 3].length) (baseStart_7944227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7944227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7944227 prefixEnd_7944227 := by exact prefixLift 7944227
  have htrace : WordTrace (prefixWord ++ tailWord_7944227) baseStart_7944227 baseEnd_7944227 := by
    simpa [prefixWord, tailWord_7944227, baseEnd_7944227] using wordTrace_append hprefix tailTrace_7944227
  have hstable : (prefixWord ++ tailWord_7944227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7944227).length < 2 ^ (prefixWord ++ tailWord_7944227).sum := by decide
  have hdescent : baseEnd_7944227 < baseStart_7944227 := by decide
  rcases family_descends (prefixWord ++ tailWord_7944227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7944234 : List Nat := [3, 1, 4, 1, 2, 1, 3, 1, 3, 4]
def baseStart_7944234 : Nat := 118140960795 + 7944234 * 2 ^ 59
def prefixEnd_7944234 : Nat := 4983230072969 + 3 ^ 40 * 7944234 * 2
def baseEnd_7944234 : Nat := 1359736824596725460546713

theorem tailTrace_7944234 : CollatzResearch.WordTrace tailWord_7944234 prefixEnd_7944234 1359736824596725460546713 := by
  unfold tailWord_7944234
  simp only [CollatzResearch.WordTrace]
  refine ⟨72437504475351114998639939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193166678600936306663039837 72437504475351114998639939)
  ·
    refine ⟨108656256713026672497959909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72437504475351114998639939 108656256713026672497959909)
    ·
      refine ⟨20373048133692501093367483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108656256713026672497959909 20373048133692501093367483)
      ·
        refine ⟨30559572200538751640051225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20373048133692501093367483 30559572200538751640051225)
        ·
          refine ⟨22919679150404063730038419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30559572200538751640051225 22919679150404063730038419)
          ·
            refine ⟨34379518725606095595057629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22919679150404063730038419 34379518725606095595057629)
            ·
              refine ⟨12892319522102285848146611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34379518725606095595057629 12892319522102285848146611)
              ·
                refine ⟨19338479283153428772219917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12892319522102285848146611 19338479283153428772219917)
                ·
                  refine ⟨7251929731182535789582469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19338479283153428772219917 7251929731182535789582469)
                  ·
                    refine ⟨1359736824596725460546713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7251929731182535789582469 1359736824596725460546713)
                    ·
                      rfl

theorem cell23_7944234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 3, 1, 3, 4].length) (baseStart_7944234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7944234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7944234 prefixEnd_7944234 := by exact prefixLift 7944234
  have htrace : WordTrace (prefixWord ++ tailWord_7944234) baseStart_7944234 baseEnd_7944234 := by
    simpa [prefixWord, tailWord_7944234, baseEnd_7944234] using wordTrace_append hprefix tailTrace_7944234
  have hstable : (prefixWord ++ tailWord_7944234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7944234).length < 2 ^ (prefixWord ++ tailWord_7944234).sum := by decide
  have hdescent : baseEnd_7944234 < baseStart_7944234 := by decide
  rcases family_descends (prefixWord ++ tailWord_7944234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7944247 : List Nat := [1, 1, 3, 1, 2, 2, 6, 1, 6]
def baseStart_7944247 : Nat := 118140960795 + 7944247 * 2 ^ 59
def prefixEnd_7944247 : Nat := 4983230072969 + 3 ^ 40 * 7944247 * 2
def baseEnd_7944247 : Nat := 453246349893187203419731

theorem tailTrace_7944247 : CollatzResearch.WordTrace tailWord_7944247 prefixEnd_7944247 453246349893187203419731 := by
  unfold tailWord_7944247
  simp only [CollatzResearch.WordTrace]
  refine ⟨289750492050357363214782995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193166994700238242143188663 289750492050357363214782995)
  ·
    refine ⟨434625738075536044822174493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289750492050357363214782995 434625738075536044822174493)
    ·
      refine ⟨162984651778326016808315435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 434625738075536044822174493 162984651778326016808315435)
      ·
        refine ⟨244476977667489025212473153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162984651778326016808315435 244476977667489025212473153)
        ·
          refine ⟨183357733250616768909354865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 244476977667489025212473153 183357733250616768909354865)
          ·
            refine ⟨137518299937962576682016149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183357733250616768909354865 137518299937962576682016149)
            ·
              refine ⟨6446170309591995781969507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 137518299937962576682016149 6446170309591995781969507)
              ·
                refine ⟨9669255464387993672954261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6446170309591995781969507 9669255464387993672954261)
                ·
                  refine ⟨453246349893187203419731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9669255464387993672954261 453246349893187203419731)
                  ·
                    rfl

theorem cell23_7944247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 6, 1, 6].length) (baseStart_7944247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7944247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7944247 prefixEnd_7944247 := by exact prefixLift 7944247
  have htrace : WordTrace (prefixWord ++ tailWord_7944247) baseStart_7944247 baseEnd_7944247 := by
    simpa [prefixWord, tailWord_7944247, baseEnd_7944247] using wordTrace_append hprefix tailTrace_7944247
  have hstable : (prefixWord ++ tailWord_7944247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7944247).length < 2 ^ (prefixWord ++ tailWord_7944247).sum := by decide
  have hdescent : baseEnd_7944247 < baseStart_7944247 := by decide
  rcases family_descends (prefixWord ++ tailWord_7944247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7944267 : List Nat := [1, 1, 1, 1, 3, 1, 2, 2, 6, 3, 2]
def baseStart_7944267 : Nat := 118140960795 + 7944267 * 2 ^ 59
def prefixEnd_7944267 : Nat := 4983230072969 + 3 ^ 40 * 7944267 * 2
def baseEnd_7944267 : Nat := 4079227418651774752527487

theorem tailTrace_7944267 : CollatzResearch.WordTrace tailWord_7944267 prefixEnd_7944267 4079227418651774752527487 := by
  unfold tailWord_7944267
  simp only [CollatzResearch.WordTrace]
  refine ⟨289751221510284906630511055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193167481006856604420340703 289751221510284906630511055)
  ·
    refine ⟨434626832265427359945766583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289751221510284906630511055 434626832265427359945766583)
    ·
      refine ⟨651940248398141039918649875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 434626832265427359945766583 651940248398141039918649875)
      ·
        refine ⟨977910372597211559877974813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 651940248398141039918649875 977910372597211559877974813)
        ·
          refine ⟨366716389723954334954240555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 977910372597211559877974813 366716389723954334954240555)
          ·
            refine ⟨550074584585931502431360833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 366716389723954334954240555 550074584585931502431360833)
            ·
              refine ⟨412555938439448626823520625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 550074584585931502431360833 412555938439448626823520625)
              ·
                refine ⟨309416953829586470117640469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 412555938439448626823520625 309416953829586470117640469)
                ·
                  refine ⟨14503919710761865786764397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 309416953829586470117640469 14503919710761865786764397)
                  ·
                    refine ⟨5438969891535699670036649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14503919710761865786764397 5438969891535699670036649)
                    ·
                      refine ⟨4079227418651774752527487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5438969891535699670036649 4079227418651774752527487)
                      ·
                        rfl

theorem cell23_7944267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 2, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 2, 6, 3, 2].length) (baseStart_7944267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7944267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7944267 prefixEnd_7944267 := by exact prefixLift 7944267
  have htrace : WordTrace (prefixWord ++ tailWord_7944267) baseStart_7944267 baseEnd_7944267 := by
    simpa [prefixWord, tailWord_7944267, baseEnd_7944267] using wordTrace_append hprefix tailTrace_7944267
  have hstable : (prefixWord ++ tailWord_7944267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7944267).length < 2 ^ (prefixWord ++ tailWord_7944267).sum := by decide
  have hdescent : baseEnd_7944267 < baseStart_7944267 := by decide
  rcases family_descends (prefixWord ++ tailWord_7944267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7944285 : List Nat := [1, 4, 4, 1, 1, 3, 2, 2, 1, 4]
def baseStart_7944285 : Nat := 118140960795 + 7944285 * 2 ^ 59
def prefixEnd_7944285 : Nat := 4983230072969 + 3 ^ 40 * 7944285 * 2
def baseEnd_7944285 : Nat := 1359745553767851894034135

theorem tailTrace_7944285 : CollatzResearch.WordTrace tailWord_7944285 prefixEnd_7944285 1359745553767851894034135 := by
  unfold tailWord_7944285
  simp only [CollatzResearch.WordTrace]
  refine ⟨289751878024219695704666309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193167918682813130469777539 289751878024219695704666309)
  ·
    refine ⟨54328477129541192944624933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 289751878024219695704666309 54328477129541192944624933)
    ·
      refine ⟨10186589461788973677117175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54328477129541192944624933 10186589461788973677117175)
      ·
        refine ⟨15279884192683460515675763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10186589461788973677117175 15279884192683460515675763)
        ·
          refine ⟨22919826289025190773513645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15279884192683460515675763 22919826289025190773513645)
          ·
            refine ⟨8594934858384446540067617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22919826289025190773513645 8594934858384446540067617)
            ·
              refine ⟨6446201143788334905050713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8594934858384446540067617 6446201143788334905050713)
              ·
                refine ⟨4834650857841251178788035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6446201143788334905050713 4834650857841251178788035)
                ·
                  refine ⟨7251976286761876768182053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4834650857841251178788035 7251976286761876768182053)
                  ·
                    refine ⟨1359745553767851894034135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7251976286761876768182053 1359745553767851894034135)
                    ·
                      rfl

theorem cell23_7944285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 2, 2, 1, 4].length) (baseStart_7944285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7944285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7944285 prefixEnd_7944285 := by exact prefixLift 7944285
  have htrace : WordTrace (prefixWord ++ tailWord_7944285) baseStart_7944285 baseEnd_7944285 := by
    simpa [prefixWord, tailWord_7944285, baseEnd_7944285] using wordTrace_append hprefix tailTrace_7944285
  have hstable : (prefixWord ++ tailWord_7944285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7944285).length < 2 ^ (prefixWord ++ tailWord_7944285).sum := by decide
  have hdescent : baseEnd_7944285 < baseStart_7944285 := by decide
  rcases family_descends (prefixWord ++ tailWord_7944285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7944327 : List Nat := [1, 1, 4, 2, 1, 1, 4, 2, 1, 2, 4]
def baseStart_7944327 : Nat := 118140960795 + 7944327 * 2 ^ 59
def prefixEnd_7944327 : Nat := 4983230072969 + 3 ^ 40 * 7944327 * 2
def baseEnd_7944327 : Nat := 4079258227491044517777211

theorem tailTrace_7944327 : CollatzResearch.WordTrace tailWord_7944327 prefixEnd_7944327 4079258227491044517777211 := by
  unfold tailWord_7944327
  simp only [CollatzResearch.WordTrace]
  refine ⟨289753409890067536877695235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193168939926711691251796823 289753409890067536877695235)
  ·
    refine ⟨434630114835101305316542853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289753409890067536877695235 434630114835101305316542853)
    ·
      refine ⟨81493146531581494746851785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 434630114835101305316542853 81493146531581494746851785)
      ·
        refine ⟨61119859898686121060138839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81493146531581494746851785 61119859898686121060138839)
        ·
          refine ⟨91679789848029181590208259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61119859898686121060138839 91679789848029181590208259)
          ·
            refine ⟨137519684772043772385312389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91679789848029181590208259 137519684772043772385312389)
            ·
              refine ⟨25784940894758207322246073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 137519684772043772385312389 25784940894758207322246073)
              ·
                refine ⟨19338705671068655491684555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25784940894758207322246073 19338705671068655491684555)
                ·
                  refine ⟨29008058506602983237526833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19338705671068655491684555 29008058506602983237526833)
                  ·
                    refine ⟨21756043879952237428145125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29008058506602983237526833 21756043879952237428145125)
                    ·
                      refine ⟨4079258227491044517777211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21756043879952237428145125 4079258227491044517777211)
                      ·
                        rfl

theorem cell23_7944327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 2, 1, 2, 4].length) (baseStart_7944327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7944327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7944327 prefixEnd_7944327 := by exact prefixLift 7944327
  have htrace : WordTrace (prefixWord ++ tailWord_7944327) baseStart_7944327 baseEnd_7944327 := by
    simpa [prefixWord, tailWord_7944327, baseEnd_7944327] using wordTrace_append hprefix tailTrace_7944327
  have hstable : (prefixWord ++ tailWord_7944327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7944327).length < 2 ^ (prefixWord ++ tailWord_7944327).sum := by decide
  have hdescent : baseEnd_7944327 < baseStart_7944327 := by decide
  rcases family_descends (prefixWord ++ tailWord_7944327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7944348 : List Nat := [2, 2, 3, 2, 1, 1, 1, 6, 1, 2, 2]
def baseStart_7944348 : Nat := 118140960795 + 7944348 * 2 ^ 59
def prefixEnd_7944348 : Nat := 4983230072969 + 3 ^ 40 * 7944348 * 2
def baseEnd_7944348 : Nat := 4079269010584788935614615

theorem tailTrace_7944348 : CollatzResearch.WordTrace tailWord_7944348 prefixEnd_7944348 4079269010584788935614615 := by
  unfold tailWord_7944348
  simp only [CollatzResearch.WordTrace]
  refine ⟨144877087911495728732104849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193169450548660971642806465 144877087911495728732104849)
  ·
    refine ⟨108657815933621796549078637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144877087911495728732104849 108657815933621796549078637)
    ·
      refine ⟨40746680975108173705904489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108657815933621796549078637 40746680975108173705904489)
      ·
        refine ⟨30560010731331130279428367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40746680975108173705904489 30560010731331130279428367)
        ·
          refine ⟨45840016096996695419142551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30560010731331130279428367 45840016096996695419142551)
          ·
            refine ⟨68760024145495043128713827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45840016096996695419142551 68760024145495043128713827)
            ·
              refine ⟨103140036218242564693070741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68760024145495043128713827 103140036218242564693070741)
              ·
                refine ⟨4834689197730120219987691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 103140036218242564693070741 4834689197730120219987691)
                ·
                  refine ⟨7252033796595180329981537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4834689197730120219987691 7252033796595180329981537)
                  ·
                    refine ⟨5439025347446385247486153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7252033796595180329981537 5439025347446385247486153)
                    ·
                      refine ⟨4079269010584788935614615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5439025347446385247486153 4079269010584788935614615)
                      ·
                        rfl

theorem cell23_7944348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 6, 1, 2, 2].length) (baseStart_7944348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7944348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7944348 prefixEnd_7944348 := by exact prefixLift 7944348
  have htrace : WordTrace (prefixWord ++ tailWord_7944348) baseStart_7944348 baseEnd_7944348 := by
    simpa [prefixWord, tailWord_7944348, baseEnd_7944348] using wordTrace_append hprefix tailTrace_7944348
  have hstable : (prefixWord ++ tailWord_7944348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7944348).length < 2 ^ (prefixWord ++ tailWord_7944348).sum := by decide
  have hdescent : baseEnd_7944348 < baseStart_7944348 := by decide
  rcases family_descends (prefixWord ++ tailWord_7944348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7944382 : List Nat := [4, 2, 1, 1, 4, 2, 1, 3, 1, 2, 2]
def baseStart_7944382 : Nat := 118140960795 + 7944382 * 2 ^ 59
def prefixEnd_7944382 : Nat := 4983230072969 + 3 ^ 40 * 7944382 * 2
def baseEnd_7944382 : Nat := 4079286468927041802589459

theorem tailTrace_7944382 : CollatzResearch.WordTrace tailWord_7944382 prefixEnd_7944382 4079286468927041802589459 := by
  unfold tailWord_7944382
  simp only [CollatzResearch.WordTrace]
  refine ⟨36219426988108535158868425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 193170277269912187513964933 36219426988108535158868425)
  ·
    refine ⟨27164570241081401369151319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36219426988108535158868425 27164570241081401369151319)
    ·
      refine ⟨40746855361622102053726979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27164570241081401369151319 40746855361622102053726979)
      ·
        refine ⟨61120283042433153080590469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40746855361622102053726979 61120283042433153080590469)
        ·
          refine ⟨11460053070456216202610713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61120283042433153080590469 11460053070456216202610713)
          ·
            refine ⟨8595039802842162151958035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11460053070456216202610713 8595039802842162151958035)
            ·
              refine ⟨12892559704263243227937053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8595039802842162151958035 12892559704263243227937053)
              ·
                refine ⟨4834709889098716210476395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12892559704263243227937053 4834709889098716210476395)
                ·
                  refine ⟨7252064833648074315714593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4834709889098716210476395 7252064833648074315714593)
                  ·
                    refine ⟨5439048625236055736785945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7252064833648074315714593 5439048625236055736785945)
                    ·
                      refine ⟨4079286468927041802589459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5439048625236055736785945 4079286468927041802589459)
                      ·
                        rfl

theorem cell23_7944382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 1, 3, 1, 2, 2].length) (baseStart_7944382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7944382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7944382 prefixEnd_7944382 := by exact prefixLift 7944382
  have htrace : WordTrace (prefixWord ++ tailWord_7944382) baseStart_7944382 baseEnd_7944382 := by
    simpa [prefixWord, tailWord_7944382, baseEnd_7944382] using wordTrace_append hprefix tailTrace_7944382
  have hstable : (prefixWord ++ tailWord_7944382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7944382).length < 2 ^ (prefixWord ++ tailWord_7944382).sum := by decide
  have hdescent : baseEnd_7944382 < baseStart_7944382 := by decide
  rcases family_descends (prefixWord ++ tailWord_7944382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7944407 : List Nat := [1, 1, 3, 2, 1, 2, 1, 3, 2, 4, 3]
def baseStart_7944407 : Nat := 118140960795 + 7944407 * 2 ^ 59
def prefixEnd_7944407 : Nat := 4983230072969 + 3 ^ 40 * 7944407 * 2
def baseEnd_7944407 : Nat := 4079299305943404204776843

theorem tailTrace_7944407 : CollatzResearch.WordTrace tailWord_7944407 prefixEnd_7944407 4079299305943404204776843 := by
  unfold tailWord_7944407
  simp only [CollatzResearch.WordTrace]
  refine ⟨289756327729777710540607475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193170885153185140360404983 289756327729777710540607475)
  ·
    refine ⟨434634491594666565810911213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289756327729777710540607475 434634491594666565810911213)
    ·
      refine ⟨162987934347999962179091705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 434634491594666565810911213 162987934347999962179091705)
      ·
        refine ⟨122240950760999971634318779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162987934347999962179091705 122240950760999971634318779)
        ·
          refine ⟨183361426141499957451478169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122240950760999971634318779 183361426141499957451478169)
          ·
            refine ⟨137521069606124968088608627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183361426141499957451478169 137521069606124968088608627)
            ·
              refine ⟨206281604409187452132912941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137521069606124968088608627 206281604409187452132912941)
              ·
                refine ⟨77355601653445294549842353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 206281604409187452132912941 77355601653445294549842353)
                ·
                  refine ⟨58016701240083970912381765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77355601653445294549842353 58016701240083970912381765)
                  ·
                    refine ⟨10878131482515744546071581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58016701240083970912381765 10878131482515744546071581)
                    ·
                      refine ⟨4079299305943404204776843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10878131482515744546071581 4079299305943404204776843)
                      ·
                        rfl

theorem cell23_7944407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 3, 2, 4, 3].length) (baseStart_7944407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7944407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7944407 prefixEnd_7944407 := by exact prefixLift 7944407
  have htrace : WordTrace (prefixWord ++ tailWord_7944407) baseStart_7944407 baseEnd_7944407 := by
    simpa [prefixWord, tailWord_7944407, baseEnd_7944407] using wordTrace_append hprefix tailTrace_7944407
  have hstable : (prefixWord ++ tailWord_7944407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7944407).length < 2 ^ (prefixWord ++ tailWord_7944407).sum := by decide
  have hdescent : baseEnd_7944407 < baseStart_7944407 := by decide
  rcases family_descends (prefixWord ++ tailWord_7944407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7944417 : List Nat := [1, 2, 3, 1, 3, 1, 2, 1, 1, 4, 4]
def baseStart_7944417 : Nat := 118140960795 + 7944417 * 2 ^ 59
def prefixEnd_7944417 : Nat := 4983230072969 + 3 ^ 40 * 7944417 * 2
def baseEnd_7944417 : Nat := 4079304440749949165651797

theorem tailTrace_7944417 : CollatzResearch.WordTrace tailWord_7944417 prefixEnd_7944417 4079304440749949165651797 := by
  unfold tailWord_7944417
  simp only [CollatzResearch.WordTrace]
  refine ⟨289756692459741482248471505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193171128306494321498981003 289756692459741482248471505)
  ·
    refine ⟨217317519344806111686353629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289756692459741482248471505 217317519344806111686353629)
    ·
      refine ⟨81494069754302291882382611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 217317519344806111686353629 81494069754302291882382611)
      ·
        refine ⟨122241104631453437823573917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81494069754302291882382611 122241104631453437823573917)
        ·
          refine ⟨45840414236795039183840219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122241104631453437823573917 45840414236795039183840219)
          ·
            refine ⟨68760621355192558775760329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45840414236795039183840219 68760621355192558775760329)
            ·
              refine ⟨51570466016394419081820247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68760621355192558775760329 51570466016394419081820247)
              ·
                refine ⟨77355699024591628622730371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51570466016394419081820247 77355699024591628622730371)
                ·
                  refine ⟨116033548536887442934095557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77355699024591628622730371 116033548536887442934095557)
                  ·
                    refine ⟨21756290350666395550142917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 116033548536887442934095557 21756290350666395550142917)
                    ·
                      refine ⟨4079304440749949165651797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21756290350666395550142917 4079304440749949165651797)
                      ·
                        rfl

theorem cell23_7944417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 1, 1, 4, 4].length) (baseStart_7944417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7944417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7944417 prefixEnd_7944417 := by exact prefixLift 7944417
  have htrace : WordTrace (prefixWord ++ tailWord_7944417) baseStart_7944417 baseEnd_7944417 := by
    simpa [prefixWord, tailWord_7944417, baseEnd_7944417] using wordTrace_append hprefix tailTrace_7944417
  have hstable : (prefixWord ++ tailWord_7944417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7944417).length < 2 ^ (prefixWord ++ tailWord_7944417).sum := by decide
  have hdescent : baseEnd_7944417 < baseStart_7944417 := by decide
  rcases family_descends (prefixWord ++ tailWord_7944417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7944537 : List Nat := [1, 2, 1, 2, 2, 2, 1, 1, 3, 2, 6]
def baseStart_7944537 : Nat := 118140960795 + 7944537 * 2 ^ 59
def prefixEnd_7944537 : Nat := 4983230072969 + 3 ^ 40 * 7944537 * 2
def baseEnd_7944537 : Nat := 4079366058428488696151245

theorem tailTrace_7944537 : CollatzResearch.WordTrace tailWord_7944537 prefixEnd_7944537 4079366058428488696151245 := by
  unfold tailWord_7944537
  simp only [CollatzResearch.WordTrace]
  refine ⟨289761069219306742742839865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193174046146204495161893243 289761069219306742742839865)
  ·
    refine ⟨217320801914480057057129899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289761069219306742742839865 217320801914480057057129899)
    ·
      refine ⟨325981202871720085585694849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217320801914480057057129899 325981202871720085585694849)
      ·
        refine ⟨244485902153790064189271137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 325981202871720085585694849 244485902153790064189271137)
        ·
          refine ⟨183364426615342548141953353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 244485902153790064189271137 183364426615342548141953353)
          ·
            refine ⟨137523319961506911106465015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183364426615342548141953353 137523319961506911106465015)
            ·
              refine ⟨206284979942260366659697523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137523319961506911106465015 206284979942260366659697523)
              ·
                refine ⟨309427469913390549989546285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 206284979942260366659697523 309427469913390549989546285)
                ·
                  refine ⟨116035301217521456246079857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 309427469913390549989546285 116035301217521456246079857)
                  ·
                    refine ⟨87026475913141092184559893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 116035301217521456246079857 87026475913141092184559893)
                    ·
                      refine ⟨4079366058428488696151245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 87026475913141092184559893 4079366058428488696151245)
                      ·
                        rfl

theorem cell23_7944537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 3, 2, 6].length) (baseStart_7944537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7944537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7944537 prefixEnd_7944537 := by exact prefixLift 7944537
  have htrace : WordTrace (prefixWord ++ tailWord_7944537) baseStart_7944537 baseEnd_7944537 := by
    simpa [prefixWord, tailWord_7944537, baseEnd_7944537] using wordTrace_append hprefix tailTrace_7944537
  have hstable : (prefixWord ++ tailWord_7944537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7944537).length < 2 ^ (prefixWord ++ tailWord_7944537).sum := by decide
  have hdescent : baseEnd_7944537 < baseStart_7944537 := by decide
  rcases family_descends (prefixWord ++ tailWord_7944537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7944571 : List Nat := [1, 1, 1, 1, 1, 7, 1, 1, 4, 3, 2]
def baseStart_7944571 : Nat := 118140960795 + 7944571 * 2 ^ 59
def prefixEnd_7944571 : Nat := 4983230072969 + 3 ^ 40 * 7944571 * 2
def baseEnd_7944571 : Nat := 4079383516770741563126089

theorem tailTrace_7944571 : CollatzResearch.WordTrace tailWord_7944571 prefixEnd_7944571 4079383516770741563126089 := by
  unfold tailWord_7944571
  simp only [CollatzResearch.WordTrace]
  refine ⟨289762309301183566549577567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193174872867455711033051711 289762309301183566549577567)
  ·
    refine ⟨434643463951775349824366351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289762309301183566549577567 434643463951775349824366351)
    ·
      refine ⟨651965195927663024736549527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 434643463951775349824366351 651965195927663024736549527)
      ·
        refine ⟨977947793891494537104824291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 651965195927663024736549527 977947793891494537104824291)
        ·
          refine ⟨1466921690837241805657236437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 977947793891494537104824291 1466921690837241805657236437)
          ·
            refine ⟨34380977128997854820091479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 1466921690837241805657236437 34380977128997854820091479)
            ·
              refine ⟨51571465693496782230137219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34380977128997854820091479 51571465693496782230137219)
              ·
                refine ⟨77357198540245173345205829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51571465693496782230137219 77357198540245173345205829)
                ·
                  refine ⟨14504474726295970002226093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77357198540245173345205829 14504474726295970002226093)
                  ·
                    refine ⟨5439178022360988750834785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14504474726295970002226093 5439178022360988750834785)
                    ·
                      refine ⟨4079383516770741563126089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5439178022360988750834785 4079383516770741563126089)
                      ·
                        rfl

theorem cell23_7944571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 1, 4, 3, 2].length) (baseStart_7944571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7944571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7944571 prefixEnd_7944571 := by exact prefixLift 7944571
  have htrace : WordTrace (prefixWord ++ tailWord_7944571) baseStart_7944571 baseEnd_7944571 := by
    simpa [prefixWord, tailWord_7944571, baseEnd_7944571] using wordTrace_append hprefix tailTrace_7944571
  have hstable : (prefixWord ++ tailWord_7944571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7944571).length < 2 ^ (prefixWord ++ tailWord_7944571).sum := by decide
  have hdescent : baseEnd_7944571 < baseStart_7944571 := by decide
  rcases family_descends (prefixWord ++ tailWord_7944571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7944605 : List Nat := [1, 4, 2, 1, 4, 1, 2, 1, 2, 3, 2]
def baseStart_7944605 : Nat := 118140960795 + 7944605 * 2 ^ 59
def prefixEnd_7944605 : Nat := 4983230072969 + 3 ^ 40 * 7944605 * 2
def baseEnd_7944605 : Nat := 4079400975112994430100933

theorem tailTrace_7944605 : CollatzResearch.WordTrace tailWord_7944605 prefixEnd_7944605 4079400975112994430100933 := by
  unfold tailWord_7944605
  simp only [CollatzResearch.WordTrace]
  refine ⟨289763549383060390356315269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193175699588706926904210179 289763549383060390356315269)
  ·
    refine ⟨54330665509323823191809113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 289763549383060390356315269 54330665509323823191809113)
    ·
      refine ⟨40747999131992867393856835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54330665509323823191809113 40747999131992867393856835)
      ·
        refine ⟨61121998697989301090785253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40747999131992867393856835 61121998697989301090785253)
        ·
          refine ⟨11460374755872993954522235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61121998697989301090785253 11460374755872993954522235)
          ·
            refine ⟨17190562133809490931783353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11460374755872993954522235 17190562133809490931783353)
            ·
              refine ⟨12892921600357118198837515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17190562133809490931783353 12892921600357118198837515)
              ·
                refine ⟨19339382400535677298256273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12892921600357118198837515 19339382400535677298256273)
                ·
                  refine ⟨14504536800401757973692205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19339382400535677298256273 14504536800401757973692205)
                  ·
                    refine ⟨5439201300150659240134577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14504536800401757973692205 5439201300150659240134577)
                    ·
                      refine ⟨4079400975112994430100933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5439201300150659240134577 4079400975112994430100933)
                      ·
                        rfl

theorem cell23_7944605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 2, 1, 2, 3, 2].length) (baseStart_7944605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7944605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7944605 prefixEnd_7944605 := by exact prefixLift 7944605
  have htrace : WordTrace (prefixWord ++ tailWord_7944605) baseStart_7944605 baseEnd_7944605 := by
    simpa [prefixWord, tailWord_7944605, baseEnd_7944605] using wordTrace_append hprefix tailTrace_7944605
  have hstable : (prefixWord ++ tailWord_7944605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7944605).length < 2 ^ (prefixWord ++ tailWord_7944605).sum := by decide
  have hdescent : baseEnd_7944605 < baseStart_7944605 := by decide
  rcases family_descends (prefixWord ++ tailWord_7944605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7944629 : List Nat := [1, 3, 3, 2, 3, 2, 2, 2, 1, 1, 3]
def baseStart_7944629 : Nat := 118140960795 + 7944629 * 2 ^ 59
def prefixEnd_7944629 : Nat := 4983230072969 + 3 ^ 40 * 7944629 * 2
def baseEnd_7944629 : Nat := 4079413298648702336200823

theorem tailTrace_7944629 : CollatzResearch.WordTrace tailWord_7944629 prefixEnd_7944629 4079413298648702336200823 := by
  unfold tailWord_7944629
  simp only [CollatzResearch.WordTrace]
  refine ⟨289764424734973442455188941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193176283156648961636792627 289764424734973442455188941)
  ·
    refine ⟨108661659275615040920695853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 289764424734973442455188941 108661659275615040920695853)
    ·
      refine ⟨40748122228355640345260945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108661659275615040920695853 40748122228355640345260945)
      ·
        refine ⟨30561091671266730258945709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40748122228355640345260945 30561091671266730258945709)
        ·
          refine ⟨11460409376725023847104641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30561091671266730258945709 11460409376725023847104641)
          ·
            refine ⟨8595307032543767885328481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11460409376725023847104641 8595307032543767885328481)
            ·
              refine ⟨6446480274407825913996361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8595307032543767885328481 6446480274407825913996361)
              ·
                refine ⟨4834860205805869435497271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6446480274407825913996361 4834860205805869435497271)
                ·
                  refine ⟨7252290308708804153245907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4834860205805869435497271 7252290308708804153245907)
                  ·
                    refine ⟨10878435463063206229868861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7252290308708804153245907 10878435463063206229868861)
                    ·
                      refine ⟨4079413298648702336200823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10878435463063206229868861 4079413298648702336200823)
                      ·
                        rfl

theorem cell23_7944629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 2, 2, 1, 1, 3].length) (baseStart_7944629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7944629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7944629 prefixEnd_7944629 := by exact prefixLift 7944629
  have htrace : WordTrace (prefixWord ++ tailWord_7944629) baseStart_7944629 baseEnd_7944629 := by
    simpa [prefixWord, tailWord_7944629, baseEnd_7944629] using wordTrace_append hprefix tailTrace_7944629
  have hstable : (prefixWord ++ tailWord_7944629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7944629).length < 2 ^ (prefixWord ++ tailWord_7944629).sum := by decide
  have hdescent : baseEnd_7944629 < baseStart_7944629 := by decide
  rcases family_descends (prefixWord ++ tailWord_7944629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7944651 : List Nat := [1, 1, 1, 1, 3, 3, 1, 2, 6, 1, 3]
def baseStart_7944651 : Nat := 118140960795 + 7944651 * 2 ^ 59
def prefixEnd_7944651 : Nat := 4983230072969 + 3 ^ 40 * 7944651 * 2
def baseEnd_7944651 : Nat := 4079424595223101250125721

theorem tailTrace_7944651 : CollatzResearch.WordTrace tailWord_7944651 prefixEnd_7944651 4079424595223101250125721 := by
  unfold tailWord_7944651
  simp only [CollatzResearch.WordTrace]
  refine ⟨289765227140893740212489807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193176818093929160141659871 289765227140893740212489807)
  ·
    refine ⟨434647840711340610318734711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289765227140893740212489807 434647840711340610318734711)
    ·
      refine ⟨651971761067010915478102067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 434647840711340610318734711 651971761067010915478102067)
      ·
        refine ⟨977957641600516373217153101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 651971761067010915478102067 977957641600516373217153101)
        ·
          refine ⟨366734115600193639956432413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 977957641600516373217153101 366734115600193639956432413)
          ·
            refine ⟨137525293350072614983662155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 366734115600193639956432413 137525293350072614983662155)
            ·
              refine ⟨206287940025108922475493233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137525293350072614983662155 206287940025108922475493233)
              ·
                refine ⟨154715955018831691856619925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 206287940025108922475493233 154715955018831691856619925)
                ·
                  refine ⟨7252310391507735555779059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 154715955018831691856619925 7252310391507735555779059)
                  ·
                    refine ⟨10878465587261603333668589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7252310391507735555779059 10878465587261603333668589)
                    ·
                      refine ⟨4079424595223101250125721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10878465587261603333668589 4079424595223101250125721)
                      ·
                        rfl

theorem cell23_7944651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 2, 6, 1, 3].length) (baseStart_7944651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7944651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7944651 prefixEnd_7944651 := by exact prefixLift 7944651
  have htrace : WordTrace (prefixWord ++ tailWord_7944651) baseStart_7944651 baseEnd_7944651 := by
    simpa [prefixWord, tailWord_7944651, baseEnd_7944651] using wordTrace_append hprefix tailTrace_7944651
  have hstable : (prefixWord ++ tailWord_7944651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7944651).length < 2 ^ (prefixWord ++ tailWord_7944651).sum := by decide
  have hdescent : baseEnd_7944651 < baseStart_7944651 := by decide
  rcases family_descends (prefixWord ++ tailWord_7944651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7944654 : List Nat := [4, 1, 1, 1, 2, 1, 1, 1, 4, 7]
def baseStart_7944654 : Nat := 118140960795 + 7944654 * 2 ^ 59
def prefixEnd_7944654 : Nat := 4983230072969 + 3 ^ 40 * 7944654 * 2
def baseEnd_7944654 : Nat := 1359808711888354912796069

theorem tailTrace_7944654 : CollatzResearch.WordTrace tailWord_7944654 prefixEnd_7944654 1359808711888354912796069 := by
  unfold tailWord_7944654
  simp only [CollatzResearch.WordTrace]
  refine ⟨36220667069985358965606127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 193176891039921914483232677 36220667069985358965606127)
  ·
    refine ⟨54331000604978038448409191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36220667069985358965606127 54331000604978038448409191)
    ·
      refine ⟨81496500907467057672613787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54331000604978038448409191 81496500907467057672613787)
      ·
        refine ⟨122244751361200586508920681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81496500907467057672613787 122244751361200586508920681)
        ·
          refine ⟨91683563520900439881690511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122244751361200586508920681 91683563520900439881690511)
          ·
            refine ⟨137525345281350659822535767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91683563520900439881690511 137525345281350659822535767)
            ·
              refine ⟨206288017922025989733803651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137525345281350659822535767 206288017922025989733803651)
              ·
                refine ⟨309432026883038984600705477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 206288017922025989733803651 309432026883038984600705477)
                ·
                  refine ⟨58018505040569809612632277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 309432026883038984600705477 58018505040569809612632277)
                  ·
                    refine ⟨1359808711888354912796069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58018505040569809612632277 1359808711888354912796069)
                    ·
                      rfl

theorem cell23_7944654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 1, 4, 7].length) (baseStart_7944654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7944654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7944654 prefixEnd_7944654 := by exact prefixLift 7944654
  have htrace : WordTrace (prefixWord ++ tailWord_7944654) baseStart_7944654 baseEnd_7944654 := by
    simpa [prefixWord, tailWord_7944654, baseEnd_7944654] using wordTrace_append hprefix tailTrace_7944654
  have hstable : (prefixWord ++ tailWord_7944654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7944654).length < 2 ^ (prefixWord ++ tailWord_7944654).sum := by decide
  have hdescent : baseEnd_7944654 < baseStart_7944654 := by decide
  rcases family_descends (prefixWord ++ tailWord_7944654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7944664 : List Nat := [2, 1, 2, 2, 2, 1, 1, 3, 2, 2, 5]
def baseStart_7944664 : Nat := 118140960795 + 7944664 * 2 ^ 59
def prefixEnd_7944664 : Nat := 4983230072969 + 3 ^ 40 * 7944664 * 2
def baseEnd_7944664 : Nat := 4079431270471609699263161

theorem tailTrace_7944664 : CollatzResearch.WordTrace tailWord_7944664 prefixEnd_7944664 4079431270471609699263161 := by
  unfold tailWord_7944664
  simp only [CollatzResearch.WordTrace]
  refine ⟨144882850644923321716356523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193177134193231095621808697 144882850644923321716356523)
  ·
    refine ⟨217324275967384982574534785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144882850644923321716356523 217324275967384982574534785)
    ·
      refine ⟨162993206975538736930901089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217324275967384982574534785 162993206975538736930901089)
      ·
        refine ⟨122244905231654052698175817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162993206975538736930901089 122244905231654052698175817)
        ·
          refine ⟨91683678923740539523631863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122244905231654052698175817 91683678923740539523631863)
          ·
            refine ⟨137525518385610809285447795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91683678923740539523631863 137525518385610809285447795)
            ·
              refine ⟨206288277578416213928171693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137525518385610809285447795 206288277578416213928171693)
              ·
                refine ⟨77358104091906080223064385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 206288277578416213928171693 77358104091906080223064385)
                ·
                  refine ⟨58018578068929560167298289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77358104091906080223064385 58018578068929560167298289)
                  ·
                    refine ⟨43513933551697170125473717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58018578068929560167298289 43513933551697170125473717)
                    ·
                      refine ⟨4079431270471609699263161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43513933551697170125473717 4079431270471609699263161)
                      ·
                        rfl

theorem cell23_7944664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 3, 2, 2, 5].length) (baseStart_7944664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7944664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7944664 prefixEnd_7944664 := by exact prefixLift 7944664
  have htrace : WordTrace (prefixWord ++ tailWord_7944664) baseStart_7944664 baseEnd_7944664 := by
    simpa [prefixWord, tailWord_7944664, baseEnd_7944664] using wordTrace_append hprefix tailTrace_7944664
  have hstable : (prefixWord ++ tailWord_7944664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7944664).length < 2 ^ (prefixWord ++ tailWord_7944664).sum := by decide
  have hdescent : baseEnd_7944664 < baseStart_7944664 := by decide
  rcases family_descends (prefixWord ++ tailWord_7944664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7944684 : List Nat := [2, 2, 1, 1, 2, 1, 3, 1, 4, 6]
def baseStart_7944684 : Nat := 118140960795 + 7944684 * 2 ^ 59
def prefixEnd_7944684 : Nat := 4983230072969 + 3 ^ 40 * 7944684 * 2
def baseEnd_7944684 : Nat := 1359813846694899873671023

theorem tailTrace_7944684 : CollatzResearch.WordTrace tailWord_7944684 prefixEnd_7944684 1359813846694899873671023 := by
  unfold tailWord_7944684
  simp only [CollatzResearch.WordTrace]
  refine ⟨144883215374887093424220553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193177620499849457898960737 144883215374887093424220553)
  ·
    refine ⟨108662411531165320068165415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144883215374887093424220553 108662411531165320068165415)
    ·
      refine ⟨162993617296747980102248123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108662411531165320068165415 162993617296747980102248123)
      ·
        refine ⟨244490425945121970153372185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162993617296747980102248123 244490425945121970153372185)
        ·
          refine ⟨183367819458841477615029139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 244490425945121970153372185 183367819458841477615029139)
          ·
            refine ⟨275051729188262216422543709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183367819458841477615029139 275051729188262216422543709)
            ·
              refine ⟨103144398445598331158453891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 275051729188262216422543709 103144398445598331158453891)
              ·
                refine ⟨154716597668397496737680837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103144398445598331158453891 154716597668397496737680837)
                ·
                  refine ⟨29009362062824530638315157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 154716597668397496737680837 29009362062824530638315157)
                  ·
                    refine ⟨1359813846694899873671023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29009362062824530638315157 1359813846694899873671023)
                    ·
                      rfl

theorem cell23_7944684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 6].length) (baseStart_7944684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7944684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7944684 prefixEnd_7944684 := by exact prefixLift 7944684
  have htrace : WordTrace (prefixWord ++ tailWord_7944684) baseStart_7944684 baseEnd_7944684 := by
    simpa [prefixWord, tailWord_7944684, baseEnd_7944684] using wordTrace_append hprefix tailTrace_7944684
  have hstable : (prefixWord ++ tailWord_7944684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7944684).length < 2 ^ (prefixWord ++ tailWord_7944684).sum := by decide
  have hdescent : baseEnd_7944684 < baseStart_7944684 := by decide
  rcases family_descends (prefixWord ++ tailWord_7944684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7944685 : List Nat := [1, 5, 1, 3, 1, 2, 1, 1, 4, 1, 3]
def baseStart_7944685 : Nat := 118140960795 + 7944685 * 2 ^ 59
def prefixEnd_7944685 : Nat := 4983230072969 + 3 ^ 40 * 7944685 * 2
def baseEnd_7944685 : Nat := 4079442053565354117100565

theorem tailTrace_7944685 : CollatzResearch.WordTrace tailWord_7944685 prefixEnd_7944685 4079442053565354117100565 := by
  unfold tailWord_7944685
  simp only [CollatzResearch.WordTrace]
  refine ⟨289766467222770564019227509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193177644815180376012818339 289766467222770564019227509)
  ·
    refine ⟨27165606302134740376802579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 289766467222770564019227509 27165606302134740376802579)
    ·
      refine ⟨40748409453202110565203869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27165606302134740376802579 40748409453202110565203869)
      ·
        refine ⟨15280653544950791461951451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40748409453202110565203869 15280653544950791461951451)
        ·
          refine ⟨22920980317426187192927177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15280653544950791461951451 22920980317426187192927177)
          ·
            refine ⟨17190735238069640394695383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22920980317426187192927177 17190735238069640394695383)
            ·
              refine ⟨25786102857104460592043075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17190735238069640394695383 25786102857104460592043075)
              ·
                refine ⟨38679154285656690888064613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25786102857104460592043075 38679154285656690888064613)
                ·
                  refine ⟨7252341428560629541512115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38679154285656690888064613 7252341428560629541512115)
                  ·
                    refine ⟨10878512142840944312268173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7252341428560629541512115 10878512142840944312268173)
                    ·
                      refine ⟨4079442053565354117100565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10878512142840944312268173 4079442053565354117100565)
                      ·
                        rfl

theorem cell23_7944685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 1, 4, 1, 3].length) (baseStart_7944685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7944685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7944685 prefixEnd_7944685 := by exact prefixLift 7944685
  have htrace : WordTrace (prefixWord ++ tailWord_7944685) baseStart_7944685 baseEnd_7944685 := by
    simpa [prefixWord, tailWord_7944685, baseEnd_7944685] using wordTrace_append hprefix tailTrace_7944685
  have hstable : (prefixWord ++ tailWord_7944685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7944685).length < 2 ^ (prefixWord ++ tailWord_7944685).sum := by decide
  have hdescent : baseEnd_7944685 < baseStart_7944685 := by decide
  rcases family_descends (prefixWord ++ tailWord_7944685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7944741 : List Nat := [1, 3, 1, 2, 2, 1, 2, 1, 4, 3, 3]
def baseStart_7944741 : Nat := 118140960795 + 7944741 * 2 ^ 59
def prefixEnd_7944741 : Nat := 4983230072969 + 3 ^ 40 * 7944741 * 2
def baseEnd_7944741 : Nat := 4079470808482005898000307

theorem tailTrace_7944741 : CollatzResearch.WordTrace tailWord_7944741 prefixEnd_7944741 4079470808482005898000307 := by
  unfold tailWord_7944741
  simp only [CollatzResearch.WordTrace]
  refine ⟨289768509710567685583266077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193179006473711790388844051 289768509710567685583266077)
  ·
    refine ⟨108663191141462882093724779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 289768509710567685583266077 108663191141462882093724779)
    ·
      refine ⟨162994786712194323140587169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108663191141462882093724779 162994786712194323140587169)
      ·
        refine ⟨122246090034145742355440377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162994786712194323140587169 122246090034145742355440377)
        ·
          refine ⟨91684567525609306766580283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122246090034145742355440377 91684567525609306766580283)
          ·
            refine ⟨137526851288413960149870425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91684567525609306766580283 137526851288413960149870425)
            ·
              refine ⟨103145138466310470112402819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137526851288413960149870425 103145138466310470112402819)
              ·
                refine ⟨154717707699465705168604229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103145138466310470112402819 154717707699465705168604229)
                ·
                  refine ⟨29009570193649819719113293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 154717707699465705168604229 29009570193649819719113293)
                  ·
                    refine ⟨10878588822618682394667485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29009570193649819719113293 10878588822618682394667485)
                    ·
                      refine ⟨4079470808482005898000307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10878588822618682394667485 4079470808482005898000307)
                      ·
                        rfl

theorem cell23_7944741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 1, 4, 3, 3].length) (baseStart_7944741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7944741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7944741 prefixEnd_7944741 := by exact prefixLift 7944741
  have htrace : WordTrace (prefixWord ++ tailWord_7944741) baseStart_7944741 baseEnd_7944741 := by
    simpa [prefixWord, tailWord_7944741, baseEnd_7944741] using wordTrace_append hprefix tailTrace_7944741
  have hstable : (prefixWord ++ tailWord_7944741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7944741).length < 2 ^ (prefixWord ++ tailWord_7944741).sum := by decide
  have hdescent : baseEnd_7944741 < baseStart_7944741 := by decide
  rcases family_descends (prefixWord ++ tailWord_7944741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7944761 : List Nat := [1, 2, 1, 5, 1, 1, 1, 2, 4, 5]
def baseStart_7944761 : Nat := 118140960795 + 7944761 * 2 ^ 59
def prefixEnd_7944761 : Nat := 4983230072969 + 3 ^ 40 * 7944761 * 2
def baseEnd_7944761 : Nat := 1359827026031698606583405

theorem tailTrace_7944761 : CollatzResearch.WordTrace tailWord_7944761 prefixEnd_7944761 1359827026031698606583405 := by
  unfold tailWord_7944761
  simp only [CollatzResearch.WordTrace]
  refine ⟨289769239170495228998994137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193179492780330152665996091 289769239170495228998994137)
  ·
    refine ⟨217326929377871421749245603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289769239170495228998994137 217326929377871421749245603)
    ·
      refine ⟨325990394066807132623868405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217326929377871421749245603 325990394066807132623868405)
      ·
        refine ⟨30561599443763168683487663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 325990394066807132623868405 30561599443763168683487663)
        ·
          refine ⟨45842399165644753025231495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30561599443763168683487663 45842399165644753025231495)
          ·
            refine ⟨68763598748467129537847243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45842399165644753025231495 68763598748467129537847243)
            ·
              refine ⟨103145398122700694306770865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68763598748467129537847243 103145398122700694306770865)
              ·
                refine ⟨77359048592025520730078149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103145398122700694306770865 77359048592025520730078149)
                ·
                  refine ⟨14504821611004785136889653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77359048592025520730078149 14504821611004785136889653)
                  ·
                    refine ⟨1359827026031698606583405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14504821611004785136889653 1359827026031698606583405)
                    ·
                      rfl

theorem cell23_7944761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 2, 4, 5].length) (baseStart_7944761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7944761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7944761 prefixEnd_7944761 := by exact prefixLift 7944761
  have htrace : WordTrace (prefixWord ++ tailWord_7944761) baseStart_7944761 baseEnd_7944761 := by
    simpa [prefixWord, tailWord_7944761, baseEnd_7944761] using wordTrace_append hprefix tailTrace_7944761
  have hstable : (prefixWord ++ tailWord_7944761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7944761).length < 2 ^ (prefixWord ++ tailWord_7944761).sum := by decide
  have hdescent : baseEnd_7944761 < baseStart_7944761 := by decide
  rcases family_descends (prefixWord ++ tailWord_7944761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7944778 : List Nat := [3, 1, 2, 1, 1, 5, 2, 1, 2, 5]
def baseStart_7944778 : Nat := 118140960795 + 7944778 * 2 ^ 59
def prefixEnd_7944778 : Nat := 4983230072969 + 3 ^ 40 * 7944778 * 2
def baseEnd_7944778 : Nat := 1359829935755407417745879

theorem tailTrace_7944778 : CollatzResearch.WordTrace tailWord_7944778 prefixEnd_7944778 1359829935755407417745879 := by
  unfold tailWord_7944778
  simp only [CollatzResearch.WordTrace]
  refine ⟨72442464802858410225590747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193179906140955760601575325 72442464802858410225590747)
  ·
    refine ⟨108663697204287615338386121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72442464802858410225590747 108663697204287615338386121)
    ·
      refine ⟨81497772903215711503789591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108663697204287615338386121 81497772903215711503789591)
      ·
        refine ⟨122246659354823567255684387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81497772903215711503789591 122246659354823567255684387)
        ·
          refine ⟨183369989032235350883526581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122246659354823567255684387 183369989032235350883526581)
          ·
            refine ⟨17190936471772064145330617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 183369989032235350883526581 17190936471772064145330617)
            ·
              refine ⟨12893202353829048108997963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17190936471772064145330617 12893202353829048108997963)
              ·
                refine ⟨19339803530743572163496945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12893202353829048108997963 19339803530743572163496945)
                ·
                  refine ⟨14504852648057679122622709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19339803530743572163496945 14504852648057679122622709)
                  ·
                    refine ⟨1359829935755407417745879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14504852648057679122622709 1359829935755407417745879)
                    ·
                      rfl

theorem cell23_7944778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 2, 1, 2, 5].length) (baseStart_7944778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7944778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7944778 prefixEnd_7944778 := by exact prefixLift 7944778
  have htrace : WordTrace (prefixWord ++ tailWord_7944778) baseStart_7944778 baseEnd_7944778 := by
    simpa [prefixWord, tailWord_7944778, baseEnd_7944778] using wordTrace_append hprefix tailTrace_7944778
  have hstable : (prefixWord ++ tailWord_7944778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7944778).length < 2 ^ (prefixWord ++ tailWord_7944778).sum := by decide
  have hdescent : baseEnd_7944778 < baseStart_7944778 := by decide
  rcases family_descends (prefixWord ++ tailWord_7944778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7944831 : List Nat := [1, 1, 2, 2, 1, 1, 1, 3, 1, 7, 3]
def baseStart_7944831 : Nat := 118140960795 + 7944831 * 2 ^ 59
def prefixEnd_7944831 : Nat := 4983230072969 + 3 ^ 40 * 7944831 * 2
def baseEnd_7944831 : Nat := 4079517021740910545874893

theorem tailTrace_7944831 : CollatzResearch.WordTrace tailWord_7944831 prefixEnd_7944831 4079517021740910545874893 := by
  unfold tailWord_7944831
  simp only [CollatzResearch.WordTrace]
  refine ⟨289771792280241630954042347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193181194853494420636028231 289771792280241630954042347)
  ·
    refine ⟨434657688420362446431063521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289771792280241630954042347 434657688420362446431063521)
    ·
      refine ⟨325993266315271834823297641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 434657688420362446431063521 325993266315271834823297641)
      ·
        refine ⟨244494949736453876117473231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 325993266315271834823297641 244494949736453876117473231)
        ·
          refine ⟨366742424604680814176209847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244494949736453876117473231 366742424604680814176209847)
          ·
            refine ⟨550113636907021221264314771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 366742424604680814176209847 550113636907021221264314771)
            ·
              refine ⟨825170455360531831896472157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 550113636907021221264314771 825170455360531831896472157)
              ·
                refine ⟨309438920760199436961177059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 825170455360531831896472157 309438920760199436961177059)
                ·
                  refine ⟨464158381140299155441765589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 309438920760199436961177059 464158381140299155441765589)
                  ·
                    refine ⟨10878712057975761455666381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 464158381140299155441765589 10878712057975761455666381)
                    ·
                      refine ⟨4079517021740910545874893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10878712057975761455666381 4079517021740910545874893)
                      ·
                        rfl

theorem cell23_7944831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 3, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 3, 1, 7, 3].length) (baseStart_7944831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7944831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7944831 prefixEnd_7944831 := by exact prefixLift 7944831
  have htrace : WordTrace (prefixWord ++ tailWord_7944831) baseStart_7944831 baseEnd_7944831 := by
    simpa [prefixWord, tailWord_7944831, baseEnd_7944831] using wordTrace_append hprefix tailTrace_7944831
  have hstable : (prefixWord ++ tailWord_7944831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7944831).length < 2 ^ (prefixWord ++ tailWord_7944831).sum := by decide
  have hdescent : baseEnd_7944831 < baseStart_7944831 := by decide
  rcases family_descends (prefixWord ++ tailWord_7944831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7944885 : List Nat := [1, 3, 3, 3, 1, 1, 1, 4, 1, 5]
def baseStart_7944885 : Nat := 118140960795 + 7944885 * 2 ^ 59
def prefixEnd_7944885 : Nat := 4983230072969 + 3 ^ 40 * 7944885 * 2
def baseEnd_7944885 : Nat := 1359848249898751111533215

theorem tailTrace_7944885 : CollatzResearch.WordTrace tailWord_7944885 prefixEnd_7944885 1359848249898751111533215 := by
  unfold tailWord_7944885
  simp only [CollatzResearch.WordTrace]
  refine ⟨289773761822045998176508109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193182507881363998784338739 289773761822045998176508109)
  ·
    refine ⟨108665160683267249316190541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 289773761822045998176508109 108665160683267249316190541)
    ·
      refine ⟨40749435256225218493571453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108665160683267249316190541 40749435256225218493571453)
      ·
        refine ⟨15281038221084456935089295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40749435256225218493571453 15281038221084456935089295)
        ·
          refine ⟨22921557331626685402633943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15281038221084456935089295 22921557331626685402633943)
          ·
            refine ⟨34382335997440028103950915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22921557331626685402633943 34382335997440028103950915)
            ·
              refine ⟨51573503996160042155926373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34382335997440028103950915 51573503996160042155926373)
              ·
                refine ⟨9670031999280007904236195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51573503996160042155926373 9670031999280007904236195)
                ·
                  refine ⟨14505047998920011856354293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9670031999280007904236195 14505047998920011856354293)
                  ·
                    refine ⟨1359848249898751111533215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14505047998920011856354293 1359848249898751111533215)
                    ·
                      rfl

theorem cell23_7944885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 4, 1, 5].length) (baseStart_7944885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7944885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7944885 prefixEnd_7944885 := by exact prefixLift 7944885
  have htrace : WordTrace (prefixWord ++ tailWord_7944885) baseStart_7944885 baseEnd_7944885 := by
    simpa [prefixWord, tailWord_7944885, baseEnd_7944885] using wordTrace_append hprefix tailTrace_7944885
  have hstable : (prefixWord ++ tailWord_7944885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7944885).length < 2 ^ (prefixWord ++ tailWord_7944885).sum := by decide
  have hdescent : baseEnd_7944885 < baseStart_7944885 := by decide
  rcases family_descends (prefixWord ++ tailWord_7944885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7944901 : List Nat := [1, 3, 1, 1, 1, 1, 2, 1, 5, 1, 6]
def baseStart_7944901 : Nat := 118140960795 + 7944901 * 2 ^ 59
def prefixEnd_7944901 : Nat := 4983230072969 + 3 ^ 40 * 7944901 * 2
def baseEnd_7944901 : Nat := 4079552965386725271999571

theorem tailTrace_7944901 : CollatzResearch.WordTrace tailWord_7944901 prefixEnd_7944901 4079552965386725271999571 := by
  unfold tailWord_7944901
  simp only [CollatzResearch.WordTrace]
  refine ⟨289774345389988032909090557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193182896926658688606060371 289774345389988032909090557)
  ·
    refine ⟨108665379521245512340908959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 289774345389988032909090557 108665379521245512340908959)
    ·
      refine ⟨162998069281868268511363439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108665379521245512340908959 162998069281868268511363439)
      ·
        refine ⟨244497103922802402767045159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162998069281868268511363439 244497103922802402767045159)
        ·
          refine ⟨366745655884203604150567739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244497103922802402767045159 366745655884203604150567739)
          ·
            refine ⟨550118483826305406225851609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 366745655884203604150567739 550118483826305406225851609)
            ·
              refine ⟨412588862869729054669388707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 550118483826305406225851609 412588862869729054669388707)
              ·
                refine ⟨618883294304593582004083061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 412588862869729054669388707 618883294304593582004083061)
                ·
                  refine ⟨58020308841055648312882787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 618883294304593582004083061 58020308841055648312882787)
                  ·
                    refine ⟨87030463261583472469324181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58020308841055648312882787 87030463261583472469324181)
                    ·
                      refine ⟨4079552965386725271999571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 87030463261583472469324181 4079552965386725271999571)
                      ·
                        rfl

theorem cell23_7944901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 5, 1, 6].length) (baseStart_7944901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7944901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7944901 prefixEnd_7944901 := by exact prefixLift 7944901
  have htrace : WordTrace (prefixWord ++ tailWord_7944901) baseStart_7944901 baseEnd_7944901 := by
    simpa [prefixWord, tailWord_7944901, baseEnd_7944901] using wordTrace_append hprefix tailTrace_7944901
  have hstable : (prefixWord ++ tailWord_7944901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7944901).length < 2 ^ (prefixWord ++ tailWord_7944901).sum := by decide
  have hdescent : baseEnd_7944901 < baseStart_7944901 := by decide
  rcases family_descends (prefixWord ++ tailWord_7944901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7944916 : List Nat := [2, 4, 1, 3, 3, 1, 1, 1, 3, 1, 3]
def baseStart_7944916 : Nat := 118140960795 + 7944916 * 2 ^ 59
def prefixEnd_7944916 : Nat := 4983230072969 + 3 ^ 40 * 7944916 * 2
def baseEnd_7944916 : Nat := 4079560667596542713312003

theorem tailTrace_7944916 : CollatzResearch.WordTrace tailWord_7944916 prefixEnd_7944916 4079560667596542713312003 := by
  unfold tailWord_7944916
  simp only [CollatzResearch.WordTrace]
  refine ⟨144887446242466845235443301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193183261656622460313924401 144887446242466845235443301)
  ·
    refine ⟨27166396170462533481645619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 144887446242466845235443301 27166396170462533481645619)
    ·
      refine ⟨40749594255693800222468429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27166396170462533481645619 40749594255693800222468429)
      ·
        refine ⟨15281097845885175083425661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40749594255693800222468429 15281097845885175083425661)
        ·
          refine ⟨5730411692206940656284623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15281097845885175083425661 5730411692206940656284623)
          ·
            refine ⟨8595617538310410984426935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5730411692206940656284623 8595617538310410984426935)
            ·
              refine ⟨12893426307465616476640403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8595617538310410984426935 12893426307465616476640403)
              ·
                refine ⟨19340139461198424714960605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12893426307465616476640403 19340139461198424714960605)
                ·
                  refine ⟨7252552297949409268110227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19340139461198424714960605 7252552297949409268110227)
                  ·
                    refine ⟨10878828446924113902165341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7252552297949409268110227 10878828446924113902165341)
                    ·
                      refine ⟨4079560667596542713312003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10878828446924113902165341 4079560667596542713312003)
                      ·
                        rfl

theorem cell23_7944916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 1, 1, 3, 1, 3].length) (baseStart_7944916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7944916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7944916 prefixEnd_7944916 := by exact prefixLift 7944916
  have htrace : WordTrace (prefixWord ++ tailWord_7944916) baseStart_7944916 baseEnd_7944916 := by
    simpa [prefixWord, tailWord_7944916, baseEnd_7944916] using wordTrace_append hprefix tailTrace_7944916
  have hstable : (prefixWord ++ tailWord_7944916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7944916).length < 2 ^ (prefixWord ++ tailWord_7944916).sum := by decide
  have hdescent : baseEnd_7944916 < baseStart_7944916 := by decide
  rcases family_descends (prefixWord ++ tailWord_7944916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7944932 : List Nat := [2, 3, 1, 1, 1, 4, 4, 1, 2, 4]
def baseStart_7944932 : Nat := 118140960795 + 7944932 * 2 ^ 59
def prefixEnd_7944932 : Nat := 4983230072969 + 3 ^ 40 * 7944932 * 2
def baseEnd_7944932 : Nat := 1359856294429004883570643

theorem tailTrace_7944932 : CollatzResearch.WordTrace tailWord_7944932 prefixEnd_7944932 1359856294429004883570643 := by
  unfold tailWord_7944932
  simp only [CollatzResearch.WordTrace]
  refine ⟨144887738026437862601734525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193183650701917150135646033 144887738026437862601734525)
  ·
    refine ⟨54332901759914198475650447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144887738026437862601734525 54332901759914198475650447)
    ·
      refine ⟨81499352639871297713475671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54332901759914198475650447 81499352639871297713475671)
      ·
        refine ⟨122249028959806946570213507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81499352639871297713475671 122249028959806946570213507)
        ·
          refine ⟨183373543439710419855320261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122249028959806946570213507 183373543439710419855320261)
          ·
            refine ⟨34382539394945703722872549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 183373543439710419855320261 34382539394945703722872549)
            ·
              refine ⟨6446726136552319448038603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34382539394945703722872549 6446726136552319448038603)
              ·
                refine ⟨9670089204828479172057905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6446726136552319448038603 9670089204828479172057905)
                ·
                  refine ⟨7252566903621359379043429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9670089204828479172057905 7252566903621359379043429)
                  ·
                    refine ⟨1359856294429004883570643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7252566903621359379043429 1359856294429004883570643)
                    ·
                      rfl

theorem cell23_7944932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 4, 1, 2, 4].length) (baseStart_7944932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7944932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7944932 prefixEnd_7944932 := by exact prefixLift 7944932
  have htrace : WordTrace (prefixWord ++ tailWord_7944932) baseStart_7944932 baseEnd_7944932 := by
    simpa [prefixWord, tailWord_7944932, baseEnd_7944932] using wordTrace_append hprefix tailTrace_7944932
  have hstable : (prefixWord ++ tailWord_7944932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7944932).length < 2 ^ (prefixWord ++ tailWord_7944932).sum := by decide
  have hdescent : baseEnd_7944932 < baseStart_7944932 := by decide
  rcases family_descends (prefixWord ++ tailWord_7944932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7944942 : List Nat := [4, 1, 2, 1, 1, 3, 3, 2, 1, 2, 3]
def baseStart_7944942 : Nat := 118140960795 + 7944942 * 2 ^ 59
def prefixEnd_7944942 : Nat := 4983230072969 + 3 ^ 40 * 7944942 * 2
def baseEnd_7944942 : Nat := 4079574018093559611586883

theorem tailTrace_7944942 : CollatzResearch.WordTrace tailWord_7944942 prefixEnd_7944942 4079574018093559611586883 := by
  unfold tailWord_7944942
  simp only [CollatzResearch.WordTrace]
  refine ⟨36221980097854937113916635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 193183893855226331274222053 36221980097854937113916635)
  ·
    refine ⟨54332970146782405670874953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36221980097854937113916635 54332970146782405670874953)
    ·
      refine ⟨40749727610086804253156215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54332970146782405670874953 40749727610086804253156215)
      ·
        refine ⟨61124591415130206379734323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40749727610086804253156215 61124591415130206379734323)
        ·
          refine ⟨91686887122695309569601485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61124591415130206379734323 91686887122695309569601485)
          ·
            refine ⟨34382582671010741088600557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91686887122695309569601485 34382582671010741088600557)
            ·
              refine ⟨12893468501629027908225209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34382582671010741088600557 12893468501629027908225209)
              ·
                refine ⟨9670101376221770931168907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12893468501629027908225209 9670101376221770931168907)
                ·
                  refine ⟨14505152064332656396753361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9670101376221770931168907 14505152064332656396753361)
                  ·
                    refine ⟨10878864048249492297565021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14505152064332656396753361 10878864048249492297565021)
                    ·
                      refine ⟨4079574018093559611586883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10878864048249492297565021 4079574018093559611586883)
                      ·
                        rfl

theorem cell23_7944942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 3, 2, 1, 2, 3].length) (baseStart_7944942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7944942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7944942 prefixEnd_7944942 := by exact prefixLift 7944942
  have htrace : WordTrace (prefixWord ++ tailWord_7944942) baseStart_7944942 baseEnd_7944942 := by
    simpa [prefixWord, tailWord_7944942, baseEnd_7944942] using wordTrace_append hprefix tailTrace_7944942
  have hstable : (prefixWord ++ tailWord_7944942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7944942).length < 2 ^ (prefixWord ++ tailWord_7944942).sum := by decide
  have hdescent : baseEnd_7944942 < baseStart_7944942 := by decide
  rcases family_descends (prefixWord ++ tailWord_7944942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7944949 : List Nat := [1, 3, 6, 1, 1, 1, 1, 2, 1, 6]
def baseStart_7944949 : Nat := 118140960795 + 7944949 * 2 ^ 59
def prefixEnd_7944949 : Nat := 4983230072969 + 3 ^ 40 * 7944949 * 2
def baseEnd_7944949 : Nat := 1359859204152713694733117

theorem tailTrace_7944949 : CollatzResearch.WordTrace tailWord_7944949 prefixEnd_7944949 1359859204152713694733117 := by
  unfold tailWord_7944949
  simp only [CollatzResearch.WordTrace]
  refine ⟨289776096093814137106837901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193184064062542758071225267 289776096093814137106837901)
  ·
    refine ⟨108666036035180301415064213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 289776096093814137106837901 108666036035180301415064213)
    ·
      refine ⟨5093720439149076628831135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 108666036035180301415064213 5093720439149076628831135)
      ·
        refine ⟨7640580658723614943246703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5093720439149076628831135 7640580658723614943246703)
        ·
          refine ⟨11460870988085422414870055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7640580658723614943246703 11460870988085422414870055)
          ·
            refine ⟨17191306482128133622305083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11460870988085422414870055 17191306482128133622305083)
            ·
              refine ⟨25786959723192200433457625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17191306482128133622305083 25786959723192200433457625)
              ·
                refine ⟨19340219792394150325093219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25786959723192200433457625 19340219792394150325093219)
                ·
                  refine ⟨29010329688591225487639829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19340219792394150325093219 29010329688591225487639829)
                  ·
                    refine ⟨1359859204152713694733117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29010329688591225487639829 1359859204152713694733117)
                    ·
                      rfl

theorem cell23_7944949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_7944949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7944949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7944949 prefixEnd_7944949 := by exact prefixLift 7944949
  have htrace : WordTrace (prefixWord ++ tailWord_7944949) baseStart_7944949 baseEnd_7944949 := by
    simpa [prefixWord, tailWord_7944949, baseEnd_7944949] using wordTrace_append hprefix tailTrace_7944949
  have hstable : (prefixWord ++ tailWord_7944949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7944949).length < 2 ^ (prefixWord ++ tailWord_7944949).sum := by decide
  have hdescent : baseEnd_7944949 < baseStart_7944949 := by decide
  rcases family_descends (prefixWord ++ tailWord_7944949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7944988 : List Nat := [2, 2, 3, 1, 1, 3, 1, 1, 1, 8]
def baseStart_7944988 : Nat := 118140960795 + 7944988 * 2 ^ 59
def prefixEnd_7944988 : Nat := 4983230072969 + 3 ^ 40 * 7944988 * 2
def baseEnd_7944988 : Nat := 1359865879401222143870557

theorem tailTrace_7944988 : CollatzResearch.WordTrace tailWord_7944988 prefixEnd_7944988 1359865879401222143870557 := by
  unfold tailWord_7944988
  simp only [CollatzResearch.WordTrace]
  refine ⟨144888759270336423383753809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193185012360448564511671745 144888759270336423383753809)
  ·
    refine ⟨108666569452752317537815357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144888759270336423383753809 108666569452752317537815357)
    ·
      refine ⟨40749963544782119076680759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108666569452752317537815357 40749963544782119076680759)
      ·
        refine ⟨61124945317173178615021139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40749963544782119076680759 61124945317173178615021139)
        ·
          refine ⟨91687417975759767922531709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61124945317173178615021139 91687417975759767922531709)
          ·
            refine ⟨34382781740909912970949391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91687417975759767922531709 34382781740909912970949391)
            ·
              refine ⟨51574172611364869456424087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34382781740909912970949391 51574172611364869456424087)
              ·
                refine ⟨77361258917047304184636131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51574172611364869456424087 77361258917047304184636131)
                ·
                  refine ⟨116041888375570956276954197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77361258917047304184636131 116041888375570956276954197)
                  ·
                    refine ⟨1359865879401222143870557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 116041888375570956276954197 1359865879401222143870557)
                    ·
                      rfl

theorem cell23_7944988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 1, 1, 8].length) (baseStart_7944988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7944988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7944988 prefixEnd_7944988 := by exact prefixLift 7944988
  have htrace : WordTrace (prefixWord ++ tailWord_7944988) baseStart_7944988 baseEnd_7944988 := by
    simpa [prefixWord, tailWord_7944988, baseEnd_7944988] using wordTrace_append hprefix tailTrace_7944988
  have hstable : (prefixWord ++ tailWord_7944988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7944988).length < 2 ^ (prefixWord ++ tailWord_7944988).sum := by decide
  have hdescent : baseEnd_7944988 < baseStart_7944988 := by decide
  rcases family_descends (prefixWord ++ tailWord_7944988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7944989 : List Nat := [1, 4, 2, 4, 1, 1, 2, 1, 1, 3, 3]
def baseStart_7944989 : Nat := 118140960795 + 7944989 * 2 ^ 59
def prefixEnd_7944989 : Nat := 4983230072969 + 3 ^ 40 * 7944989 * 2
def baseEnd_7944989 : Nat := 4079598151684320927699167

theorem tailTrace_7944989 : CollatzResearch.WordTrace tailWord_7944989 prefixEnd_7944989 4079598151684320927699167 := by
  unfold tailWord_7944989
  simp only [CollatzResearch.WordTrace]
  refine ⟨289777555013669223938294021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193185036675779482625529347 289777555013669223938294021)
  ·
    refine ⟨54333291565062979488430129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 289777555013669223938294021 54333291565062979488430129)
    ·
      refine ⟨40749968673797234616322597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54333291565062979488430129 40749968673797234616322597)
      ·
        refine ⟨7640619126336981490560487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40749968673797234616322597 7640619126336981490560487)
        ·
          refine ⟨11460928689505472235840731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7640619126336981490560487 11460928689505472235840731)
          ·
            refine ⟨17191393034258208353761097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11460928689505472235840731 17191393034258208353761097)
            ·
              refine ⟨12893544775693656265320823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17191393034258208353761097 12893544775693656265320823)
              ·
                refine ⟨19340317163540484397981235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12893544775693656265320823 19340317163540484397981235)
                ·
                  refine ⟨29010475745310726596971853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19340317163540484397981235 29010475745310726596971853)
                  ·
                    refine ⟨10878928404491522473864445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29010475745310726596971853 10878928404491522473864445)
                    ·
                      refine ⟨4079598151684320927699167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10878928404491522473864445 4079598151684320927699167)
                      ·
                        rfl

theorem cell23_7944989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_7944989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7944989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7944989 prefixEnd_7944989 := by exact prefixLift 7944989
  have htrace : WordTrace (prefixWord ++ tailWord_7944989) baseStart_7944989 baseEnd_7944989 := by
    simpa [prefixWord, tailWord_7944989, baseEnd_7944989] using wordTrace_append hprefix tailTrace_7944989
  have hstable : (prefixWord ++ tailWord_7944989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7944989).length < 2 ^ (prefixWord ++ tailWord_7944989).sum := by decide
  have hdescent : baseEnd_7944989 < baseStart_7944989 := by decide
  rcases family_descends (prefixWord ++ tailWord_7944989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7945045 : List Nat := [1, 3, 2, 2, 2, 1, 1, 3, 2, 3, 3]
def baseStart_7945045 : Nat := 118140960795 + 7945045 * 2 ^ 59
def prefixEnd_7945045 : Nat := 4983230072969 + 3 ^ 40 * 7945045 * 2
def baseEnd_7945045 : Nat := 4079626906600972708598909

theorem tailTrace_7945045 : CollatzResearch.WordTrace tailWord_7945045 prefixEnd_7945045 4079626906600972708598909 := by
  unfold tailWord_7945045
  simp only [CollatzResearch.WordTrace]
  refine ⟨289779597501466345502332589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193186398334310897001555059 289779597501466345502332589)
  ·
    refine ⟨108667349063049879563374721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 289779597501466345502332589 108667349063049879563374721)
    ·
      refine ⟨81500511797287409672531041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108667349063049879563374721 81500511797287409672531041)
      ·
        refine ⟨61125383847965557254398281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81500511797287409672531041 61125383847965557254398281)
        ·
          refine ⟨45844037885974167940798711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61125383847965557254398281 45844037885974167940798711)
          ·
            refine ⟨68766056828961251911198067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45844037885974167940798711 68766056828961251911198067)
            ·
              refine ⟨103149085243441877866797101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68766056828961251911198067 103149085243441877866797101)
              ·
                refine ⟨38680906966290704200048913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103149085243441877866797101 38680906966290704200048913)
                ·
                  refine ⟨29010680224718028150036685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38680906966290704200048913 29010680224718028150036685)
                  ·
                    refine ⟨10879005084269260556263757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29010680224718028150036685 10879005084269260556263757)
                    ·
                      refine ⟨4079626906600972708598909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10879005084269260556263757 4079626906600972708598909)
                      ·
                        rfl

theorem cell23_7945045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 3, 2, 3, 3].length) (baseStart_7945045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7945045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7945045 prefixEnd_7945045 := by exact prefixLift 7945045
  have htrace : WordTrace (prefixWord ++ tailWord_7945045) baseStart_7945045 baseEnd_7945045 := by
    simpa [prefixWord, tailWord_7945045, baseEnd_7945045] using wordTrace_append hprefix tailTrace_7945045
  have hstable : (prefixWord ++ tailWord_7945045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7945045).length < 2 ^ (prefixWord ++ tailWord_7945045).sum := by decide
  have hdescent : baseEnd_7945045 < baseStart_7945045 := by decide
  rcases family_descends (prefixWord ++ tailWord_7945045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7945085 : List Nat := [1, 4, 1, 1, 2, 1, 3, 1, 4, 1, 4]
def baseStart_7945085 : Nat := 118140960795 + 7945085 * 2 ^ 59
def prefixEnd_7945085 : Nat := 4983230072969 + 3 ^ 40 * 7945085 * 2
def baseEnd_7945085 : Nat := 4079647445827152552098725

theorem tailTrace_7945085 : CollatzResearch.WordTrace tailWord_7945085 prefixEnd_7945085 4079647445827152552098725 := by
  unfold tailWord_7945085
  simp only [CollatzResearch.WordTrace]
  refine ⟨289781056421321432333788709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193187370947547621555859139 289781056421321432333788709)
  ·
    refine ⟨54333948078997768562585383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 289781056421321432333788709 54333948078997768562585383)
    ·
      refine ⟨81500922118496652843878075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54333948078997768562585383 81500922118496652843878075)
      ·
        refine ⟨122251383177744979265817113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81500922118496652843878075 122251383177744979265817113)
        ·
          refine ⟨91688537383308734449362835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122251383177744979265817113 91688537383308734449362835)
          ·
            refine ⟨137532806074963101674044253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91688537383308734449362835 137532806074963101674044253)
            ·
              refine ⟨51574802278111163127766595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 137532806074963101674044253 51574802278111163127766595)
              ·
                refine ⟨77362203417166744691649893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51574802278111163127766595 77362203417166744691649893)
                ·
                  refine ⟨14505413140718764629684355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77362203417166744691649893 14505413140718764629684355)
                  ·
                    refine ⟨21758119711078146944526533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14505413140718764629684355 21758119711078146944526533)
                    ·
                      refine ⟨4079647445827152552098725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21758119711078146944526533 4079647445827152552098725)
                      ·
                        rfl

theorem cell23_7945085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 1, 4, 1, 4].length) (baseStart_7945085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7945085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7945085 prefixEnd_7945085 := by exact prefixLift 7945085
  have htrace : WordTrace (prefixWord ++ tailWord_7945085) baseStart_7945085 baseEnd_7945085 := by
    simpa [prefixWord, tailWord_7945085, baseEnd_7945085] using wordTrace_append hprefix tailTrace_7945085
  have hstable : (prefixWord ++ tailWord_7945085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7945085).length < 2 ^ (prefixWord ++ tailWord_7945085).sum := by decide
  have hdescent : baseEnd_7945085 < baseStart_7945085 := by decide
  rcases family_descends (prefixWord ++ tailWord_7945085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7945086 : List Nat := [4, 2, 3, 1, 3, 1, 1, 1, 7]
def baseStart_7945086 : Nat := 118140960795 + 7945086 * 2 ^ 59
def prefixEnd_7945086 : Nat := 4983230072969 + 3 ^ 40 * 7945086 * 2
def baseEnd_7945086 : Nat := 453294217700867449798469

theorem tailTrace_7945086 : CollatzResearch.WordTrace tailWord_7945086 prefixEnd_7945086 453294217700867449798469 := by
  unfold tailWord_7945086
  simp only [CollatzResearch.WordTrace]
  refine ⟨36222636611789726188071889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 193187395262878539669716741 36222636611789726188071889)
  ·
    refine ⟨27166977458842294641053917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36222636611789726188071889 27166977458842294641053917)
    ·
      refine ⟨10187616547065860490395219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27166977458842294641053917 10187616547065860490395219)
      ·
        refine ⟨15281424820598790735592829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10187616547065860490395219 15281424820598790735592829)
        ·
          refine ⟨5730534307724546525847311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15281424820598790735592829 5730534307724546525847311)
          ·
            refine ⟨8595801461586819788770967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5730534307724546525847311 8595801461586819788770967)
            ·
              refine ⟨12893702192380229683156451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8595801461586819788770967 12893702192380229683156451)
              ·
                refine ⟨19340553288570344524734677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12893702192380229683156451 19340553288570344524734677)
                ·
                  refine ⟨453294217700867449798469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19340553288570344524734677 453294217700867449798469)
                  ·
                    rfl

theorem cell23_7945086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 1, 1, 7].length) (baseStart_7945086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7945086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7945086 prefixEnd_7945086 := by exact prefixLift 7945086
  have htrace : WordTrace (prefixWord ++ tailWord_7945086) baseStart_7945086 baseEnd_7945086 := by
    simpa [prefixWord, tailWord_7945086, baseEnd_7945086] using wordTrace_append hprefix tailTrace_7945086
  have hstable : (prefixWord ++ tailWord_7945086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7945086).length < 2 ^ (prefixWord ++ tailWord_7945086).sum := by decide
  have hdescent : baseEnd_7945086 < baseStart_7945086 := by decide
  rcases family_descends (prefixWord ++ tailWord_7945086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7945088 : List Nat := [2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 5]
def baseStart_7945088 : Nat := 118140960795 + 7945088 * 2 ^ 59
def prefixEnd_7945088 : Nat := 4983230072969 + 3 ^ 40 * 7945088 * 2
def baseEnd_7945088 : Nat := 4079648986269116040361211

theorem tailTrace_7945088 : CollatzResearch.WordTrace tailWord_7945088 prefixEnd_7945088 4079648986269116040361211 := by
  unfold tailWord_7945088
  simp only [CollatzResearch.WordTrace]
  refine ⟨144890582920155281923073959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193187443893540375897431945 144890582920155281923073959)
  ·
    refine ⟨217335874380232922884610939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144890582920155281923073959 217335874380232922884610939)
    ·
      refine ⟨326003811570349384326916409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217335874380232922884610939 326003811570349384326916409)
      ·
        refine ⟨244502858677762038245187307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 326003811570349384326916409 244502858677762038245187307)
        ·
          refine ⟨366754288016643057367780961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244502858677762038245187307 366754288016643057367780961)
          ·
            refine ⟨275065716012482293025835721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 366754288016643057367780961 275065716012482293025835721)
            ·
              refine ⟨206299287009361719769376791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 275065716012482293025835721 206299287009361719769376791)
              ·
                refine ⟨309448930514042579654065187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 206299287009361719769376791 309448930514042579654065187)
                ·
                  refine ⟨464173395771063869481097781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 309448930514042579654065187 464173395771063869481097781)
                  ·
                    refine ⟨43516255853537237763852917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 464173395771063869481097781 43516255853537237763852917)
                    ·
                      refine ⟨4079648986269116040361211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43516255853537237763852917 4079648986269116040361211)
                      ·
                        rfl

theorem cell23_7945088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 5].length) (baseStart_7945088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7945088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7945088 prefixEnd_7945088 := by exact prefixLift 7945088
  have htrace : WordTrace (prefixWord ++ tailWord_7945088) baseStart_7945088 baseEnd_7945088 := by
    simpa [prefixWord, tailWord_7945088, baseEnd_7945088] using wordTrace_append hprefix tailTrace_7945088
  have hstable : (prefixWord ++ tailWord_7945088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7945088).length < 2 ^ (prefixWord ++ tailWord_7945088).sum := by decide
  have hdescent : baseEnd_7945088 < baseStart_7945088 := by decide
  rcases family_descends (prefixWord ++ tailWord_7945088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7945105 : List Nat := [1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 3]
def baseStart_7945105 : Nat := 118140960795 + 7945105 * 2 ^ 59
def prefixEnd_7945105 : Nat := 4983230072969 + 3 ^ 40 * 7945105 * 2
def baseEnd_7945105 : Nat := 4079657715440242473848633

theorem tailTrace_7945105 : CollatzResearch.WordTrace tailWord_7945105 prefixEnd_7945105 4079657715440242473848633 := by
  unfold tailWord_7945105
  simp only [CollatzResearch.WordTrace]
  refine ⟨289781785881248975749516769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193187857254165983833011179 289781785881248975749516769)
  ·
    refine ⟨217336339410936731812137577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289781785881248975749516769 217336339410936731812137577)
    ·
      refine ⟨163002254558202548859103183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217336339410936731812137577 163002254558202548859103183)
      ·
        refine ⟨244503381837303823288654775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163002254558202548859103183 244503381837303823288654775)
        ·
          refine ⟨366755072755955734932982163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244503381837303823288654775 366755072755955734932982163)
          ·
            refine ⟨550132609133933602399473245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 366755072755955734932982163 550132609133933602399473245)
            ·
              refine ⟨206299728425225100899802467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 550132609133933602399473245 206299728425225100899802467)
              ·
                refine ⟨309449592637837651349703701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 206299728425225100899802467 309449592637837651349703701)
                ·
                  refine ⟨14505449654898639907017361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 309449592637837651349703701 14505449654898639907017361)
                  ·
                    refine ⟨10879087241173979930263021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14505449654898639907017361 10879087241173979930263021)
                    ·
                      refine ⟨4079657715440242473848633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10879087241173979930263021 4079657715440242473848633)
                      ·
                        rfl

theorem cell23_7945105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 3].length) (baseStart_7945105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7945105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7945105 prefixEnd_7945105 := by exact prefixLift 7945105
  have htrace : WordTrace (prefixWord ++ tailWord_7945105) baseStart_7945105 baseEnd_7945105 := by
    simpa [prefixWord, tailWord_7945105, baseEnd_7945105] using wordTrace_append hprefix tailTrace_7945105
  have hstable : (prefixWord ++ tailWord_7945105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7945105).length < 2 ^ (prefixWord ++ tailWord_7945105).sum := by decide
  have hdescent : baseEnd_7945105 < baseStart_7945105 := by decide
  rcases family_descends (prefixWord ++ tailWord_7945105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7945162 : List Nat := [3, 1, 2, 1, 2, 1, 1, 4, 1, 5, 2]
def baseStart_7945162 : Nat := 118140960795 + 7945162 * 2 ^ 59
def prefixEnd_7945162 : Nat := 4983230072969 + 3 ^ 40 * 7945162 * 2
def baseEnd_7945162 : Nat := 4079686983837548750835871

theorem tailTrace_7945162 : CollatzResearch.WordTrace tailWord_7945162 prefixEnd_7945162 4079686983837548750835871 := by
  unfold tailWord_7945162
  simp only [CollatzResearch.WordTrace]
  refine ⟨72445966210510618621085435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193189243228028316322894493 72445966210510618621085435)
  ·
    refine ⟨108668949315765927931628153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72445966210510618621085435 108668949315765927931628153)
    ·
      refine ⟨81501711986824445948721115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108668949315765927931628153 81501711986824445948721115)
      ·
        refine ⟨122252567980236668923081673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81501711986824445948721115 122252567980236668923081673)
        ·
          refine ⟨91689425985177501692311255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122252567980236668923081673 91689425985177501692311255)
          ·
            refine ⟨137534138977766252538466883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91689425985177501692311255 137534138977766252538466883)
            ·
              refine ⟨206301208466649378807700325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137534138977766252538466883 206301208466649378807700325)
              ·
                refine ⟨38681476587496758526443811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 206301208466649378807700325 38681476587496758526443811)
                ·
                  refine ⟨58022214881245137789665717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38681476587496758526443811 58022214881245137789665717)
                  ·
                    refine ⟨5439582645116731667781161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 58022214881245137789665717 5439582645116731667781161)
                    ·
                      refine ⟨4079686983837548750835871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5439582645116731667781161 4079686983837548750835871)
                      ·
                        rfl

theorem cell23_7945162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 4, 1, 5, 2].length) (baseStart_7945162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7945162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7945162 prefixEnd_7945162 := by exact prefixLift 7945162
  have htrace : WordTrace (prefixWord ++ tailWord_7945162) baseStart_7945162 baseEnd_7945162 := by
    simpa [prefixWord, tailWord_7945162, baseEnd_7945162] using wordTrace_append hprefix tailTrace_7945162
  have hstable : (prefixWord ++ tailWord_7945162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7945162).length < 2 ^ (prefixWord ++ tailWord_7945162).sum := by decide
  have hdescent : baseEnd_7945162 < baseStart_7945162 := by decide
  rcases family_descends (prefixWord ++ tailWord_7945162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7945172 : List Nat := [2, 4, 1, 2, 1, 2, 2, 1, 3, 5]
def baseStart_7945172 : Nat := 118140960795 + 7945172 * 2 ^ 59
def prefixEnd_7945172 : Nat := 4983230072969 + 3 ^ 40 * 7945172 * 2
def baseEnd_7945172 : Nat := 1359897372881364570570275

theorem tailTrace_7945172 : CollatzResearch.WordTrace tailWord_7945172 prefixEnd_7945172 1359897372881364570570275 := by
  unfold tailWord_7945172
  simp only [CollatzResearch.WordTrace]
  refine ⟨144892114786003123096102885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193189486381337497461470513 144892114786003123096102885)
  ·
    refine ⟨27167271522375585580519291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 144892114786003123096102885 27167271522375585580519291)
    ·
      refine ⟨40750907283563378370778937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27167271522375585580519291 40750907283563378370778937)
      ·
        refine ⟨30563180462672533778084203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40750907283563378370778937 30563180462672533778084203)
        ·
          refine ⟨45844770694008800667126305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30563180462672533778084203 45844770694008800667126305)
          ·
            refine ⟨34383578020506600500344729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45844770694008800667126305 34383578020506600500344729)
            ·
              refine ⟨25787683515379950375258547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34383578020506600500344729 25787683515379950375258547)
              ·
                refine ⟨38681525273069925562887821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25787683515379950375258547 38681525273069925562887821)
                ·
                  refine ⟨14505571977401222086082933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38681525273069925562887821 14505571977401222086082933)
                  ·
                    refine ⟨1359897372881364570570275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14505571977401222086082933 1359897372881364570570275)
                    ·
                      rfl

theorem cell23_7945172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 1, 3, 5].length) (baseStart_7945172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7945172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7945172 prefixEnd_7945172 := by exact prefixLift 7945172
  have htrace : WordTrace (prefixWord ++ tailWord_7945172) baseStart_7945172 baseEnd_7945172 := by
    simpa [prefixWord, tailWord_7945172, baseEnd_7945172] using wordTrace_append hprefix tailTrace_7945172
  have hstable : (prefixWord ++ tailWord_7945172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7945172).length < 2 ^ (prefixWord ++ tailWord_7945172).sum := by decide
  have hdescent : baseEnd_7945172 < baseStart_7945172 := by decide
  rcases family_descends (prefixWord ++ tailWord_7945172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7945212 : List Nat := [2, 2, 2, 1, 2, 4, 1, 2, 1, 1, 5]
def baseStart_7945212 : Nat := 118140960795 + 7945212 * 2 ^ 59
def prefixEnd_7945212 : Nat := 4983230072969 + 3 ^ 40 * 7945212 * 2
def baseEnd_7945212 : Nat := 4079712657870273555210641

theorem tailTrace_7945212 : CollatzResearch.WordTrace tailWord_7945212 prefixEnd_7945212 4079712657870273555210641 := by
  unfold tailWord_7945212
  simp only [CollatzResearch.WordTrace]
  refine ⟨144892844245930666511830945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193190458994574222015774593 144892844245930666511830945)
  ·
    refine ⟨108669633184447999883873209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144892844245930666511830945 108669633184447999883873209)
    ·
      refine ⟨81502224888335999912904907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108669633184447999883873209 81502224888335999912904907)
      ·
        refine ⟨122253337332503999869357361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81502224888335999912904907 122253337332503999869357361)
        ·
          refine ⟨91690002999377999902018021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122253337332503999869357361 91690002999377999902018021)
          ·
            refine ⟨17191875562383374981628379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 91690002999377999902018021 17191875562383374981628379)
            ·
              refine ⟨25787813343575062472442569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17191875562383374981628379 25787813343575062472442569)
              ·
                refine ⟨19340860007681296854331927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25787813343575062472442569 19340860007681296854331927)
                ·
                  refine ⟨29011290011521945281497891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19340860007681296854331927 29011290011521945281497891)
                  ·
                    refine ⟨43516935017282917922246837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29011290011521945281497891 43516935017282917922246837)
                    ·
                      refine ⟨4079712657870273555210641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43516935017282917922246837 4079712657870273555210641)
                      ·
                        rfl

theorem cell23_7945212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 2, 1, 1, 5].length) (baseStart_7945212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7945212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7945212 prefixEnd_7945212 := by exact prefixLift 7945212
  have htrace : WordTrace (prefixWord ++ tailWord_7945212) baseStart_7945212 baseEnd_7945212 := by
    simpa [prefixWord, tailWord_7945212, baseEnd_7945212] using wordTrace_append hprefix tailTrace_7945212
  have hstable : (prefixWord ++ tailWord_7945212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7945212).length < 2 ^ (prefixWord ++ tailWord_7945212).sum := by decide
  have hdescent : baseEnd_7945212 < baseStart_7945212 := by decide
  rcases family_descends (prefixWord ++ tailWord_7945212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7945226 : List Nat := [3, 1, 2, 2, 3, 1, 2, 2, 3, 2, 2]
def baseStart_7945226 : Nat := 118140960795 + 7945226 * 2 ^ 59
def prefixEnd_7945226 : Nat := 4983230072969 + 3 ^ 40 * 7945226 * 2
def baseEnd_7945226 : Nat := 4079719846599436500435577

theorem tailTrace_7945226 : CollatzResearch.WordTrace tailWord_7945226 prefixEnd_7945226 4079719846599436500435577 := by
  unfold tailWord_7945226
  simp only [CollatzResearch.WordTrace]
  refine ⟨72446549778452653353667883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193190799409207075609781021 72446549778452653353667883)
  ·
    refine ⟨108669824667678980030501825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72446549778452653353667883 108669824667678980030501825)
    ·
      refine ⟨81502368500759235022876369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108669824667678980030501825 81502368500759235022876369)
      ·
        refine ⟨61126776375569426267157277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81502368500759235022876369 61126776375569426267157277)
        ·
          refine ⟨22922541140838534850183979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61126776375569426267157277 22922541140838534850183979)
          ·
            refine ⟨34383811711257802275275969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22922541140838534850183979 34383811711257802275275969)
            ·
              refine ⟨25787858783443351706456977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34383811711257802275275969 25787858783443351706456977)
              ·
                refine ⟨19340894087582513779842733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25787858783443351706456977 19340894087582513779842733)
                ·
                  refine ⟨7252835282843442667441025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19340894087582513779842733 7252835282843442667441025)
                  ·
                    refine ⟨5439626462132582000580769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7252835282843442667441025 5439626462132582000580769)
                    ·
                      refine ⟨4079719846599436500435577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5439626462132582000580769 4079719846599436500435577)
                      ·
                        rfl

theorem cell23_7945226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 2, 3, 2, 2].length) (baseStart_7945226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7945226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7945226 prefixEnd_7945226 := by exact prefixLift 7945226
  have htrace : WordTrace (prefixWord ++ tailWord_7945226) baseStart_7945226 baseEnd_7945226 := by
    simpa [prefixWord, tailWord_7945226, baseEnd_7945226] using wordTrace_append hprefix tailTrace_7945226
  have hstable : (prefixWord ++ tailWord_7945226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7945226).length < 2 ^ (prefixWord ++ tailWord_7945226).sum := by decide
  have hdescent : baseEnd_7945226 < baseStart_7945226 := by decide
  rcases family_descends (prefixWord ++ tailWord_7945226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7945242 : List Nat := [3, 1, 1, 3, 1, 2, 2, 1, 3, 3, 3]
def baseStart_7945242 : Nat := 118140960795 + 7945242 * 2 ^ 59
def prefixEnd_7945242 : Nat := 4983230072969 + 3 ^ 40 * 7945242 * 2
def baseEnd_7945242 : Nat := 4079728062289908437835503

theorem tailTrace_7945242 : CollatzResearch.WordTrace tailWord_7945242 prefixEnd_7945242 4079728062289908437835503 := by
  unfold tailWord_7945242
  simp only [CollatzResearch.WordTrace]
  refine ⟨72446695670438162036813495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193191188454501765431502653 72446695670438162036813495)
  ·
    refine ⟨108670043505657243055220243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72446695670438162036813495 108670043505657243055220243)
    ·
      refine ⟨163005065258485864582830365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108670043505657243055220243 163005065258485864582830365)
      ·
        refine ⟨61126899471932199218561387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163005065258485864582830365 61126899471932199218561387)
        ·
          refine ⟨91690349207898298827842081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61126899471932199218561387 91690349207898298827842081)
          ·
            refine ⟨68767761905923724120881561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91690349207898298827842081 68767761905923724120881561)
            ·
              refine ⟨51575821429442793090661171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68767761905923724120881561 51575821429442793090661171)
              ·
                refine ⟨77363732144164189635991757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51575821429442793090661171 77363732144164189635991757)
                ·
                  refine ⟨29011399554061571113496909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77363732144164189635991757 29011399554061571113496909)
                  ·
                    refine ⟨10879274832773089167561341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29011399554061571113496909 10879274832773089167561341)
                    ·
                      refine ⟨4079728062289908437835503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10879274832773089167561341 4079728062289908437835503)
                      ·
                        rfl

theorem cell23_7945242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 1, 3, 3, 3].length) (baseStart_7945242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7945242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7945242 prefixEnd_7945242 := by exact prefixLift 7945242
  have htrace : WordTrace (prefixWord ++ tailWord_7945242) baseStart_7945242 baseEnd_7945242 := by
    simpa [prefixWord, tailWord_7945242, baseEnd_7945242] using wordTrace_append hprefix tailTrace_7945242
  have hstable : (prefixWord ++ tailWord_7945242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7945242).length < 2 ^ (prefixWord ++ tailWord_7945242).sum := by decide
  have hdescent : baseEnd_7945242 < baseStart_7945242 := by decide
  rcases family_descends (prefixWord ++ tailWord_7945242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7945259 : List Nat := [1, 1, 1, 1, 2, 1, 6, 4, 2, 1, 3]
def baseStart_7945259 : Nat := 118140960795 + 7945259 * 2 ^ 59
def prefixEnd_7945259 : Nat := 4983230072969 + 3 ^ 40 * 7945259 * 2
def baseEnd_7945259 : Nat := 4079736791461034871322925

theorem tailTrace_7945259 : CollatzResearch.WordTrace tailWord_7945259 prefixEnd_7945259 4079736791461034871322925 := by
  unfold tailWord_7945259
  simp only [CollatzResearch.WordTrace]
  refine ⟨289787402722691060050622831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193191601815127373367081887 289787402722691060050622831)
  ·
    refine ⟨434681104084036590075934247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289787402722691060050622831 434681104084036590075934247)
    ·
      refine ⟨652021656126054885113901371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 434681104084036590075934247 652021656126054885113901371)
      ·
        refine ⟨978032484189082327670852057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 652021656126054885113901371 978032484189082327670852057)
        ·
          refine ⟨733524363141811745753139043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 978032484189082327670852057 733524363141811745753139043)
          ·
            refine ⟨1100286544712717618629708565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 733524363141811745753139043 1100286544712717618629708565)
            ·
              refine ⟨51575931783408638373267589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1100286544712717618629708565 51575931783408638373267589)
              ·
                refine ⟨9670487209389119694987673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51575931783408638373267589 9670487209389119694987673)
                ·
                  refine ⟨7252865407041839771240755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9670487209389119694987673 7252865407041839771240755)
                  ·
                    refine ⟨10879298110562759656861133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7252865407041839771240755 10879298110562759656861133)
                    ·
                      refine ⟨4079736791461034871322925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10879298110562759656861133 4079736791461034871322925)
                      ·
                        rfl

theorem cell23_7945259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 4, 2, 1, 3].length) (baseStart_7945259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7945259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7945259 prefixEnd_7945259 := by exact prefixLift 7945259
  have htrace : WordTrace (prefixWord ++ tailWord_7945259) baseStart_7945259 baseEnd_7945259 := by
    simpa [prefixWord, tailWord_7945259, baseEnd_7945259] using wordTrace_append hprefix tailTrace_7945259
  have hstable : (prefixWord ++ tailWord_7945259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7945259).length < 2 ^ (prefixWord ++ tailWord_7945259).sum := by decide
  have hdescent : baseEnd_7945259 < baseStart_7945259 := by decide
  rcases family_descends (prefixWord ++ tailWord_7945259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7945262 : List Nat := [4, 1, 3, 1, 1, 1, 2, 1, 2, 7]
def baseStart_7945262 : Nat := 118140960795 + 7945262 * 2 ^ 59
def prefixEnd_7945262 : Nat := 4983230072969 + 3 ^ 40 * 7945262 * 2
def baseEnd_7945262 : Nat := 1359912777300999453195137

theorem tailTrace_7945262 : CollatzResearch.WordTrace tailWord_7945262 prefixEnd_7945262 1359912777300999453195137 := by
  unfold tailWord_7945262
  simp only [CollatzResearch.WordTrace]
  refine ⟨36223439017710023945372755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 193191674761120127708654693 36223439017710023945372755)
  ·
    refine ⟨54335158526565035918059133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36223439017710023945372755 54335158526565035918059133)
    ·
      refine ⟨20375684447461888469272175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54335158526565035918059133 20375684447461888469272175)
      ·
        refine ⟨30563526671192832703908263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20375684447461888469272175 30563526671192832703908263)
        ·
          refine ⟨45845290006789249055862395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30563526671192832703908263 45845290006789249055862395)
          ·
            refine ⟨68767935010183873583793593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45845290006789249055862395 68767935010183873583793593)
            ·
              refine ⟨51575951257637905187845195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68767935010183873583793593 51575951257637905187845195)
              ·
                refine ⟨77363926886456857781767793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51575951257637905187845195 77363926886456857781767793)
                ·
                  refine ⟨58022945164842643336325845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77363926886456857781767793 58022945164842643336325845)
                  ·
                    refine ⟨1359912777300999453195137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58022945164842643336325845 1359912777300999453195137)
                    ·
                      rfl

theorem cell23_7945262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 1, 2, 7].length) (baseStart_7945262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7945262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7945262 prefixEnd_7945262 := by exact prefixLift 7945262
  have htrace : WordTrace (prefixWord ++ tailWord_7945262) baseStart_7945262 baseEnd_7945262 := by
    simpa [prefixWord, tailWord_7945262, baseEnd_7945262] using wordTrace_append hprefix tailTrace_7945262
  have hstable : (prefixWord ++ tailWord_7945262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7945262).length < 2 ^ (prefixWord ++ tailWord_7945262).sum := by decide
  have hdescent : baseEnd_7945262 < baseStart_7945262 := by decide
  rcases family_descends (prefixWord ++ tailWord_7945262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7945269 : List Nat := [1, 3, 3, 1, 1, 1, 1, 4, 3, 3, 2]
def baseStart_7945269 : Nat := 118140960795 + 7945269 * 2 ^ 59
def prefixEnd_7945269 : Nat := 4983230072969 + 3 ^ 40 * 7945269 * 2
def baseEnd_7945269 : Nat := 4079741926267579832197879

theorem tailTrace_7945269 : CollatzResearch.WordTrace tailWord_7945269 prefixEnd_7945269 4079741926267579832197879 := by
  unfold tailWord_7945269
  simp only [CollatzResearch.WordTrace]
  refine ⟨289787767452654831758486861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193191844968436554505657907 289787767452654831758486861)
  ·
    refine ⟨108670412794745561909432573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 289787767452654831758486861 108670412794745561909432573)
    ·
      refine ⟨40751404798029585716037215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108670412794745561909432573 40751404798029585716037215)
      ·
        refine ⟨61127107197044378574055823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40751404798029585716037215 61127107197044378574055823)
        ·
          refine ⟨91690660795566567861083735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61127107197044378574055823 91690660795566567861083735)
          ·
            refine ⟨137535991193349851791625603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91690660795566567861083735 137535991193349851791625603)
            ·
              refine ⟨206303986790024777687438405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137535991193349851791625603 206303986790024777687438405)
              ·
                refine ⟨38681997523129645816394701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 206303986790024777687438405 38681997523129645816394701)
                ·
                  refine ⟨14505749071173617181148013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38681997523129645816394701 14505749071173617181148013)
                  ·
                    refine ⟨5439655901690106442930505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14505749071173617181148013 5439655901690106442930505)
                    ·
                      refine ⟨4079741926267579832197879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5439655901690106442930505 4079741926267579832197879)
                      ·
                        rfl

theorem cell23_7945269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 4, 3, 3, 2].length) (baseStart_7945269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7945269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7945269 prefixEnd_7945269 := by exact prefixLift 7945269
  have htrace : WordTrace (prefixWord ++ tailWord_7945269) baseStart_7945269 baseEnd_7945269 := by
    simpa [prefixWord, tailWord_7945269, baseEnd_7945269] using wordTrace_append hprefix tailTrace_7945269
  have hstable : (prefixWord ++ tailWord_7945269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7945269).length < 2 ^ (prefixWord ++ tailWord_7945269).sum := by decide
  have hdescent : baseEnd_7945269 < baseStart_7945269 := by decide
  rcases family_descends (prefixWord ++ tailWord_7945269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7945276 : List Nat := [2, 2, 2, 2, 2, 3, 1, 3, 2, 1, 3]
def baseStart_7945276 : Nat := 118140960795 + 7945276 * 2 ^ 59
def prefixEnd_7945276 : Nat := 4983230072969 + 3 ^ 40 * 7945276 * 2
def baseEnd_7945276 : Nat := 4079745520632161304810347

theorem tailTrace_7945276 : CollatzResearch.WordTrace tailWord_7945276 prefixEnd_7945276 4079745520632161304810347 := by
  unfold tailWord_7945276
  simp only [CollatzResearch.WordTrace]
  refine ⟨144894011381814735976995841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193192015175752981302661121 144894011381814735976995841)
  ·
    refine ⟨108670508536361051982746881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144894011381814735976995841 108670508536361051982746881)
    ·
      refine ⟨81502881402270788987060161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108670508536361051982746881 81502881402270788987060161)
      ·
        refine ⟨61127161051703091740295121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81502881402270788987060161 61127161051703091740295121)
        ·
          refine ⟨45845370788777318805221341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61127161051703091740295121 45845370788777318805221341)
          ·
            refine ⟨17192014045791494551958003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45845370788777318805221341 17192014045791494551958003)
            ·
              refine ⟨25788021068687241827937005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17192014045791494551958003 25788021068687241827937005)
              ·
                refine ⟨9670507900757715685476377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25788021068687241827937005 9670507900757715685476377)
                ·
                  refine ⟨7252880925568286764107283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9670507900757715685476377 7252880925568286764107283)
                  ·
                    refine ⟨10879321388352430146160925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7252880925568286764107283 10879321388352430146160925)
                    ·
                      refine ⟨4079745520632161304810347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10879321388352430146160925 4079745520632161304810347)
                      ·
                        rfl

theorem cell23_7945276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 3, 2, 1, 3].length) (baseStart_7945276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7945276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7945276 prefixEnd_7945276 := by exact prefixLift 7945276
  have htrace : WordTrace (prefixWord ++ tailWord_7945276) baseStart_7945276 baseEnd_7945276 := by
    simpa [prefixWord, tailWord_7945276, baseEnd_7945276] using wordTrace_append hprefix tailTrace_7945276
  have hstable : (prefixWord ++ tailWord_7945276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7945276).length < 2 ^ (prefixWord ++ tailWord_7945276).sum := by decide
  have hdescent : baseEnd_7945276 < baseStart_7945276 := by decide
  rcases family_descends (prefixWord ++ tailWord_7945276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7945305 : List Nat := [1, 2, 1, 2, 2, 1, 2, 1, 11]
def baseStart_7945305 : Nat := 118140960795 + 7945305 * 2 ^ 59
def prefixEnd_7945305 : Nat := 4983230072969 + 3 ^ 40 * 7945305 * 2
def baseEnd_7945305 : Nat := 453306712396793521260857

theorem tailTrace_7945305 : CollatzResearch.WordTrace tailWord_7945305 prefixEnd_7945305 453306712396793521260857 := by
  unfold tailWord_7945305
  simp only [CollatzResearch.WordTrace]
  refine ⟨289789080480524409906797369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193192720320349606604531579 289789080480524409906797369)
  ·
    refine ⟨217341810360393307430098027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289789080480524409906797369 217341810360393307430098027)
    ·
      refine ⟨326012715540589961145147041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217341810360393307430098027 326012715540589961145147041)
      ·
        refine ⟨244509536655442470858860281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 326012715540589961145147041 244509536655442470858860281)
        ·
          refine ⟨183382152491581853144145211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 244509536655442470858860281 183382152491581853144145211)
          ·
            refine ⟨275073228737372779716217817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183382152491581853144145211 275073228737372779716217817)
            ·
              refine ⟨206304921553029584787163363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 275073228737372779716217817 206304921553029584787163363)
              ·
                refine ⟨309457382329544377180745045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 206304921553029584787163363 309457382329544377180745045)
                ·
                  refine ⟨453306712396793521260857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 309457382329544377180745045 453306712396793521260857)
                  ·
                    rfl

theorem cell23_7945305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 11].length) (baseStart_7945305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7945305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7945305 prefixEnd_7945305 := by exact prefixLift 7945305
  have htrace : WordTrace (prefixWord ++ tailWord_7945305) baseStart_7945305 baseEnd_7945305 := by
    simpa [prefixWord, tailWord_7945305, baseEnd_7945305] using wordTrace_append hprefix tailTrace_7945305
  have hstable : (prefixWord ++ tailWord_7945305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7945305).length < 2 ^ (prefixWord ++ tailWord_7945305).sum := by decide
  have hdescent : baseEnd_7945305 < baseStart_7945305 := by decide
  rcases family_descends (prefixWord ++ tailWord_7945305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7945310 : List Nat := [4, 4, 1, 1, 1, 1, 1, 4, 2, 1, 3]
def baseStart_7945310 : Nat := 118140960795 + 7945310 * 2 ^ 59
def prefixEnd_7945310 : Nat := 4983230072969 + 3 ^ 40 * 7945310 * 2
def baseEnd_7945310 : Nat := 4079762978974414171785191

theorem tailTrace_7945310 : CollatzResearch.WordTrace tailWord_7945310 prefixEnd_7945310 4079762978974414171785191 := by
  unfold tailWord_7945310
  simp only [CollatzResearch.WordTrace]
  refine ⟨36223657855688286970091173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 193192841897004197173819589 36223657855688286970091173)
  ·
    refine ⟨6791935847941553806892095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36223657855688286970091173 6791935847941553806892095)
    ·
      refine ⟨10187903771912330710338143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6791935847941553806892095 10187903771912330710338143)
      ·
        refine ⟨15281855657868496065507215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10187903771912330710338143 15281855657868496065507215)
        ·
          refine ⟨22922783486802744098260823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15281855657868496065507215 22922783486802744098260823)
          ·
            refine ⟨34384175230204116147391235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22922783486802744098260823 34384175230204116147391235)
            ·
              refine ⟨51576262845306174221086853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34384175230204116147391235 51576262845306174221086853)
              ·
                refine ⟨9670549283494907666453785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51576262845306174221086853 9670549283494907666453785)
                ·
                  refine ⟨7252911962621180749840339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9670549283494907666453785 7252911962621180749840339)
                  ·
                    refine ⟨10879367943931771124760509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7252911962621180749840339 10879367943931771124760509)
                    ·
                      refine ⟨4079762978974414171785191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10879367943931771124760509 4079762978974414171785191)
                      ·
                        rfl

theorem cell23_7945310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 4, 2, 1, 3].length) (baseStart_7945310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7945310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7945310 prefixEnd_7945310 := by exact prefixLift 7945310
  have htrace : WordTrace (prefixWord ++ tailWord_7945310) baseStart_7945310 baseEnd_7945310 := by
    simpa [prefixWord, tailWord_7945310, baseEnd_7945310] using wordTrace_append hprefix tailTrace_7945310
  have hstable : (prefixWord ++ tailWord_7945310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7945310).length < 2 ^ (prefixWord ++ tailWord_7945310).sum := by decide
  have hdescent : baseEnd_7945310 < baseStart_7945310 := by decide
  rcases family_descends (prefixWord ++ tailWord_7945310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7945312 : List Nat := [2, 1, 1, 3, 2, 2, 2, 2, 2, 2, 4]
def baseStart_7945312 : Nat := 118140960795 + 7945312 * 2 ^ 59
def prefixEnd_7945312 : Nat := 4983230072969 + 3 ^ 40 * 7945312 * 2
def baseEnd_7945312 : Nat := 4079764005935723163960181

theorem tailTrace_7945312 : CollatzResearch.WordTrace tailWord_7945312 prefixEnd_7945312 4079764005935723163960181 := by
  unfold tailWord_7945312
  simp only [CollatzResearch.WordTrace]
  refine ⟨144894667895749525051151095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193192890527666033401534793 144894667895749525051151095)
  ·
    refine ⟨217342001843624287576726643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144894667895749525051151095 217342001843624287576726643)
    ·
      refine ⟨326013002765436431365089965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217342001843624287576726643 326013002765436431365089965)
      ·
        refine ⟨122254876037038661761908737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 326013002765436431365089965 122254876037038661761908737)
        ·
          refine ⟨91691157027778996321431553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122254876037038661761908737 91691157027778996321431553)
          ·
            refine ⟨68768367770834247241073665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91691157027778996321431553 68768367770834247241073665)
            ·
              refine ⟨51576275828125685430805249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68768367770834247241073665 51576275828125685430805249)
              ·
                refine ⟨38682206871094264073103937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51576275828125685430805249 38682206871094264073103937)
                ·
                  refine ⟨29011655153320698054827953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38682206871094264073103937 29011655153320698054827953)
                  ·
                    refine ⟨21758741364990523541120965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29011655153320698054827953 21758741364990523541120965)
                    ·
                      refine ⟨4079764005935723163960181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21758741364990523541120965 4079764005935723163960181)
                      ·
                        rfl

theorem cell23_7945312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 2, 2, 2, 4].length) (baseStart_7945312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7945312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7945312 prefixEnd_7945312 := by exact prefixLift 7945312
  have htrace : WordTrace (prefixWord ++ tailWord_7945312) baseStart_7945312 baseEnd_7945312 := by
    simpa [prefixWord, tailWord_7945312, baseEnd_7945312] using wordTrace_append hprefix tailTrace_7945312
  have hstable : (prefixWord ++ tailWord_7945312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7945312).length < 2 ^ (prefixWord ++ tailWord_7945312).sum := by decide
  have hdescent : baseEnd_7945312 < baseStart_7945312 := by decide
  rcases family_descends (prefixWord ++ tailWord_7945312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7945399 : List Nat := [1, 1, 3, 1, 4, 1, 1, 4, 3, 4]
def baseStart_7945399 : Nat := 118140960795 + 7945399 * 2 ^ 59
def prefixEnd_7945399 : Nat := 4983230072969 + 3 ^ 40 * 7945399 * 2
def baseEnd_7945399 : Nat := 1359936226250888107857427

theorem tailTrace_7945399 : CollatzResearch.WordTrace tailWord_7945399 prefixEnd_7945399 1359936226250888107857427 := by
  unfold tailWord_7945399
  simp only [CollatzResearch.WordTrace]
  refine ⟨289792508942183863960719251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193195005961455909307146167 289792508942183863960719251)
  ·
    refine ⟨434688763413275795941078877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289792508942183863960719251 434688763413275795941078877)
    ·
      refine ⟨163008286279978423477904579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 434688763413275795941078877 163008286279978423477904579)
      ·
        refine ⟨244512429419967635216856869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163008286279978423477904579 244512429419967635216856869)
        ·
          refine ⟨45846080516243931603160663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 244512429419967635216856869 45846080516243931603160663)
          ·
            refine ⟨68769120774365897404740995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45846080516243931603160663 68769120774365897404740995)
            ·
              refine ⟨103153681161548846107111493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68769120774365897404740995 103153681161548846107111493)
              ·
                refine ⟨19341315217790408645083405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 103153681161548846107111493 19341315217790408645083405)
                ·
                  refine ⟨7252993206671403241906277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19341315217790408645083405 7252993206671403241906277)
                  ·
                    refine ⟨1359936226250888107857427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7252993206671403241906277 1359936226250888107857427)
                    ·
                      rfl

theorem cell23_7945399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 4, 3, 4].length) (baseStart_7945399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7945399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7945399 prefixEnd_7945399 := by exact prefixLift 7945399
  have htrace : WordTrace (prefixWord ++ tailWord_7945399) baseStart_7945399 baseEnd_7945399 := by
    simpa [prefixWord, tailWord_7945399, baseEnd_7945399] using wordTrace_append hprefix tailTrace_7945399
  have hstable : (prefixWord ++ tailWord_7945399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7945399).length < 2 ^ (prefixWord ++ tailWord_7945399).sum := by decide
  have hdescent : baseEnd_7945399 < baseStart_7945399 := by decide
  rcases family_descends (prefixWord ++ tailWord_7945399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7945402 : List Nat := [3, 1, 1, 1, 2, 2, 1, 1, 1, 6, 4]
def baseStart_7945402 : Nat := 118140960795 + 7945402 * 2 ^ 59
def prefixEnd_7945402 : Nat := 4983230072969 + 3 ^ 40 * 7945402 * 2
def baseEnd_7945402 : Nat := 4079810219194627811834767

theorem tailTrace_7945402 : CollatzResearch.WordTrace tailWord_7945402 prefixEnd_7945402 4079810219194627811834767 := by
  unfold tailWord_7945402
  simp only [CollatzResearch.WordTrace]
  refine ⟨72448154590293248868269615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193195078907448663648718973 72448154590293248868269615)
  ·
    refine ⟨108672231885439873302404423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72448154590293248868269615 108672231885439873302404423)
    ·
      refine ⟨163008347828159809953606635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108672231885439873302404423 163008347828159809953606635)
      ·
        refine ⟨244512521742239714930409953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163008347828159809953606635 244512521742239714930409953)
        ·
          refine ⟨183384391306679786197807465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 244512521742239714930409953 183384391306679786197807465)
          ·
            refine ⟨137538293480009839648355599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183384391306679786197807465 137538293480009839648355599)
            ·
              refine ⟨206307440220014759472533399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137538293480009839648355599 206307440220014759472533399)
              ·
                refine ⟨309461160330022139208800099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 206307440220014759472533399 309461160330022139208800099)
                ·
                  refine ⟨464191740495033208813200149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 309461160330022139208800099 464191740495033208813200149)
                  ·
                    refine ⟨21758987835704681663118757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 464191740495033208813200149 21758987835704681663118757)
                    ·
                      refine ⟨4079810219194627811834767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21758987835704681663118757 4079810219194627811834767)
                      ·
                        rfl

theorem cell23_7945402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 1, 1, 6, 4].length) (baseStart_7945402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7945402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7945402 prefixEnd_7945402 := by exact prefixLift 7945402
  have htrace : WordTrace (prefixWord ++ tailWord_7945402) baseStart_7945402 baseEnd_7945402 := by
    simpa [prefixWord, tailWord_7945402, baseEnd_7945402] using wordTrace_append hprefix tailTrace_7945402
  have hstable : (prefixWord ++ tailWord_7945402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7945402).length < 2 ^ (prefixWord ++ tailWord_7945402).sum := by decide
  have hdescent : baseEnd_7945402 < baseStart_7945402 := by decide
  rcases family_descends (prefixWord ++ tailWord_7945402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7945426 : List Nat := [3, 2, 2, 2, 1, 1, 3, 2, 2, 2, 3]
def baseStart_7945426 : Nat := 118140960795 + 7945426 * 2 ^ 59
def prefixEnd_7945426 : Nat := 4983230072969 + 3 ^ 40 * 7945426 * 2
def baseEnd_7945426 : Nat := 4079822542730335717934657

theorem tailTrace_7945426 : CollatzResearch.WordTrace tailWord_7945426 prefixEnd_7945426 4079822542730335717934657 := by
  unfold tailWord_7945426
  simp only [CollatzResearch.WordTrace]
  refine ⟨72448373428271511892988033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193195662475390698381301421 72448373428271511892988033)
  ·
    refine ⟨54336280071203633919741025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72448373428271511892988033 54336280071203633919741025)
    ·
      refine ⟨40752210053402725439805769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54336280071203633919741025 40752210053402725439805769)
      ·
        refine ⟨30564157540052044079854327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40752210053402725439805769 30564157540052044079854327)
        ·
          refine ⟨45846236310078066119781491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30564157540052044079854327 45846236310078066119781491)
          ·
            refine ⟨68769354465117099179672237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45846236310078066119781491 68769354465117099179672237)
            ·
              refine ⟨25788507924418912192377089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68769354465117099179672237 25788507924418912192377089)
              ·
                refine ⟨19341380943314184144282817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25788507924418912192377089 19341380943314184144282817)
                ·
                  refine ⟨14506035707485638108212113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19341380943314184144282817 14506035707485638108212113)
                  ·
                    refine ⟨10879526780614228581159085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14506035707485638108212113 10879526780614228581159085)
                    ·
                      refine ⟨4079822542730335717934657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10879526780614228581159085 4079822542730335717934657)
                      ·
                        rfl

theorem cell23_7945426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 2, 2, 2, 3].length) (baseStart_7945426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7945426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7945426 prefixEnd_7945426 := by exact prefixLift 7945426
  have htrace : WordTrace (prefixWord ++ tailWord_7945426) baseStart_7945426 baseEnd_7945426 := by
    simpa [prefixWord, tailWord_7945426, baseEnd_7945426] using wordTrace_append hprefix tailTrace_7945426
  have hstable : (prefixWord ++ tailWord_7945426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7945426).length < 2 ^ (prefixWord ++ tailWord_7945426).sum := by decide
  have hdescent : baseEnd_7945426 < baseStart_7945426 := by decide
  rcases family_descends (prefixWord ++ tailWord_7945426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7945429 : List Nat := [1, 3, 2, 4, 1, 1, 2, 1, 8]
def baseStart_7945429 : Nat := 118140960795 + 7945429 * 2 ^ 59
def prefixEnd_7945429 : Nat := 4983230072969 + 3 ^ 40 * 7945429 * 2
def baseEnd_7945429 : Nat := 453313787019144356244127

theorem tailTrace_7945429 : CollatzResearch.WordTrace tailWord_7945429 prefixEnd_7945429 453313787019144356244127 := by
  unfold tailWord_7945429
  simp only [CollatzResearch.WordTrace]
  refine ⟨289793603132075179084311341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193195735421383452722874227 289793603132075179084311341)
  ·
    refine ⟨108672601174528192156616753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 289793603132075179084311341 108672601174528192156616753)
    ·
      refine ⟨81504450880896144117462565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108672601174528192156616753 81504450880896144117462565)
      ·
        refine ⟨15282084540168027022024231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81504450880896144117462565 15282084540168027022024231)
        ·
          refine ⟨22923126810252040533036347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15282084540168027022024231 22923126810252040533036347)
          ·
            refine ⟨34384690215378060799554521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22923126810252040533036347 34384690215378060799554521)
            ·
              refine ⟨25788517661533545599665891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34384690215378060799554521 25788517661533545599665891)
              ·
                refine ⟨38682776492300318399498837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25788517661533545599665891 38682776492300318399498837)
                ·
                  refine ⟨453313787019144356244127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38682776492300318399498837 453313787019144356244127)
                  ·
                    rfl

theorem cell23_7945429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 1, 8].length) (baseStart_7945429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7945429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7945429 prefixEnd_7945429 := by exact prefixLift 7945429
  have htrace : WordTrace (prefixWord ++ tailWord_7945429) baseStart_7945429 baseEnd_7945429 := by
    simpa [prefixWord, tailWord_7945429, baseEnd_7945429] using wordTrace_append hprefix tailTrace_7945429
  have hstable : (prefixWord ++ tailWord_7945429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7945429).length < 2 ^ (prefixWord ++ tailWord_7945429).sum := by decide
  have hdescent : baseEnd_7945429 < baseStart_7945429 := by decide
  rcases family_descends (prefixWord ++ tailWord_7945429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7945459 : List Nat := [1, 1, 1, 2, 2, 6, 1, 1, 3, 5]
def baseStart_7945459 : Nat := 118140960795 + 7945459 * 2 ^ 59
def prefixEnd_7945459 : Nat := 4983230072969 + 3 ^ 40 * 7945459 * 2
def baseEnd_7945459 : Nat := 1359946495863978029607335

theorem tailTrace_7945459 : CollatzResearch.WordTrace tailWord_7945459 prefixEnd_7945459 1359946495863978029607335 := by
  unfold tailWord_7945459
  simp only [CollatzResearch.WordTrace]
  refine ⟨289794697321966494207903431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193196464881310996138602287 289794697321966494207903431)
  ·
    refine ⟨434692045982949741311855147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289794697321966494207903431 434692045982949741311855147)
    ·
      refine ⟨652038068974424611967782721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 434692045982949741311855147 652038068974424611967782721)
      ·
        refine ⟨489028551730818458975837041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 652038068974424611967782721 489028551730818458975837041)
        ·
          refine ⟨366771413798113844231877781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 489028551730818458975837041 366771413798113844231877781)
          ·
            refine ⟨17192410021786586448369271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 366771413798113844231877781 17192410021786586448369271)
            ·
              refine ⟨25788615032679879672553907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17192410021786586448369271 25788615032679879672553907)
              ·
                refine ⟨38682922549019819508830861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25788615032679879672553907 38682922549019819508830861)
                ·
                  refine ⟨14506095955882432315811573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38682922549019819508830861 14506095955882432315811573)
                  ·
                    refine ⟨1359946495863978029607335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14506095955882432315811573 1359946495863978029607335)
                    ·
                      rfl

theorem cell23_7945459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 1, 3, 5].length) (baseStart_7945459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7945459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7945459 prefixEnd_7945459 := by exact prefixLift 7945459
  have htrace : WordTrace (prefixWord ++ tailWord_7945459) baseStart_7945459 baseEnd_7945459 := by
    simpa [prefixWord, tailWord_7945459, baseEnd_7945459] using wordTrace_append hprefix tailTrace_7945459
  have hstable : (prefixWord ++ tailWord_7945459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7945459).length < 2 ^ (prefixWord ++ tailWord_7945459).sum := by decide
  have hdescent : baseEnd_7945459 < baseStart_7945459 := by decide
  rcases family_descends (prefixWord ++ tailWord_7945459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7945516 : List Nat := [2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 3]
def baseStart_7945516 : Nat := 118140960795 + 7945516 * 2 ^ 59
def prefixEnd_7945516 : Nat := 4983230072969 + 3 ^ 40 * 7945516 * 2
def baseEnd_7945516 : Nat := 4079868755989240365809243

theorem tailTrace_7945516 : CollatzResearch.WordTrace tailWord_7945516 prefixEnd_7945516 4079868755989240365809243 := by
  unfold tailWord_7945516
  simp only [CollatzResearch.WordTrace]
  refine ⟨144898388141379996471364201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193197850855173328628485601 144898388141379996471364201)
  ·
    refine ⟨108673791106034997353523151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144898388141379996471364201 108673791106034997353523151)
    ·
      refine ⟨163010686659052496030284727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108673791106034997353523151 163010686659052496030284727)
      ·
        refine ⟨244516029988578744045427091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163010686659052496030284727 244516029988578744045427091)
        ·
          refine ⟨366774044982868116068140637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244516029988578744045427091 366774044982868116068140637)
          ·
            refine ⟨137540266868575543525552739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 366774044982868116068140637 137540266868575543525552739)
            ·
              refine ⟨206310400302863315288329109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137540266868575543525552739 206310400302863315288329109)
              ·
                refine ⟨9670800014196717904140427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 206310400302863315288329109 9670800014196717904140427)
                ·
                  refine ⟨14506200021295076856210641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9670800014196717904140427 14506200021295076856210641)
                  ·
                    refine ⟨10879650015971307642157981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14506200021295076856210641 10879650015971307642157981)
                    ·
                      refine ⟨4079868755989240365809243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10879650015971307642157981 4079868755989240365809243)
                      ·
                        rfl

theorem cell23_7945516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 3].length) (baseStart_7945516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7945516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7945516 prefixEnd_7945516 := by exact prefixLift 7945516
  have htrace : WordTrace (prefixWord ++ tailWord_7945516) baseStart_7945516 baseEnd_7945516 := by
    simpa [prefixWord, tailWord_7945516, baseEnd_7945516] using wordTrace_append hprefix tailTrace_7945516
  have hstable : (prefixWord ++ tailWord_7945516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7945516).length < 2 ^ (prefixWord ++ tailWord_7945516).sum := by decide
  have hdescent : baseEnd_7945516 < baseStart_7945516 := by decide
  rcases family_descends (prefixWord ++ tailWord_7945516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7945517 : List Nat := [1, 5, 3, 1, 1, 3, 1, 1, 2, 3, 2]
def baseStart_7945517 : Nat := 118140960795 + 7945517 * 2 ^ 59
def prefixEnd_7945517 : Nat := 4983230072969 + 3 ^ 40 * 7945517 * 2
def baseEnd_7945517 : Nat := 4079869269469894861896739

theorem tailTrace_7945517 : CollatzResearch.WordTrace tailWord_7945517 prefixEnd_7945517 4079869269469894861896739 := by
  unfold tailWord_7945517
  simp only [CollatzResearch.WordTrace]
  refine ⟨289796812755756370113514805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193197875170504246742343203 289796812755756370113514805)
  ·
    refine ⟨27168451195852159698142013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 289796812755756370113514805 27168451195852159698142013)
    ·
      refine ⟨10188169198444559886803255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27168451195852159698142013 10188169198444559886803255)
      ·
        refine ⟨15282253797666839830204883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10188169198444559886803255 15282253797666839830204883)
        ·
          refine ⟨22923380696500259745307325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15282253797666839830204883 22923380696500259745307325)
          ·
            refine ⟨8596267761187597404490247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22923380696500259745307325 8596267761187597404490247)
            ·
              refine ⟨12894401641781396106735371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8596267761187597404490247 12894401641781396106735371)
              ·
                refine ⟨19341602462672094160103057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12894401641781396106735371 19341602462672094160103057)
                ·
                  refine ⟨14506201847004070620077293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19341602462672094160103057 14506201847004070620077293)
                  ·
                    refine ⟨5439825692626526482528985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14506201847004070620077293 5439825692626526482528985)
                    ·
                      refine ⟨4079869269469894861896739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5439825692626526482528985 4079869269469894861896739)
                      ·
                        rfl

theorem cell23_7945517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 1, 1, 2, 3, 2].length) (baseStart_7945517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7945517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7945517 prefixEnd_7945517 := by exact prefixLift 7945517
  have htrace : WordTrace (prefixWord ++ tailWord_7945517) baseStart_7945517 baseEnd_7945517 := by
    simpa [prefixWord, tailWord_7945517, baseEnd_7945517] using wordTrace_append hprefix tailTrace_7945517
  have hstable : (prefixWord ++ tailWord_7945517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7945517).length < 2 ^ (prefixWord ++ tailWord_7945517).sum := by decide
  have hdescent : baseEnd_7945517 < baseStart_7945517 := by decide
  rcases family_descends (prefixWord ++ tailWord_7945517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7945540 : List Nat := [2, 3, 4, 1, 1, 1, 3, 2, 2, 4]
def baseStart_7945540 : Nat := 118140960795 + 7945540 * 2 ^ 59
def prefixEnd_7945540 : Nat := 4983230072969 + 3 ^ 40 * 7945540 * 2
def baseEnd_7945540 : Nat := 1359960359841649423969711

theorem tailTrace_7945540 : CollatzResearch.WordTrace tailWord_7945540 prefixEnd_7945540 1359960359841649423969711 := by
  unfold tailWord_7945540
  simp only [CollatzResearch.WordTrace]
  refine ⟨144898825817336522520801037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193198434423115363361068049 144898825817336522520801037)
  ·
    refine ⟨54337059681501195945300389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144898825817336522520801037 54337059681501195945300389)
    ·
      refine ⟨10188198690281474239743823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54337059681501195945300389 10188198690281474239743823)
      ·
        refine ⟨15282298035422211359615735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10188198690281474239743823 15282298035422211359615735)
        ·
          refine ⟨22923447053133317039423603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15282298035422211359615735 22923447053133317039423603)
          ·
            refine ⟨34385170579699975559135405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22923447053133317039423603 34385170579699975559135405)
            ·
              refine ⟨12894438967387490834675777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34385170579699975559135405 12894438967387490834675777)
              ·
                refine ⟨9670829225540618126006833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12894438967387490834675777 9670829225540618126006833)
                ·
                  refine ⟨7253121919155463594505125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9670829225540618126006833 7253121919155463594505125)
                  ·
                    refine ⟨1359960359841649423969711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7253121919155463594505125 1359960359841649423969711)
                    ·
                      rfl

theorem cell23_7945540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 3, 2, 2, 4].length) (baseStart_7945540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7945540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7945540 prefixEnd_7945540 := by exact prefixLift 7945540
  have htrace : WordTrace (prefixWord ++ tailWord_7945540) baseStart_7945540 baseEnd_7945540 := by
    simpa [prefixWord, tailWord_7945540, baseEnd_7945540] using wordTrace_append hprefix tailTrace_7945540
  have hstable : (prefixWord ++ tailWord_7945540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7945540).length < 2 ^ (prefixWord ++ tailWord_7945540).sum := by decide
  have hdescent : baseEnd_7945540 < baseStart_7945540 := by decide
  rcases family_descends (prefixWord ++ tailWord_7945540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7945569 : List Nat := [1, 2, 3, 1, 1, 1, 1, 4, 2, 3, 4]
def baseStart_7945569 : Nat := 118140960795 + 7945569 * 2 ^ 59
def prefixEnd_7945569 : Nat := 4983230072969 + 3 ^ 40 * 7945569 * 2
def baseEnd_7945569 : Nat := 4079895970463928658446499

theorem tailTrace_7945569 : CollatzResearch.WordTrace tailWord_7945569 prefixEnd_7945569 4079895970463928658446499 := by
  unfold tailWord_7945569
  simp only [CollatzResearch.WordTrace]
  refine ⟨289798709351567982994407761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193199139567711988662938507 289798709351567982994407761)
  ·
    refine ⟨217349032013675987245805821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289798709351567982994407761 217349032013675987245805821)
    ·
      refine ⟨81505887005128495217177183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 217349032013675987245805821 81505887005128495217177183)
      ·
        refine ⟨122258830507692742825765775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81505887005128495217177183 122258830507692742825765775)
        ·
          refine ⟨183388245761539114238648663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122258830507692742825765775 183388245761539114238648663)
          ·
            refine ⟨275082368642308671357972995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183388245761539114238648663 275082368642308671357972995)
            ·
              refine ⟨412623552963463007036959493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 275082368642308671357972995 412623552963463007036959493)
              ·
                refine ⟨77366916180649313819429905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 412623552963463007036959493 77366916180649313819429905)
                ·
                  refine ⟨58025187135486985364572429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77366916180649313819429905 58025187135486985364572429)
                  ·
                    refine ⟨21759445175807619511714661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58025187135486985364572429 21759445175807619511714661)
                    ·
                      refine ⟨4079895970463928658446499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21759445175807619511714661 4079895970463928658446499)
                      ·
                        rfl

theorem cell23_7945569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 4, 2, 3, 4].length) (baseStart_7945569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7945569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7945569 prefixEnd_7945569 := by exact prefixLift 7945569
  have htrace : WordTrace (prefixWord ++ tailWord_7945569) baseStart_7945569 baseEnd_7945569 := by
    simpa [prefixWord, tailWord_7945569, baseEnd_7945569] using wordTrace_append hprefix tailTrace_7945569
  have hstable : (prefixWord ++ tailWord_7945569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7945569).length < 2 ^ (prefixWord ++ tailWord_7945569).sum := by decide
  have hdescent : baseEnd_7945569 < baseStart_7945569 := by decide
  rcases family_descends (prefixWord ++ tailWord_7945569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7945598 : List Nat := [4, 2, 3, 2, 1, 1, 3, 2, 1, 2, 2]
def baseStart_7945598 : Nat := 118140960795 + 7945598 * 2 ^ 59
def prefixEnd_7945598 : Nat := 4983230072969 + 3 ^ 40 * 7945598 * 2
def baseEnd_7945598 : Nat := 4079910861402909044983867

theorem tailTrace_7945598 : CollatzResearch.WordTrace tailWord_7945598 prefixEnd_7945598 4079910861402909044983867 := by
  unfold tailWord_7945598
  simp only [CollatzResearch.WordTrace]
  refine ⟨36224970883557865118401681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 193199844712308613964808965 36224970883557865118401681)
  ·
    refine ⟨27168728162668398838801261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36224970883557865118401681 27168728162668398838801261)
    ·
      refine ⟨10188273061000649564550473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27168728162668398838801261 10188273061000649564550473)
      ·
        refine ⟨7641204795750487173412855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10188273061000649564550473 7641204795750487173412855)
        ·
          refine ⟨11461807193625730760119283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7641204795750487173412855 11461807193625730760119283)
          ·
            refine ⟨17192710790438596140178925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11461807193625730760119283 17192710790438596140178925)
            ·
              refine ⟨6447266546414473552567097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17192710790438596140178925 6447266546414473552567097)
              ·
                refine ⟨4835449909810855164425323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6447266546414473552567097 4835449909810855164425323)
                ·
                  refine ⟨7253174864716282746637985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4835449909810855164425323 7253174864716282746637985)
                  ·
                    refine ⟨5439881148537212059978489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7253174864716282746637985 5439881148537212059978489)
                    ·
                      refine ⟨4079910861402909044983867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5439881148537212059978489 4079910861402909044983867)
                      ·
                        rfl

theorem cell23_7945598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 3, 2, 1, 2, 2].length) (baseStart_7945598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7945598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7945598 prefixEnd_7945598 := by exact prefixLift 7945598
  have htrace : WordTrace (prefixWord ++ tailWord_7945598) baseStart_7945598 baseEnd_7945598 := by
    simpa [prefixWord, tailWord_7945598, baseEnd_7945598] using wordTrace_append hprefix tailTrace_7945598
  have hstable : (prefixWord ++ tailWord_7945598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7945598).length < 2 ^ (prefixWord ++ tailWord_7945598).sum := by decide
  have hdescent : baseEnd_7945598 < baseStart_7945598 := by decide
  rcases family_descends (prefixWord ++ tailWord_7945598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7945614 : List Nat := [4, 1, 1, 4, 2, 2, 2, 1, 2, 1, 3]
def baseStart_7945614 : Nat := 118140960795 + 7945614 * 2 ^ 59
def prefixEnd_7945614 : Nat := 4983230072969 + 3 ^ 40 * 7945614 * 2
def baseEnd_7945614 : Nat := 4079919077093380982383793

theorem tailTrace_7945614 : CollatzResearch.WordTrace tailWord_7945614 prefixEnd_7945614 4079919077093380982383793 := by
  unfold tailWord_7945614
  simp only [CollatzResearch.WordTrace]
  refine ⟨36225043829550619459974487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 193200233757603303786530597 36225043829550619459974487)
  ·
    refine ⟨54337565744325929189961731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36225043829550619459974487 54337565744325929189961731)
    ·
      refine ⟨81506348616488893784942597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54337565744325929189961731 81506348616488893784942597)
      ·
        refine ⟨15282440365591667584676737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81506348616488893784942597 15282440365591667584676737)
        ·
          refine ⟨11461830274193750688507553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15282440365591667584676737 11461830274193750688507553)
          ·
            refine ⟨8596372705645313016380665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11461830274193750688507553 8596372705645313016380665)
            ·
              refine ⟨6447279529233984762285499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8596372705645313016380665 6447279529233984762285499)
              ·
                refine ⟨9670919293850977143428249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6447279529233984762285499 9670919293850977143428249)
                ·
                  refine ⟨7253189470388232857571187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9670919293850977143428249 7253189470388232857571187)
                  ·
                    refine ⟨10879784205582349286356781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7253189470388232857571187 10879784205582349286356781)
                    ·
                      refine ⟨4079919077093380982383793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10879784205582349286356781 4079919077093380982383793)
                      ·
                        rfl

theorem cell23_7945614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 2, 1, 2, 1, 3].length) (baseStart_7945614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7945614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7945614 prefixEnd_7945614 := by exact prefixLift 7945614
  have htrace : WordTrace (prefixWord ++ tailWord_7945614) baseStart_7945614 baseEnd_7945614 := by
    simpa [prefixWord, tailWord_7945614, baseEnd_7945614] using wordTrace_append hprefix tailTrace_7945614
  have hstable : (prefixWord ++ tailWord_7945614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7945614).length < 2 ^ (prefixWord ++ tailWord_7945614).sum := by decide
  have hdescent : baseEnd_7945614 < baseStart_7945614 := by decide
  rcases family_descends (prefixWord ++ tailWord_7945614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7945624 : List Nat := [2, 1, 2, 5, 3, 1, 1, 2, 1, 3, 2]
def baseStart_7945624 : Nat := 118140960795 + 7945624 * 2 ^ 59
def prefixEnd_7945624 : Nat := 4983230072969 + 3 ^ 40 * 7945624 * 2
def baseEnd_7945624 : Nat := 4079924211899925943258747

theorem tailTrace_7945624 : CollatzResearch.WordTrace tailWord_7945624 prefixEnd_7945624 4079924211899925943258747 := by
  unfold tailWord_7945624
  simp only [CollatzResearch.WordTrace]
  refine ⟨144900357683184363693829963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193200476910912484925106617 144900357683184363693829963)
  ·
    refine ⟨217350536524776545540744945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144900357683184363693829963 217350536524776545540744945)
    ·
      refine ⟨163012902393582409155558709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217350536524776545540744945 163012902393582409155558709)
      ·
        refine ⟨15282459599398350858333629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 163012902393582409155558709 15282459599398350858333629)
        ·
          refine ⟨5730922349774381571875111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15282459599398350858333629 5730922349774381571875111)
          ·
            refine ⟨8596383524661572357812667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5730922349774381571875111 8596383524661572357812667)
            ·
              refine ⟨12894575286992358536719001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8596383524661572357812667 12894575286992358536719001)
              ·
                refine ⟨9670931465244268902539251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12894575286992358536719001 9670931465244268902539251)
                ·
                  refine ⟨14506397197866403353808877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9670931465244268902539251 14506397197866403353808877)
                  ·
                    refine ⟨5439898949199901257678329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14506397197866403353808877 5439898949199901257678329)
                    ·
                      refine ⟨4079924211899925943258747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5439898949199901257678329 4079924211899925943258747)
                      ·
                        rfl

theorem cell23_7945624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 1, 2, 1, 3, 2].length) (baseStart_7945624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7945624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7945624 prefixEnd_7945624 := by exact prefixLift 7945624
  have htrace : WordTrace (prefixWord ++ tailWord_7945624) baseStart_7945624 baseEnd_7945624 := by
    simpa [prefixWord, tailWord_7945624, baseEnd_7945624] using wordTrace_append hprefix tailTrace_7945624
  have hstable : (prefixWord ++ tailWord_7945624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7945624).length < 2 ^ (prefixWord ++ tailWord_7945624).sum := by decide
  have hdescent : baseEnd_7945624 < baseStart_7945624 := by decide
  rcases family_descends (prefixWord ++ tailWord_7945624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7945636 : List Nat := [2, 3, 1, 2, 1, 1, 1, 2, 4, 3, 3]
def baseStart_7945636 : Nat := 118140960795 + 7945636 * 2 ^ 59
def prefixEnd_7945636 : Nat := 4983230072969 + 3 ^ 40 * 7945636 * 2
def baseEnd_7945636 : Nat := 4079930373667779896308691

theorem tailTrace_7945636 : CollatzResearch.WordTrace tailWord_7945636 prefixEnd_7945636 4079930373667779896308691 := by
  unfold tailWord_7945636
  simp only [CollatzResearch.WordTrace]
  refine ⟨144900576521162626718548381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193200768694883502291397841 144900576521162626718548381)
  ·
    refine ⟨54337716195435985019455643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144900576521162626718548381 54337716195435985019455643)
    ·
      refine ⟨81506574293153977529183465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54337716195435985019455643 81506574293153977529183465)
      ·
        refine ⟨61129930719865483146887599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81506574293153977529183465 61129930719865483146887599)
        ·
          refine ⟨91694896079798224720331399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61129930719865483146887599 91694896079798224720331399)
          ·
            refine ⟨137542344119697337080497099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91694896079798224720331399 137542344119697337080497099)
            ·
              refine ⟨206313516179546005620745649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137542344119697337080497099 206313516179546005620745649)
              ·
                refine ⟨154735137134659504215559237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 206313516179546005620745649 154735137134659504215559237)
                ·
                  refine ⟨29012838212748657040417357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 154735137134659504215559237 29012838212748657040417357)
                  ·
                    refine ⟨10879814329780746390156509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29012838212748657040417357 10879814329780746390156509)
                    ·
                      refine ⟨4079930373667779896308691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10879814329780746390156509 4079930373667779896308691)
                      ·
                        rfl

theorem cell23_7945636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 2, 4, 3, 3].length) (baseStart_7945636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7945636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7945636 prefixEnd_7945636 := by exact prefixLift 7945636
  have htrace : WordTrace (prefixWord ++ tailWord_7945636) baseStart_7945636 baseEnd_7945636 := by
    simpa [prefixWord, tailWord_7945636, baseEnd_7945636] using wordTrace_append hprefix tailTrace_7945636
  have hstable : (prefixWord ++ tailWord_7945636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7945636).length < 2 ^ (prefixWord ++ tailWord_7945636).sum := by decide
  have hdescent : baseEnd_7945636 < baseStart_7945636 := by decide
  rcases family_descends (prefixWord ++ tailWord_7945636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7945656 : List Nat := [2, 1, 2, 1, 2, 2, 4, 2, 2, 5]
def baseStart_7945656 : Nat := 118140960795 + 7945656 * 2 ^ 59
def prefixEnd_7945656 : Nat := 4983230072969 + 3 ^ 40 * 7945656 * 2
def baseEnd_7945656 : Nat := 1359980214426956606019533

theorem tailTrace_7945656 : CollatzResearch.WordTrace tailWord_7945656 prefixEnd_7945656 1359980214426956606019533 := by
  unfold tailWord_7945656
  simp only [CollatzResearch.WordTrace]
  refine ⟨144900941251126398426412411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193201255001501864568549881 144900941251126398426412411)
  ·
    refine ⟨217351411876689597639618617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144900941251126398426412411 217351411876689597639618617)
    ·
      refine ⟨163013558907517198229713963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217351411876689597639618617 163013558907517198229713963)
      ·
        refine ⟨244520338361275797344570945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163013558907517198229713963 244520338361275797344570945)
        ·
          refine ⟨183390253770956848008428209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 244520338361275797344570945 183390253770956848008428209)
          ·
            refine ⟨137542690328217636006321157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183390253770956848008428209 137542690328217636006321157)
            ·
              refine ⟨25789254436540806751185217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 137542690328217636006321157 25789254436540806751185217)
              ·
                refine ⟨19341940827405605063388913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25789254436540806751185217 19341940827405605063388913)
                ·
                  refine ⟨14506455620554203797541685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19341940827405605063388913 14506455620554203797541685)
                  ·
                    refine ⟨1359980214426956606019533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14506455620554203797541685 1359980214426956606019533)
                    ·
                      rfl

theorem cell23_7945656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 2, 2, 5].length) (baseStart_7945656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7945656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7945656 prefixEnd_7945656 := by exact prefixLift 7945656
  have htrace : WordTrace (prefixWord ++ tailWord_7945656) baseStart_7945656 baseEnd_7945656 := by
    simpa [prefixWord, tailWord_7945656, baseEnd_7945656] using wordTrace_append hprefix tailTrace_7945656
  have hstable : (prefixWord ++ tailWord_7945656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7945656).length < 2 ^ (prefixWord ++ tailWord_7945656).sum := by decide
  have hdescent : baseEnd_7945656 < baseStart_7945656 := by decide
  rcases family_descends (prefixWord ++ tailWord_7945656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7945660 : List Nat := [2, 2, 2, 4, 2, 1, 1, 4, 5]
def baseStart_7945660 : Nat := 118140960795 + 7945660 * 2 ^ 59
def prefixEnd_7945660 : Nat := 4983230072969 + 3 ^ 40 * 7945660 * 2
def baseEnd_7945660 : Nat := 453326966355943089156509

theorem tailTrace_7945660 : CollatzResearch.WordTrace tailWord_7945660 prefixEnd_7945660 453326966355943089156509 := by
  unfold tailWord_7945660
  simp only [CollatzResearch.WordTrace]
  refine ⟨144901014197119152767985217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193201352262825537023980289 144901014197119152767985217)
  ·
    refine ⟨108675760647839364575988913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144901014197119152767985217 108675760647839364575988913)
    ·
      refine ⟨81506820485879523431991685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108675760647839364575988913 81506820485879523431991685)
      ·
        refine ⟨15282528841102410643498441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81506820485879523431991685 15282528841102410643498441)
        ·
          refine ⟨11461896630826807982623831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15282528841102410643498441 11461896630826807982623831)
          ·
            refine ⟨17192844946240211973935747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11461896630826807982623831 17192844946240211973935747)
            ·
              refine ⟨25789267419360317960903621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17192844946240211973935747 25789267419360317960903621)
              ·
                refine ⟨4835487641130059617669429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25789267419360317960903621 4835487641130059617669429)
                ·
                  refine ⟨453326966355943089156509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4835487641130059617669429 453326966355943089156509)
                  ·
                    rfl

theorem cell23_7945660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 4, 5].length) (baseStart_7945660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7945660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7945660 prefixEnd_7945660 := by exact prefixLift 7945660
  have htrace : WordTrace (prefixWord ++ tailWord_7945660) baseStart_7945660 baseEnd_7945660 := by
    simpa [prefixWord, tailWord_7945660, baseEnd_7945660] using wordTrace_append hprefix tailTrace_7945660
  have hstable : (prefixWord ++ tailWord_7945660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7945660).length < 2 ^ (prefixWord ++ tailWord_7945660).sum := by decide
  have hdescent : baseEnd_7945660 < baseStart_7945660 := by decide
  rcases family_descends (prefixWord ++ tailWord_7945660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7945693 : List Nat := [1, 4, 3, 1, 1, 3, 1, 1, 1, 3, 4]
def baseStart_7945693 : Nat := 118140960795 + 7945693 * 2 ^ 59
def prefixEnd_7945693 : Nat := 4983230072969 + 3 ^ 40 * 7945693 * 2
def baseEnd_7945693 : Nat := 4079959642065086173295929

theorem tailTrace_7945693 : CollatzResearch.WordTrace tailWord_7945693 prefixEnd_7945693 4079959642065086173295929 := by
  unfold tailWord_7945693
  simp only [CollatzResearch.WordTrace]
  refine ⟨289803232003118752171921733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193202154668745834781281155 289803232003118752171921733)
  ·
    refine ⟨54338106000584766032235325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 289803232003118752171921733 54338106000584766032235325)
    ·
      refine ⟨20376789750219287262088247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54338106000584766032235325 20376789750219287262088247)
      ·
        refine ⟨30565184625328930893132371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20376789750219287262088247 30565184625328930893132371)
        ·
          refine ⟨45847776937993396339698557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30565184625328930893132371 45847776937993396339698557)
          ·
            refine ⟨17192916351747523627386959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45847776937993396339698557 17192916351747523627386959)
            ·
              refine ⟨25789374527621285441080439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17192916351747523627386959 25789374527621285441080439)
              ·
                refine ⟨38684061791431928161620659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25789374527621285441080439 38684061791431928161620659)
                ·
                  refine ⟨58026092687147892242430989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38684061791431928161620659 58026092687147892242430989)
                  ·
                    refine ⟨21759784757680459590911621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58026092687147892242430989 21759784757680459590911621)
                    ·
                      refine ⟨4079959642065086173295929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21759784757680459590911621 4079959642065086173295929)
                      ·
                        rfl

theorem cell23_7945693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 1, 1, 3, 4].length) (baseStart_7945693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7945693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7945693 prefixEnd_7945693 := by exact prefixLift 7945693
  have htrace : WordTrace (prefixWord ++ tailWord_7945693) baseStart_7945693 baseEnd_7945693 := by
    simpa [prefixWord, tailWord_7945693, baseEnd_7945693] using wordTrace_append hprefix tailTrace_7945693
  have hstable : (prefixWord ++ tailWord_7945693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7945693).length < 2 ^ (prefixWord ++ tailWord_7945693).sum := by decide
  have hdescent : baseEnd_7945693 < baseStart_7945693 := by decide
  rcases family_descends (prefixWord ++ tailWord_7945693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7945720 : List Nat := [2, 1, 2, 1, 1, 5, 2, 4, 1, 4]
def baseStart_7945720 : Nat := 118140960795 + 7945720 * 2 ^ 59
def prefixEnd_7945720 : Nat := 4983230072969 + 3 ^ 40 * 7945720 * 2
def baseEnd_7945720 : Nat := 1359991168680919189219435

theorem tailTrace_7945720 : CollatzResearch.WordTrace tailWord_7945720 prefixEnd_7945720 1359991168680919189219435 := by
  unfold tailWord_7945720
  simp only [CollatzResearch.WordTrace]
  refine ⟨144902108387010467891577307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193202811182680623855436409 144902108387010467891577307)
  ·
    refine ⟨217353162580515701837365961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144902108387010467891577307 217353162580515701837365961)
    ·
      refine ⟨163014871935386776378024471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217353162580515701837365961 163014871935386776378024471)
      ·
        refine ⟨244522307903080164567036707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163014871935386776378024471 244522307903080164567036707)
        ·
          refine ⟨366783461854620246850555061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244522307903080164567036707 366783461854620246850555061)
          ·
            refine ⟨34385949548870648142239537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 366783461854620246850555061 34385949548870648142239537)
            ·
              refine ⟨25789462161652986106679653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34385949548870648142239537 25789462161652986106679653)
              ·
                refine ⟨4835524155309934895002435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25789462161652986106679653 4835524155309934895002435)
                ·
                  refine ⟨7253286232964902342503653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4835524155309934895002435 7253286232964902342503653)
                  ·
                    refine ⟨1359991168680919189219435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7253286232964902342503653 1359991168680919189219435)
                    ·
                      rfl

theorem cell23_7945720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 4, 1, 4].length) (baseStart_7945720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7945720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7945720 prefixEnd_7945720 := by exact prefixLift 7945720
  have htrace : WordTrace (prefixWord ++ tailWord_7945720) baseStart_7945720 baseEnd_7945720 := by
    simpa [prefixWord, tailWord_7945720, baseEnd_7945720] using wordTrace_append hprefix tailTrace_7945720
  have hstable : (prefixWord ++ tailWord_7945720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7945720).length < 2 ^ (prefixWord ++ tailWord_7945720).sum := by decide
  have hdescent : baseEnd_7945720 < baseStart_7945720 := by decide
  rcases family_descends (prefixWord ++ tailWord_7945720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7945730 : List Nat := [3, 4, 1, 2, 1, 1, 1, 2, 1, 4, 3]
def baseStart_7945730 : Nat := 118140960795 + 7945730 * 2 ^ 59
def prefixEnd_7945730 : Nat := 4983230072969 + 3 ^ 40 * 7945730 * 2
def baseEnd_7945730 : Nat := 4079978640849302528533259

theorem tailTrace_7945730 : CollatzResearch.WordTrace tailWord_7945730 prefixEnd_7945730 4079978640849302528533259 := by
  unfold tailWord_7945730
  simp only [CollatzResearch.WordTrace]
  refine ⟨72451145375996176872754661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193203054335989804994012429 72451145375996176872754661)
  ·
    refine ⟨13584589757999283163641499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72451145375996176872754661 13584589757999283163641499)
    ·
      refine ⟨20376884636998924745462249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13584589757999283163641499 20376884636998924745462249)
      ·
        refine ⟨15282663477749193559096687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20376884636998924745462249 15282663477749193559096687)
        ·
          refine ⟨22923995216623790338645031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15282663477749193559096687 22923995216623790338645031)
          ·
            refine ⟨34385992824935685507967547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22923995216623790338645031 34385992824935685507967547)
            ·
              refine ⟨51578989237403528261951321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34385992824935685507967547 51578989237403528261951321)
              ·
                refine ⟨38684241928052646196463491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51578989237403528261951321 38684241928052646196463491)
                ·
                  refine ⟨58026362892078969294695237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38684241928052646196463491 58026362892078969294695237)
                  ·
                    refine ⟨10879943042264806742755357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58026362892078969294695237 10879943042264806742755357)
                    ·
                      refine ⟨4079978640849302528533259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10879943042264806742755357 4079978640849302528533259)
                      ·
                        rfl

theorem cell23_7945730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 2, 1, 4, 3].length) (baseStart_7945730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7945730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7945730 prefixEnd_7945730 := by exact prefixLift 7945730
  have htrace : WordTrace (prefixWord ++ tailWord_7945730) baseStart_7945730 baseEnd_7945730 := by
    simpa [prefixWord, tailWord_7945730, baseEnd_7945730] using wordTrace_append hprefix tailTrace_7945730
  have hstable : (prefixWord ++ tailWord_7945730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7945730).length < 2 ^ (prefixWord ++ tailWord_7945730).sum := by decide
  have hdescent : baseEnd_7945730 < baseStart_7945730 := by decide
  rcases family_descends (prefixWord ++ tailWord_7945730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7945793 : List Nat := [1, 2, 5, 1, 1, 1, 2, 3, 1, 6]
def baseStart_7945793 : Nat := 118140960795 + 7945793 * 2 ^ 59
def prefixEnd_7945793 : Nat := 4983230072969 + 3 ^ 40 * 7945793 * 2
def baseEnd_7945793 : Nat := 1360003663376845260681823

theorem tailTrace_7945793 : CollatzResearch.WordTrace tailWord_7945793 prefixEnd_7945793 1360003663376845260681823 := by
  unfold tailWord_7945793
  simp only [CollatzResearch.WordTrace]
  refine ⟨289806879302756469250562033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193204586201837646167041355 289806879302756469250562033)
  ·
    refine ⟨217355159477067351937921525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289806879302756469250562033 217355159477067351937921525)
    ·
      refine ⟨20377046200975064244180143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 217355159477067351937921525 20377046200975064244180143)
      ·
        refine ⟨30565569301462596366270215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20377046200975064244180143 30565569301462596366270215)
        ·
          refine ⟨45848353952193894549405323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30565569301462596366270215 45848353952193894549405323)
          ·
            refine ⟨68772530928290841824107985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45848353952193894549405323 68772530928290841824107985)
            ·
              refine ⟨51579398196218131368080989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68772530928290841824107985 51579398196218131368080989)
              ·
                refine ⟨19342274323581799263030371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51579398196218131368080989 19342274323581799263030371)
                ·
                  refine ⟨29013411485372698894545557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19342274323581799263030371 29013411485372698894545557)
                  ·
                    refine ⟨1360003663376845260681823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29013411485372698894545557 1360003663376845260681823)
                    ·
                      rfl

theorem cell23_7945793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 3, 1, 6].length) (baseStart_7945793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7945793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7945793 prefixEnd_7945793 := by exact prefixLift 7945793
  have htrace : WordTrace (prefixWord ++ tailWord_7945793) baseStart_7945793 baseEnd_7945793 := by
    simpa [prefixWord, tailWord_7945793, baseEnd_7945793] using wordTrace_append hprefix tailTrace_7945793
  have hstable : (prefixWord ++ tailWord_7945793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7945793).length < 2 ^ (prefixWord ++ tailWord_7945793).sum := by decide
  have hdescent : baseEnd_7945793 < baseStart_7945793 := by decide
  rcases family_descends (prefixWord ++ tailWord_7945793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7945820 : List Nat := [2, 2, 4, 1, 2, 1, 3, 1, 1, 1, 5]
def baseStart_7945820 : Nat := 118140960795 + 7945820 * 2 ^ 59
def prefixEnd_7945820 : Nat := 4983230072969 + 3 ^ 40 * 7945820 * 2
def baseEnd_7945820 : Nat := 4080024854108207176407845

theorem tailTrace_7945820 : CollatzResearch.WordTrace tailWord_7945820 prefixEnd_7945820 4080024854108207176407845 := by
  unfold tailWord_7945820
  simp only [CollatzResearch.WordTrace]
  refine ⟨144903932036829326430897457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193205242715772435241196609 144903932036829326430897457)
  ·
    refine ⟨108677949027621994823173093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144903932036829326430897457 108677949027621994823173093)
    ·
      refine ⟨20377115442679124029344955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108677949027621994823173093 20377115442679124029344955)
      ·
        refine ⟨30565673164018686044017433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20377115442679124029344955 30565673164018686044017433)
        ·
          refine ⟨22924254873014014533013075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30565673164018686044017433 22924254873014014533013075)
          ·
            refine ⟨34386382309521021799519613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22924254873014014533013075 34386382309521021799519613)
            ·
              refine ⟨12894893366070383174819855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34386382309521021799519613 12894893366070383174819855)
              ·
                refine ⟨19342340049105574762229783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12894893366070383174819855 19342340049105574762229783)
                ·
                  refine ⟨29013510073658362143344675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19342340049105574762229783 29013510073658362143344675)
                  ·
                    refine ⟨43520265110487543215017013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29013510073658362143344675 43520265110487543215017013)
                    ·
                      refine ⟨4080024854108207176407845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43520265110487543215017013 4080024854108207176407845)
                      ·
                        rfl

theorem cell23_7945820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 3, 1, 1, 1, 5].length) (baseStart_7945820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7945820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7945820 prefixEnd_7945820 := by exact prefixLift 7945820
  have htrace : WordTrace (prefixWord ++ tailWord_7945820) baseStart_7945820 baseEnd_7945820 := by
    simpa [prefixWord, tailWord_7945820, baseEnd_7945820] using wordTrace_append hprefix tailTrace_7945820
  have hstable : (prefixWord ++ tailWord_7945820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7945820).length < 2 ^ (prefixWord ++ tailWord_7945820).sum := by decide
  have hdescent : baseEnd_7945820 < baseStart_7945820 := by decide
  rcases family_descends (prefixWord ++ tailWord_7945820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7945893 : List Nat := [1, 3, 1, 2, 1, 2, 2, 1, 1, 6, 3]
def baseStart_7945893 : Nat := 118140960795 + 7945893 * 2 ^ 59
def prefixEnd_7945893 : Nat := 4983230072969 + 3 ^ 40 * 7945893 * 2
def baseEnd_7945893 : Nat := 4080062338195985390795009

theorem tailTrace_7945893 : CollatzResearch.WordTrace tailWord_7945893 prefixEnd_7945893 4080062338195985390795009 := by
  unfold tailWord_7945893
  simp only [CollatzResearch.WordTrace]
  refine ⟨289810526602394186329202333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193207017734929457552801555 289810526602394186329202333)
  ·
    refine ⟨108678947475897819873450875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 289810526602394186329202333 108678947475897819873450875)
    ·
      refine ⟨163018421213846729810176313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108678947475897819873450875 163018421213846729810176313)
      ·
        refine ⟨122263815910385047357632235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163018421213846729810176313 122263815910385047357632235)
        ·
          refine ⟨183395723865577571036448353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122263815910385047357632235 183395723865577571036448353)
          ·
            refine ⟨137546792899183178277336265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183395723865577571036448353 137546792899183178277336265)
            ·
              refine ⟨103160094674387383708002199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137546792899183178277336265 103160094674387383708002199)
              ·
                refine ⟨154740142011581075562003299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103160094674387383708002199 154740142011581075562003299)
                ·
                  refine ⟨232110213017371613343004949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 154740142011581075562003299 232110213017371613343004949)
                  ·
                    refine ⟨10880166235189294375453357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 232110213017371613343004949 10880166235189294375453357)
                    ·
                      refine ⟨4080062338195985390795009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10880166235189294375453357 4080062338195985390795009)
                      ·
                        rfl

theorem cell23_7945893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 1, 1, 6, 3].length) (baseStart_7945893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7945893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7945893 prefixEnd_7945893 := by exact prefixLift 7945893
  have htrace : WordTrace (prefixWord ++ tailWord_7945893) baseStart_7945893 baseEnd_7945893 := by
    simpa [prefixWord, tailWord_7945893, baseEnd_7945893] using wordTrace_append hprefix tailTrace_7945893
  have hstable : (prefixWord ++ tailWord_7945893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7945893).length < 2 ^ (prefixWord ++ tailWord_7945893).sum := by decide
  have hdescent : baseEnd_7945893 < baseStart_7945893 := by decide
  rcases family_descends (prefixWord ++ tailWord_7945893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7945903 : List Nat := [1, 1, 2, 1, 2, 4, 1, 3, 2, 2, 4]
def baseStart_7945903 : Nat := 118140960795 + 7945903 * 2 ^ 59
def prefixEnd_7945903 : Nat := 4983230072969 + 3 ^ 40 * 7945903 * 2
def baseEnd_7945903 : Nat := 4080067473002530351669963

theorem tailTrace_7945903 : CollatzResearch.WordTrace tailWord_7945903 prefixEnd_7945903 4080067473002530351669963 := by
  unfold tailWord_7945903
  simp only [CollatzResearch.WordTrace]
  refine ⟨289810891332357958037066363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193207260888238638691377575 289810891332357958037066363)
  ·
    refine ⟨434716336998536937055599545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289810891332357958037066363 434716336998536937055599545)
    ·
      refine ⟨326037252748902702791699659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 434716336998536937055599545 326037252748902702791699659)
      ·
        refine ⟨489055879123354054187549489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 326037252748902702791699659 489055879123354054187549489)
        ·
          refine ⟨366791909342515540640662117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 489055879123354054187549489 366791909342515540640662117)
          ·
            refine ⟨68773483001721663870124147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 366791909342515540640662117 68773483001721663870124147)
            ·
              refine ⟨103160224502582495805186221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68773483001721663870124147 103160224502582495805186221)
              ·
                refine ⟨38685084188468435926944833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103160224502582495805186221 38685084188468435926944833)
                ·
                  refine ⟨29013813141351326945208625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38685084188468435926944833 29013813141351326945208625)
                  ·
                    refine ⟨21760359856013495208906469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29013813141351326945208625 21760359856013495208906469)
                    ·
                      refine ⟨4080067473002530351669963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21760359856013495208906469 4080067473002530351669963)
                      ·
                        rfl

theorem cell23_7945903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 3, 2, 2, 4].length) (baseStart_7945903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7945903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7945903 prefixEnd_7945903 := by exact prefixLift 7945903
  have htrace : WordTrace (prefixWord ++ tailWord_7945903) baseStart_7945903 baseEnd_7945903 := by
    simpa [prefixWord, tailWord_7945903, baseEnd_7945903] using wordTrace_append hprefix tailTrace_7945903
  have hstable : (prefixWord ++ tailWord_7945903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7945903).length < 2 ^ (prefixWord ++ tailWord_7945903).sum := by decide
  have hdescent : baseEnd_7945903 < baseStart_7945903 := by decide
  rcases family_descends (prefixWord ++ tailWord_7945903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7945913 : List Nat := [1, 2, 1, 4, 1, 1, 4, 2, 7]
def baseStart_7945913 : Nat := 118140960795 + 7945913 * 2 ^ 59
def prefixEnd_7945913 : Nat := 4983230072969 + 3 ^ 40 * 7945913 * 2
def baseEnd_7945913 : Nat := 453341400867675034727213

theorem tailTrace_7945913 : CollatzResearch.WordTrace tailWord_7945913 prefixEnd_7945913 453341400867675034727213 := by
  unfold tailWord_7945913
  simp only [CollatzResearch.WordTrace]
  refine ⟨289811256062321729744930393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193207504041547819829953595 289811256062321729744930393)
  ·
    refine ⟨217358442046741297308697795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289811256062321729744930393 217358442046741297308697795)
    ·
      refine ⟨326037663070111945963046693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217358442046741297308697795 326037663070111945963046693)
      ·
        refine ⟨61132061825645989868071255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 326037663070111945963046693 61132061825645989868071255)
        ·
          refine ⟨91698092738468984802106883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61132061825645989868071255 91698092738468984802106883)
          ·
            refine ⟨137547139107703477203160325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91698092738468984802106883 137547139107703477203160325)
            ·
              refine ⟨25790088582694401975592561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 137547139107703477203160325 25790088582694401975592561)
              ·
                refine ⟨19342566437020801481694421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25790088582694401975592561 19342566437020801481694421)
                ·
                  refine ⟨453341400867675034727213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19342566437020801481694421 453341400867675034727213)
                  ·
                    rfl

theorem cell23_7945913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 2, 7].length) (baseStart_7945913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7945913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7945913 prefixEnd_7945913 := by exact prefixLift 7945913
  have htrace : WordTrace (prefixWord ++ tailWord_7945913) baseStart_7945913 baseEnd_7945913 := by
    simpa [prefixWord, tailWord_7945913, baseEnd_7945913] using wordTrace_append hprefix tailTrace_7945913
  have hstable : (prefixWord ++ tailWord_7945913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7945913).length < 2 ^ (prefixWord ++ tailWord_7945913).sum := by decide
  have hdescent : baseEnd_7945913 < baseStart_7945913 := by decide
  rcases family_descends (prefixWord ++ tailWord_7945913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7945963 : List Nat := [1, 1, 1, 1, 2, 4, 2, 1, 3, 3, 4]
def baseStart_7945963 : Nat := 118140960795 + 7945963 * 2 ^ 59
def prefixEnd_7945963 : Nat := 4983230072969 + 3 ^ 40 * 7945963 * 2
def baseEnd_7945963 : Nat := 4080098281841800116919687

theorem tailTrace_7945963 : CollatzResearch.WordTrace tailWord_7945963 prefixEnd_7945963 4080098281841800116919687 := by
  unfold tailWord_7945963
  simp only [CollatzResearch.WordTrace]
  refine ⟨289813079712140588284250543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193208719808093725522833695 289813079712140588284250543)
  ·
    refine ⟨434719619568210882426375815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289813079712140588284250543 434719619568210882426375815)
    ·
      refine ⟨652079429352316323639563723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 434719619568210882426375815 652079429352316323639563723)
      ·
        refine ⟨978119144028474485459345585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 652079429352316323639563723 978119144028474485459345585)
        ·
          refine ⟨733589358021355864094509189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 978119144028474485459345585 733589358021355864094509189)
          ·
            refine ⟨137548004629004224517720473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 733589358021355864094509189 137548004629004224517720473)
            ·
              refine ⟨103161003471753168388290355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137548004629004224517720473 103161003471753168388290355)
              ·
                refine ⟨154741505207629752582435533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103161003471753168388290355 154741505207629752582435533)
                ·
                  refine ⟨58028064452861157218413325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 154741505207629752582435533 58028064452861157218413325)
                  ·
                    refine ⟨21760524169822933956904997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58028064452861157218413325 21760524169822933956904997)
                    ·
                      refine ⟨4080098281841800116919687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21760524169822933956904997 4080098281841800116919687)
                      ·
                        rfl

theorem cell23_7945963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 1, 3, 3, 4].length) (baseStart_7945963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7945963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7945963 prefixEnd_7945963 := by exact prefixLift 7945963
  have htrace : WordTrace (prefixWord ++ tailWord_7945963) baseStart_7945963 baseEnd_7945963 := by
    simpa [prefixWord, tailWord_7945963, baseEnd_7945963] using wordTrace_append hprefix tailTrace_7945963
  have hstable : (prefixWord ++ tailWord_7945963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7945963).length < 2 ^ (prefixWord ++ tailWord_7945963).sum := by decide
  have hdescent : baseEnd_7945963 < baseStart_7945963 := by decide
  rcases family_descends (prefixWord ++ tailWord_7945963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7945993 : List Nat := [1, 2, 1, 1, 3, 2, 1, 3, 2, 1, 6]
def baseStart_7945993 : Nat := 118140960795 + 7945993 * 2 ^ 59
def prefixEnd_7945993 : Nat := 4983230072969 + 3 ^ 40 * 7945993 * 2
def baseEnd_7945993 : Nat := 4080113686261434999544549

theorem tailTrace_7945993 : CollatzResearch.WordTrace tailWord_7945993 prefixEnd_7945993 4080113686261434999544549 := by
  unfold tailWord_7945993
  simp only [CollatzResearch.WordTrace]
  refine ⟨289814173902031903407842633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193209449268021268938561755 289814173902031903407842633)
  ·
    refine ⟨217360630426523927555881975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289814173902031903407842633 217360630426523927555881975)
    ·
      refine ⟨326040945639785891333822963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217360630426523927555881975 326040945639785891333822963)
      ·
        refine ⟨489061418459678837000734445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 326040945639785891333822963 489061418459678837000734445)
        ·
          refine ⟨183398031922379563875275417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 489061418459678837000734445 183398031922379563875275417)
          ·
            refine ⟨137548523941784672906456563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183398031922379563875275417 137548523941784672906456563)
            ·
              refine ⟨206322785912677009359684845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137548523941784672906456563 206322785912677009359684845)
              ·
                refine ⟨77371044717253878509881817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 206322785912677009359684845 77371044717253878509881817)
                ·
                  refine ⟨58028283537940408882411363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77371044717253878509881817 58028283537940408882411363)
                  ·
                    refine ⟨87042425306910613323617045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58028283537940408882411363 87042425306910613323617045)
                    ·
                      refine ⟨4080113686261434999544549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 87042425306910613323617045 4080113686261434999544549)
                      ·
                        rfl

theorem cell23_7945993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 3, 2, 1, 6].length) (baseStart_7945993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7945993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7945993 prefixEnd_7945993 := by exact prefixLift 7945993
  have htrace : WordTrace (prefixWord ++ tailWord_7945993) baseStart_7945993 baseEnd_7945993 := by
    simpa [prefixWord, tailWord_7945993, baseEnd_7945993] using wordTrace_append hprefix tailTrace_7945993
  have hstable : (prefixWord ++ tailWord_7945993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7945993).length < 2 ^ (prefixWord ++ tailWord_7945993).sum := by decide
  have hdescent : baseEnd_7945993 < baseStart_7945993 := by decide
  rcases family_descends (prefixWord ++ tailWord_7945993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7946034 : List Nat := [3, 2, 1, 1, 3, 4, 1, 1, 2, 2, 3]
def baseStart_7946034 : Nat := 118140960795 + 7946034 * 2 ^ 59
def prefixEnd_7946034 : Nat := 4983230072969 + 3 ^ 40 * 7946034 * 2
def baseEnd_7946034 : Nat := 4080134738968269339131861

theorem tailTrace_7946034 : CollatzResearch.WordTrace tailWord_7946034 prefixEnd_7946034 4080134738968269339131861 := by
  unfold tailWord_7946034
  simp only [CollatzResearch.WordTrace]
  refine ⟨72453917323720841852521289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193210446196588911606723437 72453917323720841852521289)
  ·
    refine ⟨54340437992790631389390967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72453917323720841852521289 54340437992790631389390967)
    ·
      refine ⟨81510656989185947084086451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54340437992790631389390967 81510656989185947084086451)
      ·
        refine ⟨122265985483778920626129677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81510656989185947084086451 122265985483778920626129677)
        ·
          refine ⟨45849744556417095234798629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122265985483778920626129677 45849744556417095234798629)
          ·
            refine ⟨8596827104328205356524743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45849744556417095234798629 8596827104328205356524743)
            ·
              refine ⟨12895240656492308034787115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8596827104328205356524743 12895240656492308034787115)
              ·
                refine ⟨19342860984738462052180673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12895240656492308034787115 19342860984738462052180673)
                ·
                  refine ⟨14507145738553846539135505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19342860984738462052180673 14507145738553846539135505)
                  ·
                    refine ⟨10880359303915384904351629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14507145738553846539135505 10880359303915384904351629)
                    ·
                      refine ⟨4080134738968269339131861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10880359303915384904351629 4080134738968269339131861)
                      ·
                        rfl

theorem cell23_7946034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 1, 1, 2, 2, 3].length) (baseStart_7946034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7946034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7946034 prefixEnd_7946034 := by exact prefixLift 7946034
  have htrace : WordTrace (prefixWord ++ tailWord_7946034) baseStart_7946034 baseEnd_7946034 := by
    simpa [prefixWord, tailWord_7946034, baseEnd_7946034] using wordTrace_append hprefix tailTrace_7946034
  have hstable : (prefixWord ++ tailWord_7946034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7946034).length < 2 ^ (prefixWord ++ tailWord_7946034).sum := by decide
  have hdescent : baseEnd_7946034 < baseStart_7946034 := by decide
  rcases family_descends (prefixWord ++ tailWord_7946034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7946054 : List Nat := [6, 1, 1, 2, 1, 2, 1, 1, 8]
def baseStart_7946054 : Nat := 118140960795 + 7946054 * 2 ^ 59
def prefixEnd_7946054 : Nat := 4983230072969 + 3 ^ 40 * 7946054 * 2
def baseEnd_7946054 : Nat := 453349445397928806764641

theorem tailTrace_7946054 : CollatzResearch.WordTrace tailWord_7946054 prefixEnd_7946054 453349445397928806764641 := by
  unfold tailWord_7946054
  simp only [CollatzResearch.WordTrace]
  refine ⟨9056762461087840963306663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 193210932503207273883875477 9056762461087840963306663)
  ·
    refine ⟨13585143691631761444959995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9056762461087840963306663 13585143691631761444959995)
    ·
      refine ⟨20377715537447642167439993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13585143691631761444959995 20377715537447642167439993)
      ·
        refine ⟨15283286653085731625579995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20377715537447642167439993 15283286653085731625579995)
        ·
          refine ⟨22924929979628597438369993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15283286653085731625579995 22924929979628597438369993)
          ·
            refine ⟨17193697484721448078777495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22924929979628597438369993 17193697484721448078777495)
            ·
              refine ⟨25790546227082172118166243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17193697484721448078777495 25790546227082172118166243)
              ·
                refine ⟨38685819340623258177249365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25790546227082172118166243 38685819340623258177249365)
                ·
                  refine ⟨453349445397928806764641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38685819340623258177249365 453349445397928806764641)
                  ·
                    rfl

theorem cell23_7946054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 1, 8].length) (baseStart_7946054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7946054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7946054 prefixEnd_7946054 := by exact prefixLift 7946054
  have htrace : WordTrace (prefixWord ++ tailWord_7946054) baseStart_7946054 baseEnd_7946054 := by
    simpa [prefixWord, tailWord_7946054, baseEnd_7946054] using wordTrace_append hprefix tailTrace_7946054
  have hstable : (prefixWord ++ tailWord_7946054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7946054).length < 2 ^ (prefixWord ++ tailWord_7946054).sum := by decide
  have hdescent : baseEnd_7946054 < baseStart_7946054 := by decide
  rcases family_descends (prefixWord ++ tailWord_7946054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7946057 : List Nat := [1, 2, 1, 1, 2, 4, 2, 1, 4, 3, 2]
def baseStart_7946057 : Nat := 118140960795 + 7946057 * 2 ^ 59
def prefixEnd_7946057 : Nat := 4983230072969 + 3 ^ 40 * 7946057 * 2
def baseEnd_7946057 : Nat := 4080146549023322749144255

theorem tailTrace_7946057 : CollatzResearch.WordTrace tailWord_7946057 prefixEnd_7946057 4080146549023322749144255 := by
  unfold tailWord_7946057
  simp only [CollatzResearch.WordTrace]
  refine ⟨289816508173800042338172425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193211005449200028225448283 289816508173800042338172425)
  ·
    refine ⟨217362381130350031753629319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289816508173800042338172425 217362381130350031753629319)
    ·
      refine ⟨326043571695525047630443979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217362381130350031753629319 326043571695525047630443979)
      ·
        refine ⟨489065357543287571445665969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 326043571695525047630443979 489065357543287571445665969)
        ·
          refine ⟨366799018157465678584249477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 489065357543287571445665969 366799018157465678584249477)
          ·
            refine ⟨68774815904524814734546777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 366799018157465678584249477 68774815904524814734546777)
            ·
              refine ⟨51581111928393611050910083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68774815904524814734546777 51581111928393611050910083)
              ·
                refine ⟨77371667892590416576365125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51581111928393611050910083 77371667892590416576365125)
                ·
                  refine ⟨14507187729860703108068461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77371667892590416576365125 14507187729860703108068461)
                  ·
                    refine ⟨5440195398697763665525673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14507187729860703108068461 5440195398697763665525673)
                    ·
                      refine ⟨4080146549023322749144255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5440195398697763665525673 4080146549023322749144255)
                      ·
                        rfl

theorem cell23_7946057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 1, 4, 3, 2].length) (baseStart_7946057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7946057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7946057 prefixEnd_7946057 := by exact prefixLift 7946057
  have htrace : WordTrace (prefixWord ++ tailWord_7946057) baseStart_7946057 baseEnd_7946057 := by
    simpa [prefixWord, tailWord_7946057, baseEnd_7946057] using wordTrace_append hprefix tailTrace_7946057
  have hstable : (prefixWord ++ tailWord_7946057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7946057).length < 2 ^ (prefixWord ++ tailWord_7946057).sum := by decide
  have hdescent : baseEnd_7946057 < baseStart_7946057 := by decide
  rcases family_descends (prefixWord ++ tailWord_7946057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7946063 : List Nat := [1, 1, 2, 1, 1, 2, 1, 1, 1, 12]
def baseStart_7946063 : Nat := 118140960795 + 7946063 * 2 ^ 59
def prefixEnd_7946063 : Nat := 4983230072969 + 3 ^ 40 * 7946063 * 2
def baseEnd_7946063 : Nat := 1360049876635749908556409

theorem tailTrace_7946063 : CollatzResearch.WordTrace tailWord_7946063 prefixEnd_7946063 1360049876635749908556409 := by
  unfold tailWord_7946063
  simp only [CollatzResearch.WordTrace]
  refine ⟨289816727011778305362890843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193211151341185536908593895 289816727011778305362890843)
  ·
    refine ⟨434725090517667458044336265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289816727011778305362890843 434725090517667458044336265)
    ·
      refine ⟨326043817888250593533252199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 434725090517667458044336265 326043817888250593533252199)
      ·
        refine ⟨489065726832375890299878299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 326043817888250593533252199 489065726832375890299878299)
        ·
          refine ⟨733598590248563835449817449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 489065726832375890299878299 733598590248563835449817449)
          ·
            refine ⟨550198942686422876587363087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 733598590248563835449817449 550198942686422876587363087)
            ·
              refine ⟨825298414029634314881044631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 550198942686422876587363087 825298414029634314881044631)
              ·
                refine ⟨1237947621044451472321566947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 825298414029634314881044631 1237947621044451472321566947)
                ·
                  refine ⟨1856921431566677208482350421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1237947621044451472321566947 1856921431566677208482350421)
                  ·
                    refine ⟨1360049876635749908556409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 12 1856921431566677208482350421 1360049876635749908556409)
                    ·
                      rfl

theorem cell23_7946063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 12].length) (baseStart_7946063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7946063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7946063 prefixEnd_7946063 := by exact prefixLift 7946063
  have htrace : WordTrace (prefixWord ++ tailWord_7946063) baseStart_7946063 baseEnd_7946063 := by
    simpa [prefixWord, tailWord_7946063, baseEnd_7946063] using wordTrace_append hprefix tailTrace_7946063
  have hstable : (prefixWord ++ tailWord_7946063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7946063).length < 2 ^ (prefixWord ++ tailWord_7946063).sum := by decide
  have hdescent : baseEnd_7946063 < baseStart_7946063 := by decide
  rcases family_descends (prefixWord ++ tailWord_7946063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7946084 : List Nat := [2, 3, 1, 1, 5, 1, 2, 2, 1, 5]
def baseStart_7946084 : Nat := 118140960795 + 7946084 * 2 ^ 59
def prefixEnd_7946084 : Nat := 4983230072969 + 3 ^ 40 * 7946084 * 2
def baseEnd_7946084 : Nat := 1360053471000331381168877

theorem tailTrace_7946084 : CollatzResearch.WordTrace tailWord_7946084 prefixEnd_7946084 1360053471000331381168877 := by
  unfold tailWord_7946084
  simp only [CollatzResearch.WordTrace]
  refine ⟨144908746472351112974702653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193211661963134817299603537 144908746472351112974702653)
  ·
    refine ⟨54340779927131667365513495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144908746472351112974702653 54340779927131667365513495)
    ·
      refine ⟨81511169890697501048270243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54340779927131667365513495 81511169890697501048270243)
      ·
        refine ⟨122266754836046251572405365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81511169890697501048270243 122266754836046251572405365)
        ·
          refine ⟨11462508265879336084913003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 122266754836046251572405365 11462508265879336084913003)
          ·
            refine ⟨17193762398819004127369505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11462508265879336084913003 17193762398819004127369505)
            ·
              refine ⟨12895321799114253095527129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17193762398819004127369505 12895321799114253095527129)
              ·
                refine ⟨9671491349335689821645347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12895321799114253095527129 9671491349335689821645347)
                ·
                  refine ⟨14507237024003534732468021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9671491349335689821645347 14507237024003534732468021)
                  ·
                    refine ⟨1360053471000331381168877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14507237024003534732468021 1360053471000331381168877)
                    ·
                      rfl

theorem cell23_7946084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 2, 2, 1, 5].length) (baseStart_7946084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7946084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7946084 prefixEnd_7946084 := by exact prefixLift 7946084
  have htrace : WordTrace (prefixWord ++ tailWord_7946084) baseStart_7946084 baseEnd_7946084 := by
    simpa [prefixWord, tailWord_7946084, baseEnd_7946084] using wordTrace_append hprefix tailTrace_7946084
  have hstable : (prefixWord ++ tailWord_7946084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7946084).length < 2 ^ (prefixWord ++ tailWord_7946084).sum := by decide
  have hdescent : baseEnd_7946084 < baseStart_7946084 := by decide
  rcases family_descends (prefixWord ++ tailWord_7946084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7946087 : List Nat := [1, 1, 5, 1, 2, 1, 1, 1, 2, 6, 2]
def baseStart_7946087 : Nat := 118140960795 + 7946087 * 2 ^ 59
def prefixEnd_7946087 : Nat := 4983230072969 + 3 ^ 40 * 7946087 * 2
def baseEnd_7946087 : Nat := 4080161953442957631769117

theorem tailTrace_7946087 : CollatzResearch.WordTrace tailWord_7946087 prefixEnd_7946087 4080161953442957631769117 := by
  unfold tailWord_7946087
  simp only [CollatzResearch.WordTrace]
  refine ⟨289817602363691357461764515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193211734909127571641176343 289817602363691357461764515)
  ·
    refine ⟨434726403545537036192646773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289817602363691357461764515 434726403545537036192646773)
    ·
      refine ⟨40755600332394097143060635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 434726403545537036192646773 40755600332394097143060635)
      ·
        refine ⟨61133400498591145714590953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40755600332394097143060635 61133400498591145714590953)
        ·
          refine ⟨45850050373943359285943215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61133400498591145714590953 45850050373943359285943215)
          ·
            refine ⟨68775075560915038928914823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45850050373943359285943215 68775075560915038928914823)
            ·
              refine ⟨103162613341372558393372235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68775075560915038928914823 103162613341372558393372235)
              ·
                refine ⟨154743920012058837590058353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103162613341372558393372235 154743920012058837590058353)
                ·
                  refine ⟨116057940009044128192543765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 154743920012058837590058353 116057940009044128192543765)
                  ·
                    refine ⟨5440215937923943509025489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 116057940009044128192543765 5440215937923943509025489)
                    ·
                      refine ⟨4080161953442957631769117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5440215937923943509025489 4080161953442957631769117)
                      ·
                        rfl

theorem cell23_7946087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 1, 2, 6, 2].length) (baseStart_7946087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7946087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7946087 prefixEnd_7946087 := by exact prefixLift 7946087
  have htrace : WordTrace (prefixWord ++ tailWord_7946087) baseStart_7946087 baseEnd_7946087 := by
    simpa [prefixWord, tailWord_7946087, baseEnd_7946087] using wordTrace_append hprefix tailTrace_7946087
  have hstable : (prefixWord ++ tailWord_7946087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7946087).length < 2 ^ (prefixWord ++ tailWord_7946087).sum := by decide
  have hdescent : baseEnd_7946087 < baseStart_7946087 := by decide
  rcases family_descends (prefixWord ++ tailWord_7946087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7946141 : List Nat := [1, 4, 2, 1, 2, 4, 1, 2, 1, 2, 3]
def baseStart_7946141 : Nat := 118140960795 + 7946141 * 2 ^ 59
def prefixEnd_7946141 : Nat := 4983230072969 + 3 ^ 40 * 7946141 * 2
def baseEnd_7946141 : Nat := 4080189681398300420493869

theorem tailTrace_7946141 : CollatzResearch.WordTrace tailWord_7946141 prefixEnd_7946141 4080189681398300420493869 := by
  unfold tailWord_7946141
  simp only [CollatzResearch.WordTrace]
  refine ⟨289819571905495724684230277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193213047936997149789486851 289819571905495724684230277)
  ·
    refine ⟨54341169732280448378293177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 289819571905495724684230277 54341169732280448378293177)
    ·
      refine ⟨40755877299210336283719883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54341169732280448378293177 40755877299210336283719883)
      ·
        refine ⟨61133815948815504425579825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40755877299210336283719883 61133815948815504425579825)
        ·
          refine ⟨45850361961611628319184869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61133815948815504425579825 45850361961611628319184869)
          ·
            refine ⟨8596942867802180309847163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45850361961611628319184869 8596942867802180309847163)
            ·
              refine ⟨12895414301703270464770745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8596942867802180309847163 12895414301703270464770745)
              ·
                refine ⟨9671560726277452848578059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12895414301703270464770745 9671560726277452848578059)
                ·
                  refine ⟨14507341089416179272867089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9671560726277452848578059 14507341089416179272867089)
                  ·
                    refine ⟨10880505817062134454650317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14507341089416179272867089 10880505817062134454650317)
                    ·
                      refine ⟨4080189681398300420493869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10880505817062134454650317 4080189681398300420493869)
                      ·
                        rfl

theorem cell23_7946141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 1, 2, 1, 2, 3].length) (baseStart_7946141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7946141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7946141 prefixEnd_7946141 := by exact prefixLift 7946141
  have htrace : WordTrace (prefixWord ++ tailWord_7946141) baseStart_7946141 baseEnd_7946141 := by
    simpa [prefixWord, tailWord_7946141, baseEnd_7946141] using wordTrace_append hprefix tailTrace_7946141
  have hstable : (prefixWord ++ tailWord_7946141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7946141).length < 2 ^ (prefixWord ++ tailWord_7946141).sum := by decide
  have hdescent : baseEnd_7946141 < baseStart_7946141 := by decide
  rcases family_descends (prefixWord ++ tailWord_7946141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7946160 : List Nat := [2, 1, 1, 1, 2, 1, 1, 1, 6, 3, 4]
def baseStart_7946160 : Nat := 118140960795 + 7946160 * 2 ^ 59
def prefixEnd_7946160 : Nat := 4983230072969 + 3 ^ 40 * 7946160 * 2
def baseEnd_7946160 : Nat := 4080199437530735846156281

theorem tailTrace_7946160 : CollatzResearch.WordTrace tailWord_7946160 prefixEnd_7946160 4080199437530735846156281 := by
  unfold tailWord_7946160
  simp only [CollatzResearch.WordTrace]
  refine ⟨144910132446213445464585967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193213509928284593952781289 144910132446213445464585967)
  ·
    refine ⟨217365198669320168196878951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144910132446213445464585967 217365198669320168196878951)
    ·
      refine ⟨326047798003980252295318427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217365198669320168196878951 326047798003980252295318427)
      ·
        refine ⟨489071697005970378442977641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 326047798003980252295318427 489071697005970378442977641)
        ·
          refine ⟨366803772754477783832233231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 489071697005970378442977641 366803772754477783832233231)
          ·
            refine ⟨550205659131716675748349847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 366803772754477783832233231 550205659131716675748349847)
            ·
              refine ⟨825308488697575013622524771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 550205659131716675748349847 825308488697575013622524771)
              ·
                refine ⟨1237962733046362520433787157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 825308488697575013622524771 1237962733046362520433787157)
                ·
                  refine ⟨58029503111548243145333773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1237962733046362520433787157 58029503111548243145333773)
                  ·
                    refine ⟨21761063666830591179500165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58029503111548243145333773 21761063666830591179500165)
                    ·
                      refine ⟨4080199437530735846156281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21761063666830591179500165 4080199437530735846156281)
                      ·
                        rfl

theorem cell23_7946160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 6, 3, 4].length) (baseStart_7946160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7946160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7946160 prefixEnd_7946160 := by exact prefixLift 7946160
  have htrace : WordTrace (prefixWord ++ tailWord_7946160) baseStart_7946160 baseEnd_7946160 := by
    simpa [prefixWord, tailWord_7946160, baseEnd_7946160] using wordTrace_append hprefix tailTrace_7946160
  have hstable : (prefixWord ++ tailWord_7946160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7946160).length < 2 ^ (prefixWord ++ tailWord_7946160).sum := by decide
  have hdescent : baseEnd_7946160 < baseStart_7946160 := by decide
  rcases family_descends (prefixWord ++ tailWord_7946160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7946215 : List Nat := [1, 1, 5, 2, 3, 2, 2, 1, 1, 3, 2]
def baseStart_7946215 : Nat := 118140960795 + 7946215 * 2 ^ 59
def prefixEnd_7946215 : Nat := 4983230072969 + 3 ^ 40 * 7946215 * 2
def baseEnd_7946215 : Nat := 4080227678966733130968529

theorem tailTrace_7946215 : CollatzResearch.WordTrace tailWord_7946215 prefixEnd_7946215 4080227678966733130968529 := by
  unfold tailWord_7946215
  simp only [CollatzResearch.WordTrace]
  refine ⟨289822270907227635322424099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193214847271485090214949399 289822270907227635322424099)
  ·
    refine ⟨434733406360841452983636149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289822270907227635322424099 434733406360841452983636149)
    ·
      refine ⟨40756256846328886217215889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 434733406360841452983636149 40756256846328886217215889)
      ·
        refine ⟨30567192634746664662911917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40756256846328886217215889 30567192634746664662911917)
        ·
          refine ⟨11462697238029999248591969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30567192634746664662911917 11462697238029999248591969)
          ·
            refine ⟨8597022928522499436443977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11462697238029999248591969 8597022928522499436443977)
            ·
              refine ⟨6447767196391874577332983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8597022928522499436443977 6447767196391874577332983)
              ·
                refine ⟨9671650794587811865999475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6447767196391874577332983 9671650794587811865999475)
                ·
                  refine ⟨14507476191881717798999213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9671650794587811865999475 14507476191881717798999213)
                  ·
                    refine ⟨5440303571955644174624705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14507476191881717798999213 5440303571955644174624705)
                    ·
                      refine ⟨4080227678966733130968529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5440303571955644174624705 4080227678966733130968529)
                      ·
                        rfl

theorem cell23_7946215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 2, 1, 1, 3, 2].length) (baseStart_7946215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7946215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7946215 prefixEnd_7946215 := by exact prefixLift 7946215
  have htrace : WordTrace (prefixWord ++ tailWord_7946215) baseStart_7946215 baseEnd_7946215 := by
    simpa [prefixWord, tailWord_7946215, baseEnd_7946215] using wordTrace_append hprefix tailTrace_7946215
  have hstable : (prefixWord ++ tailWord_7946215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7946215).length < 2 ^ (prefixWord ++ tailWord_7946215).sum := by decide
  have hdescent : baseEnd_7946215 < baseStart_7946215 := by decide
  rcases family_descends (prefixWord ++ tailWord_7946215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7946247 : List Nat := [1, 1, 4, 3, 1, 2, 1, 2, 1, 7]
def baseStart_7946247 : Nat := 118140960795 + 7946247 * 2 ^ 59
def prefixEnd_7946247 : Nat := 4983230072969 + 3 ^ 40 * 7946247 * 2
def baseEnd_7946247 : Nat := 1360081370115892335256127

theorem tailTrace_7946247 : CollatzResearch.WordTrace tailWord_7946247 prefixEnd_7946247 1360081370115892335256127 := by
  unfold tailWord_7946247
  simp only [CollatzResearch.WordTrace]
  refine ⟨289823438043111704787588995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193215625362074469858392663 289823438043111704787588995)
  ·
    refine ⟨434735157064667557181383493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289823438043111704787588995 434735157064667557181383493)
    ·
      refine ⟨81512841949625166971509405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 434735157064667557181383493 81512841949625166971509405)
      ·
        refine ⟨30567315731109437614316027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81512841949625166971509405 30567315731109437614316027)
        ·
          refine ⟨45850973596664156421474041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30567315731109437614316027 45850973596664156421474041)
          ·
            refine ⟨34388230197498117316105531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45850973596664156421474041 34388230197498117316105531)
            ·
              refine ⟨51582345296247175974158297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34388230197498117316105531 51582345296247175974158297)
              ·
                refine ⟨38686758972185381980618723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51582345296247175974158297 38686758972185381980618723)
                ·
                  refine ⟨58030138458278072970928085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38686758972185381980618723 58030138458278072970928085)
                  ·
                    refine ⟨1360081370115892335256127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58030138458278072970928085 1360081370115892335256127)
                    ·
                      rfl

theorem cell23_7946247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 2, 1, 7].length) (baseStart_7946247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7946247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7946247 prefixEnd_7946247 := by exact prefixLift 7946247
  have htrace : WordTrace (prefixWord ++ tailWord_7946247) baseStart_7946247 baseEnd_7946247 := by
    simpa [prefixWord, tailWord_7946247, baseEnd_7946247] using wordTrace_append hprefix tailTrace_7946247
  have hstable : (prefixWord ++ tailWord_7946247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7946247).length < 2 ^ (prefixWord ++ tailWord_7946247).sum := by decide
  have hdescent : baseEnd_7946247 < baseStart_7946247 := by decide
  rcases family_descends (prefixWord ++ tailWord_7946247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7946284 : List Nat := [2, 2, 1, 1, 1, 2, 2, 4, 2, 4, 2]
def baseStart_7946284 : Nat := 118140960795 + 7946284 * 2 ^ 59
def prefixEnd_7946284 : Nat := 4983230072969 + 3 ^ 40 * 7946284 * 2
def baseEnd_7946284 : Nat := 4080263109131893361005711

theorem tailTrace_7946284 : CollatzResearch.WordTrace tailWord_7946284 prefixEnd_7946284 4080263109131893361005711 := by
  unfold tailWord_7946284
  simp only [CollatzResearch.WordTrace]
  refine ⟨144912393771988830053342953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193216525029318440071123937 144912393771988830053342953)
  ·
    refine ⟨108684295328991622540007215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144912393771988830053342953 108684295328991622540007215)
    ·
      refine ⟨163026442993487433810010823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108684295328991622540007215 163026442993487433810010823)
      ·
        refine ⟨244539664490231150715016235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163026442993487433810010823 244539664490231150715016235)
        ·
          refine ⟨366809496735346726072524353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244539664490231150715016235 366809496735346726072524353)
          ·
            refine ⟨275107122551510044554393265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 366809496735346726072524353 275107122551510044554393265)
            ·
              refine ⟨206330341913632533415794949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 275107122551510044554393265 206330341913632533415794949)
              ·
                refine ⟨38686939108806100015461553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 206330341913632533415794949 38686939108806100015461553)
                ·
                  refine ⟨29015204331604575011596165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38686939108806100015461553 29015204331604575011596165)
                  ·
                    refine ⟨5440350812175857814674281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29015204331604575011596165 5440350812175857814674281)
                    ·
                      refine ⟨4080263109131893361005711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5440350812175857814674281 4080263109131893361005711)
                      ·
                        rfl

theorem cell23_7946284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 4, 2].length) (baseStart_7946284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7946284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7946284 prefixEnd_7946284 := by exact prefixLift 7946284
  have htrace : WordTrace (prefixWord ++ tailWord_7946284) baseStart_7946284 baseEnd_7946284 := by
    simpa [prefixWord, tailWord_7946284, baseEnd_7946284] using wordTrace_append hprefix tailTrace_7946284
  have hstable : (prefixWord ++ tailWord_7946284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7946284).length < 2 ^ (prefixWord ++ tailWord_7946284).sum := by decide
  have hdescent : baseEnd_7946284 < baseStart_7946284 := by decide
  rcases family_descends (prefixWord ++ tailWord_7946284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7946287 : List Nat := [1, 1, 2, 1, 2, 1, 1, 4, 3, 4, 3]
def baseStart_7946287 : Nat := 118140960795 + 7946287 * 2 ^ 59
def prefixEnd_7946287 : Nat := 4983230072969 + 3 ^ 40 * 7946287 * 2
def baseEnd_7946287 : Nat := 4080264649573856849268197

theorem tailTrace_7946287 : CollatzResearch.WordTrace tailWord_7946287 prefixEnd_7946287 4080264649573856849268197 := by
  unfold tailWord_7946287
  simp only [CollatzResearch.WordTrace]
  refine ⟨289824896962966791619045115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193216597975311194412696743 289824896962966791619045115)
  ·
    refine ⟨434737345444450187428567673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289824896962966791619045115 434737345444450187428567673)
    ·
      refine ⟨326053009083337640571425755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 434737345444450187428567673 326053009083337640571425755)
      ·
        refine ⟨489079513625006460857138633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 326053009083337640571425755 489079513625006460857138633)
        ·
          refine ⟨366809635218754845642853975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 489079513625006460857138633 366809635218754845642853975)
          ·
            refine ⟨550214452828132268464280963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 366809635218754845642853975 550214452828132268464280963)
            ·
              refine ⟨825321679242198402696421445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 550214452828132268464280963 825321679242198402696421445)
              ·
                refine ⟨154747814857912200505579021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 825321679242198402696421445 154747814857912200505579021)
                ·
                  refine ⟨58030430571717075189592133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 154747814857912200505579021 58030430571717075189592133)
                  ·
                    refine ⟨10880705732196951598048525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58030430571717075189592133 10880705732196951598048525)
                    ·
                      refine ⟨4080264649573856849268197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10880705732196951598048525 4080264649573856849268197)
                      ·
                        rfl

theorem cell23_7946287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 4, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 4, 3, 4, 3].length) (baseStart_7946287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7946287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7946287 prefixEnd_7946287 := by exact prefixLift 7946287
  have htrace : WordTrace (prefixWord ++ tailWord_7946287) baseStart_7946287 baseEnd_7946287 := by
    simpa [prefixWord, tailWord_7946287, baseEnd_7946287] using wordTrace_append hprefix tailTrace_7946287
  have hstable : (prefixWord ++ tailWord_7946287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7946287).length < 2 ^ (prefixWord ++ tailWord_7946287).sum := by decide
  have hdescent : baseEnd_7946287 < baseStart_7946287 := by decide
  rcases family_descends (prefixWord ++ tailWord_7946287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7946354 : List Nat := [3, 2, 1, 2, 2, 2, 1, 2, 3, 5]
def baseStart_7946354 : Nat := 118140960795 + 7946354 * 2 ^ 59
def prefixEnd_7946354 : Nat := 4983230072969 + 3 ^ 40 * 7946354 * 2
def baseEnd_7946354 : Nat := 1360099684259236029043463

theorem tailTrace_7946354 : CollatzResearch.WordTrace tailWord_7946354 prefixEnd_7946354 1360099684259236029043463 := by
  unfold tailWord_7946354
  simp only [CollatzResearch.WordTrace]
  refine ⟨72456835163431015515433529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193218227102482708041156077 72456835163431015515433529)
  ·
    refine ⟨54342626372573261636575147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72456835163431015515433529 54342626372573261636575147)
    ·
      refine ⟨81513939558859892454862721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54342626372573261636575147 81513939558859892454862721)
      ·
        refine ⟨61135454669144919341147041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81513939558859892454862721 61135454669144919341147041)
        ·
          refine ⟨45851591001858689505860281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61135454669144919341147041 45851591001858689505860281)
          ·
            refine ⟨34388693251394017129395211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45851591001858689505860281 34388693251394017129395211)
            ·
              refine ⟨51583039877091025694092817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34388693251394017129395211 51583039877091025694092817)
              ·
                refine ⟨38687279907818269270569613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51583039877091025694092817 38687279907818269270569613)
                ·
                  refine ⟨14507729965431850976463605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38687279907818269270569613 14507729965431850976463605)
                  ·
                    refine ⟨1360099684259236029043463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14507729965431850976463605 1360099684259236029043463)
                    ·
                      rfl

theorem cell23_7946354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 2, 3, 5].length) (baseStart_7946354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7946354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7946354 prefixEnd_7946354 := by exact prefixLift 7946354
  have htrace : WordTrace (prefixWord ++ tailWord_7946354) baseStart_7946354 baseEnd_7946354 := by
    simpa [prefixWord, tailWord_7946354, baseEnd_7946354] using wordTrace_append hprefix tailTrace_7946354
  have hstable : (prefixWord ++ tailWord_7946354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7946354).length < 2 ^ (prefixWord ++ tailWord_7946354).sum := by decide
  have hdescent : baseEnd_7946354 < baseStart_7946354 := by decide
  rcases family_descends (prefixWord ++ tailWord_7946354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7946378 : List Nat := [3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 2]
def baseStart_7946378 : Nat := 118140960795 + 7946378 * 2 ^ 59
def prefixEnd_7946378 : Nat := 4983230072969 + 3 ^ 40 * 7946378 * 2
def baseEnd_7946378 : Nat := 4080311376313415993230279

theorem tailTrace_7946378 : CollatzResearch.WordTrace tailWord_7946378 prefixEnd_7946378 4080311376313415993230279 := by
  unfold tailWord_7946378
  simp only [CollatzResearch.WordTrace]
  refine ⟨72457054001409278540151947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193218810670424742773738525 72457054001409278540151947)
  ·
    refine ⟨108685581002113917810227921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72457054001409278540151947 108685581002113917810227921)
    ·
      refine ⟨81514185751585438357670941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108685581002113917810227921 81514185751585438357670941)
      ·
        refine ⟨30567819656844539384126603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81514185751585438357670941 30567819656844539384126603)
        ·
          refine ⟨45851729485266809076189905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30567819656844539384126603 45851729485266809076189905)
          ·
            refine ⟨34388797113950106807142429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45851729485266809076189905 34388797113950106807142429)
            ·
              refine ⟨12895798917731290052678411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34388797113950106807142429 12895798917731290052678411)
              ·
                refine ⟨19343698376596935079017617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12895798917731290052678411 19343698376596935079017617)
                ·
                  refine ⟨14507773782447701309263213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19343698376596935079017617 14507773782447701309263213)
                  ·
                    refine ⟨5440415168417887990973705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14507773782447701309263213 5440415168417887990973705)
                    ·
                      refine ⟨4080311376313415993230279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5440415168417887990973705 4080311376313415993230279)
                      ·
                        rfl

theorem cell23_7946378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 2].length) (baseStart_7946378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7946378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7946378 prefixEnd_7946378 := by exact prefixLift 7946378
  have htrace : WordTrace (prefixWord ++ tailWord_7946378) baseStart_7946378 baseEnd_7946378 := by
    simpa [prefixWord, tailWord_7946378, baseEnd_7946378] using wordTrace_append hprefix tailTrace_7946378
  have hstable : (prefixWord ++ tailWord_7946378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7946378).length < 2 ^ (prefixWord ++ tailWord_7946378).sum := by decide
  have hdescent : baseEnd_7946378 < baseStart_7946378 := by decide
  rcases family_descends (prefixWord ++ tailWord_7946378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7946384 : List Nat := [2, 1, 1, 1, 1, 1, 6, 2, 4, 4]
def baseStart_7946384 : Nat := 118140960795 + 7946384 * 2 ^ 59
def prefixEnd_7946384 : Nat := 4983230072969 + 3 ^ 40 * 7946384 * 2
def baseEnd_7946384 : Nat := 1360104819065780989918417

theorem tailTrace_7946384 : CollatzResearch.WordTrace tailWord_7946384 prefixEnd_7946384 1360104819065780989918417 := by
  unfold tailWord_7946384
  simp only [CollatzResearch.WordTrace]
  refine ⟨144914217421807688592663103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193218956562410251456884137 144914217421807688592663103)
  ·
    refine ⟨217371326132711532888994655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144914217421807688592663103 217371326132711532888994655)
    ·
      refine ⟨326056989199067299333491983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217371326132711532888994655 326056989199067299333491983)
      ·
        refine ⟨489085483798600949000237975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 326056989199067299333491983 489085483798600949000237975)
        ·
          refine ⟨733628225697901423500356963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 489085483798600949000237975 733628225697901423500356963)
          ·
            refine ⟨1100442338546852135250535445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 733628225697901423500356963 1100442338546852135250535445)
            ·
              refine ⟨51583234619383693839868849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1100442338546852135250535445 51583234619383693839868849)
              ·
                refine ⟨38687425964537770379901637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51583234619383693839868849 38687425964537770379901637)
                ·
                  refine ⟨7253892368350831946231557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38687425964537770379901637 7253892368350831946231557)
                  ·
                    refine ⟨1360104819065780989918417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7253892368350831946231557 1360104819065780989918417)
                    ·
                      rfl

theorem cell23_7946384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 2, 4, 4].length) (baseStart_7946384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7946384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7946384 prefixEnd_7946384 := by exact prefixLift 7946384
  have htrace : WordTrace (prefixWord ++ tailWord_7946384) baseStart_7946384 baseEnd_7946384 := by
    simpa [prefixWord, tailWord_7946384, baseEnd_7946384] using wordTrace_append hprefix tailTrace_7946384
  have hstable : (prefixWord ++ tailWord_7946384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7946384).length < 2 ^ (prefixWord ++ tailWord_7946384).sum := by decide
  have hdescent : baseEnd_7946384 < baseStart_7946384 := by decide
  rcases family_descends (prefixWord ++ tailWord_7946384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7946387 : List Nat := [1, 1, 1, 2, 1, 2, 3, 2, 3, 1, 6]
def baseStart_7946387 : Nat := 118140960795 + 7946387 * 2 ^ 59
def prefixEnd_7946387 : Nat := 4983230072969 + 3 ^ 40 * 7946387 * 2
def baseEnd_7946387 : Nat := 4080315997639306458017737

theorem tailTrace_7946387 : CollatzResearch.WordTrace tailWord_7946387 prefixEnd_7946387 4080315997639306458017737 := by
  unfold tailWord_7946387
  simp only [CollatzResearch.WordTrace]
  refine ⟨289828544262604508697685415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193219029508403005798456943 289828544262604508697685415)
  ·
    refine ⟨434742816393906763046528123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289828544262604508697685415 434742816393906763046528123)
    ·
      refine ⟨652114224590860144569792185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 434742816393906763046528123 652114224590860144569792185)
      ·
        refine ⟨489085668443145108427344139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 652114224590860144569792185 489085668443145108427344139)
        ·
          refine ⟨733628502664717662641016209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 489085668443145108427344139 733628502664717662641016209)
          ·
            refine ⟨550221376998538246980762157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 733628502664717662641016209 550221376998538246980762157)
            ·
              refine ⟨206333016374451842617785809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 550221376998538246980762157 206333016374451842617785809)
              ·
                refine ⟨154749762280838881963339357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 206333016374451842617785809 154749762280838881963339357)
                ·
                  refine ⟨58031160855314580736252259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 154749762280838881963339357 58031160855314580736252259)
                  ·
                    refine ⟨87046741282971871104378389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58031160855314580736252259 87046741282971871104378389)
                    ·
                      refine ⟨4080315997639306458017737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 87046741282971871104378389 4080315997639306458017737)
                      ·
                        rfl

theorem cell23_7946387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 2, 3, 1, 6].length) (baseStart_7946387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7946387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7946387 prefixEnd_7946387 := by exact prefixLift 7946387
  have htrace : WordTrace (prefixWord ++ tailWord_7946387) baseStart_7946387 baseEnd_7946387 := by
    simpa [prefixWord, tailWord_7946387, baseEnd_7946387] using wordTrace_append hprefix tailTrace_7946387
  have hstable : (prefixWord ++ tailWord_7946387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7946387).length < 2 ^ (prefixWord ++ tailWord_7946387).sum := by decide
  have hdescent : baseEnd_7946387 < baseStart_7946387 := by decide
  rcases family_descends (prefixWord ++ tailWord_7946387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7946401 : List Nat := [1, 2, 3, 3, 1, 3, 1, 1, 4, 4]
def baseStart_7946401 : Nat := 118140960795 + 7946401 * 2 ^ 59
def prefixEnd_7946401 : Nat := 4983230072969 + 3 ^ 40 * 7946401 * 2
def baseEnd_7946401 : Nat := 1360107728789489801080891

theorem tailTrace_7946401 : CollatzResearch.WordTrace tailWord_7946401 prefixEnd_7946401 1360107728789489801080891 := by
  unfold tailWord_7946401
  simp only [CollatzResearch.WordTrace]
  refine ⟨289829054884553789088695057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193219369923035859392463371 289829054884553789088695057)
  ·
    refine ⟨217371791163415341816521293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289829054884553789088695057 217371791163415341816521293)
    ·
      refine ⟨81514421686280753181195485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 217371791163415341816521293 81514421686280753181195485)
      ·
        refine ⟨30567908132355282442948307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81514421686280753181195485 30567908132355282442948307)
        ·
          refine ⟨45851862198532923664422461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30567908132355282442948307 45851862198532923664422461)
          ·
            refine ⟨17194448324449846374158423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45851862198532923664422461 17194448324449846374158423)
            ·
              refine ⟨25791672486674769561237635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17194448324449846374158423 25791672486674769561237635)
              ·
                refine ⟨38687508730012154341856453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25791672486674769561237635 38687508730012154341856453)
                ·
                  refine ⟨7253907886877278939098085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38687508730012154341856453 7253907886877278939098085)
                  ·
                    refine ⟨1360107728789489801080891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7253907886877278939098085 1360107728789489801080891)
                    ·
                      rfl

theorem cell23_7946401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 1, 4, 4].length) (baseStart_7946401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7946401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7946401 prefixEnd_7946401 := by exact prefixLift 7946401
  have htrace : WordTrace (prefixWord ++ tailWord_7946401) baseStart_7946401 baseEnd_7946401 := by
    simpa [prefixWord, tailWord_7946401, baseEnd_7946401] using wordTrace_append hprefix tailTrace_7946401
  have hstable : (prefixWord ++ tailWord_7946401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7946401).length < 2 ^ (prefixWord ++ tailWord_7946401).sum := by decide
  have hdescent : baseEnd_7946401 < baseStart_7946401 := by decide
  rcases family_descends (prefixWord ++ tailWord_7946401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7946418 : List Nat := [3, 2, 1, 1, 1, 3, 5, 1, 2, 4]
def baseStart_7946418 : Nat := 118140960795 + 7946418 * 2 ^ 59
def prefixEnd_7946418 : Nat := 4983230072969 + 3 ^ 40 * 7946418 * 2
def baseEnd_7946418 : Nat := 1360110638513198612243365

theorem tailTrace_7946418 : CollatzResearch.WordTrace tailWord_7946418 prefixEnd_7946418 1360110638513198612243365 := by
  unfold tailWord_7946418
  simp only [CollatzResearch.WordTrace]
  refine ⟨72457418731373050248015977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193219783283661467328042605 72457418731373050248015977)
  ·
    refine ⟨54343064048529787686011983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72457418731373050248015977 54343064048529787686011983)
    ·
      refine ⟨81514596072794681529017975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54343064048529787686011983 81514596072794681529017975)
      ·
        refine ⟨122271894109192022293526963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81514596072794681529017975 122271894109192022293526963)
        ·
          refine ⟨183407841163788033440290445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122271894109192022293526963 183407841163788033440290445)
          ·
            refine ⟨68777940436420512540108917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 183407841163788033440290445 68777940436420512540108917)
            ·
              refine ⟨6447931915914423050635211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 68777940436420512540108917 6447931915914423050635211)
              ·
                refine ⟨9671897873871634575952817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6447931915914423050635211 9671897873871634575952817)
                ·
                  refine ⟨7253923405403725931964613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9671897873871634575952817 7253923405403725931964613)
                  ·
                    refine ⟨1360110638513198612243365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7253923405403725931964613 1360110638513198612243365)
                    ·
                      rfl

theorem cell23_7946418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 5, 1, 2, 4].length) (baseStart_7946418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7946418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7946418 prefixEnd_7946418 := by exact prefixLift 7946418
  have htrace : WordTrace (prefixWord ++ tailWord_7946418) baseStart_7946418 baseEnd_7946418 := by
    simpa [prefixWord, tailWord_7946418, baseEnd_7946418] using wordTrace_append hprefix tailTrace_7946418
  have hstable : (prefixWord ++ tailWord_7946418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7946418).length < 2 ^ (prefixWord ++ tailWord_7946418).sum := by decide
  have hdescent : baseEnd_7946418 < baseStart_7946418 := by decide
  rcases family_descends (prefixWord ++ tailWord_7946418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7946464 : List Nat := [2, 1, 1, 3, 1, 3, 2, 1, 2, 3, 4]
def baseStart_7946464 : Nat := 118140960795 + 7946464 * 2 ^ 59
def prefixEnd_7946464 : Nat := 4983230072969 + 3 ^ 40 * 7946464 * 2
def baseEnd_7946464 : Nat := 4080355535649702656754883

theorem tailTrace_7946464 : CollatzResearch.WordTrace tailWord_7946464 prefixEnd_7946464 4080355535649702656754883 := by
  unfold tailWord_7946464
  simp only [CollatzResearch.WordTrace]
  refine ⟨144915676341662775424119223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193220901788883700565492297 144915676341662775424119223)
  ·
    refine ⟨217373514512494163136178835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144915676341662775424119223 217373514512494163136178835)
    ·
      refine ⟨326060271768741244704268253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217373514512494163136178835 326060271768741244704268253)
      ·
        refine ⟨122272601913277966764100595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 326060271768741244704268253 122272601913277966764100595)
        ·
          refine ⟨183408902869916950146150893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122272601913277966764100595 183408902869916950146150893)
          ·
            refine ⟨68778338576218856304806585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 183408902869916950146150893 68778338576218856304806585)
            ·
              refine ⟨51583753932164142228604939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68778338576218856304806585 51583753932164142228604939)
              ·
                refine ⟨77375630898246213342907409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51583753932164142228604939 77375630898246213342907409)
                ·
                  refine ⟨58031723173684660007180557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77375630898246213342907409 58031723173684660007180557)
                  ·
                    refine ⟨21761896190131747502692709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58031723173684660007180557 21761896190131747502692709)
                    ·
                      refine ⟨4080355535649702656754883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21761896190131747502692709 4080355535649702656754883)
                      ·
                        rfl

theorem cell23_7946464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 1, 2, 3, 4].length) (baseStart_7946464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7946464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7946464 prefixEnd_7946464 := by exact prefixLift 7946464
  have htrace : WordTrace (prefixWord ++ tailWord_7946464) baseStart_7946464 baseEnd_7946464 := by
    simpa [prefixWord, tailWord_7946464, baseEnd_7946464] using wordTrace_append hprefix tailTrace_7946464
  have hstable : (prefixWord ++ tailWord_7946464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7946464).length < 2 ^ (prefixWord ++ tailWord_7946464).sum := by decide
  have hdescent : baseEnd_7946464 < baseStart_7946464 := by decide
  rcases family_descends (prefixWord ++ tailWord_7946464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7946474 : List Nat := [3, 1, 3, 1, 1, 2, 2, 1, 1, 8]
def baseStart_7946474 : Nat := 118140960795 + 7946474 * 2 ^ 59
def prefixEnd_7946474 : Nat := 4983230072969 + 3 ^ 40 * 7946474 * 2
def baseEnd_7946474 : Nat := 1360120223485415872543279

theorem tailTrace_7946474 : CollatzResearch.WordTrace tailWord_7946474 prefixEnd_7946474 1360120223485415872543279 := by
  unfold tailWord_7946474
  simp only [CollatzResearch.WordTrace]
  refine ⟨72457929353322330639025619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193221144942192881704068317 72457929353322330639025619)
  ·
    refine ⟨108686894029983495958538429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72457929353322330639025619 108686894029983495958538429)
    ·
      refine ⟨40757585261243810984451911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108686894029983495958538429 40757585261243810984451911)
      ·
        refine ⟨61136377891865716476677867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40757585261243810984451911 61136377891865716476677867)
        ·
          refine ⟨91704566837798574715016801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61136377891865716476677867 91704566837798574715016801)
          ·
            refine ⟨68778425128348931036262601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91704566837798574715016801 68778425128348931036262601)
            ·
              refine ⟨51583818846261698277196951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68778425128348931036262601 51583818846261698277196951)
              ·
                refine ⟨77375728269392547415795427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51583818846261698277196951 77375728269392547415795427)
                ·
                  refine ⟨116063592404088821123693141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77375728269392547415795427 116063592404088821123693141)
                  ·
                    refine ⟨1360120223485415872543279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 116063592404088821123693141 1360120223485415872543279)
                    ·
                      rfl

theorem cell23_7946474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 1, 1, 8].length) (baseStart_7946474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7946474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7946474 prefixEnd_7946474 := by exact prefixLift 7946474
  have htrace : WordTrace (prefixWord ++ tailWord_7946474) baseStart_7946474 baseEnd_7946474 := by
    simpa [prefixWord, tailWord_7946474, baseEnd_7946474] using wordTrace_append hprefix tailTrace_7946474
  have hstable : (prefixWord ++ tailWord_7946474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7946474).length < 2 ^ (prefixWord ++ tailWord_7946474).sum := by decide
  have hdescent : baseEnd_7946474 < baseStart_7946474 := by decide
  rcases family_descends (prefixWord ++ tailWord_7946474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7946524 : List Nat := [2, 2, 3, 1, 1, 1, 1, 1, 2, 1, 8]
def baseStart_7946524 : Nat := 118140960795 + 7946524 * 2 ^ 59
def prefixEnd_7946524 : Nat := 4983230072969 + 3 ^ 40 * 7946524 * 2
def baseEnd_7946524 : Nat := 4080386344488972422004607

theorem tailTrace_7946524 : CollatzResearch.WordTrace tailWord_7946524 prefixEnd_7946524 4080386344488972422004607 := by
  unfold tailWord_7946524
  simp only [CollatzResearch.WordTrace]
  refine ⟨144916770531554090547711313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193222360708738787396948417 144916770531554090547711313)
  ·
    refine ⟨108687577898665567910783485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144916770531554090547711313 108687577898665567910783485)
    ·
      refine ⟨40757841711999587966543807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108687577898665567910783485 40757841711999587966543807)
      ·
        refine ⟨61136762567999381949815711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40757841711999587966543807 61136762567999381949815711)
        ·
          refine ⟨91705143851999072924723567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61136762567999381949815711 91705143851999072924723567)
          ·
            refine ⟨137557715777998609387085351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91705143851999072924723567 137557715777998609387085351)
            ·
              refine ⟨206336573666997914080628027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137557715777998609387085351 206336573666997914080628027)
              ·
                refine ⟨309504860500496871120942041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 206336573666997914080628027 309504860500496871120942041)
                ·
                  refine ⟨232128645375372653340706531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 309504860500496871120942041 232128645375372653340706531)
                  ·
                    refine ⟨348192968063058980011059797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 232128645375372653340706531 348192968063058980011059797)
                    ·
                      refine ⟨4080386344488972422004607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 348192968063058980011059797 4080386344488972422004607)
                      ·
                        rfl

theorem cell23_7946524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 1, 2, 1, 8].length) (baseStart_7946524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7946524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7946524 prefixEnd_7946524 := by exact prefixLift 7946524
  have htrace : WordTrace (prefixWord ++ tailWord_7946524) baseStart_7946524 baseEnd_7946524 := by
    simpa [prefixWord, tailWord_7946524, baseEnd_7946524] using wordTrace_append hprefix tailTrace_7946524
  have hstable : (prefixWord ++ tailWord_7946524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7946524).length < 2 ^ (prefixWord ++ tailWord_7946524).sum := by decide
  have hdescent : baseEnd_7946524 < baseStart_7946524 := by decide
  rcases family_descends (prefixWord ++ tailWord_7946524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7946531 : List Nat := [1, 1, 1, 4, 2, 2, 3, 1, 2, 3, 3]
def baseStart_7946531 : Nat := 118140960795 + 7946531 * 2 ^ 59
def prefixEnd_7946531 : Nat := 4983230072969 + 3 ^ 40 * 7946531 * 2
def baseEnd_7946531 : Nat := 4080389938853553894617075

theorem tailTrace_7946531 : CollatzResearch.WordTrace tailWord_7946531 prefixEnd_7946531 4080389938853553894617075 := by
  unfold tailWord_7946531
  simp only [CollatzResearch.WordTrace]
  refine ⟨289833796374082821290927447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193222530916055214193951631 289833796374082821290927447)
  ·
    refine ⟨434750694561124231936391171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289833796374082821290927447 434750694561124231936391171)
    ·
      refine ⟨652126041841686347904586757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 434750694561124231936391171 652126041841686347904586757)
      ·
        refine ⟨122273632845316190232110017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 652126041841686347904586757 122273632845316190232110017)
        ·
          refine ⟨91705224633987142674082513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122273632845316190232110017 91705224633987142674082513)
          ·
            refine ⟨68778918475490357005561885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91705224633987142674082513 68778918475490357005561885)
            ·
              refine ⟨25792094428308883877085707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68778918475490357005561885 25792094428308883877085707)
              ·
                refine ⟨38688141642463325815628561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25792094428308883877085707 38688141642463325815628561)
                ·
                  refine ⟨29016106231847494361721421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38688141642463325815628561 29016106231847494361721421)
                  ·
                    refine ⟨10881039836942810385645533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29016106231847494361721421 10881039836942810385645533)
                    ·
                      refine ⟨4080389938853553894617075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10881039836942810385645533 4080389938853553894617075)
                      ·
                        rfl

theorem cell23_7946531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 1, 2, 3, 3].length) (baseStart_7946531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7946531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7946531 prefixEnd_7946531 := by exact prefixLift 7946531
  have htrace : WordTrace (prefixWord ++ tailWord_7946531) baseStart_7946531 baseEnd_7946531 := by
    simpa [prefixWord, tailWord_7946531, baseEnd_7946531] using wordTrace_append hprefix tailTrace_7946531
  have hstable : (prefixWord ++ tailWord_7946531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7946531).length < 2 ^ (prefixWord ++ tailWord_7946531).sum := by decide
  have hdescent : baseEnd_7946531 < baseStart_7946531 := by decide
  rcases family_descends (prefixWord ++ tailWord_7946531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7946538 : List Nat := [3, 1, 4, 2, 2, 1, 1, 2, 7]
def baseStart_7946538 : Nat := 118140960795 + 7946538 * 2 ^ 59
def prefixEnd_7946538 : Nat := 4983230072969 + 3 ^ 40 * 7946538 * 2
def baseEnd_7946538 : Nat := 453377059246459485247727

theorem tailTrace_7946538 : CollatzResearch.WordTrace tailWord_7946538 prefixEnd_7946538 453377059246459485247727 := by
  unfold tailWord_7946538
  simp only [CollatzResearch.WordTrace]
  refine ⟨72458512921264365371608067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193222701123371640990954845 72458512921264365371608067)
  ·
    refine ⟨108687769381896548057412101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72458512921264365371608067 108687769381896548057412101)
    ·
      refine ⟨20378956759105602760764769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108687769381896548057412101 20378956759105602760764769)
      ·
        refine ⟨15284217569329202070573577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20378956759105602760764769 15284217569329202070573577)
        ·
          refine ⟨11463163176996901552930183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15284217569329202070573577 11463163176996901552930183)
          ·
            refine ⟨17194744765495352329395275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11463163176996901552930183 17194744765495352329395275)
            ·
              refine ⟨25792117148243028494092913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17194744765495352329395275 25792117148243028494092913)
              ·
                refine ⟨19344087861182271370569685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25792117148243028494092913 19344087861182271370569685)
                ·
                  refine ⟨453377059246459485247727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19344087861182271370569685 453377059246459485247727)
                  ·
                    rfl

theorem cell23_7946538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 2, 7].length) (baseStart_7946538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7946538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7946538 prefixEnd_7946538 := by exact prefixLift 7946538
  have htrace : WordTrace (prefixWord ++ tailWord_7946538) baseStart_7946538 baseEnd_7946538 := by
    simpa [prefixWord, tailWord_7946538, baseEnd_7946538] using wordTrace_append hprefix tailTrace_7946538
  have hstable : (prefixWord ++ tailWord_7946538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7946538).length < 2 ^ (prefixWord ++ tailWord_7946538).sum := by decide
  have hdescent : baseEnd_7946538 < baseStart_7946538 := by decide
  rcases family_descends (prefixWord ++ tailWord_7946538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7946544 : List Nat := [2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 5]
def baseStart_7946544 : Nat := 118140960795 + 7946544 * 2 ^ 59
def prefixEnd_7946544 : Nat := 4983230072969 + 3 ^ 40 * 7946544 * 2
def baseEnd_7946544 : Nat := 4080396614102062343754515

theorem tailTrace_7946544 : CollatzResearch.WordTrace tailWord_7946544 prefixEnd_7946544 4080396614102062343754515 := by
  unfold tailWord_7946544
  simp only [CollatzResearch.WordTrace]
  refine ⟨144917135261517862255575343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193222847015357149674100457 144917135261517862255575343)
  ·
    refine ⟨217375702892276793383363015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144917135261517862255575343 217375702892276793383363015)
    ·
      refine ⟨326063554338415190075044523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217375702892276793383363015 326063554338415190075044523)
      ·
        refine ⟨489095331507622785112566785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 326063554338415190075044523 489095331507622785112566785)
        ·
          refine ⟨366821498630717088834425089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 489095331507622785112566785 366821498630717088834425089)
          ·
            refine ⟨275116123973037816625818817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 366821498630717088834425089 275116123973037816625818817)
            ·
              refine ⟨206337092979778362469364113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 275116123973037816625818817 206337092979778362469364113)
              ·
                refine ⟨154752819734833771852023085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 206337092979778362469364113 154752819734833771852023085)
                ·
                  refine ⟨58032307400562664444508657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 154752819734833771852023085 58032307400562664444508657)
                  ·
                    refine ⟨43524230550421998333381493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58032307400562664444508657 43524230550421998333381493)
                    ·
                      refine ⟨4080396614102062343754515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43524230550421998333381493 4080396614102062343754515)
                      ·
                        rfl

theorem cell23_7946544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 5].length) (baseStart_7946544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7946544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7946544 prefixEnd_7946544 := by exact prefixLift 7946544
  have htrace : WordTrace (prefixWord ++ tailWord_7946544) baseStart_7946544 baseEnd_7946544 := by
    simpa [prefixWord, tailWord_7946544, baseEnd_7946544] using wordTrace_append hprefix tailTrace_7946544
  have hstable : (prefixWord ++ tailWord_7946544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7946544).length < 2 ^ (prefixWord ++ tailWord_7946544).sum := by decide
  have hdescent : baseEnd_7946544 < baseStart_7946544 := by decide
  rcases family_descends (prefixWord ++ tailWord_7946544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7946591 : List Nat := [1, 1, 2, 3, 1, 2, 3, 2, 1, 4, 3]
def baseStart_7946591 : Nat := 118140960795 + 7946591 * 2 ^ 59
def prefixEnd_7946591 : Nat := 4983230072969 + 3 ^ 40 * 7946591 * 2
def baseEnd_7946591 : Nat := 4080420747692823659866799

theorem tailTrace_7946591 : CollatzResearch.WordTrace tailWord_7946591 prefixEnd_7946591 4080420747692823659866799 := by
  unfold tailWord_7946591
  simp only [CollatzResearch.WordTrace]
  refine ⟨289835984753865451538111627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193223989835910301025407751 289835984753865451538111627)
  ·
    refine ⟨434753977130798177307167441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289835984753865451538111627 434753977130798177307167441)
    ·
      refine ⟨326065482848098632980375581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 434753977130798177307167441 326065482848098632980375581)
      ·
        refine ⟨122274556068036987367640843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 326065482848098632980375581 122274556068036987367640843)
        ·
          refine ⟨183411834102055481051461265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122274556068036987367640843 183411834102055481051461265)
          ·
            refine ⟨137558875576541610788595949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183411834102055481051461265 137558875576541610788595949)
            ·
              refine ⟨51584578341203104045723481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 137558875576541610788595949 51584578341203104045723481)
              ·
                refine ⟨38688433755902328034292611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51584578341203104045723481 38688433755902328034292611)
                ·
                  refine ⟨58032650633853492051438917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38688433755902328034292611 58032650633853492051438917)
                  ·
                    refine ⟨10881121993847529759644797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58032650633853492051438917 10881121993847529759644797)
                    ·
                      refine ⟨4080420747692823659866799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10881121993847529759644797 4080420747692823659866799)
                      ·
                        rfl

theorem cell23_7946591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 2, 1, 4, 3].length) (baseStart_7946591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7946591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7946591 prefixEnd_7946591 := by exact prefixLift 7946591
  have htrace : WordTrace (prefixWord ++ tailWord_7946591) baseStart_7946591 baseEnd_7946591 := by
    simpa [prefixWord, tailWord_7946591, baseEnd_7946591] using wordTrace_append hprefix tailTrace_7946591
  have hstable : (prefixWord ++ tailWord_7946591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7946591).length < 2 ^ (prefixWord ++ tailWord_7946591).sum := by decide
  have hdescent : baseEnd_7946591 < baseStart_7946591 := by decide
  rcases family_descends (prefixWord ++ tailWord_7946591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7946625 : List Nat := [1, 2, 4, 3, 1, 2, 1, 2, 2, 2, 3]
def baseStart_7946625 : Nat := 118140960795 + 7946625 * 2 ^ 59
def prefixEnd_7946625 : Nat := 4983230072969 + 3 ^ 40 * 7946625 * 2
def baseEnd_7946625 : Nat := 4080438206035076526841643

theorem tailTrace_7946625 : CollatzResearch.WordTrace tailWord_7946625 prefixEnd_7946625 4080438206035076526841643 := by
  unfold tailWord_7946625
  simp only [CollatzResearch.WordTrace]
  refine ⟨289837224835742275344849329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193224816557161516896566219 289837224835742275344849329)
  ·
    refine ⟨217377918626806706508636997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289837224835742275344849329 217377918626806706508636997)
    ·
      refine ⟨40758359742526257470369437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 217377918626806706508636997 40758359742526257470369437)
      ·
        refine ⟨15284384903447346551388539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40758359742526257470369437 15284384903447346551388539)
        ·
          refine ⟨22926577355171019827082809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15284384903447346551388539 22926577355171019827082809)
          ·
            refine ⟨17194933016378264870312107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22926577355171019827082809 17194933016378264870312107)
            ·
              refine ⟨25792399524567397305468161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17194933016378264870312107 25792399524567397305468161)
              ·
                refine ⟨19344299643425547979101121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25792399524567397305468161 19344299643425547979101121)
                ·
                  refine ⟨14508224732569160984325841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19344299643425547979101121 14508224732569160984325841)
                  ·
                    refine ⟨10881168549426870738244381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14508224732569160984325841 10881168549426870738244381)
                    ·
                      refine ⟨4080438206035076526841643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10881168549426870738244381 4080438206035076526841643)
                      ·
                        rfl

theorem cell23_7946625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 2, 2, 2, 3].length) (baseStart_7946625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7946625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7946625 prefixEnd_7946625 := by exact prefixLift 7946625
  have htrace : WordTrace (prefixWord ++ tailWord_7946625) baseStart_7946625 baseEnd_7946625 := by
    simpa [prefixWord, tailWord_7946625, baseEnd_7946625] using wordTrace_append hprefix tailTrace_7946625
  have hstable : (prefixWord ++ tailWord_7946625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7946625).length < 2 ^ (prefixWord ++ tailWord_7946625).sum := by decide
  have hdescent : baseEnd_7946625 < baseStart_7946625 := by decide
  rcases family_descends (prefixWord ++ tailWord_7946625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7946632 : List Nat := [2, 1, 3, 3, 1, 1, 5, 2, 1, 4]
def baseStart_7946632 : Nat := 118140960795 + 7946632 * 2 ^ 59
def prefixEnd_7946632 : Nat := 4983230072969 + 3 ^ 40 * 7946632 * 2
def baseEnd_7946632 : Nat := 1360147266799885999818037

theorem tailTrace_7946632 : CollatzResearch.WordTrace tailWord_7946632 prefixEnd_7946632 1360147266799885999818037 := by
  unfold tailWord_7946632
  simp only [CollatzResearch.WordTrace]
  refine ⟨144918740073358457770177075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193224986764477943693569433 144918740073358457770177075)
  ·
    refine ⟨217378110110037686655265613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144918740073358457770177075 217378110110037686655265613)
    ·
      refine ⟨81516791291264132495724605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 217378110110037686655265613 81516791291264132495724605)
      ·
        refine ⟨30568796734224049685896727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81516791291264132495724605 30568796734224049685896727)
        ·
          refine ⟨45853195101336074528845091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30568796734224049685896727 45853195101336074528845091)
          ·
            refine ⟨68779792652004111793267637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45853195101336074528845091 68779792652004111793267637)
            ·
              refine ⟨6448105561125385480618841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 68779792652004111793267637 6448105561125385480618841)
              ·
                refine ⟨4836079170844039110464131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6448105561125385480618841 4836079170844039110464131)
                ·
                  refine ⟨7254118756266058665696197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4836079170844039110464131 7254118756266058665696197)
                  ·
                    refine ⟨1360147266799885999818037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7254118756266058665696197 1360147266799885999818037)
                    ·
                      rfl

theorem cell23_7946632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 5, 2, 1, 4].length) (baseStart_7946632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7946632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7946632 prefixEnd_7946632 := by exact prefixLift 7946632
  have htrace : WordTrace (prefixWord ++ tailWord_7946632) baseStart_7946632 baseEnd_7946632 := by
    simpa [prefixWord, tailWord_7946632, baseEnd_7946632] using wordTrace_append hprefix tailTrace_7946632
  have hstable : (prefixWord ++ tailWord_7946632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7946632).length < 2 ^ (prefixWord ++ tailWord_7946632).sum := by decide
  have hdescent : baseEnd_7946632 < baseStart_7946632 := by decide
  rcases family_descends (prefixWord ++ tailWord_7946632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7946658 : List Nat := [3, 3, 1, 2, 1, 1, 3, 1, 3, 5]
def baseStart_7946658 : Nat := 118140960795 + 7946658 * 2 ^ 59
def prefixEnd_7946658 : Nat := 4983230072969 + 3 ^ 40 * 7946658 * 2
def baseEnd_7946658 : Nat := 1360151716965558299242997

theorem tailTrace_7946658 : CollatzResearch.WordTrace tailWord_7946658 prefixEnd_7946658 1360151716965558299242997 := by
  unfold tailWord_7946658
  simp only [CollatzResearch.WordTrace]
  refine ⟨72459607111155680495200157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193225618963081814653867085 72459607111155680495200157)
  ·
    refine ⟨27172352666683380185700059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72459607111155680495200157 27172352666683380185700059)
    ·
      refine ⟨40758529000025070278550089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27172352666683380185700059 40758529000025070278550089)
      ·
        refine ⟨30568896750018802708912567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40758529000025070278550089 30568896750018802708912567)
        ·
          refine ⟨45853345125028204063368851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30568896750018802708912567 45853345125028204063368851)
          ·
            refine ⟨68780017687542306095053277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45853345125028204063368851 68780017687542306095053277)
            ·
              refine ⟨25792506632828364785644979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68780017687542306095053277 25792506632828364785644979)
              ·
                refine ⟨38688759949242547178467469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25792506632828364785644979 38688759949242547178467469)
                ·
                  refine ⟨14508284980965955191925301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38688759949242547178467469 14508284980965955191925301)
                  ·
                    refine ⟨1360151716965558299242997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14508284980965955191925301 1360151716965558299242997)
                    ·
                      rfl

theorem cell23_7946658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 1, 3, 5].length) (baseStart_7946658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7946658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7946658 prefixEnd_7946658 := by exact prefixLift 7946658
  have htrace : WordTrace (prefixWord ++ tailWord_7946658) baseStart_7946658 baseEnd_7946658 := by
    simpa [prefixWord, tailWord_7946658, baseEnd_7946658] using wordTrace_append hprefix tailTrace_7946658
  have hstable : (prefixWord ++ tailWord_7946658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7946658).length < 2 ^ (prefixWord ++ tailWord_7946658).sum := by decide
  have hdescent : baseEnd_7946658 < baseStart_7946658 := by decide
  rcases family_descends (prefixWord ++ tailWord_7946658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7946691 : List Nat := [1, 1, 1, 3, 1, 1, 3, 1, 5, 2, 4]
def baseStart_7946691 : Nat := 118140960795 + 7946691 * 2 ^ 59
def prefixEnd_7946691 : Nat := 4983230072969 + 3 ^ 40 * 7946691 * 2
def baseEnd_7946691 : Nat := 4080472095758273268616339

theorem tailTrace_7946691 : CollatzResearch.WordTrace tailWord_7946691 prefixEnd_7946691 4080472095758273268616339 := by
  unfold tailWord_7946691
  simp only [CollatzResearch.WordTrace]
  refine ⟨289839632053503168616751927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193226421369002112411167951 289839632053503168616751927)
  ·
    refine ⟨434759448080254752925127891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289839632053503168616751927 434759448080254752925127891)
    ·
      refine ⟨652139172120382129387691837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 434759448080254752925127891 652139172120382129387691837)
      ·
        refine ⟨244552189545143298520384439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 652139172120382129387691837 244552189545143298520384439)
        ·
          refine ⟨366828284317714947780576659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244552189545143298520384439 366828284317714947780576659)
          ·
            refine ⟨550242426476572421670864989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 366828284317714947780576659 550242426476572421670864989)
            ·
              refine ⟨206340909928714658126574371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 550242426476572421670864989 206340909928714658126574371)
              ·
                refine ⟨309511364893071987189861557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 206340909928714658126574371 309511364893071987189861557)
                ·
                  refine ⟨29016690458725498799049521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 309511364893071987189861557 29016690458725498799049521)
                  ·
                    refine ⟨21762517844044124099287141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29016690458725498799049521 21762517844044124099287141)
                    ·
                      refine ⟨4080472095758273268616339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21762517844044124099287141 4080472095758273268616339)
                      ·
                        rfl

theorem cell23_7946691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 1, 5, 2, 4].length) (baseStart_7946691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7946691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7946691 prefixEnd_7946691 := by exact prefixLift 7946691
  have htrace : WordTrace (prefixWord ++ tailWord_7946691) baseStart_7946691 baseEnd_7946691 := by
    simpa [prefixWord, tailWord_7946691, baseEnd_7946691] using wordTrace_append hprefix tailTrace_7946691
  have hstable : (prefixWord ++ tailWord_7946691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7946691).length < 2 ^ (prefixWord ++ tailWord_7946691).sum := by decide
  have hdescent : baseEnd_7946691 < baseStart_7946691 := by decide
  rcases family_descends (prefixWord ++ tailWord_7946691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7946698 : List Nat := [3, 1, 2, 1, 2, 2, 1, 1, 5, 2, 3]
def baseStart_7946698 : Nat := 118140960795 + 7946698 * 2 ^ 59
def prefixEnd_7946698 : Nat := 4983230072969 + 3 ^ 40 * 7946698 * 2
def baseEnd_7946698 : Nat := 4080475690122854741228807

theorem tailTrace_7946698 : CollatzResearch.WordTrace tailWord_7946698 prefixEnd_7946698 4080475690122854741228807 := by
  unfold tailWord_7946698
  simp only [CollatzResearch.WordTrace]
  refine ⟨72459971841119452203064187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193226591576318539208171165 72459971841119452203064187)
  ·
    refine ⟨108689957761679178304596281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72459971841119452203064187 108689957761679178304596281)
    ·
      refine ⟨81517468321259383728447211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108689957761679178304596281 81517468321259383728447211)
      ·
        refine ⟨122276202481889075592670817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81517468321259383728447211 122276202481889075592670817)
        ·
          refine ⟨91707151861416806694503113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122276202481889075592670817 91707151861416806694503113)
          ·
            refine ⟨68780363896062605020877335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91707151861416806694503113 68780363896062605020877335)
            ·
              refine ⟨103170545844093907531316003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68780363896062605020877335 103170545844093907531316003)
              ·
                refine ⟨154755818766140861296974005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103170545844093907531316003 154755818766140861296974005)
                ·
                  refine ⟨14508358009325705746591313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 154755818766140861296974005 14508358009325705746591313)
                  ·
                    refine ⟨10881268506994279309943485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14508358009325705746591313 10881268506994279309943485)
                    ·
                      refine ⟨4080475690122854741228807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10881268506994279309943485 4080475690122854741228807)
                      ·
                        rfl

theorem cell23_7946698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 1, 5, 2, 3].length) (baseStart_7946698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7946698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7946698 prefixEnd_7946698 := by exact prefixLift 7946698
  have htrace : WordTrace (prefixWord ++ tailWord_7946698) baseStart_7946698 baseEnd_7946698 := by
    simpa [prefixWord, tailWord_7946698, baseEnd_7946698] using wordTrace_append hprefix tailTrace_7946698
  have hstable : (prefixWord ++ tailWord_7946698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7946698).length < 2 ^ (prefixWord ++ tailWord_7946698).sum := by decide
  have hdescent : baseEnd_7946698 < baseStart_7946698 := by decide
  rcases family_descends (prefixWord ++ tailWord_7946698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7946761 : List Nat := [1, 2, 1, 1, 3, 1, 2, 3, 1, 8]
def baseStart_7946761 : Nat := 118140960795 + 7946761 * 2 ^ 59
def prefixEnd_7946761 : Nat := 4983230072969 + 3 ^ 40 * 7946761 * 2
def baseEnd_7946761 : Nat := 1360169346468029331580339

theorem tailTrace_7946761 : CollatzResearch.WordTrace tailWord_7946761 prefixEnd_7946761 1360169346468029331580339 := by
  unfold tailWord_7946761
  simp only [CollatzResearch.WordTrace]
  refine ⟨289842185163249570571800137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193228123442166380381200091 289842185163249570571800137)
  ·
    refine ⟨217381638872437177928850103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289842185163249570571800137 217381638872437177928850103)
    ·
      refine ⟨326072458308655766893275155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217381638872437177928850103 326072458308655766893275155)
      ·
        refine ⟨489108687462983650339912733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 326072458308655766893275155 489108687462983650339912733)
        ·
          refine ⟨183415757798618868877467275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 489108687462983650339912733 183415757798618868877467275)
          ·
            refine ⟨275123636697928303316200913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183415757798618868877467275 275123636697928303316200913)
            ·
              refine ⟨206342727523446227487150685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 275123636697928303316200913 206342727523446227487150685)
              ·
                refine ⟨77378522821292335307681507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 206342727523446227487150685 77378522821292335307681507)
                ·
                  refine ⟨116067784231938502961522261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77378522821292335307681507 116067784231938502961522261)
                  ·
                    refine ⟨1360169346468029331580339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 116067784231938502961522261 1360169346468029331580339)
                    ·
                      rfl

theorem cell23_7946761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 3, 1, 8].length) (baseStart_7946761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7946761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7946761 prefixEnd_7946761 := by exact prefixLift 7946761
  have htrace : WordTrace (prefixWord ++ tailWord_7946761) baseStart_7946761 baseEnd_7946761 := by
    simpa [prefixWord, tailWord_7946761, baseEnd_7946761] using wordTrace_append hprefix tailTrace_7946761
  have hstable : (prefixWord ++ tailWord_7946761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7946761).length < 2 ^ (prefixWord ++ tailWord_7946761).sum := by decide
  have hdescent : baseEnd_7946761 < baseStart_7946761 := by decide
  rcases family_descends (prefixWord ++ tailWord_7946761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7946785 : List Nat := [1, 2, 3, 2, 2, 1, 2, 1, 3, 4, 2]
def baseStart_7946785 : Nat := 118140960795 + 7946785 * 2 ^ 59
def prefixEnd_7946785 : Nat := 4983230072969 + 3 ^ 40 * 7946785 * 2
def baseEnd_7946785 : Nat := 4080520362939795900840907

theorem tailTrace_7946785 : CollatzResearch.WordTrace tailWord_7946785 prefixEnd_7946785 4080520362939795900840907 := by
  unfold tailWord_7946785
  simp only [CollatzResearch.WordTrace]
  refine ⟨289843060515162622670673809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193228707010108415113782539 289843060515162622670673809)
  ·
    refine ⟨217382295386371967003005357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289843060515162622670673809 217382295386371967003005357)
    ·
      refine ⟨81518360769889487626127009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 217382295386371967003005357 81518360769889487626127009)
      ·
        refine ⟨61138770577417115719595257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81518360769889487626127009 61138770577417115719595257)
        ·
          refine ⟨45854077933062836789696443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61138770577417115719595257 45854077933062836789696443)
          ·
            refine ⟨68781116899594255184544665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45854077933062836789696443 68781116899594255184544665)
            ·
              refine ⟨51585837674695691388408499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68781116899594255184544665 51585837674695691388408499)
              ·
                refine ⟨77378756512043537082612749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51585837674695691388408499 77378756512043537082612749)
                ·
                  refine ⟨29017033692016326405979781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77378756512043537082612749 29017033692016326405979781)
                  ·
                    refine ⟨5440693817253061201121209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29017033692016326405979781 5440693817253061201121209)
                    ·
                      refine ⟨4080520362939795900840907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5440693817253061201121209 4080520362939795900840907)
                      ·
                        rfl

theorem cell23_7946785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 1, 3, 4, 2].length) (baseStart_7946785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7946785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7946785 prefixEnd_7946785 := by exact prefixLift 7946785
  have htrace : WordTrace (prefixWord ++ tailWord_7946785) baseStart_7946785 baseEnd_7946785 := by
    simpa [prefixWord, tailWord_7946785, baseEnd_7946785] using wordTrace_append hprefix tailTrace_7946785
  have hstable : (prefixWord ++ tailWord_7946785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7946785).length < 2 ^ (prefixWord ++ tailWord_7946785).sum := by decide
  have hdescent : baseEnd_7946785 < baseStart_7946785 := by decide
  rcases family_descends (prefixWord ++ tailWord_7946785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7946797 : List Nat := [1, 5, 4, 1, 1, 1, 3, 2, 1, 2, 2]
def baseStart_7946797 : Nat := 118140960795 + 7946797 * 2 ^ 59
def prefixEnd_7946797 : Nat := 4983230072969 + 3 ^ 40 * 7946797 * 2
def baseEnd_7946797 : Nat := 4080526524707649853890853

theorem tailTrace_7946797 : CollatzResearch.WordTrace tailWord_7946797 prefixEnd_7946797 4080526524707649853890853 := by
  unfold tailWord_7946797
  simp only [CollatzResearch.WordTrace]
  refine ⟨289843498191119148720110645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193228998794079432480073763 289843498191119148720110645)
  ·
    refine ⟨27172827955417420192510373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 289843498191119148720110645 27172827955417420192510373)
    ·
      refine ⟨5094905241640766286095695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27172827955417420192510373 5094905241640766286095695)
      ·
        refine ⟨7642357862461149429143543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5094905241640766286095695 7642357862461149429143543)
        ·
          refine ⟨11463536793691724143715315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7642357862461149429143543 11463536793691724143715315)
          ·
            refine ⟨17195305190537586215572973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11463536793691724143715315 17195305190537586215572973)
            ·
              refine ⟨6448239446451594830839865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17195305190537586215572973 6448239446451594830839865)
              ·
                refine ⟨4836179584838696123129899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6448239446451594830839865 4836179584838696123129899)
                ·
                  refine ⟨7254269377258044184694849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4836179584838696123129899 7254269377258044184694849)
                  ·
                    refine ⟨5440702032943533138521137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7254269377258044184694849 5440702032943533138521137)
                    ·
                      refine ⟨4080526524707649853890853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5440702032943533138521137 4080526524707649853890853)
                      ·
                        rfl

theorem cell23_7946797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 3, 2, 1, 2, 2].length) (baseStart_7946797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7946797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7946797 prefixEnd_7946797 := by exact prefixLift 7946797
  have htrace : WordTrace (prefixWord ++ tailWord_7946797) baseStart_7946797 baseEnd_7946797 := by
    simpa [prefixWord, tailWord_7946797, baseEnd_7946797] using wordTrace_append hprefix tailTrace_7946797
  have hstable : (prefixWord ++ tailWord_7946797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7946797).length < 2 ^ (prefixWord ++ tailWord_7946797).sum := by decide
  have hdescent : baseEnd_7946797 < baseStart_7946797 := by decide
  rcases family_descends (prefixWord ++ tailWord_7946797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7946802 : List Nat := [3, 2, 1, 1, 2, 1, 4, 1, 4, 2, 2]
def baseStart_7946802 : Nat := 118140960795 + 7946802 * 2 ^ 59
def prefixEnd_7946802 : Nat := 4983230072969 + 3 ^ 40 * 7946802 * 2
def baseEnd_7946802 : Nat := 4080529092110922334328329

theorem tailTrace_7946802 : CollatzResearch.WordTrace tailWord_7946802 prefixEnd_7946802 4080529092110922334328329 := by
  unfold tailWord_7946802
  simp only [CollatzResearch.WordTrace]
  refine ⟨72460920139025258643510665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193229120370734023049361773 72460920139025258643510665)
  ·
    refine ⟨54345690104268943982632999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72460920139025258643510665 54345690104268943982632999)
    ·
      refine ⟨81518535156403415973949499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54345690104268943982632999 81518535156403415973949499)
      ·
        refine ⟨122277802734605123960924249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81518535156403415973949499 122277802734605123960924249)
        ·
          refine ⟨91708352050953842970693187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122277802734605123960924249 91708352050953842970693187)
          ·
            refine ⟨137562528076430764456039781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91708352050953842970693187 137562528076430764456039781)
            ·
              refine ⟨25792974014330768335507459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 137562528076430764456039781 25792974014330768335507459)
              ·
                refine ⟨38689461021496152503261189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25792974014330768335507459 38689461021496152503261189)
                ·
                  refine ⟨7254273941530528594361473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38689461021496152503261189 7254273941530528594361473)
                  ·
                    refine ⟨5440705456147896445771105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7254273941530528594361473 5440705456147896445771105)
                    ·
                      refine ⟨4080529092110922334328329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5440705456147896445771105 4080529092110922334328329)
                      ·
                        rfl

theorem cell23_7946802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 1, 4, 2, 2].length) (baseStart_7946802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7946802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7946802 prefixEnd_7946802 := by exact prefixLift 7946802
  have htrace : WordTrace (prefixWord ++ tailWord_7946802) baseStart_7946802 baseEnd_7946802 := by
    simpa [prefixWord, tailWord_7946802, baseEnd_7946802] using wordTrace_append hprefix tailTrace_7946802
  have hstable : (prefixWord ++ tailWord_7946802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7946802).length < 2 ^ (prefixWord ++ tailWord_7946802).sum := by decide
  have hdescent : baseEnd_7946802 < baseStart_7946802 := by decide
  rcases family_descends (prefixWord ++ tailWord_7946802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7946822 : List Nat := [6, 1, 1, 1, 2, 1, 1, 2, 2, 1, 5]
def baseStart_7946822 : Nat := 118140960795 + 7946822 * 2 ^ 59
def prefixEnd_7946822 : Nat := 4983230072969 + 3 ^ 40 * 7946822 * 2
def baseEnd_7946822 : Nat := 4080539361724012256078237

theorem tailTrace_7946822 : CollatzResearch.WordTrace tailWord_7946822 prefixEnd_7946822 4080539361724012256078237 := by
  unfold tailWord_7946822
  simp only [CollatzResearch.WordTrace]
  refine ⟨9057637813000893062180335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 193229606677352385326513813 9057637813000893062180335)
  ·
    refine ⟨13586456719501339593270503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9057637813000893062180335 13586456719501339593270503)
    ·
      refine ⟨20379685079252009389905755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13586456719501339593270503 20379685079252009389905755)
      ·
        refine ⟨30569527618878014084858633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20379685079252009389905755 30569527618878014084858633)
        ·
          refine ⟨22927145714158510563643975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30569527618878014084858633 22927145714158510563643975)
          ·
            refine ⟨34390718571237765845465963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22927145714158510563643975 34390718571237765845465963)
            ·
              refine ⟨51586077856856648768198945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34390718571237765845465963 51586077856856648768198945)
              ·
                refine ⟨38689558392642486576149209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51586077856856648768198945 38689558392642486576149209)
                ·
                  refine ⟨29017168794481864932111907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38689558392642486576149209 29017168794481864932111907)
                  ·
                    refine ⟨43525753191722797398167861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29017168794481864932111907 43525753191722797398167861)
                    ·
                      refine ⟨4080539361724012256078237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43525753191722797398167861 4080539361724012256078237)
                      ·
                        rfl

theorem cell23_7946822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 2, 2, 1, 5].length) (baseStart_7946822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7946822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7946822 prefixEnd_7946822 := by exact prefixLift 7946822
  have htrace : WordTrace (prefixWord ++ tailWord_7946822) baseStart_7946822 baseEnd_7946822 := by
    simpa [prefixWord, tailWord_7946822, baseEnd_7946822] using wordTrace_append hprefix tailTrace_7946822
  have hstable : (prefixWord ++ tailWord_7946822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7946822).length < 2 ^ (prefixWord ++ tailWord_7946822).sum := by decide
  have hdescent : baseEnd_7946822 < baseStart_7946822 := by decide
  rcases family_descends (prefixWord ++ tailWord_7946822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7946848 : List Nat := [2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 5]
def baseStart_7946848 : Nat := 118140960795 + 7946848 * 2 ^ 59
def prefixEnd_7946848 : Nat := 4983230072969 + 3 ^ 40 * 7946848 * 2
def baseEnd_7946848 : Nat := 4080552712221029154353117

theorem tailTrace_7946848 : CollatzResearch.WordTrace tailWord_7946848 prefixEnd_7946848 4080552712221029154353117 := by
  unfold tailWord_7946848
  simp only [CollatzResearch.WordTrace]
  refine ⟨144922679156967192215108599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193230238875956256286811465 144922679156967192215108599)
  ·
    refine ⟨217384018735450788322662899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144922679156967192215108599 217384018735450788322662899)
    ·
      refine ⟨326076028103176182483994349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217384018735450788322662899 326076028103176182483994349)
      ·
        refine ⟨122278510538691068431497881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 326076028103176182483994349 122278510538691068431497881)
        ·
          refine ⟨91708882904018301323623411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122278510538691068431497881 91708882904018301323623411)
          ·
            refine ⟨137563324356027451985435117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91708882904018301323623411 137563324356027451985435117)
            ·
              refine ⟨51586246633510294494538169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 137563324356027451985435117 51586246633510294494538169)
              ·
                refine ⟨38689684975132720870903627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51586246633510294494538169 38689684975132720870903627)
                ·
                  refine ⟨58034527462699081306355441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38689684975132720870903627 58034527462699081306355441)
                  ·
                    refine ⟨43525895597024310979766581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58034527462699081306355441 43525895597024310979766581)
                    ·
                      refine ⟨4080552712221029154353117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43525895597024310979766581 4080552712221029154353117)
                      ·
                        rfl

theorem cell23_7946848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 5].length) (baseStart_7946848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7946848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7946848 prefixEnd_7946848 := by exact prefixLift 7946848
  have htrace : WordTrace (prefixWord ++ tailWord_7946848) baseStart_7946848 baseEnd_7946848 := by
    simpa [prefixWord, tailWord_7946848, baseEnd_7946848] using wordTrace_append hprefix tailTrace_7946848
  have hstable : (prefixWord ++ tailWord_7946848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7946848).length < 2 ^ (prefixWord ++ tailWord_7946848).sum := by decide
  have hdescent : baseEnd_7946848 < baseStart_7946848 := by decide
  rcases family_descends (prefixWord ++ tailWord_7946848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7946862 : List Nat := [4, 1, 2, 2, 2, 1, 1, 1, 2, 5, 2]
def baseStart_7946862 : Nat := 118140960795 + 7946862 * 2 ^ 59
def prefixEnd_7946862 : Nat := 4983230072969 + 3 ^ 40 * 7946862 * 2
def baseEnd_7946862 : Nat := 4080559900950192099578053

theorem tailTrace_7946862 : CollatzResearch.WordTrace tailWord_7946862 prefixEnd_7946862 4080559900950192099578053 := by
  unfold tailWord_7946862
  simp only [CollatzResearch.WordTrace]
  refine ⟨36230733616985458102653355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 193230579290589109880817893 36230733616985458102653355)
  ·
    refine ⟨54346100425478187153980033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36230733616985458102653355 54346100425478187153980033)
    ·
      refine ⟨40759575319108640365485025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54346100425478187153980033 40759575319108640365485025)
      ·
        refine ⟨30569681489331480274113769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40759575319108640365485025 30569681489331480274113769)
        ·
          refine ⟨22927261116998610205585327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30569681489331480274113769 22927261116998610205585327)
          ·
            refine ⟨34390891675497915308377991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22927261116998610205585327 34390891675497915308377991)
            ·
              refine ⟨51586337513246872962566987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34390891675497915308377991 51586337513246872962566987)
              ·
                refine ⟨77379506269870309443850481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51586337513246872962566987 77379506269870309443850481)
                ·
                  refine ⟨58034629702402732082887861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77379506269870309443850481 58034629702402732082887861)
                  ·
                    refine ⟨5440746534600256132770737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 58034629702402732082887861 5440746534600256132770737)
                    ·
                      refine ⟨4080559900950192099578053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5440746534600256132770737 4080559900950192099578053)
                      ·
                        rfl

theorem cell23_7946862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 1, 2, 5, 2].length) (baseStart_7946862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7946862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7946862 prefixEnd_7946862 := by exact prefixLift 7946862
  have htrace : WordTrace (prefixWord ++ tailWord_7946862) baseStart_7946862 baseEnd_7946862 := by
    simpa [prefixWord, tailWord_7946862, baseEnd_7946862] using wordTrace_append hprefix tailTrace_7946862
  have hstable : (prefixWord ++ tailWord_7946862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7946862).length < 2 ^ (prefixWord ++ tailWord_7946862).sum := by decide
  have hdescent : baseEnd_7946862 < baseStart_7946862 := by decide
  rcases family_descends (prefixWord ++ tailWord_7946862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7946885 : List Nat := [1, 3, 1, 1, 4, 2, 1, 1, 5, 4]
def baseStart_7946885 : Nat := 118140960795 + 7946885 * 2 ^ 59
def prefixEnd_7946885 : Nat := 4983230072969 + 3 ^ 40 * 7946885 * 2
def baseEnd_7946885 : Nat := 1360190570335081836530149

theorem tailTrace_7946885 : CollatzResearch.WordTrace tailWord_7946885 prefixEnd_7946885 1360190570335081836530149 := by
  unfold tailWord_7946885
  simp only [CollatzResearch.WordTrace]
  refine ⟨289846707814800339749314109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193231138543200226499542739 289846707814800339749314109)
  ·
    refine ⟨108692515430550127405992791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 289846707814800339749314109 108692515430550127405992791)
    ·
      refine ⟨163038773145825191108989187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108692515430550127405992791 163038773145825191108989187)
      ·
        refine ⟨244558159718737786663483781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163038773145825191108989187 244558159718737786663483781)
        ·
          refine ⟨45854654947263334999403209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 244558159718737786663483781 45854654947263334999403209)
          ·
            refine ⟨34390991210447501249552407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45854654947263334999403209 34390991210447501249552407)
            ·
              refine ⟨51586486815671251874328611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34390991210447501249552407 51586486815671251874328611)
              ·
                refine ⟨77379730223506877811492917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51586486815671251874328611 77379730223506877811492917)
                ·
                  refine ⟨7254349708453769794827461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 77379730223506877811492917 7254349708453769794827461)
                  ·
                    refine ⟨1360190570335081836530149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7254349708453769794827461 1360190570335081836530149)
                    ·
                      rfl

theorem cell23_7946885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 1, 5, 4].length) (baseStart_7946885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7946885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7946885 prefixEnd_7946885 := by exact prefixLift 7946885
  have htrace : WordTrace (prefixWord ++ tailWord_7946885) baseStart_7946885 baseEnd_7946885 := by
    simpa [prefixWord, tailWord_7946885, baseEnd_7946885] using wordTrace_append hprefix tailTrace_7946885
  have hstable : (prefixWord ++ tailWord_7946885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7946885).length < 2 ^ (prefixWord ++ tailWord_7946885).sum := by decide
  have hdescent : baseEnd_7946885 < baseStart_7946885 := by decide
  rcases family_descends (prefixWord ++ tailWord_7946885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7946952 : List Nat := [2, 1, 3, 1, 2, 3, 2, 1, 1, 5, 2]
def baseStart_7946952 : Nat := 118140960795 + 7946952 * 2 ^ 59
def prefixEnd_7946952 : Nat := 4983230072969 + 3 ^ 40 * 7946952 * 2
def baseEnd_7946952 : Nat := 4080606114209096747452639

theorem tailTrace_7946952 : CollatzResearch.WordTrace tailWord_7946952 prefixEnd_7946952 4080606114209096747452639 := by
  unfold tailWord_7946952
  simp only [CollatzResearch.WordTrace]
  refine ⟨144924575752778805096001555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193232767670371740128002073 144924575752778805096001555)
  ·
    refine ⟨217386863629168207644002333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144924575752778805096001555 217386863629168207644002333)
    ·
      refine ⟨81520073860938077866500875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 217386863629168207644002333 81520073860938077866500875)
      ·
        refine ⟨122280110791407116799751313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81520073860938077866500875 122280110791407116799751313)
        ·
          refine ⟨91710083093555337599813485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122280110791407116799751313 91710083093555337599813485)
          ·
            refine ⟨34391281160083251599930057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91710083093555337599813485 34391281160083251599930057)
            ·
              refine ⟨25793460870062438699947543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34391281160083251599930057 25793460870062438699947543)
              ·
                refine ⟨38690191305093658049921315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25793460870062438699947543 38690191305093658049921315)
                ·
                  refine ⟨58035286957640487074881973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38690191305093658049921315 58035286957640487074881973)
                  ·
                    refine ⟨5440808152278795663270185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 58035286957640487074881973 5440808152278795663270185)
                    ·
                      refine ⟨4080606114209096747452639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5440808152278795663270185 4080606114209096747452639)
                      ·
                        rfl

theorem cell23_7946952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 1, 1, 5, 2].length) (baseStart_7946952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7946952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7946952 prefixEnd_7946952 := by exact prefixLift 7946952
  have htrace : WordTrace (prefixWord ++ tailWord_7946952) baseStart_7946952 baseEnd_7946952 := by
    simpa [prefixWord, tailWord_7946952, baseEnd_7946952] using wordTrace_append hprefix tailTrace_7946952
  have hstable : (prefixWord ++ tailWord_7946952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7946952).length < 2 ^ (prefixWord ++ tailWord_7946952).sum := by decide
  have hdescent : baseEnd_7946952 < baseStart_7946952 := by decide
  rcases family_descends (prefixWord ++ tailWord_7946952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7946985 : List Nat := [1, 2, 1, 1, 1, 2, 6, 2, 1, 1, 5]
def baseStart_7946985 : Nat := 118140960795 + 7946985 * 2 ^ 59
def prefixEnd_7946985 : Nat := 4983230072969 + 3 ^ 40 * 7946985 * 2
def baseEnd_7946985 : Nat := 4080623059070695118339987

theorem tailTrace_7946985 : CollatzResearch.WordTrace tailWord_7946985 prefixEnd_7946985 4080623059070695118339987 := by
  unfold tailWord_7946985
  simp only [CollatzResearch.WordTrace]
  refine ⟨289850355114438056827954409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193233570076292037885302939 289850355114438056827954409)
  ·
    refine ⟨217387766335828542620965807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289850355114438056827954409 217387766335828542620965807)
    ·
      refine ⟨326081649503742813931448711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217387766335828542620965807 326081649503742813931448711)
      ·
        refine ⟨489122474255614220897173067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 326081649503742813931448711 489122474255614220897173067)
        ·
          refine ⟨733683711383421331345759601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 489122474255614220897173067 733683711383421331345759601)
          ·
            refine ⟨550262783537565998509319701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 733683711383421331345759601 550262783537565998509319701)
            ·
              refine ⟨25793567978323406180124361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 550262783537565998509319701 25793567978323406180124361)
              ·
                refine ⟨19345175983742554635093271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25793567978323406180124361 19345175983742554635093271)
                ·
                  refine ⟨29017763975613831952639907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19345175983742554635093271 29017763975613831952639907)
                  ·
                    refine ⟨43526645963420747928959861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29017763975613831952639907 43526645963420747928959861)
                    ·
                      refine ⟨4080623059070695118339987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43526645963420747928959861 4080623059070695118339987)
                      ·
                        rfl

theorem cell23_7946985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 2, 1, 1, 5].length) (baseStart_7946985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7946985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7946985 prefixEnd_7946985 := by exact prefixLift 7946985
  have htrace : WordTrace (prefixWord ++ tailWord_7946985) baseStart_7946985 baseEnd_7946985 := by
    simpa [prefixWord, tailWord_7946985, baseEnd_7946985] using wordTrace_append hprefix tailTrace_7946985
  have hstable : (prefixWord ++ tailWord_7946985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7946985).length < 2 ^ (prefixWord ++ tailWord_7946985).sum := by decide
  have hdescent : baseEnd_7946985 < baseStart_7946985 := by decide
  rcases family_descends (prefixWord ++ tailWord_7946985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7946992 : List Nat := [2, 1, 1, 1, 3, 1, 5, 3, 2, 4]
def baseStart_7946992 : Nat := 118140960795 + 7946992 * 2 ^ 59
def prefixEnd_7946992 : Nat := 4983230072969 + 3 ^ 40 * 7946992 * 2
def baseEnd_7946992 : Nat := 1360208884478425530317485

theorem tailTrace_7946992 : CollatzResearch.WordTrace tailWord_7946992 prefixEnd_7946992 1360208884478425530317485 := by
  unfold tailWord_7946992
  simp only [CollatzResearch.WordTrace]
  refine ⟨144925305212706348511729615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193233740283608464682306153 144925305212706348511729615)
  ·
    refine ⟨217387957819059522767594423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144925305212706348511729615 217387957819059522767594423)
    ·
      refine ⟨326081936728589284151391635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217387957819059522767594423 326081936728589284151391635)
      ·
        refine ⟨489122905092883926227087453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 326081936728589284151391635 489122905092883926227087453)
        ·
          refine ⟨183421089409831472335157795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 489122905092883926227087453 183421089409831472335157795)
          ·
            refine ⟨275131634114747208502736693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183421089409831472335157795 275131634114747208502736693)
            ·
              refine ⟨25793590698257550797131565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 275131634114747208502736693 25793590698257550797131565)
              ·
                refine ⟨9672596511846581548924337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25793590698257550797131565 9672596511846581548924337)
                ·
                  refine ⟨7254447383884936161693253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9672596511846581548924337 7254447383884936161693253)
                  ·
                    refine ⟨1360208884478425530317485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7254447383884936161693253 1360208884478425530317485)
                    ·
                      rfl

theorem cell23_7946992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 3, 2, 4].length) (baseStart_7946992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7946992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7946992 prefixEnd_7946992 := by exact prefixLift 7946992
  have htrace : WordTrace (prefixWord ++ tailWord_7946992) baseStart_7946992 baseEnd_7946992 := by
    simpa [prefixWord, tailWord_7946992, baseEnd_7946992] using wordTrace_append hprefix tailTrace_7946992
  have hstable : (prefixWord ++ tailWord_7946992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7946992).length < 2 ^ (prefixWord ++ tailWord_7946992).sum := by decide
  have hdescent : baseEnd_7946992 < baseStart_7946992 := by decide
  rcases family_descends (prefixWord ++ tailWord_7946992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7946995 : List Nat := [1, 1, 1, 2, 2, 3, 1, 5, 1, 2, 4]
def baseStart_7946995 : Nat := 118140960795 + 7946995 * 2 ^ 59
def prefixEnd_7946995 : Nat := 4983230072969 + 3 ^ 40 * 7946995 * 2
def baseEnd_7946995 : Nat := 4080628193877240079214941

theorem tailTrace_7946995 : CollatzResearch.WordTrace tailWord_7946995 prefixEnd_7946995 4080628193877240079214941 := by
  unfold tailWord_7946995
  simp only [CollatzResearch.WordTrace]
  refine ⟨289850719844401828535818439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193233813229601219023878959 289850719844401828535818439)
  ·
    refine ⟨434776079766602742803727659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289850719844401828535818439 434776079766602742803727659)
    ·
      refine ⟨652164119649904114205591489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 434776079766602742803727659 652164119649904114205591489)
      ·
        refine ⟨489123089737428085654193617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 652164119649904114205591489 489123089737428085654193617)
        ·
          refine ⟨366842317303071064240645213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 489123089737428085654193617 366842317303071064240645213)
          ·
            refine ⟨137565868988651649090241955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 366842317303071064240645213 137565868988651649090241955)
            ·
              refine ⟨206348803482977473635362933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137565868988651649090241955 206348803482977473635362933)
              ·
                refine ⟨19345200326529138153315275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 206348803482977473635362933 19345200326529138153315275)
                ·
                  refine ⟨29017800489793707229972913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19345200326529138153315275 29017800489793707229972913)
                  ·
                    refine ⟨21763350367345280422479685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29017800489793707229972913 21763350367345280422479685)
                    ·
                      refine ⟨4080628193877240079214941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21763350367345280422479685 4080628193877240079214941)
                      ·
                        rfl

theorem cell23_7946995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 5, 1, 2, 4].length) (baseStart_7946995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7946995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7946995 prefixEnd_7946995 := by exact prefixLift 7946995
  have htrace : WordTrace (prefixWord ++ tailWord_7946995) baseStart_7946995 baseEnd_7946995 := by
    simpa [prefixWord, tailWord_7946995, baseEnd_7946995] using wordTrace_append hprefix tailTrace_7946995
  have hstable : (prefixWord ++ tailWord_7946995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7946995).length < 2 ^ (prefixWord ++ tailWord_7946995).sum := by decide
  have hdescent : baseEnd_7946995 < baseStart_7946995 := by decide
  rcases family_descends (prefixWord ++ tailWord_7946995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7946996 : List Nat := [2, 6, 1, 1, 2, 1, 1, 1, 3, 5]
def baseStart_7946996 : Nat := 118140960795 + 7946996 * 2 ^ 59
def prefixEnd_7946996 : Nat := 4983230072969 + 3 ^ 40 * 7946996 * 2
def baseEnd_7946996 : Nat := 1360209569119298191767479

theorem tailTrace_7946996 : CollatzResearch.WordTrace tailWord_7946996 prefixEnd_7946996 1360209569119298191767479 := by
  unfold tailWord_7946996
  simp only [CollatzResearch.WordTrace]
  refine ⟨144925378158699102853302421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193233837544932137137736561 144925378158699102853302421)
  ·
    refine ⟨6793377101189020446248551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 144925378158699102853302421 6793377101189020446248551)
    ·
      refine ⟨10190065651783530669372827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6793377101189020446248551 10190065651783530669372827)
      ·
        refine ⟨15285098477675296004059241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10190065651783530669372827 15285098477675296004059241)
        ·
          refine ⟨11463823858256472003044431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15285098477675296004059241 11463823858256472003044431)
          ·
            refine ⟨17195735787384708004566647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11463823858256472003044431 17195735787384708004566647)
            ·
              refine ⟨25793603681077062006849971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17195735787384708004566647 25793603681077062006849971)
              ·
                refine ⟨38690405521615593010274957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25793603681077062006849971 38690405521615593010274957)
                ·
                  refine ⟨14508902070605847378853109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38690405521615593010274957 14508902070605847378853109)
                  ·
                    refine ⟨1360209569119298191767479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14508902070605847378853109 1360209569119298191767479)
                    ·
                      rfl

theorem cell23_7946996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 1, 3, 5].length) (baseStart_7946996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7946996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7946996 prefixEnd_7946996 := by exact prefixLift 7946996
  have htrace : WordTrace (prefixWord ++ tailWord_7946996) baseStart_7946996 baseEnd_7946996 := by
    simpa [prefixWord, tailWord_7946996, baseEnd_7946996] using wordTrace_append hprefix tailTrace_7946996
  have hstable : (prefixWord ++ tailWord_7946996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7946996).length < 2 ^ (prefixWord ++ tailWord_7946996).sum := by decide
  have hdescent : baseEnd_7946996 < baseStart_7946996 := by decide
  rcases family_descends (prefixWord ++ tailWord_7946996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7947012 : List Nat := [2, 3, 2, 2, 1, 1, 3, 2, 1, 2, 4]
def baseStart_7947012 : Nat := 118140960795 + 7947012 * 2 ^ 59
def prefixEnd_7947012 : Nat := 4983230072969 + 3 ^ 40 * 7947012 * 2
def baseEnd_7947012 : Nat := 4080636923048366512702363

theorem tailTrace_7947012 : CollatzResearch.WordTrace tailWord_7947012 prefixEnd_7947012 4080636923048366512702363 := by
  unfold tailWord_7947012
  simp only [CollatzResearch.WordTrace]
  refine ⟨144925669942670120219593645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193234226590226826959458193 144925669942670120219593645)
  ·
    refine ⟨54347126228501295082347617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144925669942670120219593645 54347126228501295082347617)
    ·
      refine ⟨40760344671375971311760713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54347126228501295082347617 40760344671375971311760713)
      ·
        refine ⟨30570258503531978483820535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40760344671375971311760713 30570258503531978483820535)
        ·
          refine ⟨45855387755297967725730803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30570258503531978483820535 45855387755297967725730803)
          ·
            refine ⟨68783081632946951588596205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45855387755297967725730803 68783081632946951588596205)
            ·
              refine ⟨25793655612355106845723577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68783081632946951588596205 25793655612355106845723577)
              ·
                refine ⟨19345241709266330134292683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25793655612355106845723577 19345241709266330134292683)
                ·
                  refine ⟨29017862563899495201439025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19345241709266330134292683 29017862563899495201439025)
                  ·
                    refine ⟨21763396922924621401079269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29017862563899495201439025 21763396922924621401079269)
                    ·
                      refine ⟨4080636923048366512702363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21763396922924621401079269 4080636923048366512702363)
                      ·
                        rfl

theorem cell23_7947012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 2, 1, 2, 4].length) (baseStart_7947012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7947012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7947012 prefixEnd_7947012 := by exact prefixLift 7947012
  have htrace : WordTrace (prefixWord ++ tailWord_7947012) baseStart_7947012 baseEnd_7947012 := by
    simpa [prefixWord, tailWord_7947012, baseEnd_7947012] using wordTrace_append hprefix tailTrace_7947012
  have hstable : (prefixWord ++ tailWord_7947012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7947012).length < 2 ^ (prefixWord ++ tailWord_7947012).sum := by decide
  have hdescent : baseEnd_7947012 < baseStart_7947012 := by decide
  rcases family_descends (prefixWord ++ tailWord_7947012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7947059 : List Nat := [1, 1, 1, 2, 6, 1, 2, 1, 3, 3, 2]
def baseStart_7947059 : Nat := 118140960795 + 7947059 * 2 ^ 59
def prefixEnd_7947059 : Nat := 4983230072969 + 3 ^ 40 * 7947059 * 2
def baseEnd_7947059 : Nat := 4080661056639127828814647

theorem tailTrace_7947059 : CollatzResearch.WordTrace tailWord_7947059 prefixEnd_7947059 4080661056639127828814647 := by
  unfold tailWord_7947059
  simp only [CollatzResearch.WordTrace]
  refine ⟨289853054116169967466148231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193235369410779978310765487 289853054116169967466148231)
  ·
    refine ⟨434779581174254951199222347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289853054116169967466148231 434779581174254951199222347)
    ·
      refine ⟨652169371761382426798833521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 434779581174254951199222347 652169371761382426798833521)
      ·
        refine ⟨489127028821036820099125141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 652169371761382426798833521 489127028821036820099125141)
        ·
          refine ⟨22927829475986100942146491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 489127028821036820099125141 22927829475986100942146491)
          ·
            refine ⟨34391744213979151413219737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22927829475986100942146491 34391744213979151413219737)
            ·
              refine ⟨25793808160484363559914803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34391744213979151413219737 25793808160484363559914803)
              ·
                refine ⟨38690712240726545339872205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25793808160484363559914803 38690712240726545339872205)
                ·
                  refine ⟨14509017090272454502452077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38690712240726545339872205 14509017090272454502452077)
                  ·
                    refine ⟨5440881408852170438419529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14509017090272454502452077 5440881408852170438419529)
                    ·
                      refine ⟨4080661056639127828814647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5440881408852170438419529 4080661056639127828814647)
                      ·
                        rfl

theorem cell23_7947059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 1, 3, 3, 2].length) (baseStart_7947059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7947059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7947059 prefixEnd_7947059 := by exact prefixLift 7947059
  have htrace : WordTrace (prefixWord ++ tailWord_7947059) baseStart_7947059 baseEnd_7947059 := by
    simpa [prefixWord, tailWord_7947059, baseEnd_7947059] using wordTrace_append hprefix tailTrace_7947059
  have hstable : (prefixWord ++ tailWord_7947059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7947059).length < 2 ^ (prefixWord ++ tailWord_7947059).sum := by decide
  have hdescent : baseEnd_7947059 < baseStart_7947059 := by decide
  rcases family_descends (prefixWord ++ tailWord_7947059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7947070 : List Nat := [4, 2, 1, 2, 4, 1, 2, 1, 1, 2, 3]
def baseStart_7947070 : Nat := 118140960795 + 7947070 * 2 ^ 59
def prefixEnd_7947070 : Nat := 4983230072969 + 3 ^ 40 * 7947070 * 2
def baseEnd_7947070 : Nat := 4080666704926327285777097

theorem tailTrace_7947070 : CollatzResearch.WordTrace tailWord_7947070 prefixEnd_7947070 4080666704926327285777097 := by
  unfold tailWord_7947070
  simp only [CollatzResearch.WordTrace]
  refine ⟨36231681914891264543099833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 193235636879420077563199109 36231681914891264543099833)
  ·
    refine ⟨27173761436168448407324875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36231681914891264543099833 27173761436168448407324875)
    ·
      refine ⟨40760642154252672610987313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27173761436168448407324875 40760642154252672610987313)
      ·
        refine ⟨30570481615689504458240485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40760642154252672610987313 30570481615689504458240485)
        ·
          refine ⟨5731965302941782085920091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30570481615689504458240485 5731965302941782085920091)
          ·
            refine ⟨8597947954412673128880137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5731965302941782085920091 8597947954412673128880137)
            ·
              refine ⟨6448460965809504846660103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8597947954412673128880137 6448460965809504846660103)
              ·
                refine ⟨9672691448714257269990155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6448460965809504846660103 9672691448714257269990155)
                ·
                  refine ⟨14509037173071385904985233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9672691448714257269990155 14509037173071385904985233)
                  ·
                    refine ⟨10881777879803539428738925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14509037173071385904985233 10881777879803539428738925)
                    ·
                      refine ⟨4080666704926327285777097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10881777879803539428738925 4080666704926327285777097)
                      ·
                        rfl

theorem cell23_7947070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 2, 1, 1, 2, 3].length) (baseStart_7947070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7947070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7947070 prefixEnd_7947070 := by exact prefixLift 7947070
  have htrace : WordTrace (prefixWord ++ tailWord_7947070) baseStart_7947070 baseEnd_7947070 := by
    simpa [prefixWord, tailWord_7947070, baseEnd_7947070] using wordTrace_append hprefix tailTrace_7947070
  have hstable : (prefixWord ++ tailWord_7947070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7947070).length < 2 ^ (prefixWord ++ tailWord_7947070).sum := by decide
  have hdescent : baseEnd_7947070 < baseStart_7947070 := by decide
  rcases family_descends (prefixWord ++ tailWord_7947070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7947075 : List Nat := [1, 1, 1, 3, 1, 4, 2, 1, 1, 3, 5]
def baseStart_7947075 : Nat := 118140960795 + 7947075 * 2 ^ 59
def prefixEnd_7947075 : Nat := 4983230072969 + 3 ^ 40 * 7947075 * 2
def baseEnd_7947075 : Nat := 4080669272329599766214573

theorem tailTrace_7947075 : CollatzResearch.WordTrace tailWord_7947075 prefixEnd_7947075 4080669272329599766214573 := by
  unfold tailWord_7947075
  simp only [CollatzResearch.WordTrace]
  refine ⟨289853637684112002198730679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193235758456074668132487119 289853637684112002198730679)
  ·
    refine ⟨434780456526168003298096019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289853637684112002198730679 434780456526168003298096019)
    ·
      refine ⟨652170684789252004947144029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 434780456526168003298096019 652170684789252004947144029)
      ·
        refine ⟨244564006795969501855179011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 652170684789252004947144029 244564006795969501855179011)
        ·
          refine ⟨366846010193954252782768517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244564006795969501855179011 366846010193954252782768517)
          ·
            refine ⟨68783626911366422396769097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 366846010193954252782768517 68783626911366422396769097)
            ·
              refine ⟨51587720183524816797576823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68783626911366422396769097 51587720183524816797576823)
              ·
                refine ⟨77381580275287225196365235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51587720183524816797576823 77381580275287225196365235)
                ·
                  refine ⟨116072370412930837794547853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77381580275287225196365235 116072370412930837794547853)
                  ·
                    refine ⟨43527138904849064172955445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 116072370412930837794547853 43527138904849064172955445)
                    ·
                      refine ⟨4080669272329599766214573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43527138904849064172955445 4080669272329599766214573)
                      ·
                        rfl

theorem cell23_7947075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 1, 1, 3, 5].length) (baseStart_7947075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7947075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7947075 prefixEnd_7947075 := by exact prefixLift 7947075
  have htrace : WordTrace (prefixWord ++ tailWord_7947075) baseStart_7947075 baseEnd_7947075 := by
    simpa [prefixWord, tailWord_7947075, baseEnd_7947075] using wordTrace_append hprefix tailTrace_7947075
  have hstable : (prefixWord ++ tailWord_7947075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7947075).length < 2 ^ (prefixWord ++ tailWord_7947075).sum := by decide
  have hdescent : baseEnd_7947075 < baseStart_7947075 := by decide
  rcases family_descends (prefixWord ++ tailWord_7947075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7947112 : List Nat := [2, 1, 4, 2, 1, 2, 2, 2, 7]
def baseStart_7947112 : Nat := 118140960795 + 7947112 * 2 ^ 59
def prefixEnd_7947112 : Nat := 4983230072969 + 3 ^ 40 * 7947112 * 2
def baseEnd_7947112 : Nat := 453409807901535124605767

theorem tailTrace_7947112 : CollatzResearch.WordTrace tailWord_7947112 prefixEnd_7947112 453409807901535124605767 := by
  unfold tailWord_7947112
  simp only [CollatzResearch.WordTrace]
  refine ⟨144927493592488978758913795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193236658123318638345218393 144927493592488978758913795)
  ·
    refine ⟨217391240388733468138370693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144927493592488978758913795 217391240388733468138370693)
    ·
      refine ⟨40760857572887525275944505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 217391240388733468138370693 40760857572887525275944505)
      ·
        refine ⟨30570643179665643956958379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40760857572887525275944505 30570643179665643956958379)
        ·
          refine ⟨45855964769498465935437569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30570643179665643956958379 45855964769498465935437569)
          ·
            refine ⟨34391973577123849451578177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45855964769498465935437569 34391973577123849451578177)
            ·
              refine ⟨25793980182842887088683633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34391973577123849451578177 25793980182842887088683633)
              ·
                refine ⟨19345485137132165316512725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25793980182842887088683633 19345485137132165316512725)
                ·
                  refine ⟨453409807901535124605767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19345485137132165316512725 453409807901535124605767)
                  ·
                    rfl

theorem cell23_7947112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 2, 7].length) (baseStart_7947112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7947112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7947112 prefixEnd_7947112 := by exact prefixLift 7947112
  have htrace : WordTrace (prefixWord ++ tailWord_7947112) baseStart_7947112 baseEnd_7947112 := by
    simpa [prefixWord, tailWord_7947112, baseEnd_7947112] using wordTrace_append hprefix tailTrace_7947112
  have hstable : (prefixWord ++ tailWord_7947112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7947112).length < 2 ^ (prefixWord ++ tailWord_7947112).sum := by decide
  have hdescent : baseEnd_7947112 < baseStart_7947112 := by decide
  rcases family_descends (prefixWord ++ tailWord_7947112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7947122 : List Nat := [3, 2, 1, 2, 1, 1, 2, 2, 1, 5, 3]
def baseStart_7947122 : Nat := 118140960795 + 7947122 * 2 ^ 59
def prefixEnd_7947122 : Nat := 4983230072969 + 3 ^ 40 * 7947122 * 2
def baseEnd_7947122 : Nat := 4080693405920361082326857

theorem tailTrace_7947122 : CollatzResearch.WordTrace tailWord_7947122 prefixEnd_7947122 4080693405920361082326857 := by
  unfold tailWord_7947122
  simp only [CollatzResearch.WordTrace]
  refine ⟨72463837978735432306422905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193236901276627819483794413 72463837978735432306422905)
  ·
    refine ⟨54347878484051574229817179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72463837978735432306422905 54347878484051574229817179)
    ·
      refine ⟨81521817726077361344725769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54347878484051574229817179 81521817726077361344725769)
      ·
        refine ⟨61141363294558021008544327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81521817726077361344725769 61141363294558021008544327)
        ·
          refine ⟨91712044941837031512816491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61141363294558021008544327 91712044941837031512816491)
          ·
            refine ⟨137568067412755547269224737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91712044941837031512816491 137568067412755547269224737)
            ·
              refine ⟨103176050559566660451918553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137568067412755547269224737 103176050559566660451918553)
              ·
                refine ⟨77382037919674995338938915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103176050559566660451918553 77382037919674995338938915)
                ·
                  refine ⟨116073056879512493008408373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77382037919674995338938915 116073056879512493008408373)
                  ·
                    refine ⟨10881849082454296219538285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 116073056879512493008408373 10881849082454296219538285)
                    ·
                      refine ⟨4080693405920361082326857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10881849082454296219538285 4080693405920361082326857)
                      ·
                        rfl

theorem cell23_7947122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 2, 1, 5, 3].length) (baseStart_7947122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7947122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7947122 prefixEnd_7947122 := by exact prefixLift 7947122
  have htrace : WordTrace (prefixWord ++ tailWord_7947122) baseStart_7947122 baseEnd_7947122 := by
    simpa [prefixWord, tailWord_7947122, baseEnd_7947122] using wordTrace_append hprefix tailTrace_7947122
  have hstable : (prefixWord ++ tailWord_7947122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7947122).length < 2 ^ (prefixWord ++ tailWord_7947122).sum := by decide
  have hdescent : baseEnd_7947122 < baseStart_7947122 := by decide
  rcases family_descends (prefixWord ++ tailWord_7947122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7947129 : List Nat := [1, 2, 1, 3, 2, 3, 3, 3, 5]
def baseStart_7947129 : Nat := 118140960795 + 7947129 * 2 ^ 59
def prefixEnd_7947129 : Nat := 4983230072969 + 3 ^ 40 * 7947129 * 2
def baseEnd_7947129 : Nat := 453410777809438061659925

theorem tailTrace_7947129 : CollatzResearch.WordTrace tailWord_7947129 prefixEnd_7947129 453410777809438061659925 := by
  unfold tailWord_7947129
  simp only [CollatzResearch.WordTrace]
  refine ⟨289855607225916369421196441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193237071483944246280797627 289855607225916369421196441)
  ·
    refine ⟨217391705419437277065897331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289855607225916369421196441 217391705419437277065897331)
    ·
      refine ⟨326087558129155915598845997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217391705419437277065897331 326087558129155915598845997)
      ·
        refine ⟨122282834298433468349567249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 326087558129155915598845997 122282834298433468349567249)
        ·
          refine ⟨91712125723825101262175437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122282834298433468349567249 91712125723825101262175437)
          ·
            refine ⟨34392047146434412973315789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91712125723825101262175437 34392047146434412973315789)
            ·
              refine ⟨12897017679912904864993421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34392047146434412973315789 12897017679912904864993421)
              ·
                refine ⟨4836381629967339324372533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12897017679912904864993421 4836381629967339324372533)
                ·
                  refine ⟨453410777809438061659925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4836381629967339324372533 453410777809438061659925)
                  ·
                    rfl

theorem cell23_7947129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 3, 3, 5].length) (baseStart_7947129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7947129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7947129 prefixEnd_7947129 := by exact prefixLift 7947129
  have htrace : WordTrace (prefixWord ++ tailWord_7947129) baseStart_7947129 baseEnd_7947129 := by
    simpa [prefixWord, tailWord_7947129, baseEnd_7947129] using wordTrace_append hprefix tailTrace_7947129
  have hstable : (prefixWord ++ tailWord_7947129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7947129).length < 2 ^ (prefixWord ++ tailWord_7947129).sum := by decide
  have hdescent : baseEnd_7947129 < baseStart_7947129 := by decide
  rcases family_descends (prefixWord ++ tailWord_7947129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7947155 : List Nat := [1, 1, 1, 2, 1, 2, 1, 4, 2, 8]
def baseStart_7947155 : Nat := 118140960795 + 7947155 * 2 ^ 59
def prefixEnd_7947155 : Nat := 4983230072969 + 3 ^ 40 * 7947155 * 2
def baseEnd_7947155 : Nat := 1360236783593986484404735

theorem tailTrace_7947155 : CollatzResearch.WordTrace tailWord_7947155 prefixEnd_7947155 1360236783593986484404735 := by
  unfold tailWord_7947155
  simp only [CollatzResearch.WordTrace]
  refine ⟨289856555523822175861642919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193237703682548117241095279 289856555523822175861642919)
  ·
    refine ⟨434784833285733263792464379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289856555523822175861642919 434784833285733263792464379)
    ·
      refine ⟨652177249928599895688696569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 434784833285733263792464379 652177249928599895688696569)
      ·
        refine ⟨489132937446449921766522427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 652177249928599895688696569 489132937446449921766522427)
        ·
          refine ⟨733699406169674882649783641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 489132937446449921766522427 733699406169674882649783641)
          ·
            refine ⟨550274554627256161987337731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 733699406169674882649783641 550274554627256161987337731)
            ·
              refine ⟨825411831940884242981006597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 550274554627256161987337731 825411831940884242981006597)
              ·
                refine ⟨154764718488915795558938737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 825411831940884242981006597 154764718488915795558938737)
                ·
                  refine ⟨116073538866686846669204053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 154764718488915795558938737 116073538866686846669204053)
                  ·
                    refine ⟨1360236783593986484404735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 116073538866686846669204053 1360236783593986484404735)
                    ·
                      rfl

theorem cell23_7947155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 4, 2, 8].length) (baseStart_7947155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7947155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7947155 prefixEnd_7947155 := by exact prefixLift 7947155
  have htrace : WordTrace (prefixWord ++ tailWord_7947155) baseStart_7947155 baseEnd_7947155 := by
    simpa [prefixWord, tailWord_7947155, baseEnd_7947155] using wordTrace_append hprefix tailTrace_7947155
  have hstable : (prefixWord ++ tailWord_7947155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7947155).length < 2 ^ (prefixWord ++ tailWord_7947155).sum := by decide
  have hdescent : baseEnd_7947155 < baseStart_7947155 := by decide
  rcases family_descends (prefixWord ++ tailWord_7947155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7947289 : List Nat := [1, 2, 1, 2, 1, 1, 4, 3, 3, 2, 3]
def baseStart_7947289 : Nat := 118140960795 + 7947289 * 2 ^ 59
def prefixEnd_7947289 : Nat := 4983230072969 + 3 ^ 40 * 7947289 * 2
def baseEnd_7947289 : Nat := 4080779157189661928938589

theorem tailTrace_7947289 : CollatzResearch.WordTrace tailWord_7947289 prefixEnd_7947289 4080779157189661928938589 := by
  unfold tailWord_7947289
  simp only [CollatzResearch.WordTrace]
  refine ⟨289861442905336716747020921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193240961936891144498013947 289861442905336716747020921)
  ·
    refine ⟨217396082179002537560265691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289861442905336716747020921 217396082179002537560265691)
    ·
      refine ⟨326094123268503806340398537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217396082179002537560265691 326094123268503806340398537)
      ·
        refine ⟨244570592451377854755298903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 326094123268503806340398537 244570592451377854755298903)
        ·
          refine ⟨366855888677066782132948355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244570592451377854755298903 366855888677066782132948355)
          ·
            refine ⟨550283833015600173199422533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 366855888677066782132948355 550283833015600173199422533)
            ·
              refine ⟨103178218690425032474891725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 550283833015600173199422533 103178218690425032474891725)
              ·
                refine ⟨38691832008909387178084397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103178218690425032474891725 38691832008909387178084397)
                ·
                  refine ⟨14509437003341020191781649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38691832008909387178084397 14509437003341020191781649)
                  ·
                    refine ⟨10882077752505765143836237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14509437003341020191781649 10882077752505765143836237)
                    ·
                      refine ⟨4080779157189661928938589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10882077752505765143836237 4080779157189661928938589)
                      ·
                        rfl

theorem cell23_7947289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 3, 3, 2, 3].length) (baseStart_7947289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7947289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7947289 prefixEnd_7947289 := by exact prefixLift 7947289
  have htrace : WordTrace (prefixWord ++ tailWord_7947289) baseStart_7947289 baseEnd_7947289 := by
    simpa [prefixWord, tailWord_7947289, baseEnd_7947289] using wordTrace_append hprefix tailTrace_7947289
  have hstable : (prefixWord ++ tailWord_7947289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7947289).length < 2 ^ (prefixWord ++ tailWord_7947289).sum := by decide
  have hdescent : baseEnd_7947289 < baseStart_7947289 := by decide
  rcases family_descends (prefixWord ++ tailWord_7947289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7947303 : List Nat := [1, 1, 7, 1, 1, 1, 2, 3, 1, 1, 4]
def baseStart_7947303 : Nat := 118140960795 + 7947303 * 2 ^ 59
def prefixEnd_7947303 : Nat := 4983230072969 + 3 ^ 40 * 7947303 * 2
def baseEnd_7947303 : Nat := 4080786345918824874163525

theorem tailTrace_7947303 : CollatzResearch.WordTrace tailWord_7947303 prefixEnd_7947303 4080786345918824874163525 := by
  unfold tailWord_7947303
  simp only [CollatzResearch.WordTrace]
  refine ⟨289861953527285997138030563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193241302351523998092020375 289861953527285997138030563)
  ·
    refine ⟨434792930290928995707045845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289861953527285997138030563 434792930290928995707045845)
    ·
      refine ⟨10190459303693648336883887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 434792930290928995707045845 10190459303693648336883887)
      ·
        refine ⟨15285688955540472505325831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10190459303693648336883887 15285688955540472505325831)
        ·
          refine ⟨22928533433310708757988747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15285688955540472505325831 22928533433310708757988747)
          ·
            refine ⟨34392800149966063136983121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22928533433310708757988747 34392800149966063136983121)
            ·
              refine ⟨25794600112474547352737341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34392800149966063136983121 25794600112474547352737341)
              ·
                refine ⟨9672975042177955257276503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25794600112474547352737341 9672975042177955257276503)
                ·
                  refine ⟨14509462563266932885914755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9672975042177955257276503 14509462563266932885914755)
                  ·
                    refine ⟨21764193844900399328872133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14509462563266932885914755 21764193844900399328872133)
                    ·
                      refine ⟨4080786345918824874163525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21764193844900399328872133 4080786345918824874163525)
                      ·
                        rfl

theorem cell23_7947303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 3, 1, 1, 4].length) (baseStart_7947303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7947303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7947303 prefixEnd_7947303 := by exact prefixLift 7947303
  have htrace : WordTrace (prefixWord ++ tailWord_7947303) baseStart_7947303 baseEnd_7947303 := by
    simpa [prefixWord, tailWord_7947303, baseEnd_7947303] using wordTrace_append hprefix tailTrace_7947303
  have hstable : (prefixWord ++ tailWord_7947303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7947303).length < 2 ^ (prefixWord ++ tailWord_7947303).sum := by decide
  have hdescent : baseEnd_7947303 < baseStart_7947303 := by decide
  rcases family_descends (prefixWord ++ tailWord_7947303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7947316 : List Nat := [2, 5, 1, 2, 1, 1, 1, 2, 1, 1, 6]
def baseStart_7947316 : Nat := 118140960795 + 7947316 * 2 ^ 59
def prefixEnd_7947316 : Nat := 4983230072969 + 3 ^ 40 * 7947316 * 2
def baseEnd_7947316 : Nat := 4080793021167333323300965

theorem tailTrace_7947316 : CollatzResearch.WordTrace tailWord_7947316 prefixEnd_7947316 4080793021167333323300965 := by
  unfold tailWord_7947316
  simp only [CollatzResearch.WordTrace]
  refine ⟨144931213838119450179126901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193241618450825933572169201 144931213838119450179126901)
  ·
    refine ⟨13587301297323698454293147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 144931213838119450179126901 13587301297323698454293147)
    ·
      refine ⟨20380951945985547681439721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13587301297323698454293147 20380951945985547681439721)
      ·
        refine ⟨15285713959489160761079791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20380951945985547681439721 15285713959489160761079791)
        ·
          refine ⟨22928570939233741141619687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15285713959489160761079791 22928570939233741141619687)
          ·
            refine ⟨34392856408850611712429531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22928570939233741141619687 34392856408850611712429531)
            ·
              refine ⟨51589284613275917568644297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34392856408850611712429531 51589284613275917568644297)
              ·
                refine ⟨38691963459956938176483223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51589284613275917568644297 38691963459956938176483223)
                ·
                  refine ⟨58037945189935407264724835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38691963459956938176483223 58037945189935407264724835)
                  ·
                    refine ⟨87056917784903110897087253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58037945189935407264724835 87056917784903110897087253)
                    ·
                      refine ⟨4080793021167333323300965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 87056917784903110897087253 4080793021167333323300965)
                      ·
                        rfl

theorem cell23_7947316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_7947316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7947316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7947316 prefixEnd_7947316 := by exact prefixLift 7947316
  have htrace : WordTrace (prefixWord ++ tailWord_7947316) baseStart_7947316 baseEnd_7947316 := by
    simpa [prefixWord, tailWord_7947316, baseEnd_7947316] using wordTrace_append hprefix tailTrace_7947316
  have hstable : (prefixWord ++ tailWord_7947316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7947316).length < 2 ^ (prefixWord ++ tailWord_7947316).sum := by decide
  have hdescent : baseEnd_7947316 < baseStart_7947316 := by decide
  rcases family_descends (prefixWord ++ tailWord_7947316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7947320 : List Nat := [2, 1, 2, 1, 5, 3, 1, 1, 3, 2, 2]
def baseStart_7947320 : Nat := 118140960795 + 7947320 * 2 ^ 59
def prefixEnd_7947320 : Nat := 4983230072969 + 3 ^ 40 * 7947320 * 2
def baseEnd_7947320 : Nat := 4080795075089951307650947

theorem tailTrace_7947320 : CollatzResearch.WordTrace tailWord_7947320 prefixEnd_7947320 4080795075089951307650947 := by
  unfold tailWord_7947320
  simp only [CollatzResearch.WordTrace]
  refine ⟨144931286784112204520699707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193241715712149606027599609 144931286784112204520699707)
  ·
    refine ⟨217396930176168306781049561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144931286784112204520699707 217396930176168306781049561)
    ·
      refine ⟨163047697632126230085787171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217396930176168306781049561 163047697632126230085787171)
      ·
        refine ⟨244571546448189345128680757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163047697632126230085787171 244571546448189345128680757)
        ·
          refine ⟨22928582479517751105813821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 244571546448189345128680757 22928582479517751105813821)
          ·
            refine ⟨8598218429819156664680183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22928582479517751105813821 8598218429819156664680183)
            ·
              refine ⟨12897327644728734997020275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8598218429819156664680183 12897327644728734997020275)
              ·
                refine ⟨19345991467093102495530413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12897327644728734997020275 19345991467093102495530413)
                ·
                  refine ⟨7254746800159913435823905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19345991467093102495530413 7254746800159913435823905)
                  ·
                    refine ⟨5441060100119935076867929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7254746800159913435823905 5441060100119935076867929)
                    ·
                      refine ⟨4080795075089951307650947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5441060100119935076867929 4080795075089951307650947)
                      ·
                        rfl

theorem cell23_7947320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 1, 1, 3, 2, 2].length) (baseStart_7947320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7947320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7947320 prefixEnd_7947320 := by exact prefixLift 7947320
  have htrace : WordTrace (prefixWord ++ tailWord_7947320) baseStart_7947320 baseEnd_7947320 := by
    simpa [prefixWord, tailWord_7947320, baseEnd_7947320] using wordTrace_append hprefix tailTrace_7947320
  have hstable : (prefixWord ++ tailWord_7947320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7947320).length < 2 ^ (prefixWord ++ tailWord_7947320).sum := by decide
  have hdescent : baseEnd_7947320 < baseStart_7947320 := by decide
  rcases family_descends (prefixWord ++ tailWord_7947320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7947326 : List Nat := [4, 2, 1, 3, 1, 2, 2, 8]
def baseStart_7947326 : Nat := 118140960795 + 7947326 * 2 ^ 59
def prefixEnd_7947326 : Nat := 4983230072969 + 3 ^ 40 * 7947326 * 2
def baseEnd_7947326 : Nat := 151140672443476973487997

theorem tailTrace_7947326 : CollatzResearch.WordTrace tailWord_7947326 prefixEnd_7947326 151140672443476973487997 := by
  unfold tailWord_7947326
  simp only [CollatzResearch.WordTrace]
  refine ⟨36232849050775334008264729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 193241861604135114710745221 36232849050775334008264729)
  ·
    refine ⟨27174636788081500506198547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36232849050775334008264729 27174636788081500506198547)
    ·
      refine ⟨40761955182122250759297821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27174636788081500506198547 40761955182122250759297821)
      ·
        refine ⟨15285733193295844034736683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40761955182122250759297821 15285733193295844034736683)
        ·
          refine ⟨22928599789943766052105025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15285733193295844034736683 22928599789943766052105025)
          ·
            refine ⟨17196449842457824539078769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22928599789943766052105025 17196449842457824539078769)
            ·
              refine ⟨12897337381843368404309077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17196449842457824539078769 12897337381843368404309077)
              ·
                refine ⟨151140672443476973487997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12897337381843368404309077 151140672443476973487997)
                ·
                  rfl

theorem cell23_7947326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 2, 8].length) (baseStart_7947326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7947326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7947326 prefixEnd_7947326 := by exact prefixLift 7947326
  have htrace : WordTrace (prefixWord ++ tailWord_7947326) baseStart_7947326 baseEnd_7947326 := by
    simpa [prefixWord, tailWord_7947326, baseEnd_7947326] using wordTrace_append hprefix tailTrace_7947326
  have hstable : (prefixWord ++ tailWord_7947326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7947326).length < 2 ^ (prefixWord ++ tailWord_7947326).sum := by decide
  have hdescent : baseEnd_7947326 < baseStart_7947326 := by decide
  rcases family_descends (prefixWord ++ tailWord_7947326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7947350 : List Nat := [5, 2, 2, 1, 2, 1, 1, 2, 1, 2, 4]
def baseStart_7947350 : Nat := 118140960795 + 7947350 * 2 ^ 59
def prefixEnd_7947350 : Nat := 4983230072969 + 3 ^ 40 * 7947350 * 2
def baseEnd_7947350 : Nat := 4080810479509586190275809

theorem tailTrace_7947350 : CollatzResearch.WordTrace tailWord_7947350 prefixEnd_7947350 4080810479509586190275809 := by
  unfold tailWord_7947350
  simp only [CollatzResearch.WordTrace]
  refine ⟨18116479234882232760311969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 193242445172077149443327669 18116479234882232760311969)
  ·
    refine ⟨13587359426161674570233977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18116479234882232760311969 13587359426161674570233977)
    ·
      refine ⟨10190519569621255927675483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13587359426161674570233977 10190519569621255927675483)
      ·
        refine ⟨15285779354431883891513225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10190519569621255927675483 15285779354431883891513225)
        ·
          refine ⟨11464334515823912918634919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15285779354431883891513225 11464334515823912918634919)
          ·
            refine ⟨17196501773735869377952379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11464334515823912918634919 17196501773735869377952379)
            ·
              refine ⟨25794752660603804066928569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17196501773735869377952379 25794752660603804066928569)
              ·
                refine ⟨19346064495452853050196427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25794752660603804066928569 19346064495452853050196427)
                ·
                  refine ⟨29019096743179279575294641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19346064495452853050196427 29019096743179279575294641)
                  ·
                    refine ⟨21764322557384459681470981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29019096743179279575294641 21764322557384459681470981)
                    ·
                      refine ⟨4080810479509586190275809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21764322557384459681470981 4080810479509586190275809)
                      ·
                        rfl

theorem cell23_7947350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 2, 1, 2, 4].length) (baseStart_7947350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7947350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7947350 prefixEnd_7947350 := by exact prefixLift 7947350
  have htrace : WordTrace (prefixWord ++ tailWord_7947350) baseStart_7947350 baseEnd_7947350 := by
    simpa [prefixWord, tailWord_7947350, baseEnd_7947350] using wordTrace_append hprefix tailTrace_7947350
  have hstable : (prefixWord ++ tailWord_7947350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7947350).length < 2 ^ (prefixWord ++ tailWord_7947350).sum := by decide
  have hdescent : baseEnd_7947350 < baseStart_7947350 := by decide
  rcases family_descends (prefixWord ++ tailWord_7947350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7947357 : List Nat := [1, 4, 4, 1, 2, 1, 3, 1, 1, 2, 3]
def baseStart_7947357 : Nat := 118140960795 + 7947357 * 2 ^ 59
def prefixEnd_7947357 : Nat := 4983230072969 + 3 ^ 40 * 7947357 * 2
def baseEnd_7947357 : Nat := 4080814073874167662888277

theorem tailTrace_7947357 : CollatzResearch.WordTrace tailWord_7947357 prefixEnd_7947357 4080814073874167662888277 := by
  unfold tailWord_7947357
  simp only [CollatzResearch.WordTrace]
  refine ⟨289863923069090364360496325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193242615379393576240330883 289863923069090364360496325)
  ·
    refine ⟨54349485575454443317593061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 289863923069090364360496325 54349485575454443317593061)
    ·
      refine ⟨10190528545397708122048699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54349485575454443317593061 10190528545397708122048699)
      ·
        refine ⟨15285792818096562183073049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10190528545397708122048699 15285792818096562183073049)
        ·
          refine ⟨11464344613572421637304787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15285792818096562183073049 11464344613572421637304787)
          ·
            refine ⟨17196516920358632455957181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11464344613572421637304787 17196516920358632455957181)
            ·
              refine ⟨6448693845134487170983943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17196516920358632455957181 6448693845134487170983943)
              ·
                refine ⟨9673040767701730756475915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6448693845134487170983943 9673040767701730756475915)
                ·
                  refine ⟨14509561151552596134713873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9673040767701730756475915 14509561151552596134713873)
                  ·
                    refine ⟨10882170863664447101035405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14509561151552596134713873 10882170863664447101035405)
                    ·
                      refine ⟨4080814073874167662888277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10882170863664447101035405 4080814073874167662888277)
                      ·
                        rfl

theorem cell23_7947357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 3, 1, 1, 2, 3].length) (baseStart_7947357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7947357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7947357 prefixEnd_7947357 := by exact prefixLift 7947357
  have htrace : WordTrace (prefixWord ++ tailWord_7947357) baseStart_7947357 baseEnd_7947357 := by
    simpa [prefixWord, tailWord_7947357, baseEnd_7947357] using wordTrace_append hprefix tailTrace_7947357
  have hstable : (prefixWord ++ tailWord_7947357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7947357).length < 2 ^ (prefixWord ++ tailWord_7947357).sum := by decide
  have hdescent : baseEnd_7947357 < baseStart_7947357 := by decide
  rcases family_descends (prefixWord ++ tailWord_7947357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7947370 : List Nat := [3, 1, 3, 2, 2, 2, 2, 2, 2, 1, 3]
def baseStart_7947370 : Nat := 118140960795 + 7947370 * 2 ^ 59
def prefixEnd_7947370 : Nat := 4983230072969 + 3 ^ 40 * 7947370 * 2
def baseEnd_7947370 : Nat := 4080820749122676112025717

theorem tailTrace_7947370 : CollatzResearch.WordTrace tailWord_7947370 prefixEnd_7947370 4080820749122676112025717 := by
  unfold tailWord_7947370
  simp only [CollatzResearch.WordTrace]
  refine ⟨72466099304510816895179891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193242931478695511720479709 72466099304510816895179891)
  ·
    refine ⟨108699148956766225342769837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72466099304510816895179891 108699148956766225342769837)
    ·
      refine ⟨40762180858787334503538689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108699148956766225342769837 40762180858787334503538689)
      ·
        refine ⟨30571635644090500877654017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40762180858787334503538689 30571635644090500877654017)
        ·
          refine ⟨22928726733067875658240513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30571635644090500877654017 22928726733067875658240513)
          ·
            refine ⟨17196545049800906743680385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22928726733067875658240513 17196545049800906743680385)
            ·
              refine ⟨12897408787350680057760289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17196545049800906743680385 12897408787350680057760289)
              ·
                refine ⟨9673056590513010043320217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12897408787350680057760289 9673056590513010043320217)
                ·
                  refine ⟨7254792442884757532490163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9673056590513010043320217 7254792442884757532490163)
                  ·
                    refine ⟨10882188664327136298735245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7254792442884757532490163 10882188664327136298735245)
                    ·
                      refine ⟨4080820749122676112025717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10882188664327136298735245 4080820749122676112025717)
                      ·
                        rfl

theorem cell23_7947370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 2, 2, 2, 1, 3].length) (baseStart_7947370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7947370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7947370 prefixEnd_7947370 := by exact prefixLift 7947370
  have htrace : WordTrace (prefixWord ++ tailWord_7947370) baseStart_7947370 baseEnd_7947370 := by
    simpa [prefixWord, tailWord_7947370, baseEnd_7947370] using wordTrace_append hprefix tailTrace_7947370
  have hstable : (prefixWord ++ tailWord_7947370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7947370).length < 2 ^ (prefixWord ++ tailWord_7947370).sum := by decide
  have hdescent : baseEnd_7947370 < baseStart_7947370 := by decide
  rcases family_descends (prefixWord ++ tailWord_7947370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7947376 : List Nat := [2, 1, 1, 1, 5, 1, 1, 2, 3, 4, 2]
def baseStart_7947376 : Nat := 118140960795 + 7947376 * 2 ^ 59
def prefixEnd_7947376 : Nat := 4983230072969 + 3 ^ 40 * 7947376 * 2
def baseEnd_7947376 : Nat := 4080823830006603088550689

theorem tailTrace_7947376 : CollatzResearch.WordTrace tailWord_7947376 prefixEnd_7947376 4080823830006603088550689 := by
  unfold tailWord_7947376
  simp only [CollatzResearch.WordTrace]
  refine ⟨144932308028010765302718991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193243077370681020403625321 144932308028010765302718991)
  ·
    refine ⟨217398462042016147954078487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144932308028010765302718991 217398462042016147954078487)
    ·
      refine ⟨326097693063024221931117731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217398462042016147954078487 326097693063024221931117731)
      ·
        refine ⟨489146539594536332896676597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 326097693063024221931117731 489146539594536332896676597)
        ·
          refine ⟨45857488086987781209063431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 489146539594536332896676597 45857488086987781209063431)
          ·
            refine ⟨68786232130481671813595147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45857488086987781209063431 68786232130481671813595147)
            ·
              refine ⟨103179348195722507720392721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68786232130481671813595147 103179348195722507720392721)
              ·
                refine ⟨77384511146791880790294541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103179348195722507720392721 77384511146791880790294541)
                ·
                  refine ⟨29019191680046955296360453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77384511146791880790294541 29019191680046955296360453)
                  ·
                    refine ⟨5441098440008804118067585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29019191680046955296360453 5441098440008804118067585)
                    ·
                      refine ⟨4080823830006603088550689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5441098440008804118067585 4080823830006603088550689)
                      ·
                        rfl

theorem cell23_7947376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 2, 3, 4, 2].length) (baseStart_7947376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7947376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7947376 prefixEnd_7947376 := by exact prefixLift 7947376
  have htrace : WordTrace (prefixWord ++ tailWord_7947376) baseStart_7947376 baseEnd_7947376 := by
    simpa [prefixWord, tailWord_7947376, baseEnd_7947376] using wordTrace_append hprefix tailTrace_7947376
  have hstable : (prefixWord ++ tailWord_7947376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7947376).length < 2 ^ (prefixWord ++ tailWord_7947376).sum := by decide
  have hdescent : baseEnd_7947376 < baseStart_7947376 := by decide
  rcases family_descends (prefixWord ++ tailWord_7947376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7947393 : List Nat := [1, 2, 4, 2, 2, 1, 1, 3, 1, 4, 2]
def baseStart_7947393 : Nat := 118140960795 + 7947393 * 2 ^ 59
def prefixEnd_7947393 : Nat := 4983230072969 + 3 ^ 40 * 7947393 * 2
def baseEnd_7947393 : Nat := 4080832559177729522038111

theorem tailTrace_7947393 : CollatzResearch.WordTrace tailWord_7947393 prefixEnd_7947393 4080832559177729522038111 := by
  unfold tailWord_7947393
  simp only [CollatzResearch.WordTrace]
  refine ⟨289865236096959942508806833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193243490731306628339204555 289865236096959942508806833)
  ·
    refine ⟨217398927072719956881605125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289865236096959942508806833 217398927072719956881605125)
    ·
      refine ⟨40762298826134991915300961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 217398927072719956881605125 40762298826134991915300961)
      ·
        refine ⟨30571724119601243936475721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40762298826134991915300961 30571724119601243936475721)
        ·
          refine ⟨22928793089700932952356791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30571724119601243936475721 22928793089700932952356791)
          ·
            refine ⟨34393189634551399428535187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22928793089700932952356791 34393189634551399428535187)
            ·
              refine ⟨51589784451827099142802781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34393189634551399428535187 51589784451827099142802781)
              ·
                refine ⟨19346169169435162178551043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51589784451827099142802781 19346169169435162178551043)
                ·
                  refine ⟨29019253754152743267826565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19346169169435162178551043 29019253754152743267826565)
                  ·
                    refine ⟨5441110078903639362717481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29019253754152743267826565 5441110078903639362717481)
                    ·
                      refine ⟨4080832559177729522038111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5441110078903639362717481 4080832559177729522038111)
                      ·
                        rfl

theorem cell23_7947393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 3, 1, 4, 2].length) (baseStart_7947393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7947393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7947393 prefixEnd_7947393 := by exact prefixLift 7947393
  have htrace : WordTrace (prefixWord ++ tailWord_7947393) baseStart_7947393 baseEnd_7947393 := by
    simpa [prefixWord, tailWord_7947393, baseEnd_7947393] using wordTrace_append hprefix tailTrace_7947393
  have hstable : (prefixWord ++ tailWord_7947393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7947393).length < 2 ^ (prefixWord ++ tailWord_7947393).sum := by decide
  have hdescent : baseEnd_7947393 < baseStart_7947393 := by decide
  rcases family_descends (prefixWord ++ tailWord_7947393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7947436 : List Nat := [2, 2, 1, 1, 1, 1, 1, 5, 2, 5, 2]
def baseStart_7947436 : Nat := 118140960795 + 7947436 * 2 ^ 59
def prefixEnd_7947436 : Nat := 4983230072969 + 3 ^ 40 * 7947436 * 2
def baseEnd_7947436 : Nat := 4080854638845872853800413

theorem tailTrace_7947436 : CollatzResearch.WordTrace tailWord_7947436 prefixEnd_7947436 4080854638845872853800413 := by
  unfold tailWord_7947436
  simp only [CollatzResearch.WordTrace]
  refine ⟨144933402217902080426311081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193244536290536107235081441 144933402217902080426311081)
  ·
    refine ⟨108700051663426560319733311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144933402217902080426311081 108700051663426560319733311)
    ·
      refine ⟨163050077495139840479599967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108700051663426560319733311 163050077495139840479599967)
      ·
        refine ⟨244575116242709760719399951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163050077495139840479599967 244575116242709760719399951)
        ·
          refine ⟨366862674364064641079099927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244575116242709760719399951 366862674364064641079099927)
          ·
            refine ⟨550294011546096961618649891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 366862674364064641079099927 550294011546096961618649891)
            ·
              refine ⟨825441017319145442427974837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 550294011546096961618649891 825441017319145442427974837)
              ·
                refine ⟨77385095373669885227622641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 825441017319145442427974837 77385095373669885227622641)
                ·
                  refine ⟨58038821530252413920716981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77385095373669885227622641 58038821530252413920716981)
                  ·
                    refine ⟨5441139518461163805067217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 58038821530252413920716981 5441139518461163805067217)
                    ·
                      refine ⟨4080854638845872853800413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5441139518461163805067217 4080854638845872853800413)
                      ·
                        rfl

theorem cell23_7947436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 5, 2].length) (baseStart_7947436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7947436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7947436 prefixEnd_7947436 := by exact prefixLift 7947436
  have htrace : WordTrace (prefixWord ++ tailWord_7947436) baseStart_7947436 baseEnd_7947436 := by
    simpa [prefixWord, tailWord_7947436, baseEnd_7947436] using wordTrace_append hprefix tailTrace_7947436
  have hstable : (prefixWord ++ tailWord_7947436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7947436).length < 2 ^ (prefixWord ++ tailWord_7947436).sum := by decide
  have hdescent : baseEnd_7947436 < baseStart_7947436 := by decide
  rcases family_descends (prefixWord ++ tailWord_7947436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7947439 : List Nat := [1, 1, 2, 1, 2, 3, 2, 3, 1, 2, 5]
def baseStart_7947439 : Nat := 118140960795 + 7947439 * 2 ^ 59
def prefixEnd_7947439 : Nat := 4983230072969 + 3 ^ 40 * 7947439 * 2
def baseEnd_7947439 : Nat := 4080856179287836342062899

theorem tailTrace_7947439 : CollatzResearch.WordTrace tailWord_7947439 prefixEnd_7947439 4080856179287836342062899 := by
  unfold tailWord_7947439
  simp only [CollatzResearch.WordTrace]
  refine ⟨289866913854793292364981371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193244609236528861576654247 289866913854793292364981371)
  ·
    refine ⟨434800370782189938547472057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289866913854793292364981371 434800370782189938547472057)
    ·
      refine ⟨326100278086642453910604043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 434800370782189938547472057 326100278086642453910604043)
      ·
        refine ⟨489150417129963680865906065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 326100278086642453910604043 489150417129963680865906065)
        ·
          refine ⟨366862812847472760649429549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 489150417129963680865906065 366862812847472760649429549)
          ·
            refine ⟨137573554817802285243536081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 366862812847472760649429549 137573554817802285243536081)
            ·
              refine ⟨103180166113351713932652061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137573554817802285243536081 103180166113351713932652061)
              ·
                refine ⟨38692562292506892724744523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103180166113351713932652061 38692562292506892724744523)
                ·
                  refine ⟨58038843438760339087116785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38692562292506892724744523 58038843438760339087116785)
                  ·
                    refine ⟨43529132579070254315337589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58038843438760339087116785 43529132579070254315337589)
                    ·
                      refine ⟨4080856179287836342062899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43529132579070254315337589 4080856179287836342062899)
                      ·
                        rfl

theorem cell23_7947439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 3, 1, 2, 5].length) (baseStart_7947439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7947439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7947439 prefixEnd_7947439 := by exact prefixLift 7947439
  have htrace : WordTrace (prefixWord ++ tailWord_7947439) baseStart_7947439 baseEnd_7947439 := by
    simpa [prefixWord, tailWord_7947439, baseEnd_7947439] using wordTrace_append hprefix tailTrace_7947439
  have hstable : (prefixWord ++ tailWord_7947439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7947439).length < 2 ^ (prefixWord ++ tailWord_7947439).sum := by decide
  have hdescent : baseEnd_7947439 < baseStart_7947439 := by decide
  rcases family_descends (prefixWord ++ tailWord_7947439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7947466 : List Nat := [3, 1, 2, 1, 3, 2, 2, 1, 1, 3, 4]
def baseStart_7947466 : Nat := 118140960795 + 7947466 * 2 ^ 59
def prefixEnd_7947466 : Nat := 4983230072969 + 3 ^ 40 * 7947466 * 2
def baseEnd_7947466 : Nat := 4080870043265507736425275

theorem tailTrace_7947466 : CollatzResearch.WordTrace tailWord_7947466 prefixEnd_7947466 4080870043265507736425275 := by
  unfold tailWord_7947466
  simp only [CollatzResearch.WordTrace]
  refine ⟨72466974656423868994053563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193245265750463650650809501 72466974656423868994053563)
  ·
    refine ⟨108700461984635803491080345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72466974656423868994053563 108700461984635803491080345)
    ·
      refine ⟨81525346488476852618310259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108700461984635803491080345 81525346488476852618310259)
      ·
        refine ⟨122288019732715278927465389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81525346488476852618310259 122288019732715278927465389)
        ·
          refine ⟨45858007399768229597799521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122288019732715278927465389 45858007399768229597799521)
          ·
            refine ⟨34393505549826172198349641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45858007399768229597799521 34393505549826172198349641)
            ·
              refine ⟨25795129162369629148762231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34393505549826172198349641 25795129162369629148762231)
              ·
                refine ⟨38692693743554443723143347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25795129162369629148762231 38692693743554443723143347)
                ·
                  refine ⟨58039040615331665584715021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38692693743554443723143347 58039040615331665584715021)
                  ·
                    refine ⟨21764640230749374594268133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58039040615331665584715021 21764640230749374594268133)
                    ·
                      refine ⟨4080870043265507736425275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21764640230749374594268133 4080870043265507736425275)
                      ·
                        rfl

theorem cell23_7947466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 1, 1, 3, 4].length) (baseStart_7947466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7947466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7947466 prefixEnd_7947466 := by exact prefixLift 7947466
  have htrace : WordTrace (prefixWord ++ tailWord_7947466) baseStart_7947466 baseEnd_7947466 := by
    simpa [prefixWord, tailWord_7947466, baseEnd_7947466] using wordTrace_append hprefix tailTrace_7947466
  have hstable : (prefixWord ++ tailWord_7947466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7947466).length < 2 ^ (prefixWord ++ tailWord_7947466).sum := by decide
  have hdescent : baseEnd_7947466 < baseStart_7947466 := by decide
  rcases family_descends (prefixWord ++ tailWord_7947466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7947479 : List Nat := [1, 1, 3, 2, 1, 2, 2, 1, 1, 3, 6]
def baseStart_7947479 : Nat := 118140960795 + 7947479 * 2 ^ 59
def prefixEnd_7947479 : Nat := 4983230072969 + 3 ^ 40 * 7947479 * 2
def baseEnd_7947479 : Nat := 4080876718514016185562715

theorem tailTrace_7947479 : CollatzResearch.WordTrace tailWord_7947479 prefixEnd_7947479 4080876718514016185562715 := by
  unfold tailWord_7947479
  simp only [CollatzResearch.WordTrace]
  refine ⟨289868372774648379196437491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193245581849765586130958327 289868372774648379196437491)
  ·
    refine ⟨434802559161972568794656237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289868372774648379196437491 434802559161972568794656237)
    ·
      refine ⟨163050959685739713297996089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 434802559161972568794656237 163050959685739713297996089)
      ·
        refine ⟨122288219764304784973497067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163050959685739713297996089 122288219764304784973497067)
        ·
          refine ⟨183432329646457177460245601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122288219764304784973497067 183432329646457177460245601)
          ·
            refine ⟨137574247234842883095184201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183432329646457177460245601 137574247234842883095184201)
            ·
              refine ⟨103180685426132162321388151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137574247234842883095184201 103180685426132162321388151)
              ·
                refine ⟨154771028139198243482082227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103180685426132162321388151 154771028139198243482082227)
                ·
                  refine ⟨232156542208797365223123341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 154771028139198243482082227 232156542208797365223123341)
                  ·
                    refine ⟨87058703328299011958671253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 232156542208797365223123341 87058703328299011958671253)
                    ·
                      refine ⟨4080876718514016185562715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 87058703328299011958671253 4080876718514016185562715)
                      ·
                        rfl

theorem cell23_7947479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 1, 1, 3, 6].length) (baseStart_7947479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7947479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7947479 prefixEnd_7947479 := by exact prefixLift 7947479
  have htrace : WordTrace (prefixWord ++ tailWord_7947479) baseStart_7947479 baseEnd_7947479 := by
    simpa [prefixWord, tailWord_7947479, baseEnd_7947479] using wordTrace_append hprefix tailTrace_7947479
  have hstable : (prefixWord ++ tailWord_7947479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7947479).length < 2 ^ (prefixWord ++ tailWord_7947479).sum := by decide
  have hdescent : baseEnd_7947479 < baseStart_7947479 := by decide
  rcases family_descends (prefixWord ++ tailWord_7947479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7947573 : List Nat := [1, 3, 3, 1, 2, 2, 2, 1, 3, 1, 4]
def baseStart_7947573 : Nat := 118140960795 + 7947573 * 2 ^ 59
def prefixEnd_7947573 : Nat := 4983230072969 + 3 ^ 40 * 7947573 * 2
def baseEnd_7947573 : Nat := 4080924985695538817787283

theorem tailTrace_7947573 : CollatzResearch.WordTrace tailWord_7947573 prefixEnd_7947573 4080924985695538817787283 := by
  unfold tailWord_7947573
  simp only [CollatzResearch.WordTrace]
  refine ⟨289871801236307833250359373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193247867490871888833572915 289871801236307833250359373)
  ·
    refine ⟨108701925463615437468884765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 289871801236307833250359373 108701925463615437468884765)
    ·
      refine ⟨40763222048855789050831787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108701925463615437468884765 40763222048855789050831787)
      ·
        refine ⟨61144833073283683576247681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40763222048855789050831787 61144833073283683576247681)
        ·
          refine ⟨45858624804962762682185761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61144833073283683576247681 45858624804962762682185761)
          ·
            refine ⟨34393968603722072011639321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45858624804962762682185761 34393968603722072011639321)
            ·
              refine ⟨25795476452791554008729491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34393968603722072011639321 25795476452791554008729491)
              ·
                refine ⟨38693214679187331013094237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25795476452791554008729491 38693214679187331013094237)
                ·
                  refine ⟨14509955504695249129910339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38693214679187331013094237 14509955504695249129910339)
                  ·
                    refine ⟨21764933257042873694865509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14509955504695249129910339 21764933257042873694865509)
                    ·
                      refine ⟨4080924985695538817787283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21764933257042873694865509 4080924985695538817787283)
                      ·
                        rfl

theorem cell23_7947573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 1, 3, 1, 4].length) (baseStart_7947573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7947573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7947573 prefixEnd_7947573 := by exact prefixLift 7947573
  have htrace : WordTrace (prefixWord ++ tailWord_7947573) baseStart_7947573 baseEnd_7947573 := by
    simpa [prefixWord, tailWord_7947573, baseEnd_7947573] using wordTrace_append hprefix tailTrace_7947573
  have hstable : (prefixWord ++ tailWord_7947573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7947573).length < 2 ^ (prefixWord ++ tailWord_7947573).sum := by decide
  have hdescent : baseEnd_7947573 < baseStart_7947573 := by decide
  rcases family_descends (prefixWord ++ tailWord_7947573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7947596 : List Nat := [2, 2, 1, 3, 2, 3, 10]
def baseStart_7947596 : Nat := 118140960795 + 7947596 * 2 ^ 59
def prefixEnd_7947596 : Nat := 4983230072969 + 3 ^ 40 * 7947596 * 2
def baseEnd_7947596 : Nat := 50381935750007311454317

theorem tailTrace_7947596 : CollatzResearch.WordTrace tailWord_7947596 prefixEnd_7947596 50381935750007311454317 := by
  unfold tailWord_7947596
  simp only [CollatzResearch.WordTrace]
  refine ⟨144936320057612254089223321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193248426743483005452297761 144936320057612254089223321)
  ·
    refine ⟨108702240043209190566917491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144936320057612254089223321 108702240043209190566917491)
    ·
      refine ⟨163053360064813785850376237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108702240043209190566917491 163053360064813785850376237)
      ·
        refine ⟨61145010024305169693891089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163053360064813785850376237 61145010024305169693891089)
        ·
          refine ⟨45858757518228877270418317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61145010024305169693891089 45858757518228877270418317)
          ·
            refine ⟨17197034069335828976406869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45858757518228877270418317 17197034069335828976406869)
            ·
              refine ⟨50381935750007311454317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 17197034069335828976406869 50381935750007311454317)
              ·
                rfl

theorem cell23_7947596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 10].length) (baseStart_7947596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7947596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7947596 prefixEnd_7947596 := by exact prefixLift 7947596
  have htrace : WordTrace (prefixWord ++ tailWord_7947596) baseStart_7947596 baseEnd_7947596 := by
    simpa [prefixWord, tailWord_7947596, baseEnd_7947596] using wordTrace_append hprefix tailTrace_7947596
  have hstable : (prefixWord ++ tailWord_7947596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7947596).length < 2 ^ (prefixWord ++ tailWord_7947596).sum := by decide
  have hdescent : baseEnd_7947596 < baseStart_7947596 := by decide
  rcases family_descends (prefixWord ++ tailWord_7947596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7947607 : List Nat := [1, 1, 3, 2, 3, 3, 2, 1, 3, 2, 2]
def baseStart_7947607 : Nat := 118140960795 + 7947607 * 2 ^ 59
def prefixEnd_7947607 : Nat := 4983230072969 + 3 ^ 40 * 7947607 * 2
def baseEnd_7947607 : Nat := 4080942444037791684762127

theorem tailTrace_7947607 : CollatzResearch.WordTrace tailWord_7947607 prefixEnd_7947607 4080942444037791684762127 := by
  unfold tailWord_7947607
  simp only [CollatzResearch.WordTrace]
  refine ⟨289873041318184657057097075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193248694212123104704731383 289873041318184657057097075)
  ·
    refine ⟨434809561977276985585645613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289873041318184657057097075 434809561977276985585645613)
    ·
      refine ⟨163053585741478869594617105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 434809561977276985585645613 163053585741478869594617105)
      ·
        refine ⟨122290189306109152195962829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163053585741478869594617105 122290189306109152195962829)
        ·
          refine ⟨45858820989790932073486061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122290189306109152195962829 45858820989790932073486061)
          ·
            refine ⟨17197057871171599527557273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45858820989790932073486061 17197057871171599527557273)
            ·
              refine ⟨12897793403378699645667955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17197057871171599527557273 12897793403378699645667955)
              ·
                refine ⟨19346690105068049468501933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12897793403378699645667955 19346690105068049468501933)
                ·
                  refine ⟨7255008789400518550688225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19346690105068049468501933 7255008789400518550688225)
                  ·
                    refine ⟨5441256592050388913016169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7255008789400518550688225 5441256592050388913016169)
                    ·
                      refine ⟨4080942444037791684762127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5441256592050388913016169 4080942444037791684762127)
                      ·
                        rfl

theorem cell23_7947607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 2, 1, 3, 2, 2].length) (baseStart_7947607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7947607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7947607 prefixEnd_7947607 := by exact prefixLift 7947607
  have htrace : WordTrace (prefixWord ++ tailWord_7947607) baseStart_7947607 baseEnd_7947607 := by
    simpa [prefixWord, tailWord_7947607, baseEnd_7947607] using wordTrace_append hprefix tailTrace_7947607
  have hstable : (prefixWord ++ tailWord_7947607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7947607).length < 2 ^ (prefixWord ++ tailWord_7947607).sum := by decide
  have hdescent : baseEnd_7947607 < baseStart_7947607 := by decide
  rcases family_descends (prefixWord ++ tailWord_7947607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7947620 : List Nat := [2, 3, 1, 1, 3, 4, 1, 1, 1, 2, 4]
def baseStart_7947620 : Nat := 118140960795 + 7947620 * 2 ^ 59
def prefixEnd_7947620 : Nat := 4983230072969 + 3 ^ 40 * 7947620 * 2
def baseEnd_7947620 : Nat := 4080949119286300133899567

theorem tailTrace_7947620 : CollatzResearch.WordTrace tailWord_7947620 prefixEnd_7947620 4080949119286300133899567 := by
  unfold tailWord_7947620
  simp only [CollatzResearch.WordTrace]
  refine ⟨144936757733568780138660157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193249010311425040184880209 144936757733568780138660157)
  ·
    refine ⟨54351284150088292551997559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144936757733568780138660157 54351284150088292551997559)
    ·
      refine ⟨81526926225132438827996339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54351284150088292551997559 81526926225132438827996339)
      ·
        refine ⟨122290389337698658241994509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81526926225132438827996339 122290389337698658241994509)
        ·
          refine ⟨45858896001636996840747941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122290389337698658241994509 45858896001636996840747941)
          ·
            refine ⟨8598543000306936907640239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45858896001636996840747941 8598543000306936907640239)
            ·
              refine ⟨12897814500460405361460359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8598543000306936907640239 12897814500460405361460359)
              ·
                refine ⟨19346721750690608042190539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12897814500460405361460359 19346721750690608042190539)
                ·
                  refine ⟨29020082626035912063285809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19346721750690608042190539 29020082626035912063285809)
                  ·
                    refine ⟨21765061969526934047464357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29020082626035912063285809 21765061969526934047464357)
                    ·
                      refine ⟨4080949119286300133899567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21765061969526934047464357 4080949119286300133899567)
                      ·
                        rfl

theorem cell23_7947620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 1, 1, 1, 2, 4].length) (baseStart_7947620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7947620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7947620 prefixEnd_7947620 := by exact prefixLift 7947620
  have htrace : WordTrace (prefixWord ++ tailWord_7947620) baseStart_7947620 baseEnd_7947620 := by
    simpa [prefixWord, tailWord_7947620, baseEnd_7947620] using wordTrace_append hprefix tailTrace_7947620
  have hstable : (prefixWord ++ tailWord_7947620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7947620).length < 2 ^ (prefixWord ++ tailWord_7947620).sum := by decide
  have hdescent : baseEnd_7947620 < baseStart_7947620 := by decide
  rcases family_descends (prefixWord ++ tailWord_7947620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7947630 : List Nat := [4, 1, 2, 4, 1, 1, 1, 9]
def baseStart_7947630 : Nat := 118140960795 + 7947630 * 2 ^ 59
def prefixEnd_7947630 : Nat := 4983230072969 + 3 ^ 40 * 7947630 * 2
def baseEnd_7947630 : Nat := 151146453855290559065723

theorem tailTrace_7947630 : CollatzResearch.WordTrace tailWord_7947630 prefixEnd_7947630 151146453855290559065723 := by
  unfold tailWord_7947630
  simp only [CollatzResearch.WordTrace]
  refine ⟨36234235024637666498148043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 193249253464734221323456229 36234235024637666498148043)
  ·
    refine ⟨54351352536956499747222065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36234235024637666498148043 54351352536956499747222065)
    ·
      refine ⟨40763514402717374810416549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54351352536956499747222065 40763514402717374810416549)
      ·
        refine ⟨7643158950509507776953103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40763514402717374810416549 7643158950509507776953103)
        ·
          refine ⟨11464738425764261665429655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7643158950509507776953103 11464738425764261665429655)
          ·
            refine ⟨17197107638646392498144483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11464738425764261665429655 17197107638646392498144483)
            ·
              refine ⟨25795661457969588747216725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17197107638646392498144483 25795661457969588747216725)
              ·
                refine ⟨151146453855290559065723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 25795661457969588747216725 151146453855290559065723)
                ·
                  rfl

theorem cell23_7947630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 9].length) (baseStart_7947630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7947630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7947630 prefixEnd_7947630 := by exact prefixLift 7947630
  have htrace : WordTrace (prefixWord ++ tailWord_7947630) baseStart_7947630 baseEnd_7947630 := by
    simpa [prefixWord, tailWord_7947630, baseEnd_7947630] using wordTrace_append hprefix tailTrace_7947630
  have hstable : (prefixWord ++ tailWord_7947630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7947630).length < 2 ^ (prefixWord ++ tailWord_7947630).sum := by decide
  have hdescent : baseEnd_7947630 < baseStart_7947630 := by decide
  rcases family_descends (prefixWord ++ tailWord_7947630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7947680 : List Nat := [2, 1, 1, 4, 1, 2, 2, 3, 1, 4, 2]
def baseStart_7947680 : Nat := 118140960795 + 7947680 * 2 ^ 59
def prefixEnd_7947680 : Nat := 4983230072969 + 3 ^ 40 * 7947680 * 2
def baseEnd_7947680 : Nat := 4080979928125569899149291

theorem tailTrace_7947680 : CollatzResearch.WordTrace tailWord_7947680 prefixEnd_7947680 4080979928125569899149291 := by
  unfold tailWord_7947680
  simp only [CollatzResearch.WordTrace]
  refine ⟨144937851923460095262252247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193250469231280127016336329 144937851923460095262252247)
  ·
    refine ⟨217406777885190142893378371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144937851923460095262252247 217406777885190142893378371)
    ·
      refine ⟨326110166827785214340067557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217406777885190142893378371 326110166827785214340067557)
      ·
        refine ⟨61145656280209727688762667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 326110166827785214340067557 61145656280209727688762667)
        ·
          refine ⟨91718484420314591533144001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61145656280209727688762667 91718484420314591533144001)
          ·
            refine ⟨68788863315235943649858001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91718484420314591533144001 68788863315235943649858001)
            ·
              refine ⟨51591647486426957737393501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68788863315235943649858001 51591647486426957737393501)
              ·
                refine ⟨19346867807410109151522563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51591647486426957737393501 19346867807410109151522563)
                ·
                  refine ⟨29020301711115163727283845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19346867807410109151522563 29020301711115163727283845)
                  ·
                    refine ⟨5441306570834093198865721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29020301711115163727283845 5441306570834093198865721)
                    ·
                      refine ⟨4080979928125569899149291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5441306570834093198865721 4080979928125569899149291)
                      ·
                        rfl

theorem cell23_7947680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 3, 1, 4, 2].length) (baseStart_7947680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7947680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7947680 prefixEnd_7947680 := by exact prefixLift 7947680
  have htrace : WordTrace (prefixWord ++ tailWord_7947680) baseStart_7947680 baseEnd_7947680 := by
    simpa [prefixWord, tailWord_7947680, baseEnd_7947680] using wordTrace_append hprefix tailTrace_7947680
  have hstable : (prefixWord ++ tailWord_7947680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7947680).length < 2 ^ (prefixWord ++ tailWord_7947680).sum := by decide
  have hdescent : baseEnd_7947680 < baseStart_7947680 := by decide
  rcases family_descends (prefixWord ++ tailWord_7947680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7947696 : List Nat := [2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 7]
def baseStart_7947696 : Nat := 118140960795 + 7947696 * 2 ^ 59
def prefixEnd_7947696 : Nat := 4983230072969 + 3 ^ 40 * 7947696 * 2
def baseEnd_7947696 : Nat := 4080988143816041836549217

theorem tailTrace_7947696 : CollatzResearch.WordTrace tailWord_7947696 prefixEnd_7947696 4080988143816041836549217 := by
  unfold tailWord_7947696
  simp only [CollatzResearch.WordTrace]
  refine ⟨144938143707431112628543471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193250858276574816838057961 144938143707431112628543471)
  ·
    refine ⟨217407215561146668942815207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144938143707431112628543471 217407215561146668942815207)
    ·
      refine ⟨326110823341720003414222811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217407215561146668942815207 326110823341720003414222811)
      ·
        refine ⟨489166235012580005121334217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 326110823341720003414222811 489166235012580005121334217)
        ·
          refine ⟨366874676259435003841000663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 489166235012580005121334217 366874676259435003841000663)
          ·
            refine ⟨550312014389152505761500995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 366874676259435003841000663 550312014389152505761500995)
            ·
              refine ⟨825468021583728758642251493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 550312014389152505761500995 825468021583728758642251493)
              ·
                refine ⟨154775254046949142245422155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 825468021583728758642251493 154775254046949142245422155)
                ·
                  refine ⟨232162881070423713368133233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 154775254046949142245422155 232162881070423713368133233)
                  ·
                    refine ⟨174122160802817785026099925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 232162881070423713368133233 174122160802817785026099925)
                    ·
                      refine ⟨4080988143816041836549217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 174122160802817785026099925 4080988143816041836549217)
                      ·
                        rfl

theorem cell23_7947696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 7].length) (baseStart_7947696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7947696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7947696 prefixEnd_7947696 := by exact prefixLift 7947696
  have htrace : WordTrace (prefixWord ++ tailWord_7947696) baseStart_7947696 baseEnd_7947696 := by
    simpa [prefixWord, tailWord_7947696, baseEnd_7947696] using wordTrace_append hprefix tailTrace_7947696
  have hstable : (prefixWord ++ tailWord_7947696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7947696).length < 2 ^ (prefixWord ++ tailWord_7947696).sum := by decide
  have hdescent : baseEnd_7947696 < baseStart_7947696 := by decide
  rcases family_descends (prefixWord ++ tailWord_7947696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7947720 : List Nat := [2, 1, 3, 1, 3, 1, 3, 4, 5]
def baseStart_7947720 : Nat := 118140960795 + 7947720 * 2 ^ 59
def prefixEnd_7947720 : Nat := 4983230072969 + 3 ^ 40 * 7947720 * 2
def baseEnd_7947720 : Nat := 453444496372416638072123

theorem tailTrace_7947720 : CollatzResearch.WordTrace tailWord_7947720 prefixEnd_7947720 453444496372416638072123 := by
  unfold tailWord_7947720
  simp only [CollatzResearch.WordTrace]
  refine ⟨144938581383387638677980307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193251441844516851570640409 144938581383387638677980307)
  ·
    refine ⟨217407872075081458016970461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144938581383387638677980307 217407872075081458016970461)
    ·
      refine ⟨81527952028155546756363923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 217407872075081458016970461 81527952028155546756363923)
      ·
        refine ⟨122291928042233320134545885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81527952028155546756363923 122291928042233320134545885)
        ·
          refine ⟨45859473015837495050454707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122291928042233320134545885 45859473015837495050454707)
          ·
            refine ⟨68789209523756242575682061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45859473015837495050454707 68789209523756242575682061)
            ·
              refine ⟨25795953571408590965880773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68789209523756242575682061 25795953571408590965880773)
              ·
                refine ⟨4836741294639110806102645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25795953571408590965880773 4836741294639110806102645)
                ·
                  refine ⟨453444496372416638072123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4836741294639110806102645 453444496372416638072123)
                  ·
                    rfl

theorem cell23_7947720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 4, 5].length) (baseStart_7947720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7947720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7947720 prefixEnd_7947720 := by exact prefixLift 7947720
  have htrace : WordTrace (prefixWord ++ tailWord_7947720) baseStart_7947720 baseEnd_7947720 := by
    simpa [prefixWord, tailWord_7947720, baseEnd_7947720] using wordTrace_append hprefix tailTrace_7947720
  have hstable : (prefixWord ++ tailWord_7947720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7947720).length < 2 ^ (prefixWord ++ tailWord_7947720).sum := by decide
  have hdescent : baseEnd_7947720 < baseStart_7947720 := by decide
  rcases family_descends (prefixWord ++ tailWord_7947720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7947733 : List Nat := [1, 3, 2, 3, 1, 1, 2, 2, 1, 7]
def baseStart_7947733 : Nat := 118140960795 + 7947733 * 2 ^ 59
def prefixEnd_7947733 : Nat := 4983230072969 + 3 ^ 40 * 7947733 * 2
def baseEnd_7947733 : Nat := 1360335714200086063928849

theorem tailTrace_7947733 : CollatzResearch.WordTrace tailWord_7947733 prefixEnd_7947733 1360335714200086063928849 := by
  unfold tailWord_7947733
  simp only [CollatzResearch.WordTrace]
  refine ⟨289877636915728180576183853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193251757943818787050789235 289877636915728180576183853)
  ·
    refine ⟨108704113843398067716068945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 289877636915728180576183853 108704113843398067716068945)
    ·
      refine ⟨81528085382548550787051709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108704113843398067716068945 81528085382548550787051709)
      ·
        refine ⟨30573032018455706545144391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81528085382548550787051709 30573032018455706545144391)
        ·
          refine ⟨45859548027683559817716587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30573032018455706545144391 45859548027683559817716587)
          ·
            refine ⟨68789322041525339726574881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45859548027683559817716587 68789322041525339726574881)
            ·
              refine ⟨51591991531144004794931161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68789322041525339726574881 51591991531144004794931161)
              ·
                refine ⟨38693993648358003596198371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51591991531144004794931161 38693993648358003596198371)
                ·
                  refine ⟨58040990472537005394297557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38693993648358003596198371 58040990472537005394297557)
                  ·
                    refine ⟨1360335714200086063928849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58040990472537005394297557 1360335714200086063928849)
                    ·
                      rfl

theorem cell23_7947733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 2, 1, 7].length) (baseStart_7947733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7947733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7947733 prefixEnd_7947733 := by exact prefixLift 7947733
  have htrace : WordTrace (prefixWord ++ tailWord_7947733) baseStart_7947733 baseEnd_7947733 := by
    simpa [prefixWord, tailWord_7947733, baseEnd_7947733] using wordTrace_append hprefix tailTrace_7947733
  have hstable : (prefixWord ++ tailWord_7947733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7947733).length < 2 ^ (prefixWord ++ tailWord_7947733).sum := by decide
  have hdescent : baseEnd_7947733 < baseStart_7947733 := by decide
  rcases family_descends (prefixWord ++ tailWord_7947733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7947770 : List Nat := [3, 1, 1, 1, 1, 2, 3, 1, 4, 4, 2]
def baseStart_7947770 : Nat := 118140960795 + 7947770 * 2 ^ 59
def prefixEnd_7947770 : Nat := 4983230072969 + 3 ^ 40 * 7947770 * 2
def baseEnd_7947770 : Nat := 4081026141384474547023877

theorem tailTrace_7947770 : CollatzResearch.WordTrace tailWord_7947770 prefixEnd_7947770 4081026141384474547023877 := by
  unfold tailWord_7947770
  simp only [CollatzResearch.WordTrace]
  refine ⟨72469746604148533973820191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193252657611062757263520509 72469746604148533973820191)
  ·
    refine ⟨108704619906222800960730287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72469746604148533973820191 108704619906222800960730287)
    ·
      refine ⟨163056929859334201441095431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108704619906222800960730287 163056929859334201441095431)
      ·
        refine ⟨244585394789001302161643147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163056929859334201441095431 244585394789001302161643147)
        ·
          refine ⟨366878092183501953242464721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244585394789001302161643147 366878092183501953242464721)
          ·
            refine ⟨275158569137626464931848541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 366878092183501953242464721 275158569137626464931848541)
            ·
              refine ⟨103184463426609924349443203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 275158569137626464931848541 103184463426609924349443203)
              ·
                refine ⟨154776695139914886524164805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103184463426609924349443203 154776695139914886524164805)
                ·
                  refine ⟨29020630338734041223280901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 154776695139914886524164805 29020630338734041223280901)
                  ·
                    refine ⟨5441368188512632729365169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29020630338734041223280901 5441368188512632729365169)
                    ·
                      refine ⟨4081026141384474547023877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5441368188512632729365169 4081026141384474547023877)
                      ·
                        rfl

theorem cell23_7947770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 1, 4, 4, 2].length) (baseStart_7947770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7947770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7947770 prefixEnd_7947770 := by exact prefixLift 7947770
  have htrace : WordTrace (prefixWord ++ tailWord_7947770) baseStart_7947770 baseEnd_7947770 := by
    simpa [prefixWord, tailWord_7947770, baseEnd_7947770] using wordTrace_append hprefix tailTrace_7947770
  have hstable : (prefixWord ++ tailWord_7947770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7947770).length < 2 ^ (prefixWord ++ tailWord_7947770).sum := by decide
  have hdescent : baseEnd_7947770 < baseStart_7947770 := by decide
  rcases family_descends (prefixWord ++ tailWord_7947770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7947782 : List Nat := [6, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2]
def baseStart_7947782 : Nat := 118140960795 + 7947782 * 2 ^ 59
def prefixEnd_7947782 : Nat := 4983230072969 + 3 ^ 40 * 7947782 * 2
def baseEnd_7947782 : Nat := 4081032303152328500073823

theorem tailTrace_7947782 : CollatzResearch.WordTrace tailWord_7947782 prefixEnd_7947782 4081032303152328500073823 := by
  unfold tailWord_7947782
  simp only [CollatzResearch.WordTrace]
  refine ⟨9058732002892208185772425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 193252949395033774629811733 9058732002892208185772425)
  ·
    refine ⟨6794049002169156139329319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9058732002892208185772425 6794049002169156139329319)
    ·
      refine ⟨10191073503253734208993979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6794049002169156139329319 10191073503253734208993979)
      ·
        refine ⟨15286610254880601313490969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10191073503253734208993979 15286610254880601313490969)
        ·
          refine ⟨11464957691160450985118227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15286610254880601313490969 11464957691160450985118227)
          ·
            refine ⟨17197436536740676477677341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11464957691160450985118227 17197436536740676477677341)
            ·
              refine ⟨6449038701277753679129003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17197436536740676477677341 6449038701277753679129003)
              ·
                refine ⟨9673558051916630518693505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6449038701277753679129003 9673558051916630518693505)
                ·
                  refine ⟨7255168538937472889020129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9673558051916630518693505 7255168538937472889020129)
                  ·
                    refine ⟨5441376404203104666765097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7255168538937472889020129 5441376404203104666765097)
                    ·
                      refine ⟨4081032303152328500073823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5441376404203104666765097 4081032303152328500073823)
                      ·
                        rfl

theorem cell23_7947782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2].length) (baseStart_7947782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7947782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7947782 prefixEnd_7947782 := by exact prefixLift 7947782
  have htrace : WordTrace (prefixWord ++ tailWord_7947782) baseStart_7947782 baseEnd_7947782 := by
    simpa [prefixWord, tailWord_7947782, baseEnd_7947782] using wordTrace_append hprefix tailTrace_7947782
  have hstable : (prefixWord ++ tailWord_7947782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7947782).length < 2 ^ (prefixWord ++ tailWord_7947782).sum := by decide
  have hdescent : baseEnd_7947782 < baseStart_7947782 := by decide
  rcases family_descends (prefixWord ++ tailWord_7947782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7947843 : List Nat := [1, 1, 1, 3, 1, 2, 1, 1, 1, 7, 4]
def baseStart_7947843 : Nat := 118140960795 + 7947843 * 2 ^ 59
def prefixEnd_7947843 : Nat := 4983230072969 + 3 ^ 40 * 7947843 * 2
def baseEnd_7947843 : Nat := 4081063625472252761411041

theorem tailTrace_7947843 : CollatzResearch.WordTrace tailWord_7947843 prefixEnd_7947843 4081063625472252761411041 := by
  unfold tailWord_7947843
  simp only [CollatzResearch.WordTrace]
  refine ⟨289881648945329669362688183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193254432630219779575125455 289881648945329669362688183)
  ·
    refine ⟨434822473417994504044032275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289881648945329669362688183 434822473417994504044032275)
    ·
      refine ⟨652233710126991756066048413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 434822473417994504044032275 652233710126991756066048413)
      ·
        refine ⟨244587641297621908524768155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 652233710126991756066048413 244587641297621908524768155)
        ·
          refine ⟨366881461946432862787152233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244587641297621908524768155 366881461946432862787152233)
          ·
            refine ⟨275161096459824647090364175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 366881461946432862787152233 275161096459824647090364175)
            ·
              refine ⟨412741644689736970635546263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 275161096459824647090364175 412741644689736970635546263)
              ·
                refine ⟨619112467034605455953319395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 412741644689736970635546263 619112467034605455953319395)
                ·
                  refine ⟨928668700551908183929979093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 619112467034605455953319395 928668700551908183929979093)
                  ·
                    refine ⟨21765672669185348060858885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 928668700551908183929979093 21765672669185348060858885)
                    ·
                      refine ⟨4081063625472252761411041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21765672669185348060858885 4081063625472252761411041)
                      ·
                        rfl

theorem cell23_7947843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 7, 4].length) (baseStart_7947843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7947843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7947843 prefixEnd_7947843 := by exact prefixLift 7947843
  have htrace : WordTrace (prefixWord ++ tailWord_7947843) baseStart_7947843 baseEnd_7947843 := by
    simpa [prefixWord, tailWord_7947843, baseEnd_7947843] using wordTrace_append hprefix tailTrace_7947843
  have hstable : (prefixWord ++ tailWord_7947843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7947843).length < 2 ^ (prefixWord ++ tailWord_7947843).sum := by decide
  have hdescent : baseEnd_7947843 < baseStart_7947843 := by decide
  rcases family_descends (prefixWord ++ tailWord_7947843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7947888 : List Nat := [2, 1, 1, 1, 6, 3, 2, 2, 1, 1, 3]
def baseStart_7947888 : Nat := 118140960795 + 7947888 * 2 ^ 59
def prefixEnd_7947888 : Nat := 4983230072969 + 3 ^ 40 * 7947888 * 2
def baseEnd_7947888 : Nat := 4081086732101705085348335

theorem tailTrace_7947888 : CollatzResearch.WordTrace tailWord_7947888 prefixEnd_7947888 4081086732101705085348335 := by
  unfold tailWord_7947888
  simp only [CollatzResearch.WordTrace]
  refine ⟨144941645115083321024038159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193255526820111094698717545 144941645115083321024038159)
  ·
    refine ⟨217412467672624981536057239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144941645115083321024038159 217412467672624981536057239)
    ·
      refine ⟨326118701508937472304085859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217412467672624981536057239 326118701508937472304085859)
      ·
        refine ⟨489178052263406208456128789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 326118701508937472304085859 489178052263406208456128789)
        ·
          refine ⟨22930221199847166021381037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 489178052263406208456128789 22930221199847166021381037)
          ·
            refine ⟨8598832949942687258017889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22930221199847166021381037 8598832949942687258017889)
            ·
              refine ⟨6449124712457015443513417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8598832949942687258017889 6449124712457015443513417)
              ·
                refine ⟨4836843534342761582635063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6449124712457015443513417 4836843534342761582635063)
                ·
                  refine ⟨7255265301514142373952595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4836843534342761582635063 7255265301514142373952595)
                  ·
                    refine ⟨10882897952271213560928893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7255265301514142373952595 10882897952271213560928893)
                    ·
                      refine ⟨4081086732101705085348335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10882897952271213560928893 4081086732101705085348335)
                      ·
                        rfl

theorem cell23_7947888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 2, 2, 1, 1, 3].length) (baseStart_7947888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7947888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7947888 prefixEnd_7947888 := by exact prefixLift 7947888
  have htrace : WordTrace (prefixWord ++ tailWord_7947888) baseStart_7947888 baseEnd_7947888 := by
    simpa [prefixWord, tailWord_7947888, baseEnd_7947888] using wordTrace_append hprefix tailTrace_7947888
  have hstable : (prefixWord ++ tailWord_7947888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7947888).length < 2 ^ (prefixWord ++ tailWord_7947888).sum := by decide
  have hdescent : baseEnd_7947888 < baseStart_7947888 := by decide
  rcases family_descends (prefixWord ++ tailWord_7947888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7947927 : List Nat := [1, 1, 3, 3, 2, 2, 2, 2, 1, 3, 3]
def baseStart_7947927 : Nat := 118140960795 + 7947927 * 2 ^ 59
def prefixEnd_7947927 : Nat := 4983230072969 + 3 ^ 40 * 7947927 * 2
def baseEnd_7947927 : Nat := 4081106757847230432760655

theorem tailTrace_7947927 : CollatzResearch.WordTrace tailWord_7947927 prefixEnd_7947927 4081106757847230432760655 := by
  unfold tailWord_7947927
  simp only [CollatzResearch.WordTrace]
  refine ⟨289884712677025351708746035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193256475118016901139164023 289884712677025351708746035)
  ·
    refine ⟨434827069015538027563119053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289884712677025351708746035 434827069015538027563119053)
    ·
      refine ⟨163060150880826760336169645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 434827069015538027563119053 163060150880826760336169645)
      ·
        refine ⟨61147556580310035126063617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163060150880826760336169645 61147556580310035126063617)
        ·
          refine ⟨45860667435232526344547713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61147556580310035126063617 45860667435232526344547713)
          ·
            refine ⟨34395500576424394758410785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45860667435232526344547713 34395500576424394758410785)
            ·
              refine ⟨25796625432318296068808089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34395500576424394758410785 25796625432318296068808089)
              ·
                refine ⟨19347469074238722051606067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25796625432318296068808089 19347469074238722051606067)
                ·
                  refine ⟨29021203611358083077409101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19347469074238722051606067 29021203611358083077409101)
                  ·
                    refine ⟨10882951354259281154028413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29021203611358083077409101 10882951354259281154028413)
                    ·
                      refine ⟨4081106757847230432760655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10882951354259281154028413 4081106757847230432760655)
                      ·
                        rfl

theorem cell23_7947927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 2, 1, 3, 3].length) (baseStart_7947927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7947927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7947927 prefixEnd_7947927 := by exact prefixLift 7947927
  have htrace : WordTrace (prefixWord ++ tailWord_7947927) baseStart_7947927 baseEnd_7947927 := by
    simpa [prefixWord, tailWord_7947927, baseEnd_7947927] using wordTrace_append hprefix tailTrace_7947927
  have hstable : (prefixWord ++ tailWord_7947927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7947927).length < 2 ^ (prefixWord ++ tailWord_7947927).sum := by decide
  have hdescent : baseEnd_7947927 < baseStart_7947927 := by decide
  rcases family_descends (prefixWord ++ tailWord_7947927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7947928 : List Nat := [2, 1, 2, 4, 1, 3, 2, 3, 1, 2, 2]
def baseStart_7947928 : Nat := 118140960795 + 7947928 * 2 ^ 59
def prefixEnd_7947928 : Nat := 4983230072969 + 3 ^ 40 * 7947928 * 2
def baseEnd_7947928 : Nat := 4081107271327884928848151

theorem tailTrace_7947928 : CollatzResearch.WordTrace tailWord_7947928 prefixEnd_7947928 4081107271327884928848151 := by
  unfold tailWord_7947928
  simp only [CollatzResearch.WordTrace]
  refine ⟨144942374575010864439766219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193256499433347819253021625 144942374575010864439766219)
  ·
    refine ⟨217413561862516296659649329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144942374575010864439766219 217413561862516296659649329)
    ·
      refine ⟨163060171396887222494736997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217413561862516296659649329 163060171396887222494736997)
      ·
        refine ⟨30573782136916354217763187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 163060171396887222494736997 30573782136916354217763187)
        ·
          refine ⟨45860673205374531326644781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30573782136916354217763187 45860673205374531326644781)
          ·
            refine ⟨17197752452015449247491793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45860673205374531326644781 17197752452015449247491793)
            ·
              refine ⟨12898314339011586935618845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17197752452015449247491793 12898314339011586935618845)
              ·
                refine ⟨4836867877129345100857067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12898314339011586935618845 4836867877129345100857067)
                ·
                  refine ⟨7255301815694017651285601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4836867877129345100857067 7255301815694017651285601)
                  ·
                    refine ⟨5441476361770513238464201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7255301815694017651285601 5441476361770513238464201)
                    ·
                      refine ⟨4081107271327884928848151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5441476361770513238464201 4081107271327884928848151)
                      ·
                        rfl

theorem cell23_7947928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 2, 3, 1, 2, 2].length) (baseStart_7947928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7947928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7947928 prefixEnd_7947928 := by exact prefixLift 7947928
  have htrace : WordTrace (prefixWord ++ tailWord_7947928) baseStart_7947928 baseEnd_7947928 := by
    simpa [prefixWord, tailWord_7947928, baseEnd_7947928] using wordTrace_append hprefix tailTrace_7947928
  have hstable : (prefixWord ++ tailWord_7947928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7947928).length < 2 ^ (prefixWord ++ tailWord_7947928).sum := by decide
  have hdescent : baseEnd_7947928 < baseStart_7947928 := by decide
  rcases family_descends (prefixWord ++ tailWord_7947928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7947938 : List Nat := [3, 3, 1, 4, 1, 2, 1, 2, 2, 4]
def baseStart_7947938 : Nat := 118140960795 + 7947938 * 2 ^ 59
def prefixEnd_7947938 : Nat := 4983230072969 + 3 ^ 40 * 7947938 * 2
def baseEnd_7947938 : Nat := 1360370802044809963241035

theorem tailTrace_7947938 : CollatzResearch.WordTrace tailWord_7947938 prefixEnd_7947938 1360370802044809963241035 := by
  unfold tailWord_7947938
  simp only [CollatzResearch.WordTrace]
  refine ⟨72471278469996375146849117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193256742586657000391597645 72471278469996375146849117)
  ·
    refine ⟨27176729426248640680068419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72471278469996375146849117 27176729426248640680068419)
    ·
      refine ⟨40765094139372961020102629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27176729426248640680068419 40765094139372961020102629)
      ·
        refine ⟨7643455151132430191269243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40765094139372961020102629 7643455151132430191269243)
        ·
          refine ⟨11465182726698645286903865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7643455151132430191269243 11465182726698645286903865)
          ·
            refine ⟨8598887045023983965177899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11465182726698645286903865 8598887045023983965177899)
            ·
              refine ⟨12898330567535975947766849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8598887045023983965177899 12898330567535975947766849)
              ·
                refine ⟨9673747925651981960825137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12898330567535975947766849 9673747925651981960825137)
                ·
                  refine ⟨7255310944238986470618853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9673747925651981960825137 7255310944238986470618853)
                  ·
                    refine ⟨1360370802044809963241035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7255310944238986470618853 1360370802044809963241035)
                    ·
                      rfl

theorem cell23_7947938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 1, 2, 2, 4].length) (baseStart_7947938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7947938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7947938 prefixEnd_7947938 := by exact prefixLift 7947938
  have htrace : WordTrace (prefixWord ++ tailWord_7947938) baseStart_7947938 baseEnd_7947938 := by
    simpa [prefixWord, tailWord_7947938, baseEnd_7947938] using wordTrace_append hprefix tailTrace_7947938
  have hstable : (prefixWord ++ tailWord_7947938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7947938).length < 2 ^ (prefixWord ++ tailWord_7947938).sum := by decide
  have hdescent : baseEnd_7947938 < baseStart_7947938 := by decide
  rcases family_descends (prefixWord ++ tailWord_7947938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7948027 : List Nat := [1, 1, 1, 1, 1, 3, 1, 3, 4, 5, 2]
def baseStart_7948027 : Nat := 118140960795 + 7948027 * 2 ^ 59
def prefixEnd_7948027 : Nat := 4983230072969 + 3 ^ 40 * 7948027 * 2
def baseEnd_7948027 : Nat := 4081158105912680041510195

theorem tailTrace_7948027 : CollatzResearch.WordTrace tailWord_7948027 prefixEnd_7948027 4081158105912680041510195 := by
  unfold tailWord_7948027
  simp only [CollatzResearch.WordTrace]
  refine ⟨289888359976663068787386335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193258906651108712524924223 289888359976663068787386335)
  ·
    refine ⟨434832539964994603181079503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289888359976663068787386335 434832539964994603181079503)
    ·
      refine ⟨652248809947491904771619255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 434832539964994603181079503 652248809947491904771619255)
      ·
        refine ⟨978373214921237857157428883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 652248809947491904771619255 978373214921237857157428883)
        ·
          refine ⟨1467559822381856785736143325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 978373214921237857157428883 1467559822381856785736143325)
          ·
            refine ⟨550334933393196294651053747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1467559822381856785736143325 550334933393196294651053747)
            ·
              refine ⟨825502400089794441976580621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 550334933393196294651053747 825502400089794441976580621)
              ·
                refine ⟨309563400033672915741217733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 825502400089794441976580621 309563400033672915741217733)
                ·
                  refine ⟨58043137506313671701478325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 309563400033672915741217733 58043137506313671701478325)
                  ·
                    refine ⟨5441544141216906722013593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 58043137506313671701478325 5441544141216906722013593)
                    ·
                      refine ⟨4081158105912680041510195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5441544141216906722013593 4081158105912680041510195)
                      ·
                        rfl

theorem cell23_7948027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 4, 5, 2].length) (baseStart_7948027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7948027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7948027 prefixEnd_7948027 := by exact prefixLift 7948027
  have htrace : WordTrace (prefixWord ++ tailWord_7948027) baseStart_7948027 baseEnd_7948027 := by
    simpa [prefixWord, tailWord_7948027, baseEnd_7948027] using wordTrace_append hprefix tailTrace_7948027
  have hstable : (prefixWord ++ tailWord_7948027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7948027).length < 2 ^ (prefixWord ++ tailWord_7948027).sum := by decide
  have hdescent : baseEnd_7948027 < baseStart_7948027 := by decide
  rcases family_descends (prefixWord ++ tailWord_7948027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
