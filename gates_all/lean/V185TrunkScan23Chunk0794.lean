import V185TrunkScan23Chunk0793

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4695870 : List Nat := [4, 2, 1, 2, 2, 1, 1, 2, 3, 1, 4]
def baseStart_4695870 : Nat := 118140960795 + 4695870 * 2 ^ 59
def prefixEnd_4695870 : Nat := 4983230072969 + 3 ^ 40 * 4695870 * 2
def baseEnd_4695870 : Nat := 2411238401028647620729093

theorem tailTrace_4695870 : CollatzResearch.WordTrace tailWord_4695870 prefixEnd_4695870 2411238401028647620729093 := by
  unfold tailWord_4695870
  simp only [CollatzResearch.WordTrace]
  refine ⟨21409056187209056948920633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 114181632998448303727576709 21409056187209056948920633)
  ·
    refine ⟨16056792140406792711690475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21409056187209056948920633 16056792140406792711690475)
    ·
      refine ⟨24085188210610189067535713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16056792140406792711690475 24085188210610189067535713)
      ·
        refine ⟨18063891157957641800651785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24085188210610189067535713 18063891157957641800651785)
        ·
          refine ⟨13547918368468231350488839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18063891157957641800651785 13547918368468231350488839)
          ·
            refine ⟨20321877552702347025733259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13547918368468231350488839 20321877552702347025733259)
            ·
              refine ⟨30482816329053520538599889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20321877552702347025733259 30482816329053520538599889)
              ·
                refine ⟨22862112246790140403949917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30482816329053520538599889 22862112246790140403949917)
                ·
                  refine ⟨8573292092546302651481219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22862112246790140403949917 8573292092546302651481219)
                  ·
                    refine ⟨12859938138819453977221829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8573292092546302651481219 12859938138819453977221829)
                    ·
                      refine ⟨2411238401028647620729093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12859938138819453977221829 2411238401028647620729093)
                      ·
                        rfl

theorem cell23_4695870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 2, 3, 1, 4].length) (baseStart_4695870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4695870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4695870 prefixEnd_4695870 := by exact prefixLift 4695870
  have htrace : WordTrace (prefixWord ++ tailWord_4695870) baseStart_4695870 baseEnd_4695870 := by
    simpa [prefixWord, tailWord_4695870, baseEnd_4695870] using wordTrace_append hprefix tailTrace_4695870
  have hstable : (prefixWord ++ tailWord_4695870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4695870).length < 2 ^ (prefixWord ++ tailWord_4695870).sum := by decide
  have hdescent : baseEnd_4695870 < baseStart_4695870 := by decide
  rcases family_descends (prefixWord ++ tailWord_4695870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4695880 : List Nat := [2, 1, 3, 1, 1, 4, 2, 3, 2, 4]
def baseStart_4695880 : Nat := 118140960795 + 4695880 * 2 ^ 59
def prefixEnd_4695880 : Nat := 4983230072969 + 3 ^ 40 * 4695880 * 2
def baseEnd_4695880 : Nat := 803747845278397527201349

theorem tailTrace_4695880 : CollatzResearch.WordTrace tailWord_4695880 prefixEnd_4695880 803747845278397527201349 := by
  unfold tailWord_4695880
  simp only [CollatzResearch.WordTrace]
  refine ⟨85636407113818113649614547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114181876151757484866152729 85636407113818113649614547)
  ·
    refine ⟨128454610670727170474421821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85636407113818113649614547 128454610670727170474421821)
    ·
      refine ⟨48170479001522688927908183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 128454610670727170474421821 48170479001522688927908183)
      ·
        refine ⟨72255718502284033391862275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48170479001522688927908183 72255718502284033391862275)
        ·
          refine ⟨108383577753426050087793413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72255718502284033391862275 108383577753426050087793413)
          ·
            refine ⟨20321920828767384391461265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 108383577753426050087793413 20321920828767384391461265)
            ·
              refine ⟨15241440621575538293595949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20321920828767384391461265 15241440621575538293595949)
              ·
                refine ⟨5715540233090826860098481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15241440621575538293595949 5715540233090826860098481)
                ·
                  refine ⟨4286655174818120145073861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5715540233090826860098481 4286655174818120145073861)
                  ·
                    refine ⟨803747845278397527201349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4286655174818120145073861 803747845278397527201349)
                    ·
                      rfl

theorem cell23_4695880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 3, 2, 4].length) (baseStart_4695880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4695880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4695880 prefixEnd_4695880 := by exact prefixLift 4695880
  have htrace : WordTrace (prefixWord ++ tailWord_4695880) baseStart_4695880 baseEnd_4695880 := by
    simpa [prefixWord, tailWord_4695880, baseEnd_4695880] using wordTrace_append hprefix tailTrace_4695880
  have hstable : (prefixWord ++ tailWord_4695880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4695880).length < 2 ^ (prefixWord ++ tailWord_4695880).sum := by decide
  have hdescent : baseEnd_4695880 < baseStart_4695880 := by decide
  rcases family_descends (prefixWord ++ tailWord_4695880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4695890 : List Nat := [3, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3]
def baseStart_4695890 : Nat := 118140960795 + 4695890 * 2 ^ 59
def prefixEnd_4695890 : Nat := 4983230072969 + 3 ^ 40 * 4695890 * 2
def baseEnd_4695890 : Nat := 2411248670641737542479001

theorem tailTrace_4695890 : CollatzResearch.WordTrace tailWord_4695890 prefixEnd_4695890 2411248670641737542479001 := by
  unfold tailWord_4695890
  simp only [CollatzResearch.WordTrace]
  refine ⟨42818294739399999751773281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114182119305066666004728749 42818294739399999751773281)
  ·
    refine ⟨32113721054549999813829961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42818294739399999751773281 32113721054549999813829961)
    ·
      refine ⟨24085290790912499860372471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32113721054549999813829961 24085290790912499860372471)
      ·
        refine ⟨36127936186368749790558707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24085290790912499860372471 36127936186368749790558707)
        ·
          refine ⟨54191904279553124685838061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36127936186368749790558707 54191904279553124685838061)
          ·
            refine ⟨20321964104832421757189273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54191904279553124685838061 20321964104832421757189273)
            ·
              refine ⟨15241473078624316317891955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20321964104832421757189273 15241473078624316317891955)
              ·
                refine ⟨22862209617936474476837933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15241473078624316317891955 22862209617936474476837933)
                ·
                  refine ⟨8573328606726177928814225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22862209617936474476837933 8573328606726177928814225)
                  ·
                    refine ⟨6429996455044633446610669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8573328606726177928814225 6429996455044633446610669)
                    ·
                      refine ⟨2411248670641737542479001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6429996455044633446610669 2411248670641737542479001)
                      ·
                        rfl

theorem cell23_4695890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3].length) (baseStart_4695890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4695890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4695890 prefixEnd_4695890 := by exact prefixLift 4695890
  have htrace : WordTrace (prefixWord ++ tailWord_4695890) baseStart_4695890 baseEnd_4695890 := by
    simpa [prefixWord, tailWord_4695890, baseEnd_4695890] using wordTrace_append hprefix tailTrace_4695890
  have hstable : (prefixWord ++ tailWord_4695890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4695890).length < 2 ^ (prefixWord ++ tailWord_4695890).sum := by decide
  have hdescent : baseEnd_4695890 < baseStart_4695890 := by decide
  rcases family_descends (prefixWord ++ tailWord_4695890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4695904 : List Nat := [2, 1, 1, 3, 3, 2, 1, 5, 1, 2, 2]
def baseStart_4695904 : Nat := 118140960795 + 4695904 * 2 ^ 59
def prefixEnd_4695904 : Nat := 4983230072969 + 3 ^ 40 * 4695904 * 2
def baseEnd_4695904 : Nat := 2411255859370900487703937

theorem tailTrace_4695904 : CollatzResearch.WordTrace tailWord_4695904 prefixEnd_4695904 2411255859370900487703937 := by
  unfold tailWord_4695904
  simp only [CollatzResearch.WordTrace]
  refine ⟨85636844789774639699051383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114182459719699519598735177 85636844789774639699051383)
  ·
    refine ⟨128455267184661959548577075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85636844789774639699051383 128455267184661959548577075)
    ·
      refine ⟨192682900776992939322865613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128455267184661959548577075 192682900776992939322865613)
      ·
        refine ⟨72256087791372352246074605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 192682900776992939322865613 72256087791372352246074605)
        ·
          refine ⟨27096032921764632092277977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72256087791372352246074605 27096032921764632092277977)
          ·
            refine ⟨20322024691323474069208483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27096032921764632092277977 20322024691323474069208483)
            ·
              refine ⟨30483037036985211103812725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20322024691323474069208483 30483037036985211103812725)
              ·
                refine ⟨2857784722217363540982443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30483037036985211103812725 2857784722217363540982443)
                ·
                  refine ⟨4286677083326045311473665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2857784722217363540982443 4286677083326045311473665)
                  ·
                    refine ⟨3215007812494533983605249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4286677083326045311473665 3215007812494533983605249)
                    ·
                      refine ⟨2411255859370900487703937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3215007812494533983605249 2411255859370900487703937)
                      ·
                        rfl

theorem cell23_4695904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 5, 1, 2, 2].length) (baseStart_4695904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4695904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4695904 prefixEnd_4695904 := by exact prefixLift 4695904
  have htrace : WordTrace (prefixWord ++ tailWord_4695904) baseStart_4695904 baseEnd_4695904 := by
    simpa [prefixWord, tailWord_4695904, baseEnd_4695904] using wordTrace_append hprefix tailTrace_4695904
  have hstable : (prefixWord ++ tailWord_4695904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4695904).length < 2 ^ (prefixWord ++ tailWord_4695904).sum := by decide
  have hdescent : baseEnd_4695904 < baseStart_4695904 := by decide
  rcases family_descends (prefixWord ++ tailWord_4695904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4695907 : List Nat := [1, 1, 1, 5, 4, 1, 1, 3, 1, 2, 3]
def baseStart_4695907 : Nat := 118140960795 + 4695907 * 2 ^ 59
def prefixEnd_4695907 : Nat := 4983230072969 + 3 ^ 40 * 4695907 * 2
def baseEnd_4695907 : Nat := 2411257399812863975966423

theorem tailTrace_4695907 : CollatzResearch.WordTrace tailWord_4695907 prefixEnd_4695907 2411257399812863975966423 := by
  unfold tailWord_4695907
  simp only [CollatzResearch.WordTrace]
  refine ⟨171273798998538410910461975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114182532665692273940307983 171273798998538410910461975)
  ·
    refine ⟨256910698497807616365692963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171273798998538410910461975 256910698497807616365692963)
    ·
      refine ⟨385366047746711424548539445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 256910698497807616365692963 385366047746711424548539445)
      ·
        refine ⟨36128066976254196051425573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 385366047746711424548539445 36128066976254196051425573)
        ·
          refine ⟨6774012558047661759642295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36128066976254196051425573 6774012558047661759642295)
          ·
            refine ⟨10161018837071492639463443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6774012558047661759642295 10161018837071492639463443)
            ·
              refine ⟨15241528255607238959195165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10161018837071492639463443 15241528255607238959195165)
              ·
                refine ⟨5715573095852714609698187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15241528255607238959195165 5715573095852714609698187)
                ·
                  refine ⟨8573359643779071914547281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5715573095852714609698187 8573359643779071914547281)
                  ·
                    refine ⟨6430019732834303935910461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8573359643779071914547281 6430019732834303935910461)
                    ·
                      refine ⟨2411257399812863975966423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6430019732834303935910461 2411257399812863975966423)
                      ·
                        rfl

theorem cell23_4695907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 3, 1, 2, 3].length) (baseStart_4695907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4695907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4695907 prefixEnd_4695907 := by exact prefixLift 4695907
  have htrace : WordTrace (prefixWord ++ tailWord_4695907) baseStart_4695907 baseEnd_4695907 := by
    simpa [prefixWord, tailWord_4695907, baseEnd_4695907] using wordTrace_append hprefix tailTrace_4695907
  have hstable : (prefixWord ++ tailWord_4695907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4695907).length < 2 ^ (prefixWord ++ tailWord_4695907).sum := by decide
  have hdescent : baseEnd_4695907 < baseStart_4695907 := by decide
  rcases family_descends (prefixWord ++ tailWord_4695907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4695930 : List Nat := [3, 1, 1, 1, 1, 1, 4, 1, 5, 3, 2]
def baseStart_4695930 : Nat := 118140960795 + 4695930 * 2 ^ 59
def prefixEnd_4695930 : Nat := 4983230072969 + 3 ^ 40 * 4695930 * 2
def baseEnd_4695930 : Nat := 2411269209867917385978817

theorem tailTrace_4695930 : CollatzResearch.WordTrace tailWord_4695930 prefixEnd_4695930 2411269209867917385978817 := by
  unfold tailWord_4695930
  simp only [CollatzResearch.WordTrace]
  refine ⟨42818659469363771459637311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114183091918303390559032829 42818659469363771459637311)
  ·
    refine ⟨64227989204045657189455967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42818659469363771459637311 64227989204045657189455967)
    ·
      refine ⟨96341983806068485784183951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64227989204045657189455967 96341983806068485784183951)
      ·
        refine ⟨144512975709102728676275927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96341983806068485784183951 144512975709102728676275927)
        ·
          refine ⟨216769463563654093014413891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144512975709102728676275927 216769463563654093014413891)
          ·
            refine ⟨325154195345481139521620837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 216769463563654093014413891 325154195345481139521620837)
            ·
              refine ⟨60966411627277713660303907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 325154195345481139521620837 60966411627277713660303907)
              ·
                refine ⟨91449617440916570490455861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60966411627277713660303907 91449617440916570490455861)
                ·
                  refine ⟨8573401635085928483480237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 91449617440916570490455861 8573401635085928483480237)
                  ·
                    refine ⟨3215025613157223181305089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8573401635085928483480237 3215025613157223181305089)
                    ·
                      refine ⟨2411269209867917385978817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3215025613157223181305089 2411269209867917385978817)
                      ·
                        rfl

theorem cell23_4695930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 1, 5, 3, 2].length) (baseStart_4695930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4695930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4695930 prefixEnd_4695930 := by exact prefixLift 4695930
  have htrace : WordTrace (prefixWord ++ tailWord_4695930) baseStart_4695930 baseEnd_4695930 := by
    simpa [prefixWord, tailWord_4695930, baseEnd_4695930] using wordTrace_append hprefix tailTrace_4695930
  have hstable : (prefixWord ++ tailWord_4695930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4695930).length < 2 ^ (prefixWord ++ tailWord_4695930).sum := by decide
  have hdescent : baseEnd_4695930 < baseStart_4695930 := by decide
  rcases family_descends (prefixWord ++ tailWord_4695930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4695934 : List Nat := [4, 2, 3, 1, 1, 3, 1, 1, 1, 2, 4]
def baseStart_4695934 : Nat := 118140960795 + 4695934 * 2 ^ 59
def prefixEnd_4695934 : Nat := 4983230072969 + 3 ^ 40 * 4695934 * 2
def baseEnd_4695934 : Nat := 2411271263790535370328799

theorem tailTrace_4695934 : CollatzResearch.WordTrace tailWord_4695934 prefixEnd_4695934 2411271263790535370328799 := by
  unfold tailWord_4695934
  simp only [CollatzResearch.WordTrace]
  refine ⟨21409347971180074315211857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 114183189179627063014463237 21409347971180074315211857)
  ·
    refine ⟨16057010978385055736408893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21409347971180074315211857 16057010978385055736408893)
    ·
      refine ⟨6021379116894395901153335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16057010978385055736408893 6021379116894395901153335)
      ·
        refine ⟨9032068675341593851730003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6021379116894395901153335 9032068675341593851730003)
        ·
          refine ⟨13548103013012390777595005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9032068675341593851730003 13548103013012390777595005)
          ·
            refine ⟨5080538629879646541598127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13548103013012390777595005 5080538629879646541598127)
            ·
              refine ⟨7620807944819469812397191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5080538629879646541598127 7620807944819469812397191)
              ·
                refine ⟨11431211917229204718595787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7620807944819469812397191 11431211917229204718595787)
                ·
                  refine ⟨17146817875843807077893681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11431211917229204718595787 17146817875843807077893681)
                  ·
                    refine ⟨12860113406882855308420261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17146817875843807077893681 12860113406882855308420261)
                    ·
                      refine ⟨2411271263790535370328799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12860113406882855308420261 2411271263790535370328799)
                      ·
                        rfl

theorem cell23_4695934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 1, 1, 1, 2, 4].length) (baseStart_4695934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4695934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4695934 prefixEnd_4695934 := by exact prefixLift 4695934
  have htrace : WordTrace (prefixWord ++ tailWord_4695934) baseStart_4695934 baseEnd_4695934 := by
    simpa [prefixWord, tailWord_4695934, baseEnd_4695934] using wordTrace_append hprefix tailTrace_4695934
  have hstable : (prefixWord ++ tailWord_4695934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4695934).length < 2 ^ (prefixWord ++ tailWord_4695934).sum := by decide
  have hdescent : baseEnd_4695934 < baseStart_4695934 := by decide
  rcases family_descends (prefixWord ++ tailWord_4695934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4695964 : List Nat := [2, 2, 3, 3, 1, 1, 2, 3, 1, 3, 2]
def baseStart_4695964 : Nat := 118140960795 + 4695964 * 2 ^ 59
def prefixEnd_4695964 : Nat := 4983230072969 + 3 ^ 40 * 4695964 * 2
def baseEnd_4695964 : Nat := 2411286668210170252953661

theorem tailTrace_4695964 : CollatzResearch.WordTrace tailWord_4695964 prefixEnd_4695964 2411286668210170252953661 := by
  unfold tailWord_4695964
  simp only [CollatzResearch.WordTrace]
  refine ⟨85637938979665954822643473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114183918639554606430191297 85637938979665954822643473)
  ·
    refine ⟨64228454234749466116982605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85637938979665954822643473 64228454234749466116982605)
    ·
      refine ⟨24085670338031049793868477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64228454234749466116982605 24085670338031049793868477)
      ·
        refine ⟨9032126376761643672700679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24085670338031049793868477 9032126376761643672700679)
        ·
          refine ⟨13548189565142465509051019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9032126376761643672700679 13548189565142465509051019)
          ·
            refine ⟨20322284347713698263576529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13548189565142465509051019 20322284347713698263576529)
            ·
              refine ⟨15241713260785273697682397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20322284347713698263576529 15241713260785273697682397)
              ·
                refine ⟨5715642472794477636630899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15241713260785273697682397 5715642472794477636630899)
                ·
                  refine ⟨8573463709191716454946349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5715642472794477636630899 8573463709191716454946349)
                  ·
                    refine ⟨3215048890946893670604881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8573463709191716454946349 3215048890946893670604881)
                    ·
                      refine ⟨2411286668210170252953661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3215048890946893670604881 2411286668210170252953661)
                      ·
                        rfl

theorem cell23_4695964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 3, 1, 3, 2].length) (baseStart_4695964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4695964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4695964 prefixEnd_4695964 := by exact prefixLift 4695964
  have htrace : WordTrace (prefixWord ++ tailWord_4695964) baseStart_4695964 baseEnd_4695964 := by
    simpa [prefixWord, tailWord_4695964, baseEnd_4695964] using wordTrace_append hprefix tailTrace_4695964
  have hstable : (prefixWord ++ tailWord_4695964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4695964).length < 2 ^ (prefixWord ++ tailWord_4695964).sum := by decide
  have hdescent : baseEnd_4695964 < baseStart_4695964 := by decide
  rcases family_descends (prefixWord ++ tailWord_4695964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4695973 : List Nat := [1, 3, 1, 2, 1, 1, 1, 3, 4, 2, 4]
def baseStart_4695973 : Nat := 118140960795 + 4695973 * 2 ^ 59
def prefixEnd_4695973 : Nat := 4983230072969 + 3 ^ 40 * 4695973 * 2
def baseEnd_4695973 : Nat := 2411291289536060717741119

theorem tailTrace_4695973 : CollatzResearch.WordTrace tailWord_4695973 prefixEnd_4695973 2411291289536060717741119 := by
  unfold tailWord_4695973
  simp only [CollatzResearch.WordTrace]
  refine ⟨171276206216299304182364573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114184137477532869454909715 171276206216299304182364573)
  ·
    refine ⟨64228577331112239068386715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 171276206216299304182364573 64228577331112239068386715)
    ·
      refine ⟨96342865996668358602580073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64228577331112239068386715 96342865996668358602580073)
      ·
        refine ⟨72257149497501268951935055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96342865996668358602580073 72257149497501268951935055)
        ·
          refine ⟨108385724246251903427902583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72257149497501268951935055 108385724246251903427902583)
          ·
            refine ⟨162578586369377855141853875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108385724246251903427902583 162578586369377855141853875)
            ·
              refine ⟨243867879554066782712780813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 162578586369377855141853875 243867879554066782712780813)
              ·
                refine ⟨91450454832775043517292805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 243867879554066782712780813 91450454832775043517292805)
                ·
                  refine ⟨17146960281145320659492401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 91450454832775043517292805 17146960281145320659492401)
                  ·
                    refine ⟨12860220210858990494619301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17146960281145320659492401 12860220210858990494619301)
                    ·
                      refine ⟨2411291289536060717741119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12860220210858990494619301 2411291289536060717741119)
                      ·
                        rfl

theorem cell23_4695973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 3, 4, 2, 4].length) (baseStart_4695973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4695973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4695973 prefixEnd_4695973 := by exact prefixLift 4695973
  have htrace : WordTrace (prefixWord ++ tailWord_4695973) baseStart_4695973 baseEnd_4695973 := by
    simpa [prefixWord, tailWord_4695973, baseEnd_4695973] using wordTrace_append hprefix tailTrace_4695973
  have hstable : (prefixWord ++ tailWord_4695973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4695973).length < 2 ^ (prefixWord ++ tailWord_4695973).sum := by decide
  have hdescent : baseEnd_4695973 < baseStart_4695973 := by decide
  rcases family_descends (prefixWord ++ tailWord_4695973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4696023 : List Nat := [1, 1, 3, 2, 1, 1, 3, 1, 3, 2, 5]
def baseStart_4696023 : Nat := 118140960795 + 4696023 * 2 ^ 59
def prefixEnd_4696023 : Nat := 4983230072969 + 3 ^ 40 * 4696023 * 2
def baseEnd_4696023 : Nat := 2411316963568785522115889

theorem tailTrace_4696023 : CollatzResearch.WordTrace tailWord_4696023 prefixEnd_4696023 2411316963568785522115889 := by
  unfold tailWord_4696023
  simp only [CollatzResearch.WordTrace]
  refine ⟨171278029866118162721684723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114185353244078775147789815 171278029866118162721684723)
  ·
    refine ⟨256917044799177244082527085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171278029866118162721684723 256917044799177244082527085)
    ·
      refine ⟨96343891799691466530947657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 256917044799177244082527085 96343891799691466530947657)
      ·
        refine ⟨72257918849768599898210743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96343891799691466530947657 72257918849768599898210743)
        ·
          refine ⟨108386878274652899847316115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72257918849768599898210743 108386878274652899847316115)
          ·
            refine ⟨162580317411979349770974173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108386878274652899847316115 162580317411979349770974173)
            ·
              refine ⟨60967619029492256164115315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 162580317411979349770974173 60967619029492256164115315)
              ·
                refine ⟨91451428544238384246172973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60967619029492256164115315 91451428544238384246172973)
                ·
                  refine ⟨34294285704089394092314865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 91451428544238384246172973 34294285704089394092314865)
                  ·
                    refine ⟨25720714278067045569236149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34294285704089394092314865 25720714278067045569236149)
                    ·
                      refine ⟨2411316963568785522115889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25720714278067045569236149 2411316963568785522115889)
                      ·
                        rfl

theorem cell23_4696023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 1, 3, 2, 5].length) (baseStart_4696023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4696023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4696023 prefixEnd_4696023 := by exact prefixLift 4696023
  have htrace : WordTrace (prefixWord ++ tailWord_4696023) baseStart_4696023 baseEnd_4696023 := by
    simpa [prefixWord, tailWord_4696023, baseEnd_4696023] using wordTrace_append hprefix tailTrace_4696023
  have hstable : (prefixWord ++ tailWord_4696023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4696023).length < 2 ^ (prefixWord ++ tailWord_4696023).sum := by decide
  have hdescent : baseEnd_4696023 < baseStart_4696023 := by decide
  rcases family_descends (prefixWord ++ tailWord_4696023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4696063 : List Nat := [1, 1, 2, 2, 1, 2, 1, 2, 4, 1, 6]
def baseStart_4696063 : Nat := 118140960795 + 4696063 * 2 ^ 59
def prefixEnd_4696063 : Nat := 4983230072969 + 3 ^ 40 * 4696063 * 2
def baseEnd_4696063 : Nat := 2411337502794965365615705

theorem tailTrace_4696063 : CollatzResearch.WordTrace tailWord_4696063 prefixEnd_4696063 2411337502794965365615705 := by
  unfold tailWord_4696063
  simp only [CollatzResearch.WordTrace]
  refine ⟨171279488785973249553140843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114186325857315499702093895 171279488785973249553140843)
  ·
    refine ⟨256919233178959874329711265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171279488785973249553140843 256919233178959874329711265)
    ·
      refine ⟨192689424884219905747283449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 256919233178959874329711265 192689424884219905747283449)
      ·
        refine ⟨144517068663164929310462587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 192689424884219905747283449 144517068663164929310462587)
        ·
          refine ⟨216775602994747393965693881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144517068663164929310462587 216775602994747393965693881)
          ·
            refine ⟨162581702246060545474270411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 216775602994747393965693881 162581702246060545474270411)
            ·
              refine ⟨243872553369090818211405617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 162581702246060545474270411 243872553369090818211405617)
              ·
                refine ⟨182904415026818113658554213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 243872553369090818211405617 182904415026818113658554213)
                ·
                  refine ⟨34294577817528396310978915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 182904415026818113658554213 34294577817528396310978915)
                  ·
                    refine ⟨51441866726292594466468373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34294577817528396310978915 51441866726292594466468373)
                    ·
                      refine ⟨2411337502794965365615705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 51441866726292594466468373 2411337502794965365615705)
                      ·
                        rfl

theorem cell23_4696063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 4, 1, 6].length) (baseStart_4696063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4696063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4696063 prefixEnd_4696063 := by exact prefixLift 4696063
  have htrace : WordTrace (prefixWord ++ tailWord_4696063) baseStart_4696063 baseEnd_4696063 := by
    simpa [prefixWord, tailWord_4696063, baseEnd_4696063] using wordTrace_append hprefix tailTrace_4696063
  have hstable : (prefixWord ++ tailWord_4696063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4696063).length < 2 ^ (prefixWord ++ tailWord_4696063).sum := by decide
  have hdescent : baseEnd_4696063 < baseStart_4696063 := by decide
  rcases family_descends (prefixWord ++ tailWord_4696063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4696090 : List Nat := [3, 1, 1, 3, 1, 4, 1, 1, 8]
def baseStart_4696090 : Nat := 118140960795 + 4696090 * 2 ^ 59
def prefixEnd_4696090 : Nat := 4983230072969 + 3 ^ 40 * 4696090 * 2
def baseEnd_4696090 : Nat := 267927929641404084442009

theorem tailTrace_4696090 : CollatzResearch.WordTrace tailWord_4696090 prefixEnd_4696090 267927929641404084442009 := by
  unfold tailWord_4696090
  simp only [CollatzResearch.WordTrace]
  refine ⟨42820118389218858291093431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114186982371250288776249149 42820118389218858291093431)
  ·
    refine ⟨64230177583828287436640147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42820118389218858291093431 64230177583828287436640147)
    ·
      refine ⟨96345266375742431154960221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64230177583828287436640147 96345266375742431154960221)
      ·
        refine ⟨36129474890903411683110083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96345266375742431154960221 36129474890903411683110083)
        ·
          refine ⟨54194212336355117524665125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36129474890903411683110083 54194212336355117524665125)
          ·
            refine ⟨10161414813066584535874711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 54194212336355117524665125 10161414813066584535874711)
            ·
              refine ⟨15242122219599876803812067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10161414813066584535874711 15242122219599876803812067)
              ·
                refine ⟨22863183329399815205718101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15242122219599876803812067 22863183329399815205718101)
                ·
                  refine ⟨267927929641404084442009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22863183329399815205718101 267927929641404084442009)
                  ·
                    rfl

theorem cell23_4696090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 1, 8].length) (baseStart_4696090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4696090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4696090 prefixEnd_4696090 := by exact prefixLift 4696090
  have htrace : WordTrace (prefixWord ++ tailWord_4696090) baseStart_4696090 baseEnd_4696090 := by
    simpa [prefixWord, tailWord_4696090, baseEnd_4696090] using wordTrace_append hprefix tailTrace_4696090
  have hstable : (prefixWord ++ tailWord_4696090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4696090).length < 2 ^ (prefixWord ++ tailWord_4696090).sum := by decide
  have hdescent : baseEnd_4696090 < baseStart_4696090 := by decide
  rcases family_descends (prefixWord ++ tailWord_4696090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4696127 : List Nat := [1, 1, 2, 2, 3, 1, 4, 1, 1, 5, 2]
def baseStart_4696127 : Nat := 118140960795 + 4696127 * 2 ^ 59
def prefixEnd_4696127 : Nat := 4983230072969 + 3 ^ 40 * 4696127 * 2
def baseEnd_4696127 : Nat := 2411370365556853115215411

theorem tailTrace_4696127 : CollatzResearch.WordTrace tailWord_4696127 prefixEnd_4696127 2411370365556853115215411 := by
  unfold tailWord_4696127
  simp only [CollatzResearch.WordTrace]
  refine ⟨171281823057741388483470635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114187882038494258988980423 171281823057741388483470635)
  ·
    refine ⟨256922734586612082725205953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171281823057741388483470635 256922734586612082725205953)
    ·
      refine ⟨192692050939959062043904465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 256922734586612082725205953 192692050939959062043904465)
      ·
        refine ⟨144519038204969296532928349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 192692050939959062043904465 144519038204969296532928349)
        ·
          refine ⟨54194639326863486199848131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 144519038204969296532928349 54194639326863486199848131)
          ·
            refine ⟨81291958990295229299772197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54194639326863486199848131 81291958990295229299772197)
            ·
              refine ⟨15242242310680355493707287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 81291958990295229299772197 15242242310680355493707287)
              ·
                refine ⟨22863363466020533240560931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15242242310680355493707287 22863363466020533240560931)
                ·
                  refine ⟨34295045199030799860841397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22863363466020533240560931 34295045199030799860841397)
                  ·
                    refine ⟨3215160487409137486953881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34295045199030799860841397 3215160487409137486953881)
                    ·
                      refine ⟨2411370365556853115215411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3215160487409137486953881 2411370365556853115215411)
                      ·
                        rfl

theorem cell23_4696127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 1, 1, 5, 2].length) (baseStart_4696127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4696127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4696127 prefixEnd_4696127 := by exact prefixLift 4696127
  have htrace : WordTrace (prefixWord ++ tailWord_4696127) baseStart_4696127 baseEnd_4696127 := by
    simpa [prefixWord, tailWord_4696127, baseEnd_4696127] using wordTrace_append hprefix tailTrace_4696127
  have hstable : (prefixWord ++ tailWord_4696127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4696127).length < 2 ^ (prefixWord ++ tailWord_4696127).sum := by decide
  have hdescent : baseEnd_4696127 < baseStart_4696127 := by decide
  rcases family_descends (prefixWord ++ tailWord_4696127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4696177 : List Nat := [1, 2, 2, 2, 1, 1, 5, 1, 3, 2, 3]
def baseStart_4696177 : Nat := 118140960795 + 4696177 * 2 ^ 59
def prefixEnd_4696177 : Nat := 4983230072969 + 3 ^ 40 * 4696177 * 2
def baseEnd_4696177 : Nat := 2411396039589577919590181

theorem tailTrace_4696177 : CollatzResearch.WordTrace tailWord_4696177 prefixEnd_4696177 2411396039589577919590181 := by
  unfold tailWord_4696177
  simp only [CollatzResearch.WordTrace]
  refine ⟨171283646707560247022790785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114189097805040164681860523 171283646707560247022790785)
  ·
    refine ⟨128462735030670185267093089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171283646707560247022790785 128462735030670185267093089)
    ·
      refine ⟨96347051273002638950319817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128462735030670185267093089 96347051273002638950319817)
      ·
        refine ⟨72260288454751979212739863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96347051273002638950319817 72260288454751979212739863)
        ·
          refine ⟨108390432682127968819109795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72260288454751979212739863 108390432682127968819109795)
          ·
            refine ⟨162585649023191953228664693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108390432682127968819109795 162585649023191953228664693)
            ·
              refine ⟨15242404595924245615187315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 162585649023191953228664693 15242404595924245615187315)
              ·
                refine ⟨22863606893886368422780973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15242404595924245615187315 22863606893886368422780973)
                ·
                  refine ⟨8573852585207388158542865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22863606893886368422780973 8573852585207388158542865)
                  ·
                    refine ⟨6430389438905541118907149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8573852585207388158542865 6430389438905541118907149)
                    ·
                      refine ⟨2411396039589577919590181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6430389438905541118907149 2411396039589577919590181)
                      ·
                        rfl

theorem cell23_4696177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 1, 3, 2, 3].length) (baseStart_4696177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4696177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4696177 prefixEnd_4696177 := by exact prefixLift 4696177
  have htrace : WordTrace (prefixWord ++ tailWord_4696177) baseStart_4696177 baseEnd_4696177 := by
    simpa [prefixWord, tailWord_4696177, baseEnd_4696177] using wordTrace_append hprefix tailTrace_4696177
  have hstable : (prefixWord ++ tailWord_4696177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4696177).length < 2 ^ (prefixWord ++ tailWord_4696177).sum := by decide
  have hdescent : baseEnd_4696177 < baseStart_4696177 := by decide
  rcases family_descends (prefixWord ++ tailWord_4696177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4696224 : List Nat := [2, 1, 1, 4, 2, 3, 2, 1, 1, 3, 3]
def baseStart_4696224 : Nat := 118140960795 + 4696224 * 2 ^ 59
def prefixEnd_4696224 : Nat := 4983230072969 + 3 ^ 40 * 4696224 * 2
def baseEnd_4696224 : Nat := 2411420173180339235702465

theorem tailTrace_4696224 : CollatzResearch.WordTrace tailWord_4696224 prefixEnd_4696224 2411420173180339235702465 := by
  unfold tailWord_4696224
  simp only [CollatzResearch.WordTrace]
  refine ⟨85642680469194987024875863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114190240625593316033167817 85642680469194987024875863)
  ·
    refine ⟨128464020703792480537313795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85642680469194987024875863 128464020703792480537313795)
    ·
      refine ⟨192696031055688720805970693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128464020703792480537313795 192696031055688720805970693)
      ·
        refine ⟨36130505822941635151119505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 192696031055688720805970693 36130505822941635151119505)
        ·
          refine ⟨27097879367206226363339629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36130505822941635151119505 27097879367206226363339629)
          ·
            refine ⟨10161704762702334886252361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27097879367206226363339629 10161704762702334886252361)
            ·
              refine ⟨7621278572026751164689271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10161704762702334886252361 7621278572026751164689271)
              ·
                refine ⟨11431917858040126747033907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7621278572026751164689271 11431917858040126747033907)
                ·
                  refine ⟨17147876787060190120550861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11431917858040126747033907 17147876787060190120550861)
                  ·
                    refine ⟨6430453795147571295206573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17147876787060190120550861 6430453795147571295206573)
                    ·
                      refine ⟨2411420173180339235702465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6430453795147571295206573 2411420173180339235702465)
                      ·
                        rfl

theorem cell23_4696224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 2, 1, 1, 3, 3].length) (baseStart_4696224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4696224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4696224 prefixEnd_4696224 := by exact prefixLift 4696224
  have htrace : WordTrace (prefixWord ++ tailWord_4696224) baseStart_4696224 baseEnd_4696224 := by
    simpa [prefixWord, tailWord_4696224, baseEnd_4696224] using wordTrace_append hprefix tailTrace_4696224
  have hstable : (prefixWord ++ tailWord_4696224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4696224).length < 2 ^ (prefixWord ++ tailWord_4696224).sum := by decide
  have hdescent : baseEnd_4696224 < baseStart_4696224 := by decide
  rcases family_descends (prefixWord ++ tailWord_4696224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4696240 : List Nat := [2, 1, 1, 1, 2, 1, 2, 1, 6, 6]
def baseStart_4696240 : Nat := 118140960795 + 4696240 * 2 ^ 59
def prefixEnd_4696240 : Nat := 4983230072969 + 3 ^ 40 * 4696240 * 2
def baseEnd_4696240 : Nat := 803809462956937057700797

theorem tailTrace_4696240 : CollatzResearch.WordTrace tailWord_4696240 prefixEnd_4696240 803809462956937057700797 := by
  unfold tailWord_4696240
  simp only [CollatzResearch.WordTrace]
  refine ⟨85642972253166004391167087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114190629670888005854889449 85642972253166004391167087)
  ·
    refine ⟨128464458379749006586750631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85642972253166004391167087 128464458379749006586750631)
    ·
      refine ⟨192696687569623509880125947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128464458379749006586750631 192696687569623509880125947)
      ·
        refine ⟨289045031354435264820188921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192696687569623509880125947 289045031354435264820188921)
        ·
          refine ⟨216783773515826448615141691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 289045031354435264820188921 216783773515826448615141691)
          ·
            refine ⟨325175660273739672922712537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 216783773515826448615141691 325175660273739672922712537)
            ·
              refine ⟨243881745205304754692034403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 325175660273739672922712537 243881745205304754692034403)
              ·
                refine ⟨365822617807957132038051605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 243881745205304754692034403 365822617807957132038051605)
                ·
                  refine ⟨17147935209747990564283669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 365822617807957132038051605 17147935209747990564283669)
                  ·
                    refine ⟨803809462956937057700797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17147935209747990564283669 803809462956937057700797)
                    ·
                      rfl

theorem cell23_4696240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 6, 6].length) (baseStart_4696240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4696240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4696240 prefixEnd_4696240 := by exact prefixLift 4696240
  have htrace : WordTrace (prefixWord ++ tailWord_4696240) baseStart_4696240 baseEnd_4696240 := by
    simpa [prefixWord, tailWord_4696240, baseEnd_4696240] using wordTrace_append hprefix tailTrace_4696240
  have hstable : (prefixWord ++ tailWord_4696240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4696240).length < 2 ^ (prefixWord ++ tailWord_4696240).sum := by decide
  have hdescent : baseEnd_4696240 < baseStart_4696240 := by decide
  rcases family_descends (prefixWord ++ tailWord_4696240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4696245 : List Nat := [1, 3, 3, 4, 1, 2, 2, 1, 1, 2, 3]
def baseStart_4696245 : Nat := 118140960795 + 4696245 * 2 ^ 59
def prefixEnd_4696245 : Nat := 4983230072969 + 3 ^ 40 * 4696245 * 2
def baseEnd_4696245 : Nat := 2411430956274083653539869

theorem tailTrace_4696245 : CollatzResearch.WordTrace tailWord_4696245 prefixEnd_4696245 2411430956274083653539869 := by
  unfold tailWord_4696245
  simp only [CollatzResearch.WordTrace]
  refine ⟨171286126871313894636266189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114190751247542596424177459 171286126871313894636266189)
  ·
    refine ⟨64232297576742710488599821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 171286126871313894636266189 64232297576742710488599821)
    ·
      refine ⟨24087111591278516433224933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64232297576742710488599821 24087111591278516433224933)
      ·
        refine ⟨4516333423364721831229675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24087111591278516433224933 4516333423364721831229675)
        ·
          refine ⟨6774500135047082746844513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4516333423364721831229675 6774500135047082746844513)
          ·
            refine ⟨5080875101285312060133385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6774500135047082746844513 5080875101285312060133385)
            ·
              refine ⟨3810656325963984045100039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5080875101285312060133385 3810656325963984045100039)
              ·
                refine ⟨5715984488945976067650059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3810656325963984045100039 5715984488945976067650059)
                ·
                  refine ⟨8573976733418964101475089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5715984488945976067650059 8573976733418964101475089)
                  ·
                    refine ⟨6430482550064223076106317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8573976733418964101475089 6430482550064223076106317)
                    ·
                      refine ⟨2411430956274083653539869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6430482550064223076106317 2411430956274083653539869)
                      ·
                        rfl

theorem cell23_4696245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 2, 1, 1, 2, 3].length) (baseStart_4696245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4696245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4696245 prefixEnd_4696245 := by exact prefixLift 4696245
  have htrace : WordTrace (prefixWord ++ tailWord_4696245) baseStart_4696245 baseEnd_4696245 := by
    simpa [prefixWord, tailWord_4696245, baseEnd_4696245] using wordTrace_append hprefix tailTrace_4696245
  have hstable : (prefixWord ++ tailWord_4696245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4696245).length < 2 ^ (prefixWord ++ tailWord_4696245).sum := by decide
  have hdescent : baseEnd_4696245 < baseStart_4696245 := by decide
  rcases family_descends (prefixWord ++ tailWord_4696245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4696281 : List Nat := [1, 2, 1, 2, 3, 1, 2, 5, 2, 2, 2]
def baseStart_4696281 : Nat := 118140960795 + 4696281 * 2 ^ 59
def prefixEnd_4696281 : Nat := 4983230072969 + 3 ^ 40 * 4696281 * 2
def baseEnd_4696281 : Nat := 2411449441577645512689703

theorem tailTrace_4696281 : CollatzResearch.WordTrace tailWord_4696281 prefixEnd_4696281 2411449441577645512689703 := by
  unfold tailWord_4696281
  simp only [CollatzResearch.WordTrace]
  refine ⟨171287439899183472784576697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114191626599455648523051131 171287439899183472784576697)
  ·
    refine ⟨128465579924387604588432523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171287439899183472784576697 128465579924387604588432523)
    ·
      refine ⟨192698369886581406882648785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128465579924387604588432523 192698369886581406882648785)
      ·
        refine ⟨144523777414936055161986589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 192698369886581406882648785 144523777414936055161986589)
        ·
          refine ⟨54196416530601020685744971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 144523777414936055161986589 54196416530601020685744971)
          ·
            refine ⟨81294624795901531028617457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54196416530601020685744971 81294624795901531028617457)
            ·
              refine ⟨60970968596926148271463093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81294624795901531028617457 60970968596926148271463093)
              ·
                refine ⟨5716028305961826400449665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 60970968596926148271463093 5716028305961826400449665)
                ·
                  refine ⟨4287021229471369800337249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5716028305961826400449665 4287021229471369800337249)
                  ·
                    refine ⟨3215265922103527350252937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4287021229471369800337249 3215265922103527350252937)
                    ·
                      refine ⟨2411449441577645512689703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3215265922103527350252937 2411449441577645512689703)
                      ·
                        rfl

theorem cell23_4696281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 5, 2, 2, 2].length) (baseStart_4696281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4696281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4696281 prefixEnd_4696281 := by exact prefixLift 4696281
  have htrace : WordTrace (prefixWord ++ tailWord_4696281) baseStart_4696281 baseEnd_4696281 := by
    simpa [prefixWord, tailWord_4696281, baseEnd_4696281] using wordTrace_append hprefix tailTrace_4696281
  have hstable : (prefixWord ++ tailWord_4696281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4696281).length < 2 ^ (prefixWord ++ tailWord_4696281).sum := by decide
  have hdescent : baseEnd_4696281 < baseStart_4696281 := by decide
  rcases family_descends (prefixWord ++ tailWord_4696281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4696321 : List Nat := [1, 2, 4, 1, 1, 2, 5, 2, 5]
def baseStart_4696321 : Nat := 118140960795 + 4696321 * 2 ^ 59
def prefixEnd_4696321 : Nat := 4983230072969 + 3 ^ 40 * 4696321 * 2
def baseEnd_4696321 : Nat := 267941108978202817354391

theorem tailTrace_4696321 : CollatzResearch.WordTrace tailWord_4696321 prefixEnd_4696321 267941108978202817354391 := by
  unfold tailWord_4696321
  simp only [CollatzResearch.WordTrace]
  refine ⟨171288898819038559616032817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114192599212692373077355211 171288898819038559616032817)
  ·
    refine ⟨128466674114278919712024613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171288898819038559616032817 128466674114278919712024613)
    ·
      refine ⟨24087501396427297446004615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 128466674114278919712024613 24087501396427297446004615)
      ·
        refine ⟨36131252094640946169006923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24087501396427297446004615 36131252094640946169006923)
        ·
          refine ⟨54196878141961419253510385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36131252094640946169006923 54196878141961419253510385)
          ·
            refine ⟨40647658606471064440132789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54196878141961419253510385 40647658606471064440132789)
            ·
              refine ⟨3810717994356662291262449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 40647658606471064440132789 3810717994356662291262449)
              ·
                refine ⟨2858038495767496718446837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3810717994356662291262449 2858038495767496718446837)
                ·
                  refine ⟨267941108978202817354391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2858038495767496718446837 267941108978202817354391)
                  ·
                    rfl

theorem cell23_4696321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 5, 2, 5].length) (baseStart_4696321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4696321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4696321 prefixEnd_4696321 := by exact prefixLift 4696321
  have htrace : WordTrace (prefixWord ++ tailWord_4696321) baseStart_4696321 baseEnd_4696321 := by
    simpa [prefixWord, tailWord_4696321, baseEnd_4696321] using wordTrace_append hprefix tailTrace_4696321
  have hstable : (prefixWord ++ tailWord_4696321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4696321).length < 2 ^ (prefixWord ++ tailWord_4696321).sum := by decide
  have hdescent : baseEnd_4696321 < baseStart_4696321 := by decide
  rcases family_descends (prefixWord ++ tailWord_4696321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4696417 : List Nat := [1, 2, 3, 1, 1, 1, 1, 1, 1, 6, 5]
def baseStart_4696417 : Nat := 118140960795 + 4696417 * 2 ^ 59
def prefixEnd_4696417 : Nat := 4983230072969 + 3 ^ 40 * 4696417 * 2
def baseEnd_4696417 : Nat := 2411519274946656980589077

theorem tailTrace_4696417 : CollatzResearch.WordTrace tailWord_4696417 prefixEnd_4696417 2411519274946656980589077 := by
  unfold tailWord_4696417
  simp only [CollatzResearch.WordTrace]
  refine ⟨171292400226690768011527505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114194933484460512007685003 171292400226690768011527505)
  ·
    refine ⟨128469300170018076008645629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171292400226690768011527505 128469300170018076008645629)
    ·
      refine ⟨48175987563756778503242111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 128469300170018076008645629 48175987563756778503242111)
      ·
        refine ⟨72263981345635167754863167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48175987563756778503242111 72263981345635167754863167)
        ·
          refine ⟨108395972018452751632294751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72263981345635167754863167 108395972018452751632294751)
          ·
            refine ⟨162593958027679127448442127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108395972018452751632294751 162593958027679127448442127)
            ·
              refine ⟨243890937041518691172663191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 162593958027679127448442127 243890937041518691172663191)
              ·
                refine ⟨365836405562278036758994787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 243890937041518691172663191 365836405562278036758994787)
                ·
                  refine ⟨548754608343417055138492181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 365836405562278036758994787 548754608343417055138492181)
                  ·
                    refine ⟨25722872266097674459616821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 548754608343417055138492181 25722872266097674459616821)
                    ·
                      refine ⟨2411519274946656980589077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25722872266097674459616821 2411519274946656980589077)
                      ·
                        rfl

theorem cell23_4696417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 6, 5].length) (baseStart_4696417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4696417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4696417 prefixEnd_4696417 := by exact prefixLift 4696417
  have htrace : WordTrace (prefixWord ++ tailWord_4696417) baseStart_4696417 baseEnd_4696417 := by
    simpa [prefixWord, tailWord_4696417, baseEnd_4696417] using wordTrace_append hprefix tailTrace_4696417
  have hstable : (prefixWord ++ tailWord_4696417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4696417).length < 2 ^ (prefixWord ++ tailWord_4696417).sum := by decide
  have hdescent : baseEnd_4696417 < baseStart_4696417 := by decide
  rcases family_descends (prefixWord ++ tailWord_4696417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4696428 : List Nat := [2, 2, 1, 1, 7, 1, 1, 2, 6]
def baseStart_4696428 : Nat := 118140960795 + 4696428 * 2 ^ 59
def prefixEnd_4696428 : Nat := 4983230072969 + 3 ^ 40 * 4696428 * 2
def baseEnd_4696428 : Nat := 267947213692650715283503

theorem tailTrace_4696428 : CollatzResearch.WordTrace tailWord_4696428 prefixEnd_4696428 267947213692650715283503 := by
  unfold tailWord_4696428
  simp only [CollatzResearch.WordTrace]
  refine ⟨85646400714825458445088969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114195200953100611260118625 85646400714825458445088969)
  ·
    refine ⟨64234800536119093833816727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85646400714825458445088969 64234800536119093833816727)
    ·
      refine ⟨96352200804178640750725091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64234800536119093833816727 96352200804178640750725091)
      ·
        refine ⟨144528301206267961126087637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96352200804178640750725091 144528301206267961126087637)
        ·
          refine ⟨3387382059521905338892679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 144528301206267961126087637 3387382059521905338892679)
          ·
            refine ⟨5081073089282858008339019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3387382059521905338892679 5081073089282858008339019)
            ·
              refine ⟨7621609633924287012508529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5081073089282858008339019 7621609633924287012508529)
              ·
                refine ⟨5716207225443215259381397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7621609633924287012508529 5716207225443215259381397)
                ·
                  refine ⟨267947213692650715283503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5716207225443215259381397 267947213692650715283503)
                  ·
                    rfl

theorem cell23_4696428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 1, 2, 6].length) (baseStart_4696428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4696428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4696428 prefixEnd_4696428 := by exact prefixLift 4696428
  have htrace : WordTrace (prefixWord ++ tailWord_4696428) baseStart_4696428 baseEnd_4696428 := by
    simpa [prefixWord, tailWord_4696428, baseEnd_4696428] using wordTrace_append hprefix tailTrace_4696428
  have hstable : (prefixWord ++ tailWord_4696428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4696428).length < 2 ^ (prefixWord ++ tailWord_4696428).sum := by decide
  have hdescent : baseEnd_4696428 < baseStart_4696428 := by decide
  rcases family_descends (prefixWord ++ tailWord_4696428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4696444 : List Nat := [2, 2, 2, 1, 1, 1, 2, 4, 3, 1, 4]
def baseStart_4696444 : Nat := 118140960795 + 4696444 * 2 ^ 59
def prefixEnd_4696444 : Nat := 4983230072969 + 3 ^ 40 * 4696444 * 2
def baseEnd_4696444 : Nat := 2411533138924328374951453

theorem tailTrace_4696444 : CollatzResearch.WordTrace tailWord_4696444 prefixEnd_4696444 2411533138924328374951453 := by
  unfold tailWord_4696444
  simp only [CollatzResearch.WordTrace]
  refine ⟨85646692498796475811380193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114195589998395301081840257 85646692498796475811380193)
  ·
    refine ⟨64235019374097356858535145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85646692498796475811380193 64235019374097356858535145)
    ·
      refine ⟨48176264530573017643901359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64235019374097356858535145 48176264530573017643901359)
      ·
        refine ⟨72264396795859526465852039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48176264530573017643901359 72264396795859526465852039)
        ·
          refine ⟨108396595193789289698778059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72264396795859526465852039 108396595193789289698778059)
          ·
            refine ⟨162594892790683934548167089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108396595193789289698778059 162594892790683934548167089)
            ·
              refine ⟨121946169593012950911125317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 162594892790683934548167089 121946169593012950911125317)
              ·
                refine ⟨22864906798689928295835997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 121946169593012950911125317 22864906798689928295835997)
                ·
                  refine ⟨8574340049508723110938499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22864906798689928295835997 8574340049508723110938499)
                  ·
                    refine ⟨12861510074263084666407749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8574340049508723110938499 12861510074263084666407749)
                    ·
                      refine ⟨2411533138924328374951453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12861510074263084666407749 2411533138924328374951453)
                      ·
                        rfl

theorem cell23_4696444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 4, 3, 1, 4].length) (baseStart_4696444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4696444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4696444 prefixEnd_4696444 := by exact prefixLift 4696444
  have htrace : WordTrace (prefixWord ++ tailWord_4696444) baseStart_4696444 baseEnd_4696444 := by
    simpa [prefixWord, tailWord_4696444, baseEnd_4696444] using wordTrace_append hprefix tailTrace_4696444
  have hstable : (prefixWord ++ tailWord_4696444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4696444).length < 2 ^ (prefixWord ++ tailWord_4696444).sum := by decide
  have hdescent : baseEnd_4696444 < baseStart_4696444 := by decide
  rcases family_descends (prefixWord ++ tailWord_4696444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4696472 : List Nat := [2, 1, 2, 5, 1, 3, 1, 3, 1, 1, 3]
def baseStart_4696472 : Nat := 118140960795 + 4696472 * 2 ^ 59
def prefixEnd_4696472 : Nat := 4983230072969 + 3 ^ 40 * 4696472 * 2
def baseEnd_4696472 : Nat := 2411547516382654265401325

theorem tailTrace_4696472 : CollatzResearch.WordTrace tailWord_4696472 prefixEnd_4696472 2411547516382654265401325 := by
  unfold tailWord_4696472
  simp only [CollatzResearch.WordTrace]
  refine ⟨85647203120745756202389835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114196270827661008269853113 85647203120745756202389835)
  ·
    refine ⟨128470804681118634303584753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85647203120745756202389835 128470804681118634303584753)
    ·
      refine ⟨96353103510838975727688565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128470804681118634303584753 96353103510838975727688565)
      ·
        refine ⟨9033103454141153974470803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 96353103510838975727688565 9033103454141153974470803)
        ·
          refine ⟨13549655181211730961706205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9033103454141153974470803 13549655181211730961706205)
          ·
            refine ⟨5081120692954399110639827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13549655181211730961706205 5081120692954399110639827)
            ·
              refine ⟨7621681039431598665959741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5081120692954399110639827 7621681039431598665959741)
              ·
                refine ⟨2858130389786849499734903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7621681039431598665959741 2858130389786849499734903)
                ·
                  refine ⟨4287195584680274249602355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2858130389786849499734903 4287195584680274249602355)
                  ·
                    refine ⟨6430793377020411374403533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4287195584680274249602355 6430793377020411374403533)
                    ·
                      refine ⟨2411547516382654265401325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6430793377020411374403533 2411547516382654265401325)
                      ·
                        rfl

theorem cell23_4696472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 1, 3, 1, 1, 3].length) (baseStart_4696472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4696472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4696472 prefixEnd_4696472 := by exact prefixLift 4696472
  have htrace : WordTrace (prefixWord ++ tailWord_4696472) baseStart_4696472 baseEnd_4696472 := by
    simpa [prefixWord, tailWord_4696472, baseEnd_4696472] using wordTrace_append hprefix tailTrace_4696472
  have hstable : (prefixWord ++ tailWord_4696472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4696472).length < 2 ^ (prefixWord ++ tailWord_4696472).sum := by decide
  have hdescent : baseEnd_4696472 < baseStart_4696472 := by decide
  rcases family_descends (prefixWord ++ tailWord_4696472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4696488 : List Nat := [2, 1, 6, 1, 1, 1, 2, 1, 4, 4]
def baseStart_4696488 : Nat := 118140960795 + 4696488 * 2 ^ 59
def prefixEnd_4696488 : Nat := 4983230072969 + 3 ^ 40 * 4696488 * 2
def baseEnd_4696488 : Nat := 803851910691042067600417

theorem tailTrace_4696488 : CollatzResearch.WordTrace tailWord_4696488 prefixEnd_4696488 803851910691042067600417 := by
  unfold tailWord_4696488
  simp only [CollatzResearch.WordTrace]
  refine ⟨85647494904716773568681059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114196659872955698091574745 85647494904716773568681059)
  ·
    refine ⟨128471242357075160353021589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85647494904716773568681059 128471242357075160353021589)
    ·
      refine ⟨6022089485487898141547887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 128471242357075160353021589 6022089485487898141547887)
      ·
        refine ⟨9033134228231847212321831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6022089485487898141547887 9033134228231847212321831)
        ·
          refine ⟨13549701342347770818482747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9033134228231847212321831 13549701342347770818482747)
          ·
            refine ⟨20324552013521656227724121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13549701342347770818482747 20324552013521656227724121)
            ·
              refine ⟨15243414010141242170793091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20324552013521656227724121 15243414010141242170793091)
              ·
                refine ⟨22865121015211863256189637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15243414010141242170793091 22865121015211863256189637)
                ·
                  refine ⟨4287210190352224360535557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22865121015211863256189637 4287210190352224360535557)
                  ·
                    refine ⟨803851910691042067600417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4287210190352224360535557 803851910691042067600417)
                    ·
                      rfl

theorem cell23_4696488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 1, 4, 4].length) (baseStart_4696488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4696488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4696488 prefixEnd_4696488 := by exact prefixLift 4696488
  have htrace : WordTrace (prefixWord ++ tailWord_4696488) baseStart_4696488 baseEnd_4696488 := by
    simpa [prefixWord, tailWord_4696488, baseEnd_4696488] using wordTrace_append hprefix tailTrace_4696488
  have hstable : (prefixWord ++ tailWord_4696488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4696488).length < 2 ^ (prefixWord ++ tailWord_4696488).sum := by decide
  have hdescent : baseEnd_4696488 < baseStart_4696488 := by decide
  rcases family_descends (prefixWord ++ tailWord_4696488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4696501 : List Nat := [1, 3, 3, 2, 3, 1, 2, 8]
def baseStart_4696501 : Nat := 118140960795 + 4696501 * 2 ^ 59
def prefixEnd_4696501 : Nat := 4983230072969 + 3 ^ 40 * 4696501 * 2
def baseEnd_4696501 : Nat := 89317126197097579701433

theorem tailTrace_4696501 : CollatzResearch.WordTrace tailWord_4696501 prefixEnd_4696501 89317126197097579701433 := by
  unfold tailWord_4696501
  simp only [CollatzResearch.WordTrace]
  refine ⟨171295463958386450357585357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114196975972257633571723571 171295463958386450357585357)
  ·
    refine ⟨64235798984394918884094509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 171295463958386450357585357 64235798984394918884094509)
    ·
      refine ⟨24088424619148094581535441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64235798984394918884094509 24088424619148094581535441)
      ·
        refine ⟨18066318464361070936151581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24088424619148094581535441 18066318464361070936151581)
        ·
          refine ⟨6774869424135401601056843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18066318464361070936151581 6774869424135401601056843)
          ·
            refine ⟨10162304136203102401585265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6774869424135401601056843 10162304136203102401585265)
            ·
              refine ⟨7621728102152326801188949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10162304136203102401585265 7621728102152326801188949)
              ·
                refine ⟨89317126197097579701433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7621728102152326801188949 89317126197097579701433)
                ·
                  rfl

theorem cell23_4696501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 2, 8].length) (baseStart_4696501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4696501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4696501 prefixEnd_4696501 := by exact prefixLift 4696501
  have htrace : WordTrace (prefixWord ++ tailWord_4696501) baseStart_4696501 baseEnd_4696501 := by
    simpa [prefixWord, tailWord_4696501, baseEnd_4696501] using wordTrace_append hprefix tailTrace_4696501
  have hstable : (prefixWord ++ tailWord_4696501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4696501).length < 2 ^ (prefixWord ++ tailWord_4696501).sum := by decide
  have hdescent : baseEnd_4696501 < baseStart_4696501 := by decide
  rcases family_descends (prefixWord ++ tailWord_4696501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4696505 : List Nat := [1, 2, 1, 4, 3, 3, 2, 1, 2, 4]
def baseStart_4696505 : Nat := 118140960795 + 4696505 * 2 ^ 59
def prefixEnd_4696505 : Nat := 4983230072969 + 3 ^ 40 * 4696505 * 2
def baseEnd_4696505 : Nat := 803854820414750878762891

theorem tailTrace_4696505 : CollatzResearch.WordTrace tailWord_4696505 prefixEnd_4696505 803854820414750878762891 := by
  unfold tailWord_4696505
  simp only [CollatzResearch.WordTrace]
  refine ⟨171295609850371959040730969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114197073233581306027153979 171295609850371959040730969)
  ·
    refine ⟨128471707387778969280548227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171295609850371959040730969 128471707387778969280548227)
    ·
      refine ⟨192707561081668453920822341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128471707387778969280548227 192707561081668453920822341)
      ·
        refine ⟨36132667702812835110154189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 192707561081668453920822341 36132667702812835110154189)
        ·
          refine ⟨13549750388554813166307821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36132667702812835110154189 13549750388554813166307821)
          ·
            refine ⟨5081156395708054937365433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13549750388554813166307821 5081156395708054937365433)
            ·
              refine ⟨3810867296781041203024075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5081156395708054937365433 3810867296781041203024075)
              ·
                refine ⟨5716300945171561804536113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3810867296781041203024075 5716300945171561804536113)
                ·
                  refine ⟨4287225708878671353402085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5716300945171561804536113 4287225708878671353402085)
                  ·
                    refine ⟨803854820414750878762891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4287225708878671353402085 803854820414750878762891)
                    ·
                      rfl

theorem cell23_4696505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 2, 1, 2, 4].length) (baseStart_4696505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4696505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4696505 prefixEnd_4696505 := by exact prefixLift 4696505
  have htrace : WordTrace (prefixWord ++ tailWord_4696505) baseStart_4696505 baseEnd_4696505 := by
    simpa [prefixWord, tailWord_4696505, baseEnd_4696505] using wordTrace_append hprefix tailTrace_4696505
  have hstable : (prefixWord ++ tailWord_4696505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4696505).length < 2 ^ (prefixWord ++ tailWord_4696505).sum := by decide
  have hdescent : baseEnd_4696505 < baseStart_4696505 := by decide
  rcases family_descends (prefixWord ++ tailWord_4696505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4696544 : List Nat := [2, 1, 1, 3, 1, 1, 4, 2, 2, 6]
def baseStart_4696544 : Nat := 118140960795 + 4696544 * 2 ^ 59
def prefixEnd_4696544 : Nat := 4983230072969 + 3 ^ 40 * 4696544 * 2
def baseEnd_4696544 : Nat := 803861495663259327900331

theorem tailTrace_4696544 : CollatzResearch.WordTrace tailWord_4696544 prefixEnd_4696544 803861495663259327900331 := by
  unfold tailWord_4696544
  simp only [CollatzResearch.WordTrace]
  refine ⟨85648516148615334350700343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114198021531487112467600457 85648516148615334350700343)
  ·
    refine ⟨128472774222923001526050515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85648516148615334350700343 128472774222923001526050515)
    ·
      refine ⟨192709161334384502289075773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128472774222923001526050515 192709161334384502289075773)
      ·
        refine ⟨72265935500394188358403415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 192709161334384502289075773 72265935500394188358403415)
        ·
          refine ⟨108398903250591282537605123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72265935500394188358403415 108398903250591282537605123)
          ·
            refine ⟨162598354875886923806407685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108398903250591282537605123 162598354875886923806407685)
            ·
              refine ⟨30487191539228798213701441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 162598354875886923806407685 30487191539228798213701441)
              ·
                refine ⟨22865393654421598660276081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30487191539228798213701441 22865393654421598660276081)
                ·
                  refine ⟨17149045240816198995207061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22865393654421598660276081 17149045240816198995207061)
                  ·
                    refine ⟨803861495663259327900331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17149045240816198995207061 803861495663259327900331)
                    ·
                      rfl

theorem cell23_4696544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 2, 2, 6].length) (baseStart_4696544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4696544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4696544 prefixEnd_4696544 := by exact prefixLift 4696544
  have htrace : WordTrace (prefixWord ++ tailWord_4696544) baseStart_4696544 baseEnd_4696544 := by
    simpa [prefixWord, tailWord_4696544, baseEnd_4696544] using wordTrace_append hprefix tailTrace_4696544
  have hstable : (prefixWord ++ tailWord_4696544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4696544).length < 2 ^ (prefixWord ++ tailWord_4696544).sum := by decide
  have hdescent : baseEnd_4696544 < baseStart_4696544 := by decide
  rcases family_descends (prefixWord ++ tailWord_4696544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4696546 : List Nat := [3, 3, 3, 2, 1, 1, 1, 4, 1, 2, 2]
def baseStart_4696546 : Nat := 118140960795 + 4696546 * 2 ^ 59
def prefixEnd_4696546 : Nat := 4983230072969 + 3 ^ 40 * 4696546 * 2
def baseEnd_4696546 : Nat := 2411585513951086975875985

theorem tailTrace_4696546 : CollatzResearch.WordTrace tailWord_4696546 prefixEnd_4696546 2411585513951086975875985 := by
  unfold tailWord_4696546
  simp only [CollatzResearch.WordTrace]
  refine ⟨42824276310805855760743373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114198070162148948695315661 42824276310805855760743373)
  ·
    refine ⟨16059103616552195910278765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42824276310805855760743373 16059103616552195910278765)
    ·
      refine ⟨6022163856207073466354537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16059103616552195910278765 6022163856207073466354537)
      ·
        refine ⟨4516622892155305099765903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6022163856207073466354537 4516622892155305099765903)
        ·
          refine ⟨6774934338232957649648855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4516622892155305099765903 6774934338232957649648855)
          ·
            refine ⟨10162401507349436474473283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6774934338232957649648855 10162401507349436474473283)
            ·
              refine ⟨15243602261024154711709925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10162401507349436474473283 15243602261024154711709925)
              ·
                refine ⟨2858175423942029008445611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15243602261024154711709925 2858175423942029008445611)
                ·
                  refine ⟨4287263135913043512668417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2858175423942029008445611 4287263135913043512668417)
                  ·
                    refine ⟨3215447351934782634501313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4287263135913043512668417 3215447351934782634501313)
                    ·
                      refine ⟨2411585513951086975875985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3215447351934782634501313 2411585513951086975875985)
                      ·
                        rfl

theorem cell23_4696546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 4, 1, 2, 2].length) (baseStart_4696546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4696546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4696546 prefixEnd_4696546 := by exact prefixLift 4696546
  have htrace : WordTrace (prefixWord ++ tailWord_4696546) baseStart_4696546 baseEnd_4696546 := by
    simpa [prefixWord, tailWord_4696546, baseEnd_4696546] using wordTrace_append hprefix tailTrace_4696546
  have hstable : (prefixWord ++ tailWord_4696546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4696546).length < 2 ^ (prefixWord ++ tailWord_4696546).sum := by decide
  have hdescent : baseEnd_4696546 < baseStart_4696546 := by decide
  rcases family_descends (prefixWord ++ tailWord_4696546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4696568 : List Nat := [2, 1, 2, 1, 1, 4, 4, 1, 1, 4, 2]
def baseStart_4696568 : Nat := 118140960795 + 4696568 * 2 ^ 59
def prefixEnd_4696568 : Nat := 4983230072969 + 3 ^ 40 * 4696568 * 2
def baseEnd_4696568 : Nat := 2411596810525485889800883

theorem tailTrace_4696568 : CollatzResearch.WordTrace tailWord_4696568 prefixEnd_4696568 2411596810525485889800883 := by
  unfold tailWord_4696568
  simp only [CollatzResearch.WordTrace]
  refine ⟨85648953824571860400137179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114198605099429147200182905 85648953824571860400137179)
  ·
    refine ⟨128473430736857790600205769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85648953824571860400137179 128473430736857790600205769)
    ·
      refine ⟨96355073052643342950154327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128473430736857790600205769 96355073052643342950154327)
      ·
        refine ⟨144532609578965014425231491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96355073052643342950154327 144532609578965014425231491)
        ·
          refine ⟨216798914368447521637847237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144532609578965014425231491 216798914368447521637847237)
          ·
            refine ⟨40649796444083910307096357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 216798914368447521637847237 40649796444083910307096357)
            ·
              refine ⟨7621836833265733182580567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40649796444083910307096357 7621836833265733182580567)
              ·
                refine ⟨11432755249898599773870851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7621836833265733182580567 11432755249898599773870851)
                ·
                  refine ⟨17149132874847899660806277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11432755249898599773870851 17149132874847899660806277)
                  ·
                    refine ⟨3215462414033981186401177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17149132874847899660806277 3215462414033981186401177)
                    ·
                      refine ⟨2411596810525485889800883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3215462414033981186401177 2411596810525485889800883)
                      ·
                        rfl

theorem cell23_4696568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 4, 1, 1, 4, 2].length) (baseStart_4696568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4696568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4696568 prefixEnd_4696568 := by exact prefixLift 4696568
  have htrace : WordTrace (prefixWord ++ tailWord_4696568) baseStart_4696568 baseEnd_4696568 := by
    simpa [prefixWord, tailWord_4696568, baseEnd_4696568] using wordTrace_append hprefix tailTrace_4696568
  have hstable : (prefixWord ++ tailWord_4696568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4696568).length < 2 ^ (prefixWord ++ tailWord_4696568).sum := by decide
  have hdescent : baseEnd_4696568 < baseStart_4696568 := by decide
  rcases family_descends (prefixWord ++ tailWord_4696568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4696584 : List Nat := [2, 1, 3, 2, 1, 1, 1, 2, 1, 2, 7]
def baseStart_4696584 : Nat := 118140960795 + 4696584 * 2 ^ 59
def prefixEnd_4696584 : Nat := 4983230072969 + 3 ^ 40 * 4696584 * 2
def baseEnd_4696584 : Nat := 2411605026215957827200809

theorem tailTrace_4696584 : CollatzResearch.WordTrace tailWord_4696584 prefixEnd_4696584 2411605026215957827200809 := by
  unfold tailWord_4696584
  simp only [CollatzResearch.WordTrace]
  refine ⟨85649245608542877766428403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114198994144723837021904537 85649245608542877766428403)
  ·
    refine ⟨128473868412814316649642605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85649245608542877766428403 128473868412814316649642605)
    ·
      refine ⟨48177700654805368743615977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 128473868412814316649642605 48177700654805368743615977)
      ·
        refine ⟨36133275491104026557711983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48177700654805368743615977 36133275491104026557711983)
        ·
          refine ⟨54199913236656039836567975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36133275491104026557711983 54199913236656039836567975)
          ·
            refine ⟨81299869854984059754851963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54199913236656039836567975 81299869854984059754851963)
            ·
              refine ⟨121949804782476089632277945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81299869854984059754851963 121949804782476089632277945)
              ·
                refine ⟨91462353586857067224208459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 121949804782476089632277945 91462353586857067224208459)
                ·
                  refine ⟨137193530380285600836312689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 91462353586857067224208459 137193530380285600836312689)
                  ·
                    refine ⟨102895147785214200627234517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 137193530380285600836312689 102895147785214200627234517)
                    ·
                      refine ⟨2411605026215957827200809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 102895147785214200627234517 2411605026215957827200809)
                      ·
                        rfl

theorem cell23_4696584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 2, 1, 2, 7].length) (baseStart_4696584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4696584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4696584 prefixEnd_4696584 := by exact prefixLift 4696584
  have htrace : WordTrace (prefixWord ++ tailWord_4696584) baseStart_4696584 baseEnd_4696584 := by
    simpa [prefixWord, tailWord_4696584, baseEnd_4696584] using wordTrace_append hprefix tailTrace_4696584
  have hstable : (prefixWord ++ tailWord_4696584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4696584).length < 2 ^ (prefixWord ++ tailWord_4696584).sum := by decide
  have hdescent : baseEnd_4696584 < baseStart_4696584 := by decide
  rcases family_descends (prefixWord ++ tailWord_4696584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4696589 : List Nat := [1, 7, 1, 1, 1, 2, 1, 3, 1, 3, 2]
def baseStart_4696589 : Nat := 118140960795 + 4696589 * 2 ^ 59
def prefixEnd_4696589 : Nat := 4983230072969 + 3 ^ 40 * 4696589 * 2
def baseEnd_4696589 : Nat := 2411607593619230307638287

theorem tailTrace_4696589 : CollatzResearch.WordTrace tailWord_4696589 prefixEnd_4696589 2411607593619230307638287 := by
  unfold tailWord_4696589
  simp only [CollatzResearch.WordTrace]
  refine ⟨171298673582067641386788821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114199115721378427591192547 171298673582067641386788821)
  ·
    refine ⟨4014812662079710345002863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 171298673582067641386788821 4014812662079710345002863)
    ·
      refine ⟨6022218993119565517504295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4014812662079710345002863 6022218993119565517504295)
      ·
        refine ⟨9033328489679348276256443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6022218993119565517504295 9033328489679348276256443)
        ·
          refine ⟨13549992734519022414384665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9033328489679348276256443 13549992734519022414384665)
          ·
            refine ⟨10162494550889266810788499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13549992734519022414384665 10162494550889266810788499)
            ·
              refine ⟨15243741826333900216182749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10162494550889266810788499 15243741826333900216182749)
              ·
                refine ⟨5716403184875212581068531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15243741826333900216182749 5716403184875212581068531)
                ·
                  refine ⟨8574604777312818871602797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5716403184875212581068531 8574604777312818871602797)
                  ·
                    refine ⟨3215476791492307076851049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8574604777312818871602797 3215476791492307076851049)
                    ·
                      refine ⟨2411607593619230307638287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3215476791492307076851049 2411607593619230307638287)
                      ·
                        rfl

theorem cell23_4696589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 3, 1, 3, 2].length) (baseStart_4696589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4696589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4696589 prefixEnd_4696589 := by exact prefixLift 4696589
  have htrace : WordTrace (prefixWord ++ tailWord_4696589) baseStart_4696589 baseEnd_4696589 := by
    simpa [prefixWord, tailWord_4696589, baseEnd_4696589] using wordTrace_append hprefix tailTrace_4696589
  have hstable : (prefixWord ++ tailWord_4696589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4696589).length < 2 ^ (prefixWord ++ tailWord_4696589).sum := by decide
  have hdescent : baseEnd_4696589 < baseStart_4696589 := by decide
  rcases family_descends (prefixWord ++ tailWord_4696589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4696591 : List Nat := [1, 1, 2, 1, 1, 1, 2, 9, 5]
def baseStart_4696591 : Nat := 118140960795 + 4696591 * 2 ^ 59
def prefixEnd_4696591 : Nat := 4983230072969 + 3 ^ 40 * 4696591 * 2
def baseEnd_4696591 : Nat := 267956513397837699979253

theorem tailTrace_4696591 : CollatzResearch.WordTrace tailWord_4696591 prefixEnd_4696591 267956513397837699979253 := by
  unfold tailWord_4696591
  simp only [CollatzResearch.WordTrace]
  refine ⟨171298746528060395728361627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114199164352040263818907751 171298746528060395728361627)
  ·
    refine ⟨256948119792090593592542441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171298746528060395728361627 256948119792090593592542441)
    ·
      refine ⟨192711089844067945194406831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 256948119792090593592542441 192711089844067945194406831)
      ·
        refine ⟨289066634766101917791610247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192711089844067945194406831 289066634766101917791610247)
        ·
          refine ⟨433599952149152876687415371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 289066634766101917791610247 433599952149152876687415371)
          ·
            refine ⟨650399928223729315031123057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 433599952149152876687415371 650399928223729315031123057)
            ·
              refine ⟨487799946167796986273342293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 650399928223729315031123057 487799946167796986273342293)
              ·
                refine ⟨2858202809576935466445365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 487799946167796986273342293 2858202809576935466445365)
                ·
                  refine ⟨267956513397837699979253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2858202809576935466445365 267956513397837699979253)
                  ·
                    rfl

theorem cell23_4696591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 9, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 9, 5].length) (baseStart_4696591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4696591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4696591 prefixEnd_4696591 := by exact prefixLift 4696591
  have htrace : WordTrace (prefixWord ++ tailWord_4696591) baseStart_4696591 baseEnd_4696591 := by
    simpa [prefixWord, tailWord_4696591, baseEnd_4696591] using wordTrace_append hprefix tailTrace_4696591
  have hstable : (prefixWord ++ tailWord_4696591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4696591).length < 2 ^ (prefixWord ++ tailWord_4696591).sum := by decide
  have hdescent : baseEnd_4696591 < baseStart_4696591 := by decide
  rcases family_descends (prefixWord ++ tailWord_4696591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4696608 : List Nat := [2, 1, 1, 6, 2, 1, 2, 1, 7]
def baseStart_4696608 : Nat := 118140960795 + 4696608 * 2 ^ 59
def prefixEnd_4696608 : Nat := 4983230072969 + 3 ^ 40 * 4696608 * 2
def baseEnd_4696608 : Nat := 267957483305740637033411

theorem tailTrace_4696608 : CollatzResearch.WordTrace tailWord_4696608 prefixEnd_4696608 267957483305740637033411 := by
  unfold tailWord_4696608
  simp only [CollatzResearch.WordTrace]
  refine ⟨85649683284499403815865239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114199577712665871754486985 85649683284499403815865239)
  ·
    refine ⟨128474524926749105723797859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85649683284499403815865239 128474524926749105723797859)
    ·
      refine ⟨192711787390123658585696789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128474524926749105723797859 192711787390123658585696789)
      ·
        refine ⟨9033365033912046496204537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 192711787390123658585696789 9033365033912046496204537)
        ·
          refine ⟨6775023775434034872153403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9033365033912046496204537 6775023775434034872153403)
          ·
            refine ⟨10162535663151052308230105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6775023775434034872153403 10162535663151052308230105)
            ·
              refine ⟨7621901747363289231172579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10162535663151052308230105 7621901747363289231172579)
              ·
                refine ⟨11432852621044933846758869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7621901747363289231172579 11432852621044933846758869)
                ·
                  refine ⟨267957483305740637033411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11432852621044933846758869 267957483305740637033411)
                  ·
                    rfl

theorem cell23_4696608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 2, 1, 7].length) (baseStart_4696608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4696608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4696608 prefixEnd_4696608 := by exact prefixLift 4696608
  have htrace : WordTrace (prefixWord ++ tailWord_4696608) baseStart_4696608 baseEnd_4696608 := by
    simpa [prefixWord, tailWord_4696608, baseEnd_4696608] using wordTrace_append hprefix tailTrace_4696608
  have hstable : (prefixWord ++ tailWord_4696608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4696608).length < 2 ^ (prefixWord ++ tailWord_4696608).sum := by decide
  have hdescent : baseEnd_4696608 < baseStart_4696608 := by decide
  rcases family_descends (prefixWord ++ tailWord_4696608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4696618 : List Nat := [3, 1, 4, 1, 1, 2, 2, 1, 2, 3, 3]
def baseStart_4696618 : Nat := 118140960795 + 4696618 * 2 ^ 59
def prefixEnd_4696618 : Nat := 4983230072969 + 3 ^ 40 * 4696618 * 2
def baseEnd_4696618 : Nat := 2411622484558210694175653

theorem tailTrace_4696618 : CollatzResearch.WordTrace tailWord_4696618 prefixEnd_4696618 2411622484558210694175653 := by
  unfold tailWord_4696618
  simp only [CollatzResearch.WordTrace]
  refine ⟨42824932824740644834898627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114199820865975052893063005 42824932824740644834898627)
  ·
    refine ⟨64237399237110967252347941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42824932824740644834898627 64237399237110967252347941)
    ·
      refine ⟨12044512356958306359815239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64237399237110967252347941 12044512356958306359815239)
      ·
        refine ⟨18066768535437459539722859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12044512356958306359815239 18066768535437459539722859)
        ·
          refine ⟨27100152803156189309584289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18066768535437459539722859 27100152803156189309584289)
          ·
            refine ⟨20325114602367141982188217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27100152803156189309584289 20325114602367141982188217)
            ·
              refine ⟨15243835951775356486641163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20325114602367141982188217 15243835951775356486641163)
              ·
                refine ⟨22865753927663034729961745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15243835951775356486641163 22865753927663034729961745)
                ·
                  refine ⟨17149315445747276047471309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22865753927663034729961745 17149315445747276047471309)
                  ·
                    refine ⟨6430993292155228517801741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17149315445747276047471309 6430993292155228517801741)
                    ·
                      refine ⟨2411622484558210694175653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6430993292155228517801741 2411622484558210694175653)
                      ·
                        rfl

theorem cell23_4696618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 1, 2, 3, 3].length) (baseStart_4696618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4696618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4696618 prefixEnd_4696618 := by exact prefixLift 4696618
  have htrace : WordTrace (prefixWord ++ tailWord_4696618) baseStart_4696618 baseEnd_4696618 := by
    simpa [prefixWord, tailWord_4696618, baseEnd_4696618] using wordTrace_append hprefix tailTrace_4696618
  have hstable : (prefixWord ++ tailWord_4696618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4696618).length < 2 ^ (prefixWord ++ tailWord_4696618).sum := by decide
  have hdescent : baseEnd_4696618 < baseStart_4696618 := by decide
  rcases family_descends (prefixWord ++ tailWord_4696618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4696651 : List Nat := [1, 1, 1, 1, 3, 1, 4, 2, 5, 4]
def baseStart_4696651 : Nat := 118140960795 + 4696651 * 2 ^ 59
def prefixEnd_4696651 : Nat := 4983230072969 + 3 ^ 40 * 4696651 * 2
def baseEnd_4696651 : Nat := 803879809806603021687667

theorem tailTrace_4696651 : CollatzResearch.WordTrace tailWord_4696651 prefixEnd_4696651 803879809806603021687667 := by
  unfold tailWord_4696651
  simp only [CollatzResearch.WordTrace]
  refine ⟨171300934907843025975545807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114200623271895350650363871 171300934907843025975545807)
  ·
    refine ⟨256951402361764538963318711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171300934907843025975545807 256951402361764538963318711)
    ·
      refine ⟨385427103542646808444978067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 256951402361764538963318711 385427103542646808444978067)
      ·
        refine ⟨578140655313970212667467101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 385427103542646808444978067 578140655313970212667467101)
        ·
          refine ⟨216802745742738829750300163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 578140655313970212667467101 216802745742738829750300163)
          ·
            refine ⟨325204118614108244625450245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 216802745742738829750300163 325204118614108244625450245)
            ·
              refine ⟨60975772240145295867271921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 325204118614108244625450245 60975772240145295867271921)
              ·
                refine ⟨45731829180108971900453941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60975772240145295867271921 45731829180108971900453941)
                ·
                  refine ⟨4287358985635216115667557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 45731829180108971900453941 4287358985635216115667557)
                  ·
                    refine ⟨803879809806603021687667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4287358985635216115667557 803879809806603021687667)
                    ·
                      rfl

theorem cell23_4696651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 2, 5, 4].length) (baseStart_4696651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4696651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4696651 prefixEnd_4696651 := by exact prefixLift 4696651
  have htrace : WordTrace (prefixWord ++ tailWord_4696651) baseStart_4696651 baseEnd_4696651 := by
    simpa [prefixWord, tailWord_4696651, baseEnd_4696651] using wordTrace_append hprefix tailTrace_4696651
  have hstable : (prefixWord ++ tailWord_4696651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4696651).length < 2 ^ (prefixWord ++ tailWord_4696651).sum := by decide
  have hdescent : baseEnd_4696651 < baseStart_4696651 := by decide
  rcases family_descends (prefixWord ++ tailWord_4696651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4696658 : List Nat := [3, 2, 2, 1, 2, 1, 3, 2, 2, 1, 4]
def baseStart_4696658 : Nat := 118140960795 + 4696658 * 2 ^ 59
def prefixEnd_4696658 : Nat := 4983230072969 + 3 ^ 40 * 4696658 * 2
def baseEnd_4696658 : Nat := 2411643023784390537675469

theorem tailTrace_4696658 : CollatzResearch.WordTrace tailWord_4696658 prefixEnd_4696658 2411643023784390537675469 := by
  unfold tailWord_4696658
  simp only [CollatzResearch.WordTrace]
  refine ⟨42825297554704416542762657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114200793479211777447367085 42825297554704416542762657)
  ·
    refine ⟨32118973166028312407071993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42825297554704416542762657 32118973166028312407071993)
    ·
      refine ⟨24089229874521234305303995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32118973166028312407071993 24089229874521234305303995)
      ·
        refine ⟨36133844811781851457955993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24089229874521234305303995 36133844811781851457955993)
        ·
          refine ⟨27100383608836388593466995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36133844811781851457955993 27100383608836388593466995)
          ·
            refine ⟨40650575413254582890200493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27100383608836388593466995 40650575413254582890200493)
            ·
              refine ⟨15243965779970468583825185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40650575413254582890200493 15243965779970468583825185)
              ·
                refine ⟨11432974334977851437868889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15243965779970468583825185 11432974334977851437868889)
                ·
                  refine ⟨8574730751233388578401667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11432974334977851437868889 8574730751233388578401667)
                  ·
                    refine ⟨12862096126850082867602501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8574730751233388578401667 12862096126850082867602501)
                    ·
                      refine ⟨2411643023784390537675469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12862096126850082867602501 2411643023784390537675469)
                      ·
                        rfl

theorem cell23_4696658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 2, 2, 1, 4].length) (baseStart_4696658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4696658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4696658 prefixEnd_4696658 := by exact prefixLift 4696658
  have htrace : WordTrace (prefixWord ++ tailWord_4696658) baseStart_4696658 baseEnd_4696658 := by
    simpa [prefixWord, tailWord_4696658, baseEnd_4696658] using wordTrace_append hprefix tailTrace_4696658
  have hstable : (prefixWord ++ tailWord_4696658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4696658).length < 2 ^ (prefixWord ++ tailWord_4696658).sum := by decide
  have hdescent : baseEnd_4696658 < baseStart_4696658 := by decide
  rcases family_descends (prefixWord ++ tailWord_4696658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4696670 : List Nat := [4, 4, 1, 2, 1, 2, 2, 1, 2, 2, 2]
def baseStart_4696670 : Nat := 118140960795 + 4696670 * 2 ^ 59
def prefixEnd_4696670 : Nat := 4983230072969 + 3 ^ 40 * 4696670 * 2
def baseEnd_4696670 : Nat := 2411649185552244490725415

theorem tailTrace_4696670 : CollatzResearch.WordTrace tailWord_4696670 prefixEnd_4696670 2411649185552244490725415 := by
  unfold tailWord_4696670
  simp only [CollatzResearch.WordTrace]
  refine ⟨21412703486846774027560933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 114201085263182794813658309 21412703486846774027560933)
  ·
    refine ⟨4014881903783770130167675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21412703486846774027560933 4014881903783770130167675)
    ·
      refine ⟨6022322855675655195251513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4014881903783770130167675 6022322855675655195251513)
      ·
        refine ⟨4516742141756741396438635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6022322855675655195251513 4516742141756741396438635)
        ·
          refine ⟨6775113212635112094657953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4516742141756741396438635 6775113212635112094657953)
          ·
            refine ⟨5081334909476334070993465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6775113212635112094657953 5081334909476334070993465)
            ·
              refine ⟨3811001182107250553245099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5081334909476334070993465 3811001182107250553245099)
              ·
                refine ⟨5716501773160875829867649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3811001182107250553245099 5716501773160875829867649)
                ·
                  refine ⟨4287376329870656872400737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5716501773160875829867649 4287376329870656872400737)
                  ·
                    refine ⟨3215532247402992654300553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4287376329870656872400737 3215532247402992654300553)
                    ·
                      refine ⟨2411649185552244490725415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3215532247402992654300553 2411649185552244490725415)
                      ·
                        rfl

theorem cell23_4696670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 2, 1, 2, 2, 2].length) (baseStart_4696670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4696670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4696670 prefixEnd_4696670 := by exact prefixLift 4696670
  have htrace : WordTrace (prefixWord ++ tailWord_4696670) baseStart_4696670 baseEnd_4696670 := by
    simpa [prefixWord, tailWord_4696670, baseEnd_4696670] using wordTrace_append hprefix tailTrace_4696670
  have hstable : (prefixWord ++ tailWord_4696670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4696670).length < 2 ^ (prefixWord ++ tailWord_4696670).sum := by decide
  have hdescent : baseEnd_4696670 < baseStart_4696670 := by decide
  rcases family_descends (prefixWord ++ tailWord_4696670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4696746 : List Nat := [3, 1, 5, 2, 2, 1, 1, 1, 2, 2, 3]
def baseStart_4696746 : Nat := 118140960795 + 4696746 * 2 ^ 59
def prefixEnd_4696746 : Nat := 4983230072969 + 3 ^ 40 * 4696746 * 2
def baseEnd_4696746 : Nat := 2411688210081986193375065

theorem tailTrace_4696746 : CollatzResearch.WordTrace tailWord_4696746 prefixEnd_4696746 2411688210081986193375065 := by
  unfold tailWord_4696746
  simp only [CollatzResearch.WordTrace]
  refine ⟨42826099960624714300063523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114202933228332571466836061 42826099960624714300063523)
  ·
    refine ⟨64239149940937071450095285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42826099960624714300063523 64239149940937071450095285)
    ·
      refine ⟨6022420306962850448446433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 64239149940937071450095285 6022420306962850448446433)
      ·
        refine ⟨4516815230222137836334825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6022420306962850448446433 4516815230222137836334825)
        ·
          refine ⟨3387611422666603377251119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4516815230222137836334825 3387611422666603377251119)
          ·
            refine ⟨5081417133999905065876679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3387611422666603377251119 5081417133999905065876679)
            ·
              refine ⟨7622125700999857598815019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5081417133999905065876679 7622125700999857598815019)
              ·
                refine ⟨11433188551499786398222529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7622125700999857598815019 11433188551499786398222529)
                ·
                  refine ⟨8574891413624839798666897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11433188551499786398222529 8574891413624839798666897)
                  ·
                    refine ⟨6431168560218629849000173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8574891413624839798666897 6431168560218629849000173)
                    ·
                      refine ⟨2411688210081986193375065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6431168560218629849000173 2411688210081986193375065)
                      ·
                        rfl

theorem cell23_4696746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 1, 1, 2, 2, 3].length) (baseStart_4696746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4696746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4696746 prefixEnd_4696746 := by exact prefixLift 4696746
  have htrace : WordTrace (prefixWord ++ tailWord_4696746) baseStart_4696746 baseEnd_4696746 := by
    simpa [prefixWord, tailWord_4696746, baseEnd_4696746] using wordTrace_append hprefix tailTrace_4696746
  have hstable : (prefixWord ++ tailWord_4696746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4696746).length < 2 ^ (prefixWord ++ tailWord_4696746).sum := by decide
  have hdescent : baseEnd_4696746 < baseStart_4696746 := by decide
  rcases family_descends (prefixWord ++ tailWord_4696746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4696759 : List Nat := [1, 1, 3, 1, 6, 1, 2, 3, 1, 1, 3]
def baseStart_4696759 : Nat := 118140960795 + 4696759 * 2 ^ 59
def prefixEnd_4696759 : Nat := 4983230072969 + 3 ^ 40 * 4696759 * 2
def baseEnd_4696759 : Nat := 2411694885330494642512505

theorem tailTrace_4696759 : CollatzResearch.WordTrace tailWord_4696759 prefixEnd_4696759 2411694885330494642512505 := by
  unfold tailWord_4696759
  simp only [CollatzResearch.WordTrace]
  refine ⟨171304873991451760420477331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114203249327634506946984887 171304873991451760420477331)
  ·
    refine ⟨256957310987177640630715997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171304873991451760420477331 256957310987177640630715997)
    ·
      refine ⟨96358991620191615236518499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 256957310987177640630715997 96358991620191615236518499)
      ·
        refine ⟨144538487430287422854777749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96358991620191615236518499 144538487430287422854777749)
        ·
          refine ⟨6775241598294722946317707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 144538487430287422854777749 6775241598294722946317707)
          ·
            refine ⟨10162862397442084419476561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6775241598294722946317707 10162862397442084419476561)
            ·
              refine ⟨7622146798081563314607421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10162862397442084419476561 7622146798081563314607421)
              ·
                refine ⟨2858305049280586242977783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7622146798081563314607421 2858305049280586242977783)
                ·
                  refine ⟨4287457573920879364466675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2858305049280586242977783 4287457573920879364466675)
                  ·
                    refine ⟨6431186360881319046700013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4287457573920879364466675 6431186360881319046700013)
                    ·
                      refine ⟨2411694885330494642512505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6431186360881319046700013 2411694885330494642512505)
                      ·
                        rfl

theorem cell23_4696759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 2, 3, 1, 1, 3].length) (baseStart_4696759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4696759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4696759 prefixEnd_4696759 := by exact prefixLift 4696759
  have htrace : WordTrace (prefixWord ++ tailWord_4696759) baseStart_4696759 baseEnd_4696759 := by
    simpa [prefixWord, tailWord_4696759, baseEnd_4696759] using wordTrace_append hprefix tailTrace_4696759
  have hstable : (prefixWord ++ tailWord_4696759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4696759).length < 2 ^ (prefixWord ++ tailWord_4696759).sum := by decide
  have hdescent : baseEnd_4696759 < baseStart_4696759 := by decide
  rcases family_descends (prefixWord ++ tailWord_4696759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4696761 : List Nat := [1, 2, 1, 4, 1, 1, 1, 2, 3, 1, 6]
def baseStart_4696761 : Nat := 118140960795 + 4696761 * 2 ^ 59
def prefixEnd_4696761 : Nat := 4983230072969 + 3 ^ 40 * 4696761 * 2
def baseEnd_4696761 : Nat := 2411695912291803634687495

theorem tailTrace_4696761 : CollatzResearch.WordTrace tailWord_4696761 prefixEnd_4696761 2411695912291803634687495 := by
  unfold tailWord_4696761
  simp only [CollatzResearch.WordTrace]
  refine ⟨171304946937444514762050137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114203297958296343174700091 171304946937444514762050137)
  ·
    refine ⟨128478710203083386071537603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171304946937444514762050137 128478710203083386071537603)
    ·
      refine ⟨192718065304625079107306405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128478710203083386071537603 192718065304625079107306405)
      ·
        refine ⟨36134637244617202332619951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 192718065304625079107306405 36134637244617202332619951)
        ·
          refine ⟨54201955866925803498929927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36134637244617202332619951 54201955866925803498929927)
          ·
            refine ⟨81302933800388705248394891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54201955866925803498929927 81302933800388705248394891)
            ·
              refine ⟨121954400700583057872592337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81302933800388705248394891 121954400700583057872592337)
              ·
                refine ⟨91465800525437293404444253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 121954400700583057872592337 91465800525437293404444253)
                ·
                  refine ⟨34299675197038985026666595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 91465800525437293404444253 34299675197038985026666595)
                  ·
                    refine ⟨51449512795558477539999893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34299675197038985026666595 51449512795558477539999893)
                    ·
                      refine ⟨2411695912291803634687495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 51449512795558477539999893 2411695912291803634687495)
                      ·
                        rfl

theorem cell23_4696761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 2, 3, 1, 6].length) (baseStart_4696761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4696761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4696761 prefixEnd_4696761 := by exact prefixLift 4696761
  have htrace : WordTrace (prefixWord ++ tailWord_4696761) baseStart_4696761 baseEnd_4696761 := by
    simpa [prefixWord, tailWord_4696761, baseEnd_4696761] using wordTrace_append hprefix tailTrace_4696761
  have hstable : (prefixWord ++ tailWord_4696761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4696761).length < 2 ^ (prefixWord ++ tailWord_4696761).sum := by decide
  have hdescent : baseEnd_4696761 < baseStart_4696761 := by decide
  rcases family_descends (prefixWord ++ tailWord_4696761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4696765 : List Nat := [1, 4, 1, 2, 1, 4, 1, 3, 1, 1, 4]
def baseStart_4696765 : Nat := 118140960795 + 4696765 * 2 ^ 59
def prefixEnd_4696765 : Nat := 4983230072969 + 3 ^ 40 * 4696765 * 2
def baseEnd_4696765 : Nat := 2411697966214421619037477

theorem tailTrace_4696765 : CollatzResearch.WordTrace tailWord_4696765 prefixEnd_4696765 2411697966214421619037477 := by
  unfold tailWord_4696765
  simp only [CollatzResearch.WordTrace]
  refine ⟨171305092829430023445195749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114203395219620015630130499 171305092829430023445195749)
  ·
    refine ⟨32119704905518129395974203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 171305092829430023445195749 32119704905518129395974203)
    ·
      refine ⟨48179557358277194093961305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32119704905518129395974203 48179557358277194093961305)
      ·
        refine ⟨36134668018707895570470979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48179557358277194093961305 36134668018707895570470979)
        ·
          refine ⟨54202002028061843355706469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36134668018707895570470979 54202002028061843355706469)
          ·
            refine ⟨10162875380261595629194963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 54202002028061843355706469 10162875380261595629194963)
            ·
              refine ⟨15244313070392393443792445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10162875380261595629194963 15244313070392393443792445)
              ·
                refine ⟨5716617401397147541422167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15244313070392393443792445 5716617401397147541422167)
                ·
                  refine ⟨8574926102095721312133251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5716617401397147541422167 8574926102095721312133251)
                  ·
                    refine ⟨12862389153143581968199877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8574926102095721312133251 12862389153143581968199877)
                    ·
                      refine ⟨2411697966214421619037477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12862389153143581968199877 2411697966214421619037477)
                      ·
                        rfl

theorem cell23_4696765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 3, 1, 1, 4].length) (baseStart_4696765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4696765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4696765 prefixEnd_4696765 := by exact prefixLift 4696765
  have htrace : WordTrace (prefixWord ++ tailWord_4696765) baseStart_4696765 baseEnd_4696765 := by
    simpa [prefixWord, tailWord_4696765, baseEnd_4696765] using wordTrace_append hprefix tailTrace_4696765
  have hstable : (prefixWord ++ tailWord_4696765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4696765).length < 2 ^ (prefixWord ++ tailWord_4696765).sum := by decide
  have hdescent : baseEnd_4696765 < baseStart_4696765 := by decide
  rcases family_descends (prefixWord ++ tailWord_4696765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4696782 : List Nat := [4, 1, 1, 1, 3, 2, 1, 3, 3, 2, 2]
def baseStart_4696782 : Nat := 118140960795 + 4696782 * 2 ^ 59
def prefixEnd_4696782 : Nat := 4983230072969 + 3 ^ 40 * 4696782 * 2
def baseEnd_4696782 : Nat := 2411706695385548052524899

theorem tailTrace_4696782 : CollatzResearch.WordTrace tailWord_4696782 prefixEnd_4696782 2411706695385548052524899 := by
  unfold tailWord_4696782
  simp only [CollatzResearch.WordTrace]
  refine ⟨21413214108796054418570575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 114203808580245623565709733 21413214108796054418570575)
  ·
    refine ⟨32119821163194081627855863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21413214108796054418570575 32119821163194081627855863)
    ·
      refine ⟨48179731744791122441783795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32119821163194081627855863 48179731744791122441783795)
      ·
        refine ⟨72269597617186683662675693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48179731744791122441783795 72269597617186683662675693)
        ·
          refine ⟨27101099106445006373503385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72269597617186683662675693 27101099106445006373503385)
          ·
            refine ⟨20325824329833754780127539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27101099106445006373503385 20325824329833754780127539)
            ·
              refine ⟨30488736494750632170191309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20325824329833754780127539 30488736494750632170191309)
              ·
                refine ⟨11433276185531487063821741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30488736494750632170191309 11433276185531487063821741)
                ·
                  refine ⟨4287478569574307648933153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11433276185531487063821741 4287478569574307648933153)
                  ·
                    refine ⟨3215608927180730736699865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4287478569574307648933153 3215608927180730736699865)
                    ·
                      refine ⟨2411706695385548052524899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3215608927180730736699865 2411706695385548052524899)
                      ·
                        rfl

theorem cell23_4696782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 3, 3, 2, 2].length) (baseStart_4696782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4696782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4696782 prefixEnd_4696782 := by exact prefixLift 4696782
  have htrace : WordTrace (prefixWord ++ tailWord_4696782) baseStart_4696782 baseEnd_4696782 := by
    simpa [prefixWord, tailWord_4696782, baseEnd_4696782] using wordTrace_append hprefix tailTrace_4696782
  have hstable : (prefixWord ++ tailWord_4696782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4696782).length < 2 ^ (prefixWord ++ tailWord_4696782).sum := by decide
  have hdescent : baseEnd_4696782 < baseStart_4696782 := by decide
  rcases family_descends (prefixWord ++ tailWord_4696782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4696792 : List Nat := [2, 1, 2, 2, 3, 3, 3, 1, 2, 4]
def baseStart_4696792 : Nat := 118140960795 + 4696792 * 2 ^ 59
def prefixEnd_4696792 : Nat := 4983230072969 + 3 ^ 40 * 4696792 * 2
def baseEnd_4696792 : Nat := 803903943397364337799951

theorem tailTrace_4696792 : CollatzResearch.WordTrace tailWord_4696792 prefixEnd_4696792 803903943397364337799951 := by
  unfold tailWord_4696792
  simp only [CollatzResearch.WordTrace]
  refine ⟨85653038800166103528214315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114204051733554804704285753 85653038800166103528214315)
  ·
    refine ⟨128479558200249155292321473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85653038800166103528214315 128479558200249155292321473)
    ·
      refine ⟨96359668650186866469241105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128479558200249155292321473 96359668650186866469241105)
      ·
        refine ⟨72269751487640149851930829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96359668650186866469241105 72269751487640149851930829)
        ·
          refine ⟨27101156807865056194474061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72269751487640149851930829 27101156807865056194474061)
          ·
            refine ⟨10162933802949396072927773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27101156807865056194474061 10162933802949396072927773)
            ·
              refine ⟨3811100176106023527347915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10162933802949396072927773 3811100176106023527347915)
              ·
                refine ⟨5716650264159035291021873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3811100176106023527347915 5716650264159035291021873)
                ·
                  refine ⟨4287487698119276468266405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5716650264159035291021873 4287487698119276468266405)
                  ·
                    refine ⟨803903943397364337799951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4287487698119276468266405 803903943397364337799951)
                    ·
                      rfl

theorem cell23_4696792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 3, 1, 2, 4].length) (baseStart_4696792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4696792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4696792 prefixEnd_4696792 := by exact prefixLift 4696792
  have htrace : WordTrace (prefixWord ++ tailWord_4696792) baseStart_4696792 baseEnd_4696792 := by
    simpa [prefixWord, tailWord_4696792, baseEnd_4696792] using wordTrace_append hprefix tailTrace_4696792
  have hstable : (prefixWord ++ tailWord_4696792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4696792).length < 2 ^ (prefixWord ++ tailWord_4696792).sum := by decide
  have hdescent : baseEnd_4696792 < baseStart_4696792 := by decide
  rcases family_descends (prefixWord ++ tailWord_4696792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4696805 : List Nat := [1, 3, 1, 4, 1, 4, 2, 7]
def baseStart_4696805 : Nat := 118140960795 + 4696805 * 2 ^ 59
def prefixEnd_4696805 : Nat := 4983230072969 + 3 ^ 40 * 4696805 * 2
def baseEnd_4696805 : Nat := 89322907608911165279159

theorem tailTrace_4696805 : CollatzResearch.WordTrace tailWord_4696805 prefixEnd_4696805 89322907608911165279159 := by
  unfold tailWord_4696805
  simp only [CollatzResearch.WordTrace]
  refine ⟨171306551749285110276651869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114204367832856740184434579 171306551749285110276651869)
  ·
    refine ⟨64239956905981916353744451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 171306551749285110276651869 64239956905981916353744451)
    ·
      refine ⟨96359935358972874530616677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64239956905981916353744451 96359935358972874530616677)
      ·
        refine ⟨18067487879807413974490627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 96359935358972874530616677 18067487879807413974490627)
        ·
          refine ⟨27101231819711120961735941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18067487879807413974490627 27101231819711120961735941)
          ·
            refine ⟨5081480966195835180325489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27101231819711120961735941 5081480966195835180325489)
            ·
              refine ⟨3811110724646876385244117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5081480966195835180325489 3811110724646876385244117)
              ·
                refine ⟨89322907608911165279159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3811110724646876385244117 89322907608911165279159)
                ·
                  rfl

theorem cell23_4696805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 2, 7].length) (baseStart_4696805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4696805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4696805 prefixEnd_4696805 := by exact prefixLift 4696805
  have htrace : WordTrace (prefixWord ++ tailWord_4696805) baseStart_4696805 baseEnd_4696805 := by
    simpa [prefixWord, tailWord_4696805, baseEnd_4696805] using wordTrace_append hprefix tailTrace_4696805
  have hstable : (prefixWord ++ tailWord_4696805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4696805).length < 2 ^ (prefixWord ++ tailWord_4696805).sum := by decide
  have hdescent : baseEnd_4696805 < baseStart_4696805 := by decide
  rcases family_descends (prefixWord ++ tailWord_4696805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4696815 : List Nat := [1, 1, 2, 1, 5, 2, 1, 2, 4, 1, 3]
def baseStart_4696815 : Nat := 118140960795 + 4696815 * 2 ^ 59
def prefixEnd_4696815 : Nat := 4983230072969 + 3 ^ 40 * 4696815 * 2
def baseEnd_4696815 : Nat := 2411723640247146423412247

theorem tailTrace_4696815 : CollatzResearch.WordTrace tailWord_4696815 prefixEnd_4696815 2411723640247146423412247 := by
  unfold tailWord_4696815
  simp only [CollatzResearch.WordTrace]
  refine ⟨171306916479248881984515899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114204610986165921323010599 171306916479248881984515899)
  ·
    refine ⟨256960374718873322976773849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171306916479248881984515899 256960374718873322976773849)
    ·
      refine ⟨192720281039154992232580387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 256960374718873322976773849 192720281039154992232580387)
      ·
        refine ⟨289080421558732488348870581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192720281039154992232580387 289080421558732488348870581)
        ·
          refine ⟨27101289521131170782706617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 289080421558732488348870581 27101289521131170782706617)
          ·
            refine ⟨20325967140848378087029963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27101289521131170782706617 20325967140848378087029963)
            ·
              refine ⟨30488950711272567130544945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20325967140848378087029963 30488950711272567130544945)
              ·
                refine ⟨22866713033454425347908709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30488950711272567130544945 22866713033454425347908709)
                ·
                  refine ⟨4287508693772704752732883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22866713033454425347908709 4287508693772704752732883)
                  ·
                    refine ⟨6431263040659057129099325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4287508693772704752732883 6431263040659057129099325)
                    ·
                      refine ⟨2411723640247146423412247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6431263040659057129099325 2411723640247146423412247)
                      ·
                        rfl

theorem cell23_4696815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 2, 4, 1, 3].length) (baseStart_4696815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4696815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4696815 prefixEnd_4696815 := by exact prefixLift 4696815
  have htrace : WordTrace (prefixWord ++ tailWord_4696815) baseStart_4696815 baseEnd_4696815 := by
    simpa [prefixWord, tailWord_4696815, baseEnd_4696815] using wordTrace_append hprefix tailTrace_4696815
  have hstable : (prefixWord ++ tailWord_4696815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4696815).length < 2 ^ (prefixWord ++ tailWord_4696815).sum := by decide
  have hdescent : baseEnd_4696815 < baseStart_4696815 := by decide
  rcases family_descends (prefixWord ++ tailWord_4696815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4696858 : List Nat := [3, 1, 1, 3, 2, 1, 1, 1, 4, 1, 5]
def baseStart_4696858 : Nat := 118140960795 + 4696858 * 2 ^ 59
def prefixEnd_4696858 : Nat := 4983230072969 + 3 ^ 40 * 4696858 * 2
def baseEnd_4696858 : Nat := 2411745719915289755174549

theorem tailTrace_4696858 : CollatzResearch.WordTrace tailWord_4696858 prefixEnd_4696858 2411745719915289755174549 := by
  unfold tailWord_4696858
  simp only [CollatzResearch.WordTrace]
  refine ⟨42827121204523275082082807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114205656545395400218887485 42827121204523275082082807)
  ·
    refine ⟨64240681806784912623124211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42827121204523275082082807 64240681806784912623124211)
    ·
      refine ⟨96361022710177368934686317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64240681806784912623124211 96361022710177368934686317)
      ·
        refine ⟨36135383516316513350507369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96361022710177368934686317 36135383516316513350507369)
        ·
          refine ⟨27101537637237385012880527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36135383516316513350507369 27101537637237385012880527)
          ·
            refine ⟨40652306455856077519320791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27101537637237385012880527 40652306455856077519320791)
            ·
              refine ⟨60978459683784116278981187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40652306455856077519320791 60978459683784116278981187)
              ·
                refine ⟨91467689525676174418471781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60978459683784116278981187 91467689525676174418471781)
                ·
                  refine ⟨17150191786064282703463459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 91467689525676174418471781 17150191786064282703463459)
                  ·
                    refine ⟨25725287679096424055195189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17150191786064282703463459 25725287679096424055195189)
                    ·
                      refine ⟨2411745719915289755174549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25725287679096424055195189 2411745719915289755174549)
                      ·
                        rfl

theorem cell23_4696858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 1, 4, 1, 5].length) (baseStart_4696858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4696858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4696858 prefixEnd_4696858 := by exact prefixLift 4696858
  have htrace : WordTrace (prefixWord ++ tailWord_4696858) baseStart_4696858 baseEnd_4696858 := by
    simpa [prefixWord, tailWord_4696858, baseEnd_4696858] using wordTrace_append hprefix tailTrace_4696858
  have hstable : (prefixWord ++ tailWord_4696858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4696858).length < 2 ^ (prefixWord ++ tailWord_4696858).sum := by decide
  have hdescent : baseEnd_4696858 < baseStart_4696858 := by decide
  rcases family_descends (prefixWord ++ tailWord_4696858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4696872 : List Nat := [2, 1, 5, 1, 1, 1, 3, 2, 1, 4, 2]
def baseStart_4696872 : Nat := 118140960795 + 4696872 * 2 ^ 59
def prefixEnd_4696872 : Nat := 4983230072969 + 3 ^ 40 * 4696872 * 2
def baseEnd_4696872 : Nat := 2411752908644452700399485

theorem tailTrace_4696872 : CollatzResearch.WordTrace tailWord_4696872 prefixEnd_4696872 2411752908644452700399485 := by
  unfold tailWord_4696872
  simp only [CollatzResearch.WordTrace]
  refine ⟨85654497720021190359670435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114205996960028253812893913 85654497720021190359670435)
  ·
    refine ⟨128481746580031785539505653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85654497720021190359670435 128481746580031785539505653)
    ·
      refine ⟨12045163741877979894328655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 128481746580031785539505653 12045163741877979894328655)
      ·
        refine ⟨18067745612816969841492983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12045163741877979894328655 18067745612816969841492983)
        ·
          refine ⟨27101618419225454762239475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18067745612816969841492983 27101618419225454762239475)
          ·
            refine ⟨40652427628838182143359213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27101618419225454762239475 40652427628838182143359213)
            ·
              refine ⟨15244660360814318303759705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40652427628838182143359213 15244660360814318303759705)
              ·
                refine ⟨11433495270610738727819779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15244660360814318303759705 11433495270610738727819779)
                ·
                  refine ⟨17150242905916108091729669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11433495270610738727819779 17150242905916108091729669)
                  ·
                    refine ⟨3215670544859270267199313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17150242905916108091729669 3215670544859270267199313)
                    ·
                      refine ⟨2411752908644452700399485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3215670544859270267199313 2411752908644452700399485)
                      ·
                        rfl

theorem cell23_4696872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 2, 1, 4, 2].length) (baseStart_4696872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4696872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4696872 prefixEnd_4696872 := by exact prefixLift 4696872
  have htrace : WordTrace (prefixWord ++ tailWord_4696872) baseStart_4696872 baseEnd_4696872 := by
    simpa [prefixWord, tailWord_4696872, baseEnd_4696872] using wordTrace_append hprefix tailTrace_4696872
  have hstable : (prefixWord ++ tailWord_4696872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4696872).length < 2 ^ (prefixWord ++ tailWord_4696872).sum := by decide
  have hdescent : baseEnd_4696872 < baseStart_4696872 := by decide
  rcases family_descends (prefixWord ++ tailWord_4696872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4696905 : List Nat := [1, 2, 1, 1, 2, 6, 1, 1, 2, 3, 3]
def baseStart_4696905 : Nat := 118140960795 + 4696905 * 2 ^ 59
def prefixEnd_4696905 : Nat := 4983230072969 + 3 ^ 40 * 4696905 * 2
def baseEnd_4696905 : Nat := 2411769853506051071286833

theorem tailTrace_4696905 : CollatzResearch.WordTrace tailWord_4696905 prefixEnd_4696905 2411769853506051071286833 := by
  unfold tailWord_4696905
  simp only [CollatzResearch.WordTrace]
  refine ⟨171310199048922827355292169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114206799365948551570194779 171310199048922827355292169)
  ·
    refine ⟨128482649286692120516469127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171310199048922827355292169 128482649286692120516469127)
    ·
      refine ⟨192723973930038180774703691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128482649286692120516469127 192723973930038180774703691)
      ·
        refine ⟨289085960895057271162055537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192723973930038180774703691 289085960895057271162055537)
        ·
          refine ⟨216814470671292953371541653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 289085960895057271162055537 216814470671292953371541653)
          ·
            refine ⟨10163178312716857189291015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 216814470671292953371541653 10163178312716857189291015)
            ·
              refine ⟨15244767469075285783936523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10163178312716857189291015 15244767469075285783936523)
              ·
                refine ⟨22867151203612928675904785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15244767469075285783936523 22867151203612928675904785)
                ·
                  refine ⟨17150363402709696506928589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22867151203612928675904785 17150363402709696506928589)
                  ·
                    refine ⟨6431386276016136190098221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17150363402709696506928589 6431386276016136190098221)
                    ·
                      refine ⟨2411769853506051071286833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6431386276016136190098221 2411769853506051071286833)
                      ·
                        rfl

theorem cell23_4696905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 1, 2, 3, 3].length) (baseStart_4696905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4696905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4696905 prefixEnd_4696905 := by exact prefixLift 4696905
  have htrace : WordTrace (prefixWord ++ tailWord_4696905) baseStart_4696905 baseEnd_4696905 := by
    simpa [prefixWord, tailWord_4696905, baseEnd_4696905] using wordTrace_append hprefix tailTrace_4696905
  have hstable : (prefixWord ++ tailWord_4696905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4696905).length < 2 ^ (prefixWord ++ tailWord_4696905).sum := by decide
  have hdescent : baseEnd_4696905 < baseStart_4696905 := by decide
  rcases family_descends (prefixWord ++ tailWord_4696905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4696955 : List Nat := [1, 1, 1, 1, 1, 5, 3, 3, 3, 4]
def baseStart_4696955 : Nat := 118140960795 + 4696955 * 2 ^ 59
def prefixEnd_4696955 : Nat := 4983230072969 + 3 ^ 40 * 4696955 * 2
def baseEnd_4696955 : Nat := 803931842512925291887201

theorem tailTrace_4696955 : CollatzResearch.WordTrace tailWord_4696955 prefixEnd_4696955 803931842512925291887201 := by
  unfold tailWord_4696955
  simp only [CollatzResearch.WordTrace]
  refine ⟨171312022698741685894612319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114208015132494457263074879 171312022698741685894612319)
  ·
    refine ⟨256968034048112528841918479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171312022698741685894612319 256968034048112528841918479)
    ·
      refine ⟨385452051072168793262877719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 256968034048112528841918479 385452051072168793262877719)
      ·
        refine ⟨578178076608253189894316579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 385452051072168793262877719 578178076608253189894316579)
        ·
          refine ⟨867267114912379784841474869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 578178076608253189894316579 867267114912379784841474869)
          ·
            refine ⟨81306292023035604828888269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 867267114912379784841474869 81306292023035604828888269)
            ·
              refine ⟨30489859508638351810833101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 81306292023035604828888269 30489859508638351810833101)
              ·
                refine ⟨11433697315739381929062413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30489859508638351810833101 11433697315739381929062413)
                ·
                  refine ⟨4287636493402268223398405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11433697315739381929062413 4287636493402268223398405)
                  ·
                    refine ⟨803931842512925291887201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4287636493402268223398405 803931842512925291887201)
                    ·
                      rfl

theorem cell23_4696955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 3, 3, 4].length) (baseStart_4696955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4696955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4696955 prefixEnd_4696955 := by exact prefixLift 4696955
  have htrace : WordTrace (prefixWord ++ tailWord_4696955) baseStart_4696955 baseEnd_4696955 := by
    simpa [prefixWord, tailWord_4696955, baseEnd_4696955] using wordTrace_append hprefix tailTrace_4696955
  have hstable : (prefixWord ++ tailWord_4696955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4696955).length < 2 ^ (prefixWord ++ tailWord_4696955).sum := by decide
  have hdescent : baseEnd_4696955 < baseStart_4696955 := by decide
  rcases family_descends (prefixWord ++ tailWord_4696955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4696965 : List Nat := [1, 3, 1, 1, 3, 3, 1, 2, 1, 4, 3]
def baseStart_4696965 : Nat := 118140960795 + 4696965 * 2 ^ 59
def prefixEnd_4696965 : Nat := 4983230072969 + 3 ^ 40 * 4696965 * 2
def baseEnd_4696965 : Nat := 2411800662345320836536557

theorem tailTrace_4696965 : CollatzResearch.WordTrace tailWord_4696965 prefixEnd_4696965 2411800662345320836536557 := by
  unfold tailWord_4696965
  simp only [CollatzResearch.WordTrace]
  refine ⟨171312387428705457602476349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114208258285803638401650899 171312387428705457602476349)
  ·
    refine ⟨64242145285764546600928631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 171312387428705457602476349 64242145285764546600928631)
    ·
      refine ⟨96363217928646819901392947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64242145285764546600928631 96363217928646819901392947)
      ·
        refine ⟨144544826892970229852089421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96363217928646819901392947 144544826892970229852089421)
        ·
          refine ⟨54204310084863836194533533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 144544826892970229852089421 54204310084863836194533533)
          ·
            refine ⟨20326616281823938572950075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54204310084863836194533533 20326616281823938572950075)
            ·
              refine ⟨30489924422735907859425113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20326616281823938572950075 30489924422735907859425113)
              ·
                refine ⟨22867443317051930894568835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30489924422735907859425113 22867443317051930894568835)
                ·
                  refine ⟨34301164975577896341853253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22867443317051930894568835 34301164975577896341853253)
                  ·
                    refine ⟨6431468432920855564097485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34301164975577896341853253 6431468432920855564097485)
                    ·
                      refine ⟨2411800662345320836536557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6431468432920855564097485 2411800662345320836536557)
                      ·
                        rfl

theorem cell23_4696965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 2, 1, 4, 3].length) (baseStart_4696965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4696965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4696965 prefixEnd_4696965 := by exact prefixLift 4696965
  have htrace : WordTrace (prefixWord ++ tailWord_4696965) baseStart_4696965 baseEnd_4696965 := by
    simpa [prefixWord, tailWord_4696965, baseEnd_4696965] using wordTrace_append hprefix tailTrace_4696965
  have hstable : (prefixWord ++ tailWord_4696965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4696965).length < 2 ^ (prefixWord ++ tailWord_4696965).sum := by decide
  have hdescent : baseEnd_4696965 < baseStart_4696965 := by decide
  rcases family_descends (prefixWord ++ tailWord_4696965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4696999 : List Nat := [1, 1, 6, 1, 3, 1, 1, 2, 2, 2, 3]
def baseStart_4696999 : Nat := 118140960795 + 4696999 * 2 ^ 59
def prefixEnd_4696999 : Nat := 4983230072969 + 3 ^ 40 * 4696999 * 2
def baseEnd_4696999 : Nat := 2411818120687573703511401

theorem tailTrace_4696999 : CollatzResearch.WordTrace tailWord_4696999 prefixEnd_4696999 2411818120687573703511401 := by
  unfold tailWord_4696999
  simp only [CollatzResearch.WordTrace]
  refine ⟨171313627510582281409214051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114209085007054854272809367 171313627510582281409214051)
  ·
    refine ⟨256970441265873422113821077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171313627510582281409214051 256970441265873422113821077)
    ·
      refine ⟨12045489434337816661585363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 256970441265873422113821077 12045489434337816661585363)
      ·
        refine ⟨18068234151506724992378045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12045489434337816661585363 18068234151506724992378045)
        ·
          refine ⟨6775587806815021872141767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18068234151506724992378045 6775587806815021872141767)
          ·
            refine ⟨10163381710222532808212651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6775587806815021872141767 10163381710222532808212651)
            ·
              refine ⟨15245072565333799212318977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10163381710222532808212651 15245072565333799212318977)
              ·
                refine ⟨11433804424000349409239233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15245072565333799212318977 11433804424000349409239233)
                ·
                  refine ⟨8575353318000262056929425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11433804424000349409239233 8575353318000262056929425)
                  ·
                    refine ⟨6431514988500196542697069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8575353318000262056929425 6431514988500196542697069)
                    ·
                      refine ⟨2411818120687573703511401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6431514988500196542697069 2411818120687573703511401)
                      ·
                        rfl

theorem cell23_4696999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 2, 2, 2, 3].length) (baseStart_4696999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4696999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4696999 prefixEnd_4696999 := by exact prefixLift 4696999
  have htrace : WordTrace (prefixWord ++ tailWord_4696999) baseStart_4696999 baseEnd_4696999 := by
    simpa [prefixWord, tailWord_4696999, baseEnd_4696999] using wordTrace_append hprefix tailTrace_4696999
  have hstable : (prefixWord ++ tailWord_4696999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4696999).length < 2 ^ (prefixWord ++ tailWord_4696999).sum := by decide
  have hdescent : baseEnd_4696999 < baseStart_4696999 := by decide
  rcases family_descends (prefixWord ++ tailWord_4696999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4697030 : List Nat := [6, 1, 3, 1, 1, 1, 2, 1, 2, 1, 4]
def baseStart_4697030 : Nat := 118140960795 + 4697030 * 2 ^ 59
def prefixEnd_4697030 : Nat := 4983230072969 + 3 ^ 40 * 4697030 * 2
def baseEnd_4697030 : Nat := 2411834038587863082223759

theorem tailTrace_4697030 : CollatzResearch.WordTrace tailWord_4697030 prefixEnd_4697030 2411834038587863082223759 := by
  unfold tailWord_4697030
  simp only [CollatzResearch.WordTrace]
  refine ⟨5353586192920936678237267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 114209838782313315802395029 5353586192920936678237267)
  ·
    refine ⟨8030379289381405017355901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5353586192920936678237267 8030379289381405017355901)
    ·
      refine ⟨3011392233518026881508463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8030379289381405017355901 3011392233518026881508463)
      ·
        refine ⟨4517088350277040322262695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3011392233518026881508463 4517088350277040322262695)
        ·
          refine ⟨6775632525415560483394043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4517088350277040322262695 6775632525415560483394043)
          ·
            refine ⟨10163448788123340725091065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6775632525415560483394043 10163448788123340725091065)
            ·
              refine ⟨7622586591092505543818299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10163448788123340725091065 7622586591092505543818299)
              ·
                refine ⟨11433879886638758315727449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7622586591092505543818299 11433879886638758315727449)
                ·
                  refine ⟨8575409914979068736795587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11433879886638758315727449 8575409914979068736795587)
                  ·
                    refine ⟨12863114872468603105193381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8575409914979068736795587 12863114872468603105193381)
                    ·
                      refine ⟨2411834038587863082223759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12863114872468603105193381 2411834038587863082223759)
                      ·
                        rfl

theorem cell23_4697030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_4697030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4697030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4697030 prefixEnd_4697030 := by exact prefixLift 4697030
  have htrace : WordTrace (prefixWord ++ tailWord_4697030) baseStart_4697030 baseEnd_4697030 := by
    simpa [prefixWord, tailWord_4697030, baseEnd_4697030] using wordTrace_append hprefix tailTrace_4697030
  have hstable : (prefixWord ++ tailWord_4697030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4697030).length < 2 ^ (prefixWord ++ tailWord_4697030).sum := by decide
  have hdescent : baseEnd_4697030 < baseStart_4697030 := by decide
  rcases family_descends (prefixWord ++ tailWord_4697030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4697032 : List Nat := [2, 1, 3, 1, 5, 1, 1, 1, 3, 5]
def baseStart_4697032 : Nat := 118140960795 + 4697032 * 2 ^ 59
def prefixEnd_4697032 : Nat := 4983230072969 + 3 ^ 40 * 4697032 * 2
def baseEnd_4697032 : Nat := 803945021849724024799583

theorem tailTrace_4697032 : CollatzResearch.WordTrace tailWord_4697032 prefixEnd_4697032 803945021849724024799583 := by
  unfold tailWord_4697032
  simp only [CollatzResearch.WordTrace]
  refine ⟨85657415559731364022582675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114209887412975152030110233 85657415559731364022582675)
  ·
    refine ⟨128486123339597046033874013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85657415559731364022582675 128486123339597046033874013)
    ·
      refine ⟨48182296252348892262702755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 128486123339597046033874013 48182296252348892262702755)
      ·
        refine ⟨72273444378523338394054133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48182296252348892262702755 72273444378523338394054133)
        ·
          refine ⟨6775635410486562974442575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 72273444378523338394054133 6775635410486562974442575)
          ·
            refine ⟨10163453115729844461663863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6775635410486562974442575 10163453115729844461663863)
            ·
              refine ⟨15245179673594766692495795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10163453115729844461663863 15245179673594766692495795)
              ·
                refine ⟨22867769510392150038743693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15245179673594766692495795 22867769510392150038743693)
                ·
                  refine ⟨8575413566397056264528885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22867769510392150038743693 8575413566397056264528885)
                  ·
                    refine ⟨803945021849724024799583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8575413566397056264528885 803945021849724024799583)
                    ·
                      rfl

theorem cell23_4697032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 1, 3, 5].length) (baseStart_4697032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4697032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4697032 prefixEnd_4697032 := by exact prefixLift 4697032
  have htrace : WordTrace (prefixWord ++ tailWord_4697032) baseStart_4697032 baseEnd_4697032 := by
    simpa [prefixWord, tailWord_4697032, baseEnd_4697032] using wordTrace_append hprefix tailTrace_4697032
  have hstable : (prefixWord ++ tailWord_4697032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4697032).length < 2 ^ (prefixWord ++ tailWord_4697032).sum := by decide
  have hdescent : baseEnd_4697032 < baseStart_4697032 := by decide
  rcases family_descends (prefixWord ++ tailWord_4697032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4697039 : List Nat := [1, 1, 2, 1, 1, 7, 2, 1, 2, 3, 2]
def baseStart_4697039 : Nat := 118140960795 + 4697039 * 2 ^ 59
def prefixEnd_4697039 : Nat := 4983230072969 + 3 ^ 40 * 4697039 * 2
def baseEnd_4697039 : Nat := 2411838659913753547011217

theorem tailTrace_4697039 : CollatzResearch.WordTrace tailWord_4697039 prefixEnd_4697039 2411838659913753547011217 := by
  unfold tailWord_4697039
  simp only [CollatzResearch.WordTrace]
  refine ⟨171315086430437368240670171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114210057620291578827113447 171315086430437368240670171)
  ·
    refine ⟨256972629645656052361005257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171315086430437368240670171 256972629645656052361005257)
    ·
      refine ⟨192729472234242039270753943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 256972629645656052361005257 192729472234242039270753943)
      ·
        refine ⟨289094208351363058906130915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192729472234242039270753943 289094208351363058906130915)
        ·
          refine ⟨433641312527044588359196373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 289094208351363058906130915 433641312527044588359196373)
          ·
            refine ⟨10163468262352607539668665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 433641312527044588359196373 10163468262352607539668665)
            ·
              refine ⟨7622601196764455654751499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10163468262352607539668665 7622601196764455654751499)
              ·
                refine ⟨11433901795146683482127249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7622601196764455654751499 11433901795146683482127249)
                ·
                  refine ⟨8575426346360012611595437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11433901795146683482127249 8575426346360012611595437)
                  ·
                    refine ⟨3215784879885004729348289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8575426346360012611595437 3215784879885004729348289)
                    ·
                      refine ⟨2411838659913753547011217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3215784879885004729348289 2411838659913753547011217)
                      ·
                        rfl

theorem cell23_4697039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 2, 1, 2, 3, 2].length) (baseStart_4697039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4697039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4697039 prefixEnd_4697039 := by exact prefixLift 4697039
  have htrace : WordTrace (prefixWord ++ tailWord_4697039) baseStart_4697039 baseEnd_4697039 := by
    simpa [prefixWord, tailWord_4697039, baseEnd_4697039] using wordTrace_append hprefix tailTrace_4697039
  have hstable : (prefixWord ++ tailWord_4697039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4697039).length < 2 ^ (prefixWord ++ tailWord_4697039).sum := by decide
  have hdescent : baseEnd_4697039 < baseStart_4697039 := by decide
  rcases family_descends (prefixWord ++ tailWord_4697039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4697049 : List Nat := [1, 2, 1, 2, 5, 2, 3, 1, 1, 5]
def baseStart_4697049 : Nat := 118140960795 + 4697049 * 2 ^ 59
def prefixEnd_4697049 : Nat := 4983230072969 + 3 ^ 40 * 4697049 * 2
def baseEnd_4697049 : Nat := 803947931573432835962057

theorem tailTrace_4697049 : CollatzResearch.WordTrace tailWord_4697049 prefixEnd_4697049 803947931573432835962057 := by
  unfold tailWord_4697049
  simp only [CollatzResearch.WordTrace]
  refine ⟨171315451160401139948534201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114210300773600759965689467 171315451160401139948534201)
  ·
    refine ⟨128486588370300854961400651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171315451160401139948534201 128486588370300854961400651)
    ·
      refine ⟨192729882555451282442100977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128486588370300854961400651 192729882555451282442100977)
      ·
        refine ⟨144547411916588461831575733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 192729882555451282442100977 144547411916588461831575733)
        ·
          refine ⟨13551319867180168296710225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 144547411916588461831575733 13551319867180168296710225)
          ·
            refine ⟨10163489900385126222532669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13551319867180168296710225 10163489900385126222532669)
            ·
              refine ⟨3811308712644422333449751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10163489900385126222532669 3811308712644422333449751)
              ·
                refine ⟨5716963068966633500174627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3811308712644422333449751 5716963068966633500174627)
                ·
                  refine ⟨8575444603449950250261941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5716963068966633500174627 8575444603449950250261941)
                  ·
                    refine ⟨803947931573432835962057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8575444603449950250261941 803947931573432835962057)
                    ·
                      rfl

theorem cell23_4697049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 3, 1, 1, 5].length) (baseStart_4697049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4697049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4697049 prefixEnd_4697049 := by exact prefixLift 4697049
  have htrace : WordTrace (prefixWord ++ tailWord_4697049) baseStart_4697049 baseEnd_4697049 := by
    simpa [prefixWord, tailWord_4697049, baseEnd_4697049] using wordTrace_append hprefix tailTrace_4697049
  have hstable : (prefixWord ++ tailWord_4697049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4697049).length < 2 ^ (prefixWord ++ tailWord_4697049).sum := by decide
  have hdescent : baseEnd_4697049 < baseStart_4697049 := by decide
  rcases family_descends (prefixWord ++ tailWord_4697049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4697063 : List Nat := [1, 1, 5, 2, 2, 1, 4, 2, 1, 1, 3]
def baseStart_4697063 : Nat := 118140960795 + 4697063 * 2 ^ 59
def prefixEnd_4697063 : Nat := 4983230072969 + 3 ^ 40 * 4697063 * 2
def baseEnd_4697063 : Nat := 2411850983449461453111107

theorem tailTrace_4697063 : CollatzResearch.WordTrace tailWord_4697063 prefixEnd_4697063 2411850983449461453111107 := by
  unfold tailWord_4697063
  simp only [CollatzResearch.WordTrace]
  refine ⟨171315961782350420339543843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114210641188233613559695895 171315961782350420339543843)
  ·
    refine ⟨256973942673525630509315765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171315961782350420339543843 256973942673525630509315765)
    ·
      refine ⟨24091307125643027860248353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 256973942673525630509315765 24091307125643027860248353)
      ·
        refine ⟨18068480344232270895186265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24091307125643027860248353 18068480344232270895186265)
        ·
          refine ⟨13551360258174203171389699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18068480344232270895186265 13551360258174203171389699)
          ·
            refine ⟨20327040387261304757084549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13551360258174203171389699 20327040387261304757084549)
            ·
              refine ⟨3811320072611494641953353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20327040387261304757084549 3811320072611494641953353)
              ·
                refine ⟨2858490054458620981465015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3811320072611494641953353 2858490054458620981465015)
                ·
                  refine ⟨4287735081687931472197523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2858490054458620981465015 4287735081687931472197523)
                  ·
                    refine ⟨6431602622531897208296285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4287735081687931472197523 6431602622531897208296285)
                    ·
                      refine ⟨2411850983449461453111107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6431602622531897208296285 2411850983449461453111107)
                      ·
                        rfl

theorem cell23_4697063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 4, 2, 1, 1, 3].length) (baseStart_4697063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4697063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4697063 prefixEnd_4697063 := by exact prefixLift 4697063
  have htrace : WordTrace (prefixWord ++ tailWord_4697063) baseStart_4697063 baseEnd_4697063 := by
    simpa [prefixWord, tailWord_4697063, baseEnd_4697063] using wordTrace_append hprefix tailTrace_4697063
  have hstable : (prefixWord ++ tailWord_4697063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4697063).length < 2 ^ (prefixWord ++ tailWord_4697063).sum := by decide
  have hdescent : baseEnd_4697063 < baseStart_4697063 := by decide
  rcases family_descends (prefixWord ++ tailWord_4697063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4697090 : List Nat := [3, 4, 1, 3, 1, 2, 1, 1, 2, 3, 2]
def baseStart_4697090 : Nat := 118140960795 + 4697090 * 2 ^ 59
def prefixEnd_4697090 : Nat := 4983230072969 + 3 ^ 40 * 4697090 * 2
def baseEnd_4697090 : Nat := 2411864847427132847473483

theorem tailTrace_4697090 : CollatzResearch.WordTrace tailWord_4697090 prefixEnd_4697090 2411864847427132847473483 := by
  unfold tailWord_4697090
  simp only [CollatzResearch.WordTrace]
  refine ⟨42829236638313150987694181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114211297702168402633851149 42829236638313150987694181)
  ·
    refine ⟨8030481869683715810192659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42829236638313150987694181 8030481869683715810192659)
    ·
      refine ⟨12045722804525573715288989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8030481869683715810192659 12045722804525573715288989)
      ·
        refine ⟨4517146051697090143233371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12045722804525573715288989 4517146051697090143233371)
        ·
          refine ⟨6775719077545635214850057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4517146051697090143233371 6775719077545635214850057)
          ·
            refine ⟨5081789308159226411137543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6775719077545635214850057 5081789308159226411137543)
            ·
              refine ⟨7622683962238839616706315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5081789308159226411137543 7622683962238839616706315)
              ·
                refine ⟨11434025943358259425059473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7622683962238839616706315 11434025943358259425059473)
                ·
                  refine ⟨8575519457518694568794605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11434025943358259425059473 8575519457518694568794605)
                  ·
                    refine ⟨3215819796569510463297977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8575519457518694568794605 3215819796569510463297977)
                    ·
                      refine ⟨2411864847427132847473483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3215819796569510463297977 2411864847427132847473483)
                      ·
                        rfl

theorem cell23_4697090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 1, 1, 2, 3, 2].length) (baseStart_4697090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4697090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4697090 prefixEnd_4697090 := by exact prefixLift 4697090
  have htrace : WordTrace (prefixWord ++ tailWord_4697090) baseStart_4697090 baseEnd_4697090 := by
    simpa [prefixWord, tailWord_4697090, baseEnd_4697090] using wordTrace_append hprefix tailTrace_4697090
  have hstable : (prefixWord ++ tailWord_4697090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4697090).length < 2 ^ (prefixWord ++ tailWord_4697090).sum := by decide
  have hdescent : baseEnd_4697090 < baseStart_4697090 := by decide
  rcases family_descends (prefixWord ++ tailWord_4697090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4697119 : List Nat := [1, 1, 2, 4, 1, 4, 1, 1, 4, 1, 3]
def baseStart_4697119 : Nat := 118140960795 + 4697119 * 2 ^ 59
def prefixEnd_4697119 : Nat := 4983230072969 + 3 ^ 40 * 4697119 * 2
def baseEnd_4697119 : Nat := 2411879738366113234010849

theorem tailTrace_4697119 : CollatzResearch.WordTrace tailWord_4697119 prefixEnd_4697119 2411879738366113234010849 := by
  unfold tailWord_4697119
  simp only [CollatzResearch.WordTrace]
  refine ⟨171318004270147541903582411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114212002846765027935721607 171318004270147541903582411)
  ·
    refine ⟨256977006405221312855373617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171318004270147541903582411 256977006405221312855373617)
    ·
      refine ⟨192732754803915984641530213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 256977006405221312855373617 192732754803915984641530213)
      ·
        refine ⟨36137391525734247120286915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 192732754803915984641530213 36137391525734247120286915)
        ·
          refine ⟨54206087288601370680430373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36137391525734247120286915 54206087288601370680430373)
          ·
            refine ⟨10163641366612757002580695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 54206087288601370680430373 10163641366612757002580695)
            ·
              refine ⟨15245462049919135503871043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10163641366612757002580695 15245462049919135503871043)
              ·
                refine ⟨22868193074878703255806565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15245462049919135503871043 22868193074878703255806565)
                ·
                  refine ⟨4287786201539756860463731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22868193074878703255806565 4287786201539756860463731)
                  ·
                    refine ⟨6431679302309635290695597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4287786201539756860463731 6431679302309635290695597)
                    ·
                      refine ⟨2411879738366113234010849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6431679302309635290695597 2411879738366113234010849)
                      ·
                        rfl

theorem cell23_4697119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 1, 4, 1, 3].length) (baseStart_4697119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4697119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4697119 prefixEnd_4697119 := by exact prefixLift 4697119
  have htrace : WordTrace (prefixWord ++ tailWord_4697119) baseStart_4697119 baseEnd_4697119 := by
    simpa [prefixWord, tailWord_4697119, baseEnd_4697119] using wordTrace_append hprefix tailTrace_4697119
  have hstable : (prefixWord ++ tailWord_4697119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4697119).length < 2 ^ (prefixWord ++ tailWord_4697119).sum := by decide
  have hdescent : baseEnd_4697119 < baseStart_4697119 := by decide
  rcases family_descends (prefixWord ++ tailWord_4697119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4697136 : List Nat := [2, 1, 1, 1, 2, 4, 5, 1, 2, 1, 3]
def baseStart_4697136 : Nat := 118140960795 + 4697136 * 2 ^ 59
def prefixEnd_4697136 : Nat := 4983230072969 + 3 ^ 40 * 4697136 * 2
def baseEnd_4697136 : Nat := 2411888467537239667498271

theorem tailTrace_4697136 : CollatzResearch.WordTrace tailWord_4697136 prefixEnd_4697136 2411888467537239667498271 := by
  unfold tailWord_4697136
  simp only [CollatzResearch.WordTrace]
  refine ⟨85659312155542976903475631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114212416207390635871300841 85659312155542976903475631)
  ·
    refine ⟨128488968233314465355213447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85659312155542976903475631 128488968233314465355213447)
    ·
      refine ⟨192733452349971698032820171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128488968233314465355213447 192733452349971698032820171)
      ·
        refine ⟨289100178524957547049230257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192733452349971698032820171 289100178524957547049230257)
        ·
          refine ⟨216825133893718160286922693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 289100178524957547049230257 216825133893718160286922693)
          ·
            refine ⟨40654712605072155053798005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 216825133893718160286922693 40654712605072155053798005)
            ·
              refine ⟨3811379306725514536293563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 40654712605072155053798005 3811379306725514536293563)
              ·
                refine ⟨5717068960088271804440345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3811379306725514536293563 5717068960088271804440345)
                ·
                  refine ⟨4287801720066203853330259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5717068960088271804440345 4287801720066203853330259)
                  ·
                    refine ⟨6431702580099305779995389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4287801720066203853330259 6431702580099305779995389)
                    ·
                      refine ⟨2411888467537239667498271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6431702580099305779995389 2411888467537239667498271)
                      ·
                        rfl

theorem cell23_4697136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 5, 1, 2, 1, 3].length) (baseStart_4697136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4697136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4697136 prefixEnd_4697136 := by exact prefixLift 4697136
  have htrace : WordTrace (prefixWord ++ tailWord_4697136) baseStart_4697136 baseEnd_4697136 := by
    simpa [prefixWord, tailWord_4697136, baseEnd_4697136] using wordTrace_append hprefix tailTrace_4697136
  have hstable : (prefixWord ++ tailWord_4697136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4697136).length < 2 ^ (prefixWord ++ tailWord_4697136).sum := by decide
  have hdescent : baseEnd_4697136 < baseStart_4697136 := by decide
  rcases family_descends (prefixWord ++ tailWord_4697136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4697172 : List Nat := [2, 4, 1, 1, 1, 1, 2, 1, 4, 2, 4]
def baseStart_4697172 : Nat := 118140960795 + 4697172 * 2 ^ 59
def prefixEnd_4697172 : Nat := 4983230072969 + 3 ^ 40 * 4697172 * 2
def baseEnd_4697172 : Nat := 2411906952840801526648105

theorem tailTrace_4697172 : CollatzResearch.WordTrace tailWord_4697172 prefixEnd_4697172 2411906952840801526648105 := by
  unfold tailWord_4697172
  simp only [CollatzResearch.WordTrace]
  refine ⟨85659968669477765977630885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114213291559303687970174513 85659968669477765977630885)
  ·
    refine ⟨16061244125527081120805791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 85659968669477765977630885 16061244125527081120805791)
    ·
      refine ⟨24091866188290621681208687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16061244125527081120805791 24091866188290621681208687)
      ·
        refine ⟨36137799282435932521813031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24091866188290621681208687 36137799282435932521813031)
        ·
          refine ⟨54206698923653898782719547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36137799282435932521813031 54206698923653898782719547)
          ·
            refine ⟨81310048385480848174079321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54206698923653898782719547 81310048385480848174079321)
            ·
              refine ⟨60982536289110636130559491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81310048385480848174079321 60982536289110636130559491)
              ·
                refine ⟨91473804433665954195839237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60982536289110636130559491 91473804433665954195839237)
                ·
                  refine ⟨17151338331312366411719857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 91473804433665954195839237 17151338331312366411719857)
                  ·
                    refine ⟨12863503748484274808789893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17151338331312366411719857 12863503748484274808789893)
                    ·
                      refine ⟨2411906952840801526648105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12863503748484274808789893 2411906952840801526648105)
                      ·
                        rfl

theorem cell23_4697172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 1, 4, 2, 4].length) (baseStart_4697172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4697172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4697172 prefixEnd_4697172 := by exact prefixLift 4697172
  have htrace : WordTrace (prefixWord ++ tailWord_4697172) baseStart_4697172 baseEnd_4697172 := by
    simpa [prefixWord, tailWord_4697172, baseEnd_4697172] using wordTrace_append hprefix tailTrace_4697172
  have hstable : (prefixWord ++ tailWord_4697172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4697172).length < 2 ^ (prefixWord ++ tailWord_4697172).sum := by decide
  have hdescent : baseEnd_4697172 < baseStart_4697172 := by decide
  rcases family_descends (prefixWord ++ tailWord_4697172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4697175 : List Nat := [1, 1, 3, 2, 2, 1, 1, 1, 1, 1, 9]
def baseStart_4697175 : Nat := 118140960795 + 4697175 * 2 ^ 59
def prefixEnd_4697175 : Nat := 4983230072969 + 3 ^ 40 * 4697175 * 2
def baseEnd_4697175 : Nat := 2411908493282765014910591

theorem tailTrace_4697175 : CollatzResearch.WordTrace tailWord_4697175 prefixEnd_4697175 2411908493282765014910591 := by
  unfold tailWord_4697175
  simp only [CollatzResearch.WordTrace]
  refine ⟨171320046757944663467620979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114213364505296442311747319 171320046757944663467620979)
  ·
    refine ⟨256980070136916995201431469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171320046757944663467620979 256980070136916995201431469)
    ·
      refine ⟨96367526301343873200536801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 256980070136916995201431469 96367526301343873200536801)
      ·
        refine ⟨72275644726007904900402601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96367526301343873200536801 72275644726007904900402601)
        ·
          refine ⟨54206733544505928675301951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72275644726007904900402601 54206733544505928675301951)
          ·
            refine ⟨81310100316758893012952927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54206733544505928675301951 81310100316758893012952927)
            ·
              refine ⟨121965150475138339519429391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81310100316758893012952927 121965150475138339519429391)
              ·
                refine ⟨182947725712707509279144087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 121965150475138339519429391 182947725712707509279144087)
                ·
                  refine ⟨274421588569061263918716131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 182947725712707509279144087 274421588569061263918716131)
                  ·
                    refine ⟨411632382853591895878074197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 274421588569061263918716131 411632382853591895878074197)
                    ·
                      refine ⟨2411908493282765014910591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 411632382853591895878074197 2411908493282765014910591)
                      ·
                        rfl

theorem cell23_4697175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 1, 1, 1, 9].length) (baseStart_4697175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4697175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4697175 prefixEnd_4697175 := by exact prefixLift 4697175
  have htrace : WordTrace (prefixWord ++ tailWord_4697175) baseStart_4697175 baseEnd_4697175 := by
    simpa [prefixWord, tailWord_4697175, baseEnd_4697175] using wordTrace_append hprefix tailTrace_4697175
  have hstable : (prefixWord ++ tailWord_4697175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4697175).length < 2 ^ (prefixWord ++ tailWord_4697175).sum := by decide
  have hdescent : baseEnd_4697175 < baseStart_4697175 := by decide
  rcases family_descends (prefixWord ++ tailWord_4697175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4697176 : List Nat := [2, 1, 2, 2, 1, 3, 2, 4, 2, 2, 2]
def baseStart_4697176 : Nat := 118140960795 + 4697176 * 2 ^ 59
def prefixEnd_4697176 : Nat := 4983230072969 + 3 ^ 40 * 4697176 * 2
def baseEnd_4697176 : Nat := 2411909006763419510998087

theorem tailTrace_4697176 : CollatzResearch.WordTrace tailWord_4697176 prefixEnd_4697176 2411909006763419510998087 := by
  unfold tailWord_4697176
  simp only [CollatzResearch.WordTrace]
  refine ⟨85660041615470520319203691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114213388820627360425604921 85660041615470520319203691)
  ·
    refine ⟨128490062423205780478805537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85660041615470520319203691 128490062423205780478805537)
    ·
      refine ⟨96367546817404335359104153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128490062423205780478805537 96367546817404335359104153)
      ·
        refine ⟨72275660113053251519328115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96367546817404335359104153 72275660113053251519328115)
        ·
          refine ⟨108413490169579877278992173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72275660113053251519328115 108413490169579877278992173)
          ·
            refine ⟨40655058813592453979622065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 108413490169579877278992173 40655058813592453979622065)
            ·
              refine ⟨30491294110194340484716549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40655058813592453979622065 30491294110194340484716549)
              ·
                refine ⟨5717117645661438840884353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30491294110194340484716549 5717117645661438840884353)
                ·
                  refine ⟨4287838234246079130663265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5717117645661438840884353 4287838234246079130663265)
                  ·
                    refine ⟨3215878675684559347997449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4287838234246079130663265 3215878675684559347997449)
                    ·
                      refine ⟨2411909006763419510998087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3215878675684559347997449 2411909006763419510998087)
                      ·
                        rfl

theorem cell23_4697176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 4, 2, 2, 2].length) (baseStart_4697176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4697176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4697176 prefixEnd_4697176 := by exact prefixLift 4697176
  have htrace : WordTrace (prefixWord ++ tailWord_4697176) baseStart_4697176 baseEnd_4697176 := by
    simpa [prefixWord, tailWord_4697176, baseEnd_4697176] using wordTrace_append hprefix tailTrace_4697176
  have hstable : (prefixWord ++ tailWord_4697176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4697176).length < 2 ^ (prefixWord ++ tailWord_4697176).sum := by decide
  have hdescent : baseEnd_4697176 < baseStart_4697176 := by decide
  rcases family_descends (prefixWord ++ tailWord_4697176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4697193 : List Nat := [1, 2, 1, 1, 1, 6, 4, 1, 2, 2, 2]
def baseStart_4697193 : Nat := 118140960795 + 4697193 * 2 ^ 59
def prefixEnd_4697193 : Nat := 4983230072969 + 3 ^ 40 * 4697193 * 2
def baseEnd_4697193 : Nat := 2411917735934545944485509

theorem tailTrace_4697193 : CollatzResearch.WordTrace tailWord_4697193 prefixEnd_4697193 2411917735934545944485509 := by
  unfold tailWord_4697193
  simp only [CollatzResearch.WordTrace]
  refine ⟨171320703271879452541776233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114213802181252968361184155 171320703271879452541776233)
  ·
    refine ⟨128490527453909589406332175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171320703271879452541776233 128490527453909589406332175)
    ·
      refine ⟨192735791180864384109498263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128490527453909589406332175 192735791180864384109498263)
      ·
        refine ⟨289103686771296576164247395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192735791180864384109498263 289103686771296576164247395)
        ·
          refine ⟨433655530156944864246371093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 289103686771296576164247395 433655530156944864246371093)
          ·
            refine ⟨20327602976106790511548645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 433655530156944864246371093 20327602976106790511548645)
            ·
              refine ⟨3811425558020023220915371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20327602976106790511548645 3811425558020023220915371)
              ·
                refine ⟨5717138337030034831373057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3811425558020023220915371 5717138337030034831373057)
                ·
                  refine ⟨4287853752772526123529793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5717138337030034831373057 4287853752772526123529793)
                  ·
                    refine ⟨3215890314579394592647345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4287853752772526123529793 3215890314579394592647345)
                    ·
                      refine ⟨2411917735934545944485509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3215890314579394592647345 2411917735934545944485509)
                      ·
                        rfl

theorem cell23_4697193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 4, 1, 2, 2, 2].length) (baseStart_4697193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4697193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4697193 prefixEnd_4697193 := by exact prefixLift 4697193
  have htrace : WordTrace (prefixWord ++ tailWord_4697193) baseStart_4697193 baseEnd_4697193 := by
    simpa [prefixWord, tailWord_4697193, baseEnd_4697193] using wordTrace_append hprefix tailTrace_4697193
  have hstable : (prefixWord ++ tailWord_4697193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4697193).length < 2 ^ (prefixWord ++ tailWord_4697193).sum := by decide
  have hdescent : baseEnd_4697193 < baseStart_4697193 := by decide
  rcases family_descends (prefixWord ++ tailWord_4697193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4697214 : List Nat := [4, 2, 4, 1, 1, 1, 3, 1, 1, 3, 2]
def baseStart_4697214 : Nat := 118140960795 + 4697214 * 2 ^ 59
def prefixEnd_4697214 : Nat := 4983230072969 + 3 ^ 40 * 4697214 * 2
def baseEnd_4697214 : Nat := 2411928519028290362322913

theorem tailTrace_4697214 : CollatzResearch.WordTrace tailWord_4697214 prefixEnd_4697214 2411928519028290362322913 := by
  unfold tailWord_4697214
  simp only [CollatzResearch.WordTrace]
  refine ⟨21415183650600421641036337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 114214312803202248752193797 21415183650600421641036337)
  ·
    refine ⟨16061387737950316230777253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21415183650600421641036337 16061387737950316230777253)
    ·
      refine ⟨3011510200865684293270735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16061387737950316230777253 3011510200865684293270735)
      ·
        refine ⟨4517265301298526439906103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3011510200865684293270735 4517265301298526439906103)
        ·
          refine ⟨6775897951947789659859155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4517265301298526439906103 6775897951947789659859155)
          ·
            refine ⟨10163846927921684489788733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6775897951947789659859155 10163846927921684489788733)
            ·
              refine ⟨3811442597970631683670775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10163846927921684489788733 3811442597970631683670775)
              ·
                refine ⟨5717163896955947525506163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3811442597970631683670775 5717163896955947525506163)
                ·
                  refine ⟨8575745845433921288259245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5717163896955947525506163 8575745845433921288259245)
                  ·
                    refine ⟨3215904692037720483097217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8575745845433921288259245 3215904692037720483097217)
                    ·
                      refine ⟨2411928519028290362322913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3215904692037720483097217 2411928519028290362322913)
                      ·
                        rfl

theorem cell23_4697214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 3, 1, 1, 3, 2].length) (baseStart_4697214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4697214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4697214 prefixEnd_4697214 := by exact prefixLift 4697214
  have htrace : WordTrace (prefixWord ++ tailWord_4697214) baseStart_4697214 baseEnd_4697214 := by
    simpa [prefixWord, tailWord_4697214, baseEnd_4697214] using wordTrace_append hprefix tailTrace_4697214
  have hstable : (prefixWord ++ tailWord_4697214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4697214).length < 2 ^ (prefixWord ++ tailWord_4697214).sum := by decide
  have hdescent : baseEnd_4697214 < baseStart_4697214 := by decide
  rcases family_descends (prefixWord ++ tailWord_4697214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4697232 : List Nat := [2, 1, 1, 1, 1, 1, 4, 3, 4, 1, 4]
def baseStart_4697232 : Nat := 118140960795 + 4697232 * 2 ^ 59
def prefixEnd_4697232 : Nat := 4983230072969 + 3 ^ 40 * 4697232 * 2
def baseEnd_4697232 : Nat := 2411937761680071291897829

theorem tailTrace_4697232 : CollatzResearch.WordTrace tailWord_4697232 prefixEnd_4697232 2411937761680071291897829 := by
  unfold tailWord_4697232
  simp only [CollatzResearch.WordTrace]
  refine ⟨85661062859369081101222975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114214750479158774801630633 85661062859369081101222975)
  ·
    refine ⟨128491594289053621651834463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85661062859369081101222975 128491594289053621651834463)
    ·
      refine ⟨192737391433580432477751695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128491594289053621651834463 192737391433580432477751695)
      ·
        refine ⟨289106087150370648716627543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192737391433580432477751695 289106087150370648716627543)
        ·
          refine ⟨433659130725555973074941315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 289106087150370648716627543 433659130725555973074941315)
          ·
            refine ⟨650488696088333959612411973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 433659130725555973074941315 650488696088333959612411973)
            ·
              refine ⟨121966630516562617427327245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 650488696088333959612411973 121966630516562617427327245)
              ·
                refine ⟨45737486443710981535247717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 121966630516562617427327245 45737486443710981535247717)
                ·
                  refine ⟨8575778708195809037858947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45737486443710981535247717 8575778708195809037858947)
                  ·
                    refine ⟨12863668062293713556788421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8575778708195809037858947 12863668062293713556788421)
                    ·
                      refine ⟨2411937761680071291897829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12863668062293713556788421 2411937761680071291897829)
                      ·
                        rfl

theorem cell23_4697232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 3, 4, 1, 4].length) (baseStart_4697232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4697232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4697232 prefixEnd_4697232 := by exact prefixLift 4697232
  have htrace : WordTrace (prefixWord ++ tailWord_4697232) baseStart_4697232 baseEnd_4697232 := by
    simpa [prefixWord, tailWord_4697232, baseEnd_4697232] using wordTrace_append hprefix tailTrace_4697232
  have hstable : (prefixWord ++ tailWord_4697232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4697232).length < 2 ^ (prefixWord ++ tailWord_4697232).sum := by decide
  have hdescent : baseEnd_4697232 < baseStart_4697232 := by decide
  rcases family_descends (prefixWord ++ tailWord_4697232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4697266 : List Nat := [3, 2, 1, 1, 1, 6, 1, 1, 2, 1, 4]
def baseStart_4697266 : Nat := 118140960795 + 4697266 * 2 ^ 59
def prefixEnd_4697266 : Nat := 4983230072969 + 3 ^ 40 * 4697266 * 2
def baseEnd_4697266 : Nat := 2411955220022324158872673

theorem tailTrace_4697266 : CollatzResearch.WordTrace tailWord_4697266 prefixEnd_4697266 2411955220022324158872673 := by
  unfold tailWord_4697266
  simp only [CollatzResearch.WordTrace]
  refine ⟨42830841450153746502295913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114215577200409990672789101 42830841450153746502295913)
  ·
    refine ⟨32123131087615309876721935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42830841450153746502295913 32123131087615309876721935)
    ·
      refine ⟨48184696631422964815082903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32123131087615309876721935 48184696631422964815082903)
      ·
        refine ⟨72277044947134447222624355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48184696631422964815082903 72277044947134447222624355)
        ·
          refine ⟨108415567420701670833936533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72277044947134447222624355 108415567420701670833936533)
          ·
            refine ⟨5081979722845390820340775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 108415567420701670833936533 5081979722845390820340775)
            ·
              refine ⟨7622969584268086230511163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5081979722845390820340775 7622969584268086230511163)
              ·
                refine ⟨11434454376402129345766745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7622969584268086230511163 11434454376402129345766745)
                ·
                  refine ⟨8575840782301597009325059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11434454376402129345766745 8575840782301597009325059)
                  ·
                    refine ⟨12863761173452395513987589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8575840782301597009325059 12863761173452395513987589)
                    ·
                      refine ⟨2411955220022324158872673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12863761173452395513987589 2411955220022324158872673)
                      ·
                        rfl

theorem cell23_4697266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 1, 1, 2, 1, 4].length) (baseStart_4697266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4697266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4697266 prefixEnd_4697266 := by exact prefixLift 4697266
  have htrace : WordTrace (prefixWord ++ tailWord_4697266) baseStart_4697266 baseEnd_4697266 := by
    simpa [prefixWord, tailWord_4697266, baseEnd_4697266] using wordTrace_append hprefix tailTrace_4697266
  have hstable : (prefixWord ++ tailWord_4697266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4697266).length < 2 ^ (prefixWord ++ tailWord_4697266).sum := by decide
  have hdescent : baseEnd_4697266 < baseStart_4697266 := by decide
  rcases family_descends (prefixWord ++ tailWord_4697266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4697299 : List Nat := [1, 1, 1, 2, 1, 1, 1, 4, 7, 1, 3]
def baseStart_4697299 : Nat := 118140960795 + 4697299 * 2 ^ 59
def prefixEnd_4697299 : Nat := 4983230072969 + 3 ^ 40 * 4697299 * 2
def baseEnd_4697299 : Nat := 2411972164883922529760021

theorem tailTrace_4697299 : CollatzResearch.WordTrace tailWord_4697299 prefixEnd_4697299 2411972164883922529760021 := by
  unfold tailWord_4697299
  simp only [CollatzResearch.WordTrace]
  refine ⟨171324569409495432645134951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114216379606330288430089967 171324569409495432645134951)
  ·
    refine ⟨256986854114243148967702427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171324569409495432645134951 256986854114243148967702427)
    ·
      refine ⟨385480281171364723451553641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 256986854114243148967702427 385480281171364723451553641)
      ·
        refine ⟨289110210878523542588665231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 385480281171364723451553641 289110210878523542588665231)
        ·
          refine ⟨433665316317785313882997847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 289110210878523542588665231 433665316317785313882997847)
          ·
            refine ⟨650497974476677970824496771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 433665316317785313882997847 650497974476677970824496771)
            ·
              refine ⟨975746961715016956236745157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 650497974476677970824496771 975746961715016956236745157)
              ·
                refine ⟨182952555321565679294389717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 975746961715016956236745157 182952555321565679294389717)
                ·
                  refine ⟨4287950515349195608462259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 182952555321565679294389717 4287950515349195608462259)
                  ·
                    refine ⟨6431925773023793412693389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4287950515349195608462259 6431925773023793412693389)
                    ·
                      refine ⟨2411972164883922529760021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6431925773023793412693389 2411972164883922529760021)
                      ·
                        rfl

theorem cell23_4697299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 7, 1, 3].length) (baseStart_4697299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4697299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4697299 prefixEnd_4697299 := by exact prefixLift 4697299
  have htrace : WordTrace (prefixWord ++ tailWord_4697299) baseStart_4697299 baseEnd_4697299 := by
    simpa [prefixWord, tailWord_4697299, baseEnd_4697299] using wordTrace_append hprefix tailTrace_4697299
  have hstable : (prefixWord ++ tailWord_4697299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4697299).length < 2 ^ (prefixWord ++ tailWord_4697299).sum := by decide
  have hdescent : baseEnd_4697299 < baseStart_4697299 := by decide
  rcases family_descends (prefixWord ++ tailWord_4697299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4697316 : List Nat := [2, 3, 1, 1, 1, 2, 4, 2, 3, 1, 3]
def baseStart_4697316 : Nat := 118140960795 + 4697316 * 2 ^ 59
def prefixEnd_4697316 : Nat := 4983230072969 + 3 ^ 40 * 4697316 * 2
def baseEnd_4697316 : Nat := 2411980894055048963247443

theorem tailTrace_4697316 : CollatzResearch.WordTrace tailWord_4697316 prefixEnd_4697316 2411980894055048963247443 := by
  unfold tailWord_4697316
  simp only [CollatzResearch.WordTrace]
  refine ⟨85662594725216922274251901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114216792966955896365669201 85662594725216922274251901)
  ·
    refine ⟨32123473021956345852844463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85662594725216922274251901 32123473021956345852844463)
    ·
      refine ⟨48185209532934518779266695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32123473021956345852844463 48185209532934518779266695)
      ·
        refine ⟨72277814299401778168900043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48185209532934518779266695 72277814299401778168900043)
        ·
          refine ⟨108416721449102667253350065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72277814299401778168900043 108416721449102667253350065)
          ·
            refine ⟨81312541086827000440012549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 108416721449102667253350065 81312541086827000440012549)
            ·
              refine ⟨15246101453780062582502353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 81312541086827000440012549 15246101453780062582502353)
              ·
                refine ⟨11434576090335046936876765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15246101453780062582502353 11434576090335046936876765)
                ·
                  refine ⟨4287966033875642601328787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11434576090335046936876765 4287966033875642601328787)
                  ·
                    refine ⟨6431949050813463901993181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4287966033875642601328787 6431949050813463901993181)
                    ·
                      refine ⟨2411980894055048963247443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6431949050813463901993181 2411980894055048963247443)
                      ·
                        rfl

theorem cell23_4697316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 2, 3, 1, 3].length) (baseStart_4697316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4697316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4697316 prefixEnd_4697316 := by exact prefixLift 4697316
  have htrace : WordTrace (prefixWord ++ tailWord_4697316) baseStart_4697316 baseEnd_4697316 := by
    simpa [prefixWord, tailWord_4697316, baseEnd_4697316] using wordTrace_append hprefix tailTrace_4697316
  have hstable : (prefixWord ++ tailWord_4697316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4697316).length < 2 ^ (prefixWord ++ tailWord_4697316).sum := by decide
  have hdescent : baseEnd_4697316 < baseStart_4697316 := by decide
  rcases family_descends (prefixWord ++ tailWord_4697316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4697326 : List Nat := [4, 1, 2, 1, 1, 1, 4, 1, 1, 5, 2]
def baseStart_4697326 : Nat := 118140960795 + 4697326 * 2 ^ 59
def prefixEnd_4697326 : Nat := 4983230072969 + 3 ^ 40 * 4697326 * 2
def baseEnd_4697326 : Nat := 2411986028861593924122397

theorem tailTrace_4697326 : CollatzResearch.WordTrace tailWord_4697326 prefixEnd_4697326 2411986028861593924122397 := by
  unfold tailWord_4697326
  simp only [CollatzResearch.WordTrace]
  refine ⟨21415694272549702032045979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 114217036120265077504245221 21415694272549702032045979)
  ·
    refine ⟨32123541408824553048068969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21415694272549702032045979 32123541408824553048068969)
    ·
      refine ⟨24092656056618414786051727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32123541408824553048068969 24092656056618414786051727)
      ·
        refine ⟨36138984084927622179077591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24092656056618414786051727 36138984084927622179077591)
        ·
          refine ⟨54208476127391433268616387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36138984084927622179077591 54208476127391433268616387)
          ·
            refine ⟨81312714191087149902924581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54208476127391433268616387 81312714191087149902924581)
            ·
              refine ⟨15246133910828840606798359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 81312714191087149902924581 15246133910828840606798359)
              ·
                refine ⟨22869200866243260910197539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15246133910828840606798359 22869200866243260910197539)
                ·
                  refine ⟨34303801299364891365296309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22869200866243260910197539 34303801299364891365296309)
                  ·
                    refine ⟨3215981371815458565496529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34303801299364891365296309 3215981371815458565496529)
                    ·
                      refine ⟨2411986028861593924122397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3215981371815458565496529 2411986028861593924122397)
                      ·
                        rfl

theorem cell23_4697326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 1, 1, 5, 2].length) (baseStart_4697326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4697326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4697326 prefixEnd_4697326 := by exact prefixLift 4697326
  have htrace : WordTrace (prefixWord ++ tailWord_4697326) baseStart_4697326 baseEnd_4697326 := by
    simpa [prefixWord, tailWord_4697326, baseEnd_4697326] using wordTrace_append hprefix tailTrace_4697326
  have hstable : (prefixWord ++ tailWord_4697326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4697326).length < 2 ^ (prefixWord ++ tailWord_4697326).sum := by decide
  have hdescent : baseEnd_4697326 < baseStart_4697326 := by decide
  rcases family_descends (prefixWord ++ tailWord_4697326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4697349 : List Nat := [1, 3, 1, 1, 2, 1, 3, 3, 4, 4]
def baseStart_4697349 : Nat := 118140960795 + 4697349 * 2 ^ 59
def prefixEnd_4697349 : Nat := 4983230072969 + 3 ^ 40 * 4697349 * 2
def baseEnd_4697349 : Nat := 803999279638882444711597

theorem tailTrace_4697349 : CollatzResearch.WordTrace tailWord_4697349 prefixEnd_4697349 803999279638882444711597 := by
  unfold tailWord_4697349
  simp only [CollatzResearch.WordTrace]
  refine ⟨171326393059314291184455101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114217595372876194122970067 171326393059314291184455101)
  ·
    refine ⟨64247397397242859194170663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 171326393059314291184455101 64247397397242859194170663)
    ·
      refine ⟨96371096095864288791255995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64247397397242859194170663 96371096095864288791255995)
      ·
        refine ⟨144556644143796433186883993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96371096095864288791255995 144556644143796433186883993)
        ·
          refine ⟨108417483107847324890162995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 144556644143796433186883993 108417483107847324890162995)
          ·
            refine ⟨162626224661770987335244493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108417483107847324890162995 162626224661770987335244493)
            ·
              refine ⟨60984834248164120250716685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 162626224661770987335244493 60984834248164120250716685)
              ·
                refine ⟨22869312843061545094018757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 60984834248164120250716685 22869312843061545094018757)
                ·
                  refine ⟨4287996158074039705128517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22869312843061545094018757 4287996158074039705128517)
                  ·
                    refine ⟨803999279638882444711597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4287996158074039705128517 803999279638882444711597)
                    ·
                      rfl

theorem cell23_4697349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 3, 4, 4].length) (baseStart_4697349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4697349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4697349 prefixEnd_4697349 := by exact prefixLift 4697349
  have htrace : WordTrace (prefixWord ++ tailWord_4697349) baseStart_4697349 baseEnd_4697349 := by
    simpa [prefixWord, tailWord_4697349, baseEnd_4697349] using wordTrace_append hprefix tailTrace_4697349
  have hstable : (prefixWord ++ tailWord_4697349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4697349).length < 2 ^ (prefixWord ++ tailWord_4697349).sum := by decide
  have hdescent : baseEnd_4697349 < baseStart_4697349 := by decide
  rcases family_descends (prefixWord ++ tailWord_4697349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4697373 : List Nat := [1, 4, 2, 3, 1, 1, 3, 2, 1, 1, 4]
def baseStart_4697373 : Nat := 118140960795 + 4697373 * 2 ^ 59
def prefixEnd_4697373 : Nat := 4983230072969 + 3 ^ 40 * 4697373 * 2
def baseEnd_4697373 : Nat := 2412010162452355240234681

theorem tailTrace_4697373 : CollatzResearch.WordTrace tailWord_4697373 prefixEnd_4697373 2412010162452355240234681 := by
  unfold tailWord_4697373
  simp only [CollatzResearch.WordTrace]
  refine ⟨171327268411227343283328773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114218178940818228855552515 171327268411227343283328773)
  ·
    refine ⟨32123862827105126865624145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 171327268411227343283328773 32123862827105126865624145)
    ·
      refine ⟨24092897120328845149218109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32123862827105126865624145 24092897120328845149218109)
      ·
        refine ⟨9034836420123316930956791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24092897120328845149218109 9034836420123316930956791)
        ·
          refine ⟨13552254630184975396435187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9034836420123316930956791 13552254630184975396435187)
          ·
            refine ⟨20328381945277463094652781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13552254630184975396435187 20328381945277463094652781)
            ·
              refine ⟨7623143229479048660494793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20328381945277463094652781 7623143229479048660494793)
              ·
                refine ⟨5717357422109286495371095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7623143229479048660494793 5717357422109286495371095)
                ·
                  refine ⟨8576036133163929743056643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5717357422109286495371095 8576036133163929743056643)
                  ·
                    refine ⟨12864054199745894614584965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8576036133163929743056643 12864054199745894614584965)
                    ·
                      refine ⟨2412010162452355240234681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12864054199745894614584965 2412010162452355240234681)
                      ·
                        rfl

theorem cell23_4697373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 3, 2, 1, 1, 4].length) (baseStart_4697373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4697373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4697373 prefixEnd_4697373 := by exact prefixLift 4697373
  have htrace : WordTrace (prefixWord ++ tailWord_4697373) baseStart_4697373 baseEnd_4697373 := by
    simpa [prefixWord, tailWord_4697373, baseEnd_4697373] using wordTrace_append hprefix tailTrace_4697373
  have hstable : (prefixWord ++ tailWord_4697373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4697373).length < 2 ^ (prefixWord ++ tailWord_4697373).sum := by decide
  have hdescent : baseEnd_4697373 < baseStart_4697373 := by decide
  rcases family_descends (prefixWord ++ tailWord_4697373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4697386 : List Nat := [3, 1, 4, 2, 1, 1, 1, 1, 3, 2, 4]
def baseStart_4697386 : Nat := 118140960795 + 4697386 * 2 ^ 59
def prefixEnd_4697386 : Nat := 4983230072969 + 3 ^ 40 * 4697386 * 2
def baseEnd_4697386 : Nat := 2412016837700863689372121

theorem tailTrace_4697386 : CollatzResearch.WordTrace tailWord_4697386 prefixEnd_4697386 2412016837700863689372121 := by
  unfold tailWord_4697386
  simp only [CollatzResearch.WordTrace]
  refine ⟨42831935640045061625888003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114218495040120164335701341 42831935640045061625888003)
  ·
    refine ⟨64247903460067592438832005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42831935640045061625888003 64247903460067592438832005)
    ·
      refine ⟨12046481898762673582281001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64247903460067592438832005 12046481898762673582281001)
      ·
        refine ⟨9034861424072005186710751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12046481898762673582281001 9034861424072005186710751)
        ·
          refine ⟨13552292136108007780066127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9034861424072005186710751 13552292136108007780066127)
          ·
            refine ⟨20328438204162011670099191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13552292136108007780066127 20328438204162011670099191)
            ·
              refine ⟨30492657306243017505148787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20328438204162011670099191 30492657306243017505148787)
              ·
                refine ⟨45738985959364526257723181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30492657306243017505148787 45738985959364526257723181)
                ·
                  refine ⟨17152119734761697346646193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45738985959364526257723181 17152119734761697346646193)
                  ·
                    refine ⟨12864089801071273009984645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17152119734761697346646193 12864089801071273009984645)
                    ·
                      refine ⟨2412016837700863689372121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12864089801071273009984645 2412016837700863689372121)
                      ·
                        rfl

theorem cell23_4697386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_4697386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4697386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4697386 prefixEnd_4697386 := by exact prefixLift 4697386
  have htrace : WordTrace (prefixWord ++ tailWord_4697386) baseStart_4697386 baseEnd_4697386 := by
    simpa [prefixWord, tailWord_4697386, baseEnd_4697386] using wordTrace_append hprefix tailTrace_4697386
  have hstable : (prefixWord ++ tailWord_4697386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4697386).length < 2 ^ (prefixWord ++ tailWord_4697386).sum := by decide
  have hdescent : baseEnd_4697386 < baseStart_4697386 := by decide
  rcases family_descends (prefixWord ++ tailWord_4697386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4697406 : List Nat := [4, 2, 1, 2, 1, 1, 1, 2, 3, 3, 3]
def baseStart_4697406 : Nat := 118140960795 + 4697406 * 2 ^ 59
def prefixEnd_4697406 : Nat := 4983230072969 + 3 ^ 40 * 4697406 * 2
def baseEnd_4697406 : Nat := 2412027107313953611122029

theorem tailTrace_4697406 : CollatzResearch.WordTrace tailWord_4697406 prefixEnd_4697406 2412027107313953611122029 := by
  unfold tailWord_4697406
  simp only [CollatzResearch.WordTrace]
  refine ⟨21416059002513473739910009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 114218981346738526612853381 21416059002513473739910009)
  ·
    refine ⟨16062044251885105304932507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21416059002513473739910009 16062044251885105304932507)
    ·
      refine ⟨24093066377827657957398761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16062044251885105304932507 24093066377827657957398761)
      ·
        refine ⟨18069799783370743468049071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24093066377827657957398761 18069799783370743468049071)
        ·
          refine ⟨27104699675056115202073607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18069799783370743468049071 27104699675056115202073607)
          ·
            refine ⟨40657049512584172803110411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27104699675056115202073607 40657049512584172803110411)
            ·
              refine ⟨60985574268876259204665617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40657049512584172803110411 60985574268876259204665617)
              ·
                refine ⟨45739180701657194403499213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60985574268876259204665617 45739180701657194403499213)
                ·
                  refine ⟨17152192763121447901312205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45739180701657194403499213 17152192763121447901312205)
                  ·
                    refine ⟨6432072286170542962992077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17152192763121447901312205 6432072286170542962992077)
                    ·
                      refine ⟨2412027107313953611122029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6432072286170542962992077 2412027107313953611122029)
                      ·
                        rfl

theorem cell23_4697406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 2, 3, 3, 3].length) (baseStart_4697406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4697406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4697406 prefixEnd_4697406 := by exact prefixLift 4697406
  have htrace : WordTrace (prefixWord ++ tailWord_4697406) baseStart_4697406 baseEnd_4697406 := by
    simpa [prefixWord, tailWord_4697406, baseEnd_4697406] using wordTrace_append hprefix tailTrace_4697406
  have hstable : (prefixWord ++ tailWord_4697406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4697406).length < 2 ^ (prefixWord ++ tailWord_4697406).sum := by decide
  have hdescent : baseEnd_4697406 < baseStart_4697406 := by decide
  rcases family_descends (prefixWord ++ tailWord_4697406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4697407 : List Nat := [1, 1, 2, 2, 4, 2, 4, 2, 1, 2, 2]
def baseStart_4697407 : Nat := 118140960795 + 4697407 * 2 ^ 59
def prefixEnd_4697407 : Nat := 4983230072969 + 3 ^ 40 * 4697407 * 2
def baseEnd_4697407 : Nat := 2412027620794608107209525

theorem tailTrace_4697407 : CollatzResearch.WordTrace tailWord_4697407 prefixEnd_4697407 2412027620794608107209525 := by
  unfold tailWord_4697407
  simp only [CollatzResearch.WordTrace]
  refine ⟨171328508493104167090066475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114219005662069444726710983 171328508493104167090066475)
  ·
    refine ⟨256992762739656250635099713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171328508493104167090066475 256992762739656250635099713)
    ·
      refine ⟨192744572054742187976324785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 256992762739656250635099713 192744572054742187976324785)
      ·
        refine ⟨144558429041056640982243589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 192744572054742187976324785 144558429041056640982243589)
        ·
          refine ⟨27104705445198120184170673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 144558429041056640982243589 27104705445198120184170673)
          ·
            refine ⟨20328529083898590138128005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27104705445198120184170673 20328529083898590138128005)
            ·
              refine ⟨3811599203230985650899001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20328529083898590138128005 3811599203230985650899001)
              ·
                refine ⟨2858699402423239238174251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3811599203230985650899001 2858699402423239238174251)
                ·
                  refine ⟨4288049103634858857261377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2858699402423239238174251 4288049103634858857261377)
                  ·
                    refine ⟨3216036827726144142946033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4288049103634858857261377 3216036827726144142946033)
                    ·
                      refine ⟨2412027620794608107209525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3216036827726144142946033 2412027620794608107209525)
                      ·
                        rfl

theorem cell23_4697407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 4, 2, 1, 2, 2].length) (baseStart_4697407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4697407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4697407 prefixEnd_4697407 := by exact prefixLift 4697407
  have htrace : WordTrace (prefixWord ++ tailWord_4697407) baseStart_4697407 baseEnd_4697407 := by
    simpa [prefixWord, tailWord_4697407, baseEnd_4697407] using wordTrace_append hprefix tailTrace_4697407
  have hstable : (prefixWord ++ tailWord_4697407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4697407).length < 2 ^ (prefixWord ++ tailWord_4697407).sum := by decide
  have hdescent : baseEnd_4697407 < baseStart_4697407 := by decide
  rcases family_descends (prefixWord ++ tailWord_4697407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4697449 : List Nat := [1, 2, 1, 1, 1, 3, 2, 2, 1, 6, 3]
def baseStart_4697449 : Nat := 118140960795 + 4697449 * 2 ^ 59
def prefixEnd_4697449 : Nat := 4983230072969 + 3 ^ 40 * 4697449 * 2
def baseEnd_4697449 : Nat := 2412049186982096942884331

theorem tailTrace_4697449 : CollatzResearch.WordTrace tailWord_4697449 prefixEnd_4697449 2412049186982096942884331 := by
  unfold tailWord_4697449
  simp only [CollatzResearch.WordTrace]
  refine ⟨171330040358952008263095401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114220026905968005508730267 171330040358952008263095401)
  ·
    refine ⟨128497530269214006197321551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171330040358952008263095401 128497530269214006197321551)
    ·
      refine ⟨192746295403821009295982327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128497530269214006197321551 192746295403821009295982327)
      ·
        refine ⟨289119443105731513943973491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192746295403821009295982327 289119443105731513943973491)
        ·
          refine ⟨433679164658597270915960237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 289119443105731513943973491 433679164658597270915960237)
          ·
            refine ⟨162629686746973976593485089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 433679164658597270915960237 162629686746973976593485089)
            ·
              refine ⟨121972265060230482445113817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 162629686746973976593485089 121972265060230482445113817)
              ·
                refine ⟨91479198795172861833835363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 121972265060230482445113817 91479198795172861833835363)
                ·
                  refine ⟨137218798192759292750753045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 91479198795172861833835363 137218798192759292750753045)
                  ·
                    refine ⟨6432131165285591847691549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 137218798192759292750753045 6432131165285591847691549)
                    ·
                      refine ⟨2412049186982096942884331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6432131165285591847691549 2412049186982096942884331)
                      ·
                        rfl

theorem cell23_4697449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 2, 1, 6, 3].length) (baseStart_4697449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4697449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4697449 prefixEnd_4697449 := by exact prefixLift 4697449
  have htrace : WordTrace (prefixWord ++ tailWord_4697449) baseStart_4697449 baseEnd_4697449 := by
    simpa [prefixWord, tailWord_4697449, baseEnd_4697449] using wordTrace_append hprefix tailTrace_4697449
  have hstable : (prefixWord ++ tailWord_4697449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4697449).length < 2 ^ (prefixWord ++ tailWord_4697449).sum := by decide
  have hdescent : baseEnd_4697449 < baseStart_4697449 := by decide
  rcases family_descends (prefixWord ++ tailWord_4697449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4697463 : List Nat := [1, 1, 3, 1, 1, 2, 5, 1, 4, 2, 2]
def baseStart_4697463 : Nat := 118140960795 + 4697463 * 2 ^ 59
def prefixEnd_4697463 : Nat := 4983230072969 + 3 ^ 40 * 4697463 * 2
def baseEnd_4697463 : Nat := 2412056375711259888109267

theorem tailTrace_4697463 : CollatzResearch.WordTrace tailWord_4697463 prefixEnd_4697463 2412056375711259888109267 := by
  unfold tailWord_4697463
  simp only [CollatzResearch.WordTrace]
  refine ⟨171330550980901288654105043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114220367320600859102736695 171330550980901288654105043)
  ·
    refine ⟨256995826471351932981157565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171330550980901288654105043 256995826471351932981157565)
    ·
      refine ⟨96373434926756974867934087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 256995826471351932981157565 96373434926756974867934087)
      ·
        refine ⟨144560152390135462301901131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96373434926756974867934087 144560152390135462301901131)
        ·
          refine ⟨216840228585203193452851697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144560152390135462301901131 216840228585203193452851697)
          ·
            refine ⟨162630171438902395089638773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 216840228585203193452851697 162630171438902395089638773)
            ·
              refine ⟨15246578572397099539653635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 162630171438902395089638773 15246578572397099539653635)
              ·
                refine ⟨22869867858595649309480453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15246578572397099539653635 22869867858595649309480453)
                ·
                  refine ⟨4288100223486684245527585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22869867858595649309480453 4288100223486684245527585)
                  ·
                    refine ⟨3216075167615013184145689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4288100223486684245527585 3216075167615013184145689)
                    ·
                      refine ⟨2412056375711259888109267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3216075167615013184145689 2412056375711259888109267)
                      ·
                        rfl

theorem cell23_4697463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 1, 4, 2, 2].length) (baseStart_4697463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4697463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4697463 prefixEnd_4697463 := by exact prefixLift 4697463
  have htrace : WordTrace (prefixWord ++ tailWord_4697463) baseStart_4697463 baseEnd_4697463 := by
    simpa [prefixWord, tailWord_4697463, baseEnd_4697463] using wordTrace_append hprefix tailTrace_4697463
  have hstable : (prefixWord ++ tailWord_4697463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4697463).length < 2 ^ (prefixWord ++ tailWord_4697463).sum := by decide
  have hdescent : baseEnd_4697463 < baseStart_4697463 := by decide
  rcases family_descends (prefixWord ++ tailWord_4697463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4697474 : List Nat := [3, 4, 2, 1, 1, 2, 3, 1, 2, 1, 3]
def baseStart_4697474 : Nat := 118140960795 + 4697474 * 2 ^ 59
def prefixEnd_4697474 : Nat := 4983230072969 + 3 ^ 40 * 4697474 * 2
def baseEnd_4697474 : Nat := 2412062023998459345071717

theorem tailTrace_4697474 : CollatzResearch.WordTrace tailWord_4697474 prefixEnd_4697474 2412062023998459345071717 := by
  unfold tailWord_4697474
  simp only [CollatzResearch.WordTrace]
  refine ⟨42832738045965359383188869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114220634789240958355170317 42832738045965359383188869)
  ·
    refine ⟨8031138383618504884347913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42832738045965359383188869 8031138383618504884347913)
    ·
      refine ⟨6023353787713878663260935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8031138383618504884347913 6023353787713878663260935)
      ·
        refine ⟨9035030681570817994891403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6023353787713878663260935 9035030681570817994891403)
        ·
          refine ⟨13552546022356226992337105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9035030681570817994891403 13552546022356226992337105)
          ·
            refine ⟨10164409516767170244252829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13552546022356226992337105 10164409516767170244252829)
            ·
              refine ⟨3811653568787688841594811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10164409516767170244252829 3811653568787688841594811)
              ·
                refine ⟨5717480353181533262392217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3811653568787688841594811 5717480353181533262392217)
                ·
                  refine ⟨4288110264886149946794163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5717480353181533262392217 4288110264886149946794163)
                  ·
                    refine ⟨6432165397329224920191245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4288110264886149946794163 6432165397329224920191245)
                    ·
                      refine ⟨2412062023998459345071717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6432165397329224920191245 2412062023998459345071717)
                      ·
                        rfl

theorem cell23_4697474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 3, 1, 2, 1, 3].length) (baseStart_4697474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4697474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4697474 prefixEnd_4697474 := by exact prefixLift 4697474
  have htrace : WordTrace (prefixWord ++ tailWord_4697474) baseStart_4697474 baseEnd_4697474 := by
    simpa [prefixWord, tailWord_4697474, baseEnd_4697474] using wordTrace_append hprefix tailTrace_4697474
  have hstable : (prefixWord ++ tailWord_4697474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4697474).length < 2 ^ (prefixWord ++ tailWord_4697474).sum := by decide
  have hdescent : baseEnd_4697474 < baseStart_4697474 := by decide
  rcases family_descends (prefixWord ++ tailWord_4697474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4697476 : List Nat := [2, 3, 2, 1, 1, 3, 2, 1, 2, 2, 4]
def baseStart_4697476 : Nat := 118140960795 + 4697476 * 2 ^ 59
def prefixEnd_4697476 : Nat := 4983230072969 + 3 ^ 40 * 4697476 * 2
def baseEnd_4697476 : Nat := 2412063050959768337246707

theorem tailTrace_4697476 : CollatzResearch.WordTrace tailWord_4697476 prefixEnd_4697476 2412063050959768337246707 := by
  unfold tailWord_4697476
  simp only [CollatzResearch.WordTrace]
  refine ⟨85665512564927095937164141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114220683419902794582885521 85665512564927095937164141)
  ·
    refine ⟨32124567211847660976436553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85665512564927095937164141 32124567211847660976436553)
    ·
      refine ⟨24093425408885745732327415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32124567211847660976436553 24093425408885745732327415)
      ·
        refine ⟨36140138113328618598491123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24093425408885745732327415 36140138113328618598491123)
        ·
          refine ⟨54210207169992927897736685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36140138113328618598491123 54210207169992927897736685)
          ·
            refine ⟨20328827688747347961651257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54210207169992927897736685 20328827688747347961651257)
            ·
              refine ⟨15246620766560510971238443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20328827688747347961651257 15246620766560510971238443)
              ·
                refine ⟨22869931149840766456857665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15246620766560510971238443 22869931149840766456857665)
                ·
                  refine ⟨17152448362380574842643249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22869931149840766456857665 17152448362380574842643249)
                  ·
                    refine ⟨12864336271785431131982437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17152448362380574842643249 12864336271785431131982437)
                    ·
                      refine ⟨2412063050959768337246707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12864336271785431131982437 2412063050959768337246707)
                      ·
                        rfl

theorem cell23_4697476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 1, 2, 2, 4].length) (baseStart_4697476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4697476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4697476 prefixEnd_4697476 := by exact prefixLift 4697476
  have htrace : WordTrace (prefixWord ++ tailWord_4697476) baseStart_4697476 baseEnd_4697476 := by
    simpa [prefixWord, tailWord_4697476, baseEnd_4697476] using wordTrace_append hprefix tailTrace_4697476
  have hstable : (prefixWord ++ tailWord_4697476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4697476).length < 2 ^ (prefixWord ++ tailWord_4697476).sum := by decide
  have hdescent : baseEnd_4697476 < baseStart_4697476 := by decide
  rcases family_descends (prefixWord ++ tailWord_4697476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4697480 : List Nat := [2, 1, 3, 3, 1, 4, 1, 1, 1, 4, 2]
def baseStart_4697480 : Nat := 118140960795 + 4697480 * 2 ^ 59
def prefixEnd_4697480 : Nat := 4983230072969 + 3 ^ 40 * 4697480 * 2
def baseEnd_4697480 : Nat := 2412065104882386321596689

theorem tailTrace_4697480 : CollatzResearch.WordTrace tailWord_4697480 prefixEnd_4697480 2412065104882386321596689 := by
  unfold tailWord_4697480
  simp only [CollatzResearch.WordTrace]
  refine ⟨85665585510919850278736947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114220780681226467038315929 85665585510919850278736947)
  ·
    refine ⟨128498378266379775418105421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85665585510919850278736947 128498378266379775418105421)
    ·
      refine ⟨48186891849892415781789533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 128498378266379775418105421 48186891849892415781789533)
      ·
        refine ⟨18070084443709655918171075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48186891849892415781789533 18070084443709655918171075)
        ·
          refine ⟨27105126665564483877256613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18070084443709655918171075 27105126665564483877256613)
          ·
            refine ⟨5082211249793340726985615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27105126665564483877256613 5082211249793340726985615)
            ·
              refine ⟨7623316874690011090478423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5082211249793340726985615 7623316874690011090478423)
              ·
                refine ⟨11434975312035016635717635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7623316874690011090478423 11434975312035016635717635)
                ·
                  refine ⟨17152462968052524953576453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11434975312035016635717635 17152462968052524953576453)
                  ·
                    refine ⟨3216086806509848428795585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17152462968052524953576453 3216086806509848428795585)
                    ·
                      refine ⟨2412065104882386321596689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3216086806509848428795585 2412065104882386321596689)
                      ·
                        rfl

theorem cell23_4697480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 1, 1, 1, 4, 2].length) (baseStart_4697480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4697480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4697480 prefixEnd_4697480 := by exact prefixLift 4697480
  have htrace : WordTrace (prefixWord ++ tailWord_4697480) baseStart_4697480 baseEnd_4697480 := by
    simpa [prefixWord, tailWord_4697480, baseEnd_4697480] using wordTrace_append hprefix tailTrace_4697480
  have hstable : (prefixWord ++ tailWord_4697480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4697480).length < 2 ^ (prefixWord ++ tailWord_4697480).sum := by decide
  have hdescent : baseEnd_4697480 < baseStart_4697480 := by decide
  rcases family_descends (prefixWord ++ tailWord_4697480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4697503 : List Nat := [1, 1, 2, 5, 1, 2, 3, 3, 5]
def baseStart_4697503 : Nat := 118140960795 + 4697503 * 2 ^ 59
def prefixEnd_4697503 : Nat := 4983230072969 + 3 ^ 40 * 4697503 * 2
def baseEnd_4697503 : Nat := 268008546104159970178787

theorem tailTrace_4697503 : CollatzResearch.WordTrace tailWord_4697503 prefixEnd_4697503 268008546104159970178787 := by
  unfold tailWord_4697503
  simp only [CollatzResearch.WordTrace]
  refine ⟨171332009900756375485561163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114221339933837583657040775 171332009900756375485561163)
  ·
    refine ⟨256998014851134563228341745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171332009900756375485561163 256998014851134563228341745)
    ·
      refine ⟨192748511138350922421256309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 256998014851134563228341745 192748511138350922421256309)
      ·
        refine ⟨18070172919220398976992779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 192748511138350922421256309 18070172919220398976992779)
        ·
          refine ⟨27105259378830598465489169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18070172919220398976992779 27105259378830598465489169)
          ·
            refine ⟨20328944534122948849116877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27105259378830598465489169 20328944534122948849116877)
            ·
              refine ⟨7623354200296105818418829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20328944534122948849116877 7623354200296105818418829)
              ·
                refine ⟨2858757825111039681907061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7623354200296105818418829 2858757825111039681907061)
                ·
                  refine ⟨268008546104159970178787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2858757825111039681907061 268008546104159970178787)
                  ·
                    rfl

theorem cell23_4697503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 3, 3, 5].length) (baseStart_4697503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4697503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4697503 prefixEnd_4697503 := by exact prefixLift 4697503
  have htrace : WordTrace (prefixWord ++ tailWord_4697503) baseStart_4697503 baseEnd_4697503 := by
    simpa [prefixWord, tailWord_4697503, baseEnd_4697503] using wordTrace_append hprefix tailTrace_4697503
  have hstable : (prefixWord ++ tailWord_4697503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4697503).length < 2 ^ (prefixWord ++ tailWord_4697503).sum := by decide
  have hdescent : baseEnd_4697503 < baseStart_4697503 := by decide
  rcases family_descends (prefixWord ++ tailWord_4697503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4697559 : List Nat := [1, 1, 3, 2, 1, 1, 1, 3, 10]
def baseStart_4697559 : Nat := 118140960795 + 4697559 * 2 ^ 59
def prefixEnd_4697559 : Nat := 4983230072969 + 3 ^ 40 * 4697559 * 2
def baseEnd_4697559 : Nat := 268011741094899056945425

theorem tailTrace_4697559 : CollatzResearch.WordTrace tailWord_4697559 prefixEnd_4697559 268011741094899056945425 := by
  unfold tailWord_4697559
  simp only [CollatzResearch.WordTrace]
  refine ⟨171334052388553497049599731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114222701592368998033066487 171334052388553497049599731)
  ·
    refine ⟨257001078582830245574399597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171334052388553497049599731 257001078582830245574399597)
    ·
      refine ⟨96375404468561342090399849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 257001078582830245574399597 96375404468561342090399849)
      ·
        refine ⟨72281553351421006567799887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96375404468561342090399849 72281553351421006567799887)
        ·
          refine ⟨108422330027131509851699831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72281553351421006567799887 108422330027131509851699831)
          ·
            refine ⟨162633495040697264777549747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108422330027131509851699831 162633495040697264777549747)
            ·
              refine ⟨243950242561045897166324621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 162633495040697264777549747 243950242561045897166324621)
              ·
                refine ⟨91481340960392211437371733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 243950242561045897166324621 91481340960392211437371733)
                ·
                  refine ⟨268011741094899056945425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 91481340960392211437371733 268011741094899056945425)
                  ·
                    rfl

theorem cell23_4697559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 3, 10].length) (baseStart_4697559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4697559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4697559 prefixEnd_4697559 := by exact prefixLift 4697559
  have htrace : WordTrace (prefixWord ++ tailWord_4697559) baseStart_4697559 baseEnd_4697559 := by
    simpa [prefixWord, tailWord_4697559, baseEnd_4697559] using wordTrace_append hprefix tailTrace_4697559
  have hstable : (prefixWord ++ tailWord_4697559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4697559).length < 2 ^ (prefixWord ++ tailWord_4697559).sum := by decide
  have hdescent : baseEnd_4697559 < baseStart_4697559 := by decide
  rcases family_descends (prefixWord ++ tailWord_4697559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4697653 : List Nat := [1, 3, 3, 1, 1, 3, 3, 1, 1, 6]
def baseStart_4697653 : Nat := 118140960795 + 4697653 * 2 ^ 59
def prefixEnd_4697653 : Nat := 4983230072969 + 3 ^ 40 * 4697653 * 2
def baseEnd_4697653 : Nat := 804051312345204714911131

theorem tailTrace_4697653 : CollatzResearch.WordTrace tailWord_4697653 prefixEnd_4697653 804051312345204714911131 := by
  unfold tailWord_4697653
  simp only [CollatzResearch.WordTrace]
  refine ⟨171337480850212951103521613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114224987233475300735681075 171337480850212951103521613)
  ·
    refine ⟨64251555318829856663820605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 171337480850212951103521613 64251555318829856663820605)
    ·
      refine ⟨24094333244561196248932727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64251555318829856663820605 24094333244561196248932727)
      ·
        refine ⟨36141499866841794373399091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24094333244561196248932727 36141499866841794373399091)
        ·
          refine ⟨54212249800262691560098637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36141499866841794373399091 54212249800262691560098637)
          ·
            refine ⟨20329593675098509335036989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54212249800262691560098637 20329593675098509335036989)
            ·
              refine ⟨7623597628161941000638871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20329593675098509335036989 7623597628161941000638871)
              ·
                refine ⟨11435396442242911500958307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7623597628161941000638871 11435396442242911500958307)
                ·
                  refine ⟨17153094663364367251437461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11435396442242911500958307 17153094663364367251437461)
                  ·
                    refine ⟨804051312345204714911131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17153094663364367251437461 804051312345204714911131)
                    ·
                      rfl

theorem cell23_4697653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 3, 1, 1, 6].length) (baseStart_4697653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4697653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4697653 prefixEnd_4697653 := by exact prefixLift 4697653
  have htrace : WordTrace (prefixWord ++ tailWord_4697653) baseStart_4697653 baseEnd_4697653 := by
    simpa [prefixWord, tailWord_4697653, baseEnd_4697653] using wordTrace_append hprefix tailTrace_4697653
  have hstable : (prefixWord ++ tailWord_4697653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4697653).length < 2 ^ (prefixWord ++ tailWord_4697653).sum := by decide
  have hdescent : baseEnd_4697653 < baseStart_4697653 := by decide
  rcases family_descends (prefixWord ++ tailWord_4697653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4697671 : List Nat := [1, 1, 4, 1, 6, 1, 1, 3, 1, 1, 3]
def baseStart_4697671 : Nat := 118140960795 + 4697671 * 2 ^ 59
def prefixEnd_4697671 : Nat := 4983230072969 + 3 ^ 40 * 4697671 * 2
def baseEnd_4697671 : Nat := 2412163179687395074308311

theorem tailTrace_4697671 : CollatzResearch.WordTrace tailWord_4697671 prefixEnd_4697671 2412163179687395074308311 := by
  unfold tailWord_4697671
  simp only [CollatzResearch.WordTrace]
  refine ⟨171338137364147740177676867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114225424909431826785117911 171338137364147740177676867)
  ·
    refine ⟨257007206046221610266515301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171338137364147740177676867 257007206046221610266515301)
    ·
      refine ⟨48188851133666551924971619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 257007206046221610266515301 48188851133666551924971619)
      ·
        refine ⟨72283276700499827887457429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48188851133666551924971619 72283276700499827887457429)
        ·
          refine ⟨3388278595335929432224567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 72283276700499827887457429 3388278595335929432224567)
          ·
            refine ⟨5082417893003894148336851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3388278595335929432224567 5082417893003894148336851)
            ·
              refine ⟨7623626839505841222505277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5082417893003894148336851 7623626839505841222505277)
              ·
                refine ⟨2858860064814690458439479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7623626839505841222505277 2858860064814690458439479)
                ·
                  refine ⟨4288290097222035687659219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2858860064814690458439479 4288290097222035687659219)
                  ·
                    refine ⟨6432435145833053531488829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4288290097222035687659219 6432435145833053531488829)
                    ·
                      refine ⟨2412163179687395074308311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6432435145833053531488829 2412163179687395074308311)
                      ·
                        rfl

theorem cell23_4697671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 1, 3, 1, 1, 3].length) (baseStart_4697671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4697671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4697671 prefixEnd_4697671 := by exact prefixLift 4697671
  have htrace : WordTrace (prefixWord ++ tailWord_4697671) baseStart_4697671 baseEnd_4697671 := by
    simpa [prefixWord, tailWord_4697671, baseEnd_4697671] using wordTrace_append hprefix tailTrace_4697671
  have hstable : (prefixWord ++ tailWord_4697671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4697671).length < 2 ^ (prefixWord ++ tailWord_4697671).sum := by decide
  have hdescent : baseEnd_4697671 < baseStart_4697671 := by decide
  rcases family_descends (prefixWord ++ tailWord_4697671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4697696 : List Nat := [2, 1, 1, 3, 2, 1, 1, 3, 2, 7]
def baseStart_4697696 : Nat := 118140960795 + 4697696 * 2 ^ 59
def prefixEnd_4697696 : Nat := 4983230072969 + 3 ^ 40 * 4697696 * 2
def baseEnd_4697696 : Nat := 804058672234585825498565

theorem tailTrace_4697696 : CollatzResearch.WordTrace tailWord_4697696 prefixEnd_4697696 804058672234585825498565 := by
  unfold tailWord_4697696
  simp only [CollatzResearch.WordTrace]
  refine ⟨85669524594528584723668471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114226032792704779631557961 85669524594528584723668471)
  ·
    refine ⟨128504286891792877085502707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85669524594528584723668471 128504286891792877085502707)
    ·
      refine ⟨192756430337689315628254061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128504286891792877085502707 192756430337689315628254061)
      ·
        refine ⟨72283661376633493360595273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 192756430337689315628254061 72283661376633493360595273)
        ·
          refine ⟨54212746032475120020446455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72283661376633493360595273 54212746032475120020446455)
          ·
            refine ⟨81319119048712680030669683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54212746032475120020446455 81319119048712680030669683)
            ·
              refine ⟨121978678573069020046004525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81319119048712680030669683 121978678573069020046004525)
              ·
                refine ⟨45742004464900882517251697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 121978678573069020046004525 45742004464900882517251697)
                ·
                  refine ⟨34306503348675661887938773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45742004464900882517251697 34306503348675661887938773)
                  ·
                    refine ⟨804058672234585825498565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34306503348675661887938773 804058672234585825498565)
                    ·
                      rfl

theorem cell23_4697696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 3, 2, 7].length) (baseStart_4697696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4697696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4697696 prefixEnd_4697696 := by exact prefixLift 4697696
  have htrace : WordTrace (prefixWord ++ tailWord_4697696) baseStart_4697696 baseEnd_4697696 := by
    simpa [prefixWord, tailWord_4697696, baseEnd_4697696] using wordTrace_append hprefix tailTrace_4697696
  have hstable : (prefixWord ++ tailWord_4697696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4697696).length < 2 ^ (prefixWord ++ tailWord_4697696).sum := by decide
  have hdescent : baseEnd_4697696 < baseStart_4697696 := by decide
  rcases family_descends (prefixWord ++ tailWord_4697696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4697704 : List Nat := [2, 1, 4, 3, 1, 3, 2, 1, 2, 4]
def baseStart_4697704 : Nat := 118140960795 + 4697704 * 2 ^ 59
def prefixEnd_4697704 : Nat := 4983230072969 + 3 ^ 40 * 4697704 * 2
def baseEnd_4697704 : Nat := 804060041516331148398553

theorem tailTrace_4697704 : CollatzResearch.WordTrace tailWord_4697704 prefixEnd_4697704 804060041516331148398553 := by
  unfold tailWord_4697704
  simp only [CollatzResearch.WordTrace]
  refine ⟨85669670486514093406814083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114226227315352124542418777 85669670486514093406814083)
  ·
    refine ⟨128504505729771140110221125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85669670486514093406814083 128504505729771140110221125)
    ·
      refine ⟨24094594824332088770666461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 128504505729771140110221125 24094594824332088770666461)
      ·
        refine ⟨9035473059124533288999923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24094594824332088770666461 9035473059124533288999923)
        ·
          refine ⟨13553209588686799933499885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9035473059124533288999923 13553209588686799933499885)
          ·
            refine ⟨5082453595757549975062457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13553209588686799933499885 5082453595757549975062457)
            ·
              refine ⟨3811840196818162481296843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5082453595757549975062457 3811840196818162481296843)
              ·
                refine ⟨5717760295227243721945265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3811840196818162481296843 5717760295227243721945265)
                ·
                  refine ⟨4288320221420432791458949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5717760295227243721945265 4288320221420432791458949)
                  ·
                    refine ⟨804060041516331148398553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4288320221420432791458949 804060041516331148398553)
                    ·
                      rfl

theorem cell23_4697704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 2, 1, 2, 4].length) (baseStart_4697704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4697704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4697704 prefixEnd_4697704 := by exact prefixLift 4697704
  have htrace : WordTrace (prefixWord ++ tailWord_4697704) baseStart_4697704 baseEnd_4697704 := by
    simpa [prefixWord, tailWord_4697704, baseEnd_4697704] using wordTrace_append hprefix tailTrace_4697704
  have hstable : (prefixWord ++ tailWord_4697704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4697704).length < 2 ^ (prefixWord ++ tailWord_4697704).sum := by decide
  have hdescent : baseEnd_4697704 < baseStart_4697704 := by decide
  rcases family_descends (prefixWord ++ tailWord_4697704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4697763 : List Nat := [1, 1, 1, 4, 1, 1, 5, 1, 2, 2, 4]
def baseStart_4697763 : Nat := 118140960795 + 4697763 * 2 ^ 59
def prefixEnd_4697763 : Nat := 4983230072969 + 3 ^ 40 * 4697763 * 2
def baseEnd_4697763 : Nat := 2412210419907608714357887

theorem tailTrace_4697763 : CollatzResearch.WordTrace tailWord_4697763 prefixEnd_4697763 2412210419907608714357887 := by
  unfold tailWord_4697763
  simp only [CollatzResearch.WordTrace]
  refine ⟨171341492879814439890025943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114227661919876293260017295 171341492879814439890025943)
  ·
    refine ⟨257012239319721659835038915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171341492879814439890025943 257012239319721659835038915)
    ·
      refine ⟨385518358979582489752558373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 257012239319721659835038915 385518358979582489752558373)
      ·
        refine ⟨72284692308671716828604695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 385518358979582489752558373 72284692308671716828604695)
        ·
          refine ⟨108427038463007575242907043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72284692308671716828604695 108427038463007575242907043)
          ·
            refine ⟨162640557694511362864360565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108427038463007575242907043 162640557694511362864360565)
            ·
              refine ⟨15247552283860440268533803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 162640557694511362864360565 15247552283860440268533803)
              ·
                refine ⟨22871328425790660402800705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15247552283860440268533803 22871328425790660402800705)
                ·
                  refine ⟨17153496319342995302100529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22871328425790660402800705 17153496319342995302100529)
                  ·
                    refine ⟨12865122239507246476575397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17153496319342995302100529 12865122239507246476575397)
                    ·
                      refine ⟨2412210419907608714357887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12865122239507246476575397 2412210419907608714357887)
                      ·
                        rfl

theorem cell23_4697763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 1, 2, 2, 4].length) (baseStart_4697763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4697763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4697763 prefixEnd_4697763 := by exact prefixLift 4697763
  have htrace : WordTrace (prefixWord ++ tailWord_4697763) baseStart_4697763 baseEnd_4697763 := by
    simpa [prefixWord, tailWord_4697763, baseEnd_4697763] using wordTrace_append hprefix tailTrace_4697763
  have hstable : (prefixWord ++ tailWord_4697763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4697763).length < 2 ^ (prefixWord ++ tailWord_4697763).sum := by decide
  have hdescent : baseEnd_4697763 < baseStart_4697763 := by decide
  rcases family_descends (prefixWord ++ tailWord_4697763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4697803 : List Nat := [1, 1, 1, 1, 3, 2, 1, 6, 2, 5]
def baseStart_4697803 : Nat := 118140960795 + 4697803 * 2 ^ 59
def prefixEnd_4697803 : Nat := 4983230072969 + 3 ^ 40 * 4697803 * 2
def baseEnd_4697803 : Nat := 804076986377929519285901

theorem tailTrace_4697803 : CollatzResearch.WordTrace tailWord_4697803 prefixEnd_4697803 804076986377929519285901 := by
  unfold tailWord_4697803
  simp only [CollatzResearch.WordTrace]
  refine ⟨171342951799669526721482063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114228634533113017814321375 171342951799669526721482063)
  ·
    refine ⟨257014427699504290082223095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171342951799669526721482063 257014427699504290082223095)
    ·
      refine ⟨385521641549256435123334643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 257014427699504290082223095 385521641549256435123334643)
      ·
        refine ⟨578282462323884652685001965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 385521641549256435123334643 578282462323884652685001965)
        ·
          refine ⟨216855923371456744756875737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 578282462323884652685001965 216855923371456744756875737)
          ·
            refine ⟨162641942528592558567656803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 216855923371456744756875737 162641942528592558567656803)
            ·
              refine ⟨243962913792888837851485205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 162641942528592558567656803 243962913792888837851485205)
              ·
                refine ⟨11435761584041664274288369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 243962913792888837851485205 11435761584041664274288369)
                ·
                  refine ⟨8576821188031248205716277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11435761584041664274288369 8576821188031248205716277)
                  ·
                    refine ⟨804076986377929519285901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8576821188031248205716277 804076986377929519285901)
                    ·
                      rfl

theorem cell23_4697803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 6, 2, 5].length) (baseStart_4697803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4697803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4697803 prefixEnd_4697803 := by exact prefixLift 4697803
  have htrace : WordTrace (prefixWord ++ tailWord_4697803) baseStart_4697803 baseEnd_4697803 := by
    simpa [prefixWord, tailWord_4697803, baseEnd_4697803] using wordTrace_append hprefix tailTrace_4697803
  have hstable : (prefixWord ++ tailWord_4697803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4697803).length < 2 ^ (prefixWord ++ tailWord_4697803).sum := by decide
  have hdescent : baseEnd_4697803 < baseStart_4697803 := by decide
  rcases family_descends (prefixWord ++ tailWord_4697803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4697823 : List Nat := [1, 1, 2, 3, 2, 2, 1, 1, 3, 3, 4]
def baseStart_4697823 : Nat := 118140960795 + 4697823 * 2 ^ 59
def prefixEnd_4697823 : Nat := 4983230072969 + 3 ^ 40 * 4697823 * 2
def baseEnd_4697823 : Nat := 2412241228746878479607611

theorem tailTrace_4697823 : CollatzResearch.WordTrace tailWord_4697823 prefixEnd_4697823 2412241228746878479607611 := by
  unfold tailWord_4697823
  simp only [CollatzResearch.WordTrace]
  refine ⟨171343681259597070137210123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114229120839731380091473415 171343681259597070137210123)
  ·
    refine ⟨257015521889395605205815185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171343681259597070137210123 257015521889395605205815185)
    ·
      refine ⟨192761641417046703904361389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 257015521889395605205815185 192761641417046703904361389)
      ·
        refine ⟨72285615531392513964135521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 192761641417046703904361389 72285615531392513964135521)
        ·
          refine ⟨54214211648544385473101641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72285615531392513964135521 54214211648544385473101641)
          ·
            refine ⟨40660658736408289104826231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54214211648544385473101641 40660658736408289104826231)
            ·
              refine ⟨60990988104612433657239347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40660658736408289104826231 60990988104612433657239347)
              ·
                refine ⟨91486482156918650485859021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60990988104612433657239347 91486482156918650485859021)
                ·
                  refine ⟨34307430808844493932197133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 91486482156918650485859021 34307430808844493932197133)
                  ·
                    refine ⟨12865286553316685224573925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34307430808844493932197133 12865286553316685224573925)
                    ·
                      refine ⟨2412241228746878479607611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12865286553316685224573925 2412241228746878479607611)
                      ·
                        rfl

theorem cell23_4697823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 1, 3, 3, 4].length) (baseStart_4697823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4697823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4697823 prefixEnd_4697823 := by exact prefixLift 4697823
  have htrace : WordTrace (prefixWord ++ tailWord_4697823) baseStart_4697823 baseEnd_4697823 := by
    simpa [prefixWord, tailWord_4697823, baseEnd_4697823] using wordTrace_append hprefix tailTrace_4697823
  have hstable : (prefixWord ++ tailWord_4697823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4697823).length < 2 ^ (prefixWord ++ tailWord_4697823).sum := by decide
  have hdescent : baseEnd_4697823 < baseStart_4697823 := by decide
  rcases family_descends (prefixWord ++ tailWord_4697823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4697840 : List Nat := [2, 1, 1, 1, 3, 1, 2, 2, 4, 4, 2]
def baseStart_4697840 : Nat := 118140960795 + 4697840 * 2 ^ 59
def prefixEnd_4697840 : Nat := 4983230072969 + 3 ^ 40 * 4697840 * 2
def baseEnd_4697840 : Nat := 2412249957918004913095033

theorem tailTrace_4697840 : CollatzResearch.WordTrace tailWord_4697840 prefixEnd_4697840 2412249957918004913095033 := by
  unfold tailWord_4697840
  simp only [CollatzResearch.WordTrace]
  refine ⟨85672150650267741020289487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114229534200356988027052649 85672150650267741020289487)
  ·
    refine ⟨128508225975401611530434231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85672150650267741020289487 128508225975401611530434231)
    ·
      refine ⟨192762338963102417295651347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128508225975401611530434231 192762338963102417295651347)
      ·
        refine ⟨289143508444653625943477021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192762338963102417295651347 289143508444653625943477021)
        ·
          refine ⟨108428815666745109728803883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 289143508444653625943477021 108428815666745109728803883)
          ·
            refine ⟨162643223500117664593205825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108428815666745109728803883 162643223500117664593205825)
            ·
              refine ⟨121982417625088248444904369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 162643223500117664593205825 121982417625088248444904369)
              ·
                refine ⟨91486813218816186333678277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 121982417625088248444904369 91486813218816186333678277)
                ·
                  refine ⟨17153777478528034937564677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 91486813218816186333678277 17153777478528034937564677)
                  ·
                    refine ⟨3216333277224006550793377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17153777478528034937564677 3216333277224006550793377)
                    ·
                      refine ⟨2412249957918004913095033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3216333277224006550793377 2412249957918004913095033)
                      ·
                        rfl

theorem cell23_4697840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 2, 4, 4, 2].length) (baseStart_4697840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4697840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4697840 prefixEnd_4697840 := by exact prefixLift 4697840
  have htrace : WordTrace (prefixWord ++ tailWord_4697840) baseStart_4697840 baseEnd_4697840 := by
    simpa [prefixWord, tailWord_4697840, baseEnd_4697840] using wordTrace_append hprefix tailTrace_4697840
  have hstable : (prefixWord ++ tailWord_4697840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4697840).length < 2 ^ (prefixWord ++ tailWord_4697840).sum := by decide
  have hdescent : baseEnd_4697840 < baseStart_4697840 := by decide
  rcases family_descends (prefixWord ++ tailWord_4697840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4697853 : List Nat := [1, 4, 1, 1, 1, 1, 2, 3, 2, 1, 6]
def baseStart_4697853 : Nat := 118140960795 + 4697853 * 2 ^ 59
def prefixEnd_4697853 : Nat := 4983230072969 + 3 ^ 40 * 4697853 * 2
def baseEnd_4697853 : Nat := 2412256633166513362232473

theorem tailTrace_4697853 : CollatzResearch.WordTrace tailWord_4697853 prefixEnd_4697853 2412256633166513362232473 := by
  unfold tailWord_4697853
  simp only [CollatzResearch.WordTrace]
  refine ⟨171344775449488385260802213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114229850299658923507201475 171344775449488385260802213)
  ·
    refine ⟨32127145396779072236400415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 171344775449488385260802213 32127145396779072236400415)
    ·
      refine ⟨48190718095168608354600623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32127145396779072236400415 48190718095168608354600623)
      ·
        refine ⟨72286077142752912531900935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48190718095168608354600623 72286077142752912531900935)
        ·
          refine ⟨108429115714129368797851403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72286077142752912531900935 108429115714129368797851403)
          ·
            refine ⟨162643673571194053196777105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108429115714129368797851403 162643673571194053196777105)
            ·
              refine ⟨121982755178395539897582829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 162643673571194053196777105 121982755178395539897582829)
              ·
                refine ⟨45743533191898327461593561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 121982755178395539897582829 45743533191898327461593561)
                ·
                  refine ⟨34307649893923745596195171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45743533191898327461593561 34307649893923745596195171)
                  ·
                    refine ⟨51461474840885618394292757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34307649893923745596195171 51461474840885618394292757)
                    ·
                      refine ⟨2412256633166513362232473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 51461474840885618394292757 2412256633166513362232473)
                      ·
                        rfl

theorem cell23_4697853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 3, 2, 1, 6].length) (baseStart_4697853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4697853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4697853 prefixEnd_4697853 := by exact prefixLift 4697853
  have htrace : WordTrace (prefixWord ++ tailWord_4697853) baseStart_4697853 baseEnd_4697853 := by
    simpa [prefixWord, tailWord_4697853, baseEnd_4697853] using wordTrace_append hprefix tailTrace_4697853
  have hstable : (prefixWord ++ tailWord_4697853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4697853).length < 2 ^ (prefixWord ++ tailWord_4697853).sum := by decide
  have hdescent : baseEnd_4697853 < baseStart_4697853 := by decide
  rcases family_descends (prefixWord ++ tailWord_4697853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4697867 : List Nat := [1, 1, 1, 1, 5, 1, 2, 6, 1, 4]
def baseStart_4697867 : Nat := 118140960795 + 4697867 * 2 ^ 59
def prefixEnd_4697867 : Nat := 4983230072969 + 3 ^ 40 * 4697867 * 2
def baseEnd_4697867 : Nat := 804087940631892102485803

theorem tailTrace_4697867 : CollatzResearch.WordTrace tailWord_4697867 prefixEnd_4697867 804087940631892102485803 := by
  unfold tailWord_4697867
  simp only [CollatzResearch.WordTrace]
  refine ⟨171345286071437665651811855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114230190714291777101207903 171345286071437665651811855)
  ·
    refine ⟨257017929107156498477717783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171345286071437665651811855 257017929107156498477717783)
    ·
      refine ⟨385526893660734747716576675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 257017929107156498477717783 385526893660734747716576675)
      ·
        refine ⟨578290340491102121574865013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 385526893660734747716576675 578290340491102121574865013)
        ·
          refine ⟨54214719421040823897643595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 578290340491102121574865013 54214719421040823897643595)
          ·
            refine ⟨81322079131561235846465393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54214719421040823897643595 81322079131561235846465393)
            ·
              refine ⟨60991559348670926884849045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81322079131561235846465393 60991559348670926884849045)
              ·
                refine ⟨2858979344468949697727299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 60991559348670926884849045 2858979344468949697727299)
                ·
                  refine ⟨4288469016703424546590949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2858979344468949697727299 4288469016703424546590949)
                  ·
                    refine ⟨804087940631892102485803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4288469016703424546590949 804087940631892102485803)
                    ·
                      rfl

theorem cell23_4697867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 6, 1, 4].length) (baseStart_4697867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4697867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4697867 prefixEnd_4697867 := by exact prefixLift 4697867
  have htrace : WordTrace (prefixWord ++ tailWord_4697867) baseStart_4697867 baseEnd_4697867 := by
    simpa [prefixWord, tailWord_4697867, baseEnd_4697867] using wordTrace_append hprefix tailTrace_4697867
  have hstable : (prefixWord ++ tailWord_4697867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4697867).length < 2 ^ (prefixWord ++ tailWord_4697867).sum := by decide
  have hdescent : baseEnd_4697867 < baseStart_4697867 := by decide
  rcases family_descends (prefixWord ++ tailWord_4697867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4697869 : List Nat := [1, 7, 2, 1, 1, 2, 2, 1, 2, 2, 2]
def baseStart_4697869 : Nat := 118140960795 + 4697869 * 2 ^ 59
def prefixEnd_4697869 : Nat := 4983230072969 + 3 ^ 40 * 4697869 * 2
def baseEnd_4697869 : Nat := 2412264848856985299632401

theorem tailTrace_4697869 : CollatzResearch.WordTrace tailWord_4697869 prefixEnd_4697869 2412264848856985299632401 := by
  unfold tailWord_4697869
  simp only [CollatzResearch.WordTrace]
  refine ⟨171345359017430419993384661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114230239344953613328923107 171345359017430419993384661)
  ·
    refine ⟨4015906851971025468594953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 171345359017430419993384661 4015906851971025468594953)
    ·
      refine ⟨3011930138978269101446215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4015906851971025468594953 3011930138978269101446215)
      ·
        refine ⟨4517895208467403652169323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3011930138978269101446215 4517895208467403652169323)
        ·
          refine ⟨6776842812701105478253985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4517895208467403652169323 6776842812701105478253985)
          ·
            refine ⟨5082632109525829108690489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6776842812701105478253985 5082632109525829108690489)
            ·
              refine ⟨3811974082144371831517867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5082632109525829108690489 3811974082144371831517867)
              ·
                refine ⟨5717961123216557747276801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3811974082144371831517867 5717961123216557747276801)
                ·
                  refine ⟨4288470842412418310457601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5717961123216557747276801 4288470842412418310457601)
                  ·
                    refine ⟨3216353131809313732843201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4288470842412418310457601 3216353131809313732843201)
                    ·
                      refine ⟨2412264848856985299632401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3216353131809313732843201 2412264848856985299632401)
                      ·
                        rfl

theorem cell23_4697869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 2, 1, 2, 2, 2].length) (baseStart_4697869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4697869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4697869 prefixEnd_4697869 := by exact prefixLift 4697869
  have htrace : WordTrace (prefixWord ++ tailWord_4697869) baseStart_4697869 baseEnd_4697869 := by
    simpa [prefixWord, tailWord_4697869, baseEnd_4697869] using wordTrace_append hprefix tailTrace_4697869
  have hstable : (prefixWord ++ tailWord_4697869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4697869).length < 2 ^ (prefixWord ++ tailWord_4697869).sum := by decide
  have hdescent : baseEnd_4697869 < baseStart_4697869 := by decide
  rcases family_descends (prefixWord ++ tailWord_4697869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4697918 : List Nat := [4, 2, 1, 2, 2, 3, 2, 2, 1, 4]
def baseStart_4697918 : Nat := 118140960795 + 4697918 * 2 ^ 59
def prefixEnd_4697918 : Nat := 4983230072969 + 3 ^ 40 * 4697918 * 2
def baseEnd_4697918 : Nat := 804096669803018535973225

theorem tailTrace_4697918 : CollatzResearch.WordTrace tailWord_4697918 prefixEnd_4697918 804096669803018535973225 := by
  unfold tailWord_4697918
  simp only [CollatzResearch.WordTrace]
  refine ⟨21418393274281612670239801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 114231430796168600907945605 21418393274281612670239801)
  ·
    refine ⟨16063794955711209502679851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21418393274281612670239801 16063794955711209502679851)
    ·
      refine ⟨24095692433566814254019777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16063794955711209502679851 24095692433566814254019777)
      ·
        refine ⟨18071769325175110690514833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24095692433566814254019777 18071769325175110690514833)
        ·
          refine ⟨13553826993881333017886125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18071769325175110690514833 13553826993881333017886125)
          ·
            refine ⟨5082685122705499881707297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13553826993881333017886125 5082685122705499881707297)
            ·
              refine ⟨3812013842029124911280473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5082685122705499881707297 3812013842029124911280473)
              ·
                refine ⟨2859010381521843683460355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3812013842029124911280473 2859010381521843683460355)
                ·
                  refine ⟨4288515572282765525190533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2859010381521843683460355 4288515572282765525190533)
                  ·
                    refine ⟨804096669803018535973225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4288515572282765525190533 804096669803018535973225)
                    ·
                      rfl

theorem cell23_4697918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 2, 2, 1, 4].length) (baseStart_4697918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4697918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4697918 prefixEnd_4697918 := by exact prefixLift 4697918
  have htrace : WordTrace (prefixWord ++ tailWord_4697918) baseStart_4697918 baseEnd_4697918 := by
    simpa [prefixWord, tailWord_4697918, baseEnd_4697918] using wordTrace_append hprefix tailTrace_4697918
  have hstable : (prefixWord ++ tailWord_4697918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4697918).length < 2 ^ (prefixWord ++ tailWord_4697918).sum := by decide
  have hdescent : baseEnd_4697918 < baseStart_4697918 := by decide
  rcases family_descends (prefixWord ++ tailWord_4697918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4697930 : List Nat := [3, 1, 2, 1, 1, 1, 3, 1, 5, 1, 4]
def baseStart_4697930 : Nat := 118140960795 + 4697930 * 2 ^ 59
def prefixEnd_4697930 : Nat := 4983230072969 + 3 ^ 40 * 4697930 * 2
def baseEnd_4697930 : Nat := 2412296171176909560969619

theorem tailTrace_4697930 : CollatzResearch.WordTrace tailWord_4697930 prefixEnd_4697930 2412296171176909560969619 := by
  unfold tailWord_4697930
  simp only [CollatzResearch.WordTrace]
  refine ⟨42836895967552356852838811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114231722580139618274236829 42836895967552356852838811)
  ·
    refine ⟨64255343951328535279258217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42836895967552356852838811 64255343951328535279258217)
    ·
      refine ⟨48191507963496401459443663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64255343951328535279258217 48191507963496401459443663)
      ·
        refine ⟨72287261945244602189165495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48191507963496401459443663 72287261945244602189165495)
        ·
          refine ⟨108430892917866903283748243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72287261945244602189165495 108430892917866903283748243)
          ·
            refine ⟨162646339376800354925622365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108430892917866903283748243 162646339376800354925622365)
            ·
              refine ⟨60992377266300133097108387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 162646339376800354925622365 60992377266300133097108387)
              ·
                refine ⟨91488565899450199645662581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60992377266300133097108387 91488565899450199645662581)
                ·
                  refine ⟨8577053053073456216780867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 91488565899450199645662581 8577053053073456216780867)
                  ·
                    refine ⟨12865579579610184325171301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8577053053073456216780867 12865579579610184325171301)
                    ·
                      refine ⟨2412296171176909560969619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12865579579610184325171301 2412296171176909560969619)
                      ·
                        rfl

theorem cell23_4697930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 1, 5, 1, 4].length) (baseStart_4697930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4697930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4697930 prefixEnd_4697930 := by exact prefixLift 4697930
  have htrace : WordTrace (prefixWord ++ tailWord_4697930) baseStart_4697930 baseEnd_4697930 := by
    simpa [prefixWord, tailWord_4697930, baseEnd_4697930] using wordTrace_append hprefix tailTrace_4697930
  have hstable : (prefixWord ++ tailWord_4697930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4697930).length < 2 ^ (prefixWord ++ tailWord_4697930).sum := by decide
  have hdescent : baseEnd_4697930 < baseStart_4697930 := by decide
  rcases family_descends (prefixWord ++ tailWord_4697930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4697964 : List Nat := [2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 4]
def baseStart_4697964 : Nat := 118140960795 + 4697964 * 2 ^ 59
def prefixEnd_4697964 : Nat := 4983230072969 + 3 ^ 40 * 4697964 * 2
def baseEnd_4697964 : Nat := 2412313629519162427944463

theorem tailTrace_4697964 : CollatzResearch.WordTrace tailWord_4697964 prefixEnd_4697964 2412313629519162427944463 := by
  unfold tailWord_4697964
  simp only [CollatzResearch.WordTrace]
  refine ⟨85674411976043125609046473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114232549301390834145395297 85674411976043125609046473)
  ·
    refine ⟨64255808982032344206784855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85674411976043125609046473 64255808982032344206784855)
    ·
      refine ⟨96383713473048516310177283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64255808982032344206784855 96383713473048516310177283)
      ·
        refine ⟨144575570209572774465265925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96383713473048516310177283 144575570209572774465265925)
        ·
          refine ⟨27107919414294895212237361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 144575570209572774465265925 27107919414294895212237361)
          ·
            refine ⟨20330939560721171409178021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27107919414294895212237361 20330939560721171409178021)
            ·
              refine ⟨3812051167635219639220879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20330939560721171409178021 3812051167635219639220879)
              ·
                refine ⟨5718076751452829458831319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3812051167635219639220879 5718076751452829458831319)
                ·
                  refine ⟨8577115127179244188246979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5718076751452829458831319 8577115127179244188246979)
                  ·
                    refine ⟨12865672690768866282370469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8577115127179244188246979 12865672690768866282370469)
                    ·
                      refine ⟨2412313629519162427944463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12865672690768866282370469 2412313629519162427944463)
                      ·
                        rfl

theorem cell23_4697964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 4].length) (baseStart_4697964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4697964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4697964 prefixEnd_4697964 := by exact prefixLift 4697964
  have htrace : WordTrace (prefixWord ++ tailWord_4697964) baseStart_4697964 baseEnd_4697964 := by
    simpa [prefixWord, tailWord_4697964, baseEnd_4697964] using wordTrace_append hprefix tailTrace_4697964
  have hstable : (prefixWord ++ tailWord_4697964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4697964).length < 2 ^ (prefixWord ++ tailWord_4697964).sum := by decide
  have hdescent : baseEnd_4697964 < baseStart_4697964 := by decide
  rcases family_descends (prefixWord ++ tailWord_4697964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4697980 : List Nat := [2, 2, 2, 1, 1, 1, 1, 1, 2, 7, 3]
def baseStart_4697980 : Nat := 118140960795 + 4697980 * 2 ^ 59
def prefixEnd_4697980 : Nat := 4983230072969 + 3 ^ 40 * 4697980 * 2
def baseEnd_4697980 : Nat := 2412321845209634365344389

theorem tailTrace_4697980 : CollatzResearch.WordTrace tailWord_4697980 prefixEnd_4697980 2412321845209634365344389 := by
  unfold tailWord_4697980
  simp only [CollatzResearch.WordTrace]
  refine ⟨85674703760014142975337697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114232938346685523967116929 85674703760014142975337697)
  ·
    refine ⟨64256027820010607231503273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85674703760014142975337697 64256027820010607231503273)
    ·
      refine ⟨48192020865007955423627455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64256027820010607231503273 48192020865007955423627455)
      ·
        refine ⟨72288031297511933135441183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48192020865007955423627455 72288031297511933135441183)
        ·
          refine ⟨108432046946267899703161775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72288031297511933135441183 108432046946267899703161775)
          ·
            refine ⟨162648070419401849554742663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108432046946267899703161775 162648070419401849554742663)
            ·
              refine ⟨243972105629102774332113995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 162648070419401849554742663 243972105629102774332113995)
              ·
                refine ⟨365958158443654161498170993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 243972105629102774332113995 365958158443654161498170993)
                ·
                  refine ⟨274468618832740621123628245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 365958158443654161498170993 274468618832740621123628245)
                  ·
                    refine ⟨6432858253892358307585037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 274468618832740621123628245 6432858253892358307585037)
                    ·
                      refine ⟨2412321845209634365344389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6432858253892358307585037 2412321845209634365344389)
                      ·
                        rfl

theorem cell23_4697980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 2, 7, 3].length) (baseStart_4697980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4697980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4697980 prefixEnd_4697980 := by exact prefixLift 4697980
  have htrace : WordTrace (prefixWord ++ tailWord_4697980) baseStart_4697980 baseEnd_4697980 := by
    simpa [prefixWord, tailWord_4697980, baseEnd_4697980] using wordTrace_append hprefix tailTrace_4697980
  have hstable : (prefixWord ++ tailWord_4697980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4697980).length < 2 ^ (prefixWord ++ tailWord_4697980).sum := by decide
  have hdescent : baseEnd_4697980 < baseStart_4697980 := by decide
  rcases family_descends (prefixWord ++ tailWord_4697980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4697991 : List Nat := [1, 1, 4, 2, 4, 1, 3, 1, 2, 4]
def baseStart_4697991 : Nat := 118140960795 + 4697991 * 2 ^ 59
def prefixEnd_4697991 : Nat := 4983230072969 + 3 ^ 40 * 4697991 * 2
def baseEnd_4697991 : Nat := 804109164498944607435613

theorem tailTrace_4697991 : CollatzResearch.WordTrace tailWord_4697991 prefixEnd_4697991 804109164498944607435613 := by
  unfold tailWord_4697991
  simp only [CollatzResearch.WordTrace]
  refine ⟨171349808722988434829325827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114233205815325623219550551 171349808722988434829325827)
  ·
    refine ⟨257024713084482652243988741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171349808722988434829325827 257024713084482652243988741)
    ·
      refine ⟨48192133703340497295747889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 257024713084482652243988741 48192133703340497295747889)
      ·
        refine ⟨36144100277505372971810917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48192133703340497295747889 36144100277505372971810917)
        ·
          refine ⟨6777018802032257432214547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36144100277505372971810917 6777018802032257432214547)
          ·
            refine ⟨10165528203048386148321821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6777018802032257432214547 10165528203048386148321821)
            ·
              refine ⟨3812073076143144805620683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10165528203048386148321821 3812073076143144805620683)
              ·
                refine ⟨5718109614214717208431025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3812073076143144805620683 5718109614214717208431025)
                ·
                  refine ⟨4288582210661037906323269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5718109614214717208431025 4288582210661037906323269)
                  ·
                    refine ⟨804109164498944607435613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4288582210661037906323269 804109164498944607435613)
                    ·
                      rfl

theorem cell23_4697991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 3, 1, 2, 4].length) (baseStart_4697991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4697991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4697991 prefixEnd_4697991 := by exact prefixLift 4697991
  have htrace : WordTrace (prefixWord ++ tailWord_4697991) baseStart_4697991 baseEnd_4697991 := by
    simpa [prefixWord, tailWord_4697991, baseEnd_4697991] using wordTrace_append hprefix tailTrace_4697991
  have hstable : (prefixWord ++ tailWord_4697991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4697991).length < 2 ^ (prefixWord ++ tailWord_4697991).sum := by decide
  have hdescent : baseEnd_4697991 < baseStart_4697991 := by decide
  rcases family_descends (prefixWord ++ tailWord_4697991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4698004 : List Nat := [2, 4, 2, 1, 1, 4, 2, 7]
def baseStart_4698004 : Nat := 118140960795 + 4698004 * 2 ^ 59
def prefixEnd_4698004 : Nat := 4983230072969 + 3 ^ 40 * 4698004 * 2
def baseEnd_4698004 : Nat := 89345709953531195238677

theorem tailTrace_4698004 : CollatzResearch.WordTrace tailWord_4698004 prefixEnd_4698004 89345709953531195238677 := by
  unfold tailWord_4698004
  simp only [CollatzResearch.WordTrace]
  refine ⟨85675141435970669024774533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114233521914627558699699377 85675141435970669024774533)
  ·
    refine ⟨16064089019244500442145225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 85675141435970669024774533 16064089019244500442145225)
    ·
      refine ⟨12048066764433375331608919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16064089019244500442145225 12048066764433375331608919)
      ·
        refine ⟨18072100146650062997413379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12048066764433375331608919 18072100146650062997413379)
        ·
          refine ⟨27108150219975094496120069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18072100146650062997413379 27108150219975094496120069)
          ·
            refine ⟨5082778166245330218022513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27108150219975094496120069 5082778166245330218022513)
            ·
              refine ⟨3812083624683997663516885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5082778166245330218022513 3812083624683997663516885)
              ·
                refine ⟨89345709953531195238677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3812083624683997663516885 89345709953531195238677)
                ·
                  rfl

theorem cell23_4698004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 2, 7].length) (baseStart_4698004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4698004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4698004 prefixEnd_4698004 := by exact prefixLift 4698004
  have htrace : WordTrace (prefixWord ++ tailWord_4698004) baseStart_4698004 baseEnd_4698004 := by
    simpa [prefixWord, tailWord_4698004, baseEnd_4698004] using wordTrace_append hprefix tailTrace_4698004
  have hstable : (prefixWord ++ tailWord_4698004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4698004).length < 2 ^ (prefixWord ++ tailWord_4698004).sum := by decide
  have hdescent : baseEnd_4698004 < baseStart_4698004 := by decide
  rcases family_descends (prefixWord ++ tailWord_4698004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4698015 : List Nat := [1, 1, 2, 5, 3, 2, 1, 3, 1, 2, 2]
def baseStart_4698015 : Nat := 118140960795 + 4698015 * 2 ^ 59
def prefixEnd_4698015 : Nat := 4983230072969 + 3 ^ 40 * 4698015 * 2
def baseEnd_4698015 : Nat := 2412339817032541728406729

theorem tailTrace_4698015 : CollatzResearch.WordTrace tailWord_4698015 prefixEnd_4698015 2412339817032541728406729 := by
  unfold tailWord_4698015
  simp only [CollatzResearch.WordTrace]
  refine ⟨171350684074901486928199499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114233789383267657952132999 171350684074901486928199499)
  ·
    refine ⟨257026026112352230392299249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171350684074901486928199499 257026026112352230392299249)
    ·
      refine ⟨192769519584264172794224437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 257026026112352230392299249 192769519584264172794224437)
      ·
        refine ⟨18072142461024766199458541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 192769519584264172794224437 18072142461024766199458541)
        ·
          refine ⟨6777053422884287324796953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18072142461024766199458541 6777053422884287324796953)
          ·
            refine ⟨5082790067163215493597715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6777053422884287324796953 5082790067163215493597715)
            ·
              refine ⟨7624185100744823240396573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5082790067163215493597715 7624185100744823240396573)
              ·
                refine ⟨2859069412779308715148715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7624185100744823240396573 2859069412779308715148715)
                ·
                  refine ⟨4288604119168963072723073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2859069412779308715148715 4288604119168963072723073)
                  ·
                    refine ⟨3216453089376722304542305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4288604119168963072723073 3216453089376722304542305)
                    ·
                      refine ⟨2412339817032541728406729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3216453089376722304542305 2412339817032541728406729)
                      ·
                        rfl

theorem cell23_4698015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 1, 3, 1, 2, 2].length) (baseStart_4698015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4698015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4698015 prefixEnd_4698015 := by exact prefixLift 4698015
  have htrace : WordTrace (prefixWord ++ tailWord_4698015) baseStart_4698015 baseEnd_4698015 := by
    simpa [prefixWord, tailWord_4698015, baseEnd_4698015] using wordTrace_append hprefix tailTrace_4698015
  have hstable : (prefixWord ++ tailWord_4698015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4698015).length < 2 ^ (prefixWord ++ tailWord_4698015).sum := by decide
  have hdescent : baseEnd_4698015 < baseStart_4698015 := by decide
  rcases family_descends (prefixWord ++ tailWord_4698015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4698040 : List Nat := [2, 1, 2, 1, 2, 3, 1, 2, 1, 3, 5]
def baseStart_4698040 : Nat := 118140960795 + 4698040 * 2 ^ 59
def prefixEnd_4698040 : Nat := 4983230072969 + 3 ^ 40 * 4698040 * 2
def baseEnd_4698040 : Nat := 2412352654048904130594113

theorem tailTrace_4698040 : CollatzResearch.WordTrace tailWord_4698040 prefixEnd_4698040 2412352654048904130594113 := by
  unfold tailWord_4698040
  simp only [CollatzResearch.WordTrace]
  refine ⟨85675797949905458098929787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114234397266540610798573049 85675797949905458098929787)
  ·
    refine ⟨128513696924858187148394681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85675797949905458098929787 128513696924858187148394681)
    ·
      refine ⟨96385272693643640361296011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128513696924858187148394681 96385272693643640361296011)
      ·
        refine ⟨144577909040465460541944017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96385272693643640361296011 144577909040465460541944017)
        ·
          refine ⟨108433431780349095406458013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 144577909040465460541944017 108433431780349095406458013)
          ·
            refine ⟨40662536917630910777421755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 108433431780349095406458013 40662536917630910777421755)
            ·
              refine ⟨60993805376446366166132633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40662536917630910777421755 60993805376446366166132633)
              ·
                refine ⟨45745354032334774624599475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60993805376446366166132633 45745354032334774624599475)
                ·
                  refine ⟨68618031048502161936899213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45745354032334774624599475 68618031048502161936899213)
                  ·
                    refine ⟨25731761643188310726337205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 68618031048502161936899213 25731761643188310726337205)
                    ·
                      refine ⟨2412352654048904130594113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25731761643188310726337205 2412352654048904130594113)
                      ·
                        rfl

theorem cell23_4698040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 2, 1, 3, 5].length) (baseStart_4698040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4698040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4698040 prefixEnd_4698040 := by exact prefixLift 4698040
  have htrace : WordTrace (prefixWord ++ tailWord_4698040) baseStart_4698040 baseEnd_4698040 := by
    simpa [prefixWord, tailWord_4698040, baseEnd_4698040] using wordTrace_append hprefix tailTrace_4698040
  have hstable : (prefixWord ++ tailWord_4698040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4698040).length < 2 ^ (prefixWord ++ tailWord_4698040).sum := by decide
  have hdescent : baseEnd_4698040 < baseStart_4698040 := by decide
  rcases family_descends (prefixWord ++ tailWord_4698040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4698137 : List Nat := [1, 2, 1, 2, 1, 1, 3, 1, 7, 4]
def baseStart_4698137 : Nat := 118140960795 + 4698137 * 2 ^ 59
def prefixEnd_4698137 : Nat := 4983230072969 + 3 ^ 40 * 4698137 * 2
def baseEnd_4698137 : Nat := 804134153890796750360389

theorem tailTrace_4698137 : CollatzResearch.WordTrace tailWord_4698137 prefixEnd_4698137 804134153890796750360389 := by
  unfold tailWord_4698137
  simp only [CollatzResearch.WordTrace]
  refine ⟨171355133780459501764140665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114236755853639667842760443 171355133780459501764140665)
  ·
    refine ⟨128516350335344626323105499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171355133780459501764140665 128516350335344626323105499)
    ·
      refine ⟨192774525503016939484658249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128516350335344626323105499 192774525503016939484658249)
      ·
        refine ⟨144580894127262704613493687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 192774525503016939484658249 144580894127262704613493687)
        ·
          refine ⟨216871341190894056920240531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144580894127262704613493687 216871341190894056920240531)
          ·
            refine ⟨325307011786341085380360797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 216871341190894056920240531 325307011786341085380360797)
            ·
              refine ⟨121990129419877907017635299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 325307011786341085380360797 121990129419877907017635299)
              ·
                refine ⟨182985194129816860526452949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 121990129419877907017635299 182985194129816860526452949)
                ·
                  refine ⟨4288715487417582668588741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 182985194129816860526452949 4288715487417582668588741)
                  ·
                    refine ⟨804134153890796750360389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4288715487417582668588741 804134153890796750360389)
                    ·
                      rfl

theorem cell23_4698137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 7, 4].length) (baseStart_4698137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4698137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4698137 prefixEnd_4698137 := by exact prefixLift 4698137
  have htrace : WordTrace (prefixWord ++ tailWord_4698137) baseStart_4698137 baseEnd_4698137 := by
    simpa [prefixWord, tailWord_4698137, baseEnd_4698137] using wordTrace_append hprefix tailTrace_4698137
  have hstable : (prefixWord ++ tailWord_4698137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4698137).length < 2 ^ (prefixWord ++ tailWord_4698137).sum := by decide
  have hdescent : baseEnd_4698137 < baseStart_4698137 := by decide
  rcases family_descends (prefixWord ++ tailWord_4698137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4698167 : List Nat := [1, 1, 3, 1, 2, 2, 2, 5, 6]
def baseStart_4698167 : Nat := 118140960795 + 4698167 * 2 ^ 59
def prefixEnd_4698167 : Nat := 4983230072969 + 3 ^ 40 * 4698167 * 2
def baseEnd_4698167 : Nat := 268046429565780570411781

theorem tailTrace_4698167 : CollatzResearch.WordTrace tailWord_4698167 prefixEnd_4698167 268046429565780570411781 := by
  unfold tailWord_4698167
  simp only [CollatzResearch.WordTrace]
  refine ⟨171356227970350816887732755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114237485313567211258488503 171356227970350816887732755)
  ·
    refine ⟨257034341955526225331599133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171356227970350816887732755 257034341955526225331599133)
    ·
      refine ⟨96387878233322334499349675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 257034341955526225331599133 96387878233322334499349675)
      ·
        refine ⟨144581817349983501749024513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96387878233322334499349675 144581817349983501749024513)
        ·
          refine ⟨108436363012487626311768385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 144581817349983501749024513 108436363012487626311768385)
          ·
            refine ⟨81327272259365719733826289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 108436363012487626311768385 81327272259365719733826289)
            ·
              refine ⟨60995454194524289800369717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81327272259365719733826289 60995454194524289800369717)
              ·
                refine ⟨5718323830736652168784661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 60995454194524289800369717 5718323830736652168784661)
                ·
                  refine ⟨268046429565780570411781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5718323830736652168784661 268046429565780570411781)
                  ·
                    rfl

theorem cell23_4698167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 5, 6].length) (baseStart_4698167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4698167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4698167 prefixEnd_4698167 := by exact prefixLift 4698167
  have htrace : WordTrace (prefixWord ++ tailWord_4698167) baseStart_4698167 baseEnd_4698167 := by
    simpa [prefixWord, tailWord_4698167, baseEnd_4698167] using wordTrace_append hprefix tailTrace_4698167
  have hstable : (prefixWord ++ tailWord_4698167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4698167).length < 2 ^ (prefixWord ++ tailWord_4698167).sum := by decide
  have hdescent : baseEnd_4698167 < baseStart_4698167 := by decide
  rcases family_descends (prefixWord ++ tailWord_4698167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4698198 : List Nat := [5, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3]
def baseStart_4698198 : Nat := 118140960795 + 4698198 * 2 ^ 59
def prefixEnd_4698198 : Nat := 4983230072969 + 3 ^ 40 * 4698198 * 2
def baseEnd_4698198 : Nat := 2412433783992314512418387

theorem tailTrace_4698198 : CollatzResearch.WordTrace tailWord_4698198 prefixEnd_4698198 2412433783992314512418387 := by
  unfold tailWord_4698198
  simp only [CollatzResearch.WordTrace]
  refine ⟨10709834914577406823881953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 114238239088825672788074165 10709834914577406823881953)
  ·
    refine ⟨8032376185933055117911465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10709834914577406823881953 8032376185933055117911465)
    ·
      refine ⟨6024282139449791338433599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8032376185933055117911465 6024282139449791338433599)
      ·
        refine ⟨9036423209174687007650399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6024282139449791338433599 9036423209174687007650399)
        ·
          refine ⟨13554634813762030511475599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9036423209174687007650399 13554634813762030511475599)
          ·
            refine ⟨20331952220643045767213399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13554634813762030511475599 20331952220643045767213399)
            ·
              refine ⟨30497928330964568650820099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20331952220643045767213399 30497928330964568650820099)
              ·
                refine ⟨45746892496446852976230149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30497928330964568650820099 45746892496446852976230149)
                ·
                  refine ⟨8577542343083784933043153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45746892496446852976230149 8577542343083784933043153)
                  ·
                    refine ⟨6433156757312838699782365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8577542343083784933043153 6433156757312838699782365)
                    ·
                      refine ⟨2412433783992314512418387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6433156757312838699782365 2412433783992314512418387)
                      ·
                        rfl

theorem cell23_4698198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3].length) (baseStart_4698198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4698198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4698198 prefixEnd_4698198 := by exact prefixLift 4698198
  have htrace : WordTrace (prefixWord ++ tailWord_4698198) baseStart_4698198 baseEnd_4698198 := by
    simpa [prefixWord, tailWord_4698198, baseEnd_4698198] using wordTrace_append hprefix tailTrace_4698198
  have hstable : (prefixWord ++ tailWord_4698198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4698198).length < 2 ^ (prefixWord ++ tailWord_4698198).sum := by decide
  have hdescent : baseEnd_4698198 < baseStart_4698198 := by decide
  rcases family_descends (prefixWord ++ tailWord_4698198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4698211 : List Nat := [1, 1, 1, 5, 1, 1, 5, 1, 3, 1, 3]
def baseStart_4698211 : Nat := 118140960795 + 4698211 * 2 ^ 59
def prefixEnd_4698211 : Nat := 4983230072969 + 3 ^ 40 * 4698211 * 2
def baseEnd_4698211 : Nat := 2412440459240822961555827

theorem tailTrace_4698211 : CollatzResearch.WordTrace tailWord_4698211 prefixEnd_4698211 2412440459240822961555827 := by
  unfold tailWord_4698211
  simp only [CollatzResearch.WordTrace]
  refine ⟨171357832782191412402334487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114238555188127608268222991 171357832782191412402334487)
  ·
    refine ⟨257036749173287118603501731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171357832782191412402334487 257036749173287118603501731)
    ·
      refine ⟨385555123759930677905252597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 257036749173287118603501731 385555123759930677905252597)
      ·
        refine ⟨36145792852493501053617431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 385555123759930677905252597 36145792852493501053617431)
        ·
          refine ⟨54218689278740251580426147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36145792852493501053617431 54218689278740251580426147)
          ·
            refine ⟨81328033918110377370639221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54218689278740251580426147 81328033918110377370639221)
            ·
              refine ⟨7624503179822847878497427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 81328033918110377370639221 7624503179822847878497427)
              ·
                refine ⟨11436754769734271817746141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7624503179822847878497427 11436754769734271817746141)
                ·
                  refine ⟨4288783038650351931654803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11436754769734271817746141 4288783038650351931654803)
                  ·
                    refine ⟨6433174557975527897482205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4288783038650351931654803 6433174557975527897482205)
                    ·
                      refine ⟨2412440459240822961555827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6433174557975527897482205 2412440459240822961555827)
                      ·
                        rfl

theorem cell23_4698211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 5, 1, 3, 1, 3].length) (baseStart_4698211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4698211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4698211 prefixEnd_4698211 := by exact prefixLift 4698211
  have htrace : WordTrace (prefixWord ++ tailWord_4698211) baseStart_4698211 baseEnd_4698211 := by
    simpa [prefixWord, tailWord_4698211, baseEnd_4698211] using wordTrace_append hprefix tailTrace_4698211
  have hstable : (prefixWord ++ tailWord_4698211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4698211).length < 2 ^ (prefixWord ++ tailWord_4698211).sum := by decide
  have hdescent : baseEnd_4698211 < baseStart_4698211 := by decide
  rcases family_descends (prefixWord ++ tailWord_4698211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4698218 : List Nat := [3, 1, 3, 2, 3, 2, 2, 1, 6]
def baseStart_4698218 : Nat := 118140960795 + 4698218 * 2 ^ 59
def prefixEnd_4698218 : Nat := 4983230072969 + 3 ^ 40 * 4698218 * 2
def baseEnd_4698218 : Nat := 268049339289489381574255

theorem tailTrace_4698218 : CollatzResearch.WordTrace tailWord_4698218 prefixEnd_4698218 268049339289489381574255 := by
  unfold tailWord_4698218
  simp only [CollatzResearch.WordTrace]
  refine ⟨42839522023291513149459827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114238725395444035065226205 42839522023291513149459827)
  ·
    refine ⟨64259283034937269724189741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42839522023291513149459827 64259283034937269724189741)
    ·
      refine ⟨24097231138101476146571153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64259283034937269724189741 24097231138101476146571153)
      ·
        refine ⟨18072923353576107109928365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24097231138101476146571153 18072923353576107109928365)
        ·
          refine ⟨6777346257591040166223137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18072923353576107109928365 6777346257591040166223137)
          ·
            refine ⟨5083009693193280124667353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6777346257591040166223137 5083009693193280124667353)
            ·
              refine ⟨3812257269894960093500515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5083009693193280124667353 3812257269894960093500515)
              ·
                refine ⟨5718385904842440140250773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3812257269894960093500515 5718385904842440140250773)
                ·
                  refine ⟨268049339289489381574255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5718385904842440140250773 268049339289489381574255)
                  ·
                    rfl

theorem cell23_4698218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 2, 1, 6].length) (baseStart_4698218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4698218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4698218 prefixEnd_4698218 := by exact prefixLift 4698218
  have htrace : WordTrace (prefixWord ++ tailWord_4698218) baseStart_4698218 baseEnd_4698218 := by
    simpa [prefixWord, tailWord_4698218, baseEnd_4698218] using wordTrace_append hprefix tailTrace_4698218
  have hstable : (prefixWord ++ tailWord_4698218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4698218).length < 2 ^ (prefixWord ++ tailWord_4698218).sum := by decide
  have hdescent : baseEnd_4698218 < baseStart_4698218 := by decide
  rcases family_descends (prefixWord ++ tailWord_4698218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4698221 : List Nat := [1, 5, 1, 1, 2, 1, 1, 2, 4, 3, 2]
def baseStart_4698221 : Nat := 118140960795 + 4698221 * 2 ^ 59
def prefixEnd_4698221 : Nat := 4983230072969 + 3 ^ 40 * 4698221 * 2
def baseEnd_4698221 : Nat := 2412445594047367922430781

theorem tailTrace_4698221 : CollatzResearch.WordTrace tailWord_4698221 prefixEnd_4698221 2412445594047367922430781 := by
  unfold tailWord_4698221
  simp only [CollatzResearch.WordTrace]
  refine ⟨171358197512155184110198517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114238798341436789406799011 171358197512155184110198517)
  ·
    refine ⟨16064831016764548510331111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 171358197512155184110198517 16064831016764548510331111)
    ·
      refine ⟨24097246525146822765496667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16064831016764548510331111 24097246525146822765496667)
      ·
        refine ⟨36145869787720234148245001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24097246525146822765496667 36145869787720234148245001)
        ·
          refine ⟨27109402340790175611183751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36145869787720234148245001 27109402340790175611183751)
          ·
            refine ⟨40664103511185263416775627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27109402340790175611183751 40664103511185263416775627)
            ·
              refine ⟨60996155266777895125163441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40664103511185263416775627 60996155266777895125163441)
              ·
                refine ⟨45747116450083421343872581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60996155266777895125163441 45747116450083421343872581)
                ·
                  refine ⟨8577584334390641501976109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45747116450083421343872581 8577584334390641501976109)
                  ·
                    refine ⟨3216594125396490563241041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8577584334390641501976109 3216594125396490563241041)
                    ·
                      refine ⟨2412445594047367922430781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3216594125396490563241041 2412445594047367922430781)
                      ·
                        rfl

theorem cell23_4698221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 2, 4, 3, 2].length) (baseStart_4698221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4698221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4698221 prefixEnd_4698221 := by exact prefixLift 4698221
  have htrace : WordTrace (prefixWord ++ tailWord_4698221) baseStart_4698221 baseEnd_4698221 := by
    simpa [prefixWord, tailWord_4698221, baseEnd_4698221] using wordTrace_append hprefix tailTrace_4698221
  have hstable : (prefixWord ++ tailWord_4698221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4698221).length < 2 ^ (prefixWord ++ tailWord_4698221).sum := by decide
  have hdescent : baseEnd_4698221 < baseStart_4698221 := by decide
  rcases family_descends (prefixWord ++ tailWord_4698221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4698231 : List Nat := [1, 1, 3, 1, 1, 7, 1, 2, 1, 5]
def baseStart_4698231 : Nat := 118140960795 + 4698231 * 2 ^ 59
def prefixEnd_4698231 : Nat := 4983230072969 + 3 ^ 40 * 4698231 * 2
def baseEnd_4698231 : Nat := 804150242951304294435245

theorem tailTrace_4698231 : CollatzResearch.WordTrace tailWord_4698231 prefixEnd_4698231 804150242951304294435245 := by
  unfold tailWord_4698231
  simp only [CollatzResearch.WordTrace]
  refine ⟨171358562242118955818062547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114239041494745970545375031 171358562242118955818062547)
  ·
    refine ⟨257037843363178433727093821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171358562242118955818062547 257037843363178433727093821)
    ·
      refine ⟨96389191261191912647660183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 257037843363178433727093821 96389191261191912647660183)
      ·
        refine ⟨144583786891787868971490275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96389191261191912647660183 144583786891787868971490275)
        ·
          refine ⟨216875680337681803457235413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144583786891787868971490275 216875680337681803457235413)
          ·
            refine ⟨5083023757914417268528955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 216875680337681803457235413 5083023757914417268528955)
            ·
              refine ⟨7624535636871625902793433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5083023757914417268528955 7624535636871625902793433)
              ·
                refine ⟨5718401727653719427095075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7624535636871625902793433 5718401727653719427095075)
                ·
                  refine ⟨8577602591480579140642613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5718401727653719427095075 8577602591480579140642613)
                  ·
                    refine ⟨804150242951304294435245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8577602591480579140642613 804150242951304294435245)
                    ·
                      rfl

theorem cell23_4698231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 1, 2, 1, 5].length) (baseStart_4698231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4698231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4698231 prefixEnd_4698231 := by exact prefixLift 4698231
  have htrace : WordTrace (prefixWord ++ tailWord_4698231) baseStart_4698231 baseEnd_4698231 := by
    simpa [prefixWord, tailWord_4698231, baseEnd_4698231] using wordTrace_append hprefix tailTrace_4698231
  have hstable : (prefixWord ++ tailWord_4698231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4698231).length < 2 ^ (prefixWord ++ tailWord_4698231).sum := by decide
  have hdescent : baseEnd_4698231 < baseStart_4698231 := by decide
  rcases family_descends (prefixWord ++ tailWord_4698231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4698244 : List Nat := [2, 3, 2, 1, 2, 1, 3, 2, 1, 6]
def baseStart_4698244 : Nat := 118140960795 + 4698244 * 2 ^ 59
def prefixEnd_4698244 : Nat := 4983230072969 + 3 ^ 40 * 4698244 * 2
def baseEnd_4698244 : Nat := 804152468034140444147725

theorem tailTrace_4698244 : CollatzResearch.WordTrace tailWord_4698244 prefixEnd_4698244 804152468034140444147725 := by
  unfold tailWord_4698244
  simp only [CollatzResearch.WordTrace]
  refine ⟨85679518195535929519142893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114239357594047906025523857 85679518195535929519142893)
  ·
    refine ⟨32129819323325973569678585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85679518195535929519142893 32129819323325973569678585)
    ·
      refine ⟨24097364492494480177258939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32129819323325973569678585 24097364492494480177258939)
      ·
        refine ⟨36146046738741720265888409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24097364492494480177258939 36146046738741720265888409)
        ·
          refine ⟨27109535054056290199416307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36146046738741720265888409 27109535054056290199416307)
          ·
            refine ⟨40664302581084435299124461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27109535054056290199416307 40664302581084435299124461)
            ·
              refine ⟨15249113467906663237171673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40664302581084435299124461 15249113467906663237171673)
              ·
                refine ⟨11436835100929997427878755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15249113467906663237171673 11436835100929997427878755)
                ·
                  refine ⟨17155252651394996141818133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11436835100929997427878755 17155252651394996141818133)
                  ·
                    refine ⟨804152468034140444147725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17155252651394996141818133 804152468034140444147725)
                    ·
                      rfl

theorem cell23_4698244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 2, 1, 6].length) (baseStart_4698244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4698244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4698244 prefixEnd_4698244 := by exact prefixLift 4698244
  have htrace : WordTrace (prefixWord ++ tailWord_4698244) baseStart_4698244 baseEnd_4698244 := by
    simpa [prefixWord, tailWord_4698244, baseEnd_4698244] using wordTrace_append hprefix tailTrace_4698244
  have hstable : (prefixWord ++ tailWord_4698244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4698244).length < 2 ^ (prefixWord ++ tailWord_4698244).sum := by decide
  have hdescent : baseEnd_4698244 < baseStart_4698244 := by decide
  rcases family_descends (prefixWord ++ tailWord_4698244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4698248 : List Nat := [2, 1, 3, 4, 1, 2, 3, 1, 1, 5]
def baseStart_4698248 : Nat := 118140960795 + 4698248 * 2 ^ 59
def prefixEnd_4698248 : Nat := 4983230072969 + 3 ^ 40 * 4698248 * 2
def baseEnd_4698248 : Nat := 804153152675013105597719

theorem tailTrace_4698248 : CollatzResearch.WordTrace tailWord_4698248 prefixEnd_4698248 804153152675013105597719 := by
  unfold tailWord_4698248
  simp only [CollatzResearch.WordTrace]
  refine ⟨85679591141528683860715699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114239454855371578480954265 85679591141528683860715699)
  ·
    refine ⟨128519386712293025791073549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85679591141528683860715699 128519386712293025791073549)
    ·
      refine ⟨48194770017109884671652581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 128519386712293025791073549 48194770017109884671652581)
      ·
        refine ⟨9036519378208103375934859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48194770017109884671652581 9036519378208103375934859)
        ·
          refine ⟨13554779067312155063902289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9036519378208103375934859 13554779067312155063902289)
          ·
            refine ⟨10166084300484116297926717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13554779067312155063902289 10166084300484116297926717)
            ·
              refine ⟨3812281612681543611722519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10166084300484116297926717 3812281612681543611722519)
              ·
                refine ⟨5718422419022315417583779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3812281612681543611722519 5718422419022315417583779)
                ·
                  refine ⟨8577633628533473126375669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5718422419022315417583779 8577633628533473126375669)
                  ·
                    refine ⟨804153152675013105597719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8577633628533473126375669 804153152675013105597719)
                    ·
                      rfl

theorem cell23_4698248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 3, 1, 1, 5].length) (baseStart_4698248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4698248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4698248 prefixEnd_4698248 := by exact prefixLift 4698248
  have htrace : WordTrace (prefixWord ++ tailWord_4698248) baseStart_4698248 baseEnd_4698248 := by
    simpa [prefixWord, tailWord_4698248, baseEnd_4698248] using wordTrace_append hprefix tailTrace_4698248
  have hstable : (prefixWord ++ tailWord_4698248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4698248).length < 2 ^ (prefixWord ++ tailWord_4698248).sum := by decide
  have hdescent : baseEnd_4698248 < baseStart_4698248 := by decide
  rcases family_descends (prefixWord ++ tailWord_4698248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4698261 : List Nat := [1, 3, 2, 1, 1, 1, 6, 2, 2, 4]
def baseStart_4698261 : Nat := 118140960795 + 4698261 * 2 ^ 59
def prefixEnd_4698261 : Nat := 4983230072969 + 3 ^ 40 * 4698261 * 2
def baseEnd_4698261 : Nat := 804155377757849255310199

theorem tailTrace_4698261 : CollatzResearch.WordTrace tailWord_4698261 prefixEnd_4698261 804155377757849255310199 := by
  unfold tailWord_4698261
  simp only [CollatzResearch.WordTrace]
  refine ⟨171359656432010270941654637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114239770954673513961103091 171359656432010270941654637)
  ·
    refine ⟨64259871162003851603120489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 171359656432010270941654637 64259871162003851603120489)
    ·
      refine ⟨48194903371502888702340367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64259871162003851603120489 48194903371502888702340367)
      ·
        refine ⟨72292355057254333053510551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48194903371502888702340367 72292355057254333053510551)
        ·
          refine ⟨108438532585881499580265827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72292355057254333053510551 108438532585881499580265827)
          ·
            refine ⟨162657798878822249370398741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108438532585881499580265827 162657798878822249370398741)
            ·
              refine ⟨7624584322444792939237441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 162657798878822249370398741 7624584322444792939237441)
              ·
                refine ⟨5718438241833594704428081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7624584322444792939237441 5718438241833594704428081)
                ·
                  refine ⟨4288828681375196028321061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5718438241833594704428081 4288828681375196028321061)
                  ·
                    refine ⟨804155377757849255310199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4288828681375196028321061 804155377757849255310199)
                    ·
                      rfl

theorem cell23_4698261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 6, 2, 2, 4].length) (baseStart_4698261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4698261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4698261 prefixEnd_4698261 := by exact prefixLift 4698261
  have htrace : WordTrace (prefixWord ++ tailWord_4698261) baseStart_4698261 baseEnd_4698261 := by
    simpa [prefixWord, tailWord_4698261, baseEnd_4698261] using wordTrace_append hprefix tailTrace_4698261
  have hstable : (prefixWord ++ tailWord_4698261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4698261).length < 2 ^ (prefixWord ++ tailWord_4698261).sum := by decide
  have hdescent : baseEnd_4698261 < baseStart_4698261 := by decide
  rcases family_descends (prefixWord ++ tailWord_4698261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4698268 : List Nat := [2, 2, 3, 2, 1, 1, 2, 3, 3, 2, 2]
def baseStart_4698268 : Nat := 118140960795 + 4698268 * 2 ^ 59
def prefixEnd_4698268 : Nat := 4983230072969 + 3 ^ 40 * 4698268 * 2
def baseEnd_4698268 : Nat := 2412469727638129238543065

theorem tailTrace_4698268 : CollatzResearch.WordTrace tailWord_4698268 prefixEnd_4698268 2412469727638129238543065 := by
  unfold tailWord_4698268
  simp only [CollatzResearch.WordTrace]
  refine ⟨85679955871492455568579729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114239941161989940758106305 85679955871492455568579729)
  ·
    refine ⟨64259966903619341676434797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85679955871492455568579729 64259966903619341676434797)
    ·
      refine ⟨24097487588857253128663049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64259966903619341676434797 24097487588857253128663049)
      ·
        refine ⟨18073115691642939846497287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24097487588857253128663049 18073115691642939846497287)
        ·
          refine ⟨27109673537464409769745931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18073115691642939846497287 27109673537464409769745931)
          ·
            refine ⟨40664510306196614654618897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27109673537464409769745931 40664510306196614654618897)
            ·
              refine ⟨30498382729647460990964173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40664510306196614654618897 30498382729647460990964173)
              ·
                refine ⟨11436893523617797871611565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30498382729647460990964173 11436893523617797871611565)
                ·
                  refine ⟨4288835071356674201854337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11436893523617797871611565 4288835071356674201854337)
                  ·
                    refine ⟨3216626303517505651390753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4288835071356674201854337 3216626303517505651390753)
                    ·
                      refine ⟨2412469727638129238543065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3216626303517505651390753 2412469727638129238543065)
                      ·
                        rfl

theorem cell23_4698268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 3, 3, 2, 2].length) (baseStart_4698268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4698268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4698268 prefixEnd_4698268 := by exact prefixLift 4698268
  have htrace : WordTrace (prefixWord ++ tailWord_4698268) baseStart_4698268 baseEnd_4698268 := by
    simpa [prefixWord, tailWord_4698268, baseEnd_4698268] using wordTrace_append hprefix tailTrace_4698268
  have hstable : (prefixWord ++ tailWord_4698268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4698268).length < 2 ^ (prefixWord ++ tailWord_4698268).sum := by decide
  have hdescent : baseEnd_4698268 < baseStart_4698268 := by decide
  rcases family_descends (prefixWord ++ tailWord_4698268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4698271 : List Nat := [1, 1, 2, 6, 1, 1, 1, 2, 3, 2, 3]
def baseStart_4698271 : Nat := 118140960795 + 4698271 * 2 ^ 59
def prefixEnd_4698271 : Nat := 4983230072969 + 3 ^ 40 * 4698271 * 2
def baseEnd_4698271 : Nat := 2412471268080092726805551

theorem tailTrace_4698271 : CollatzResearch.WordTrace tailWord_4698271 prefixEnd_4698271 2412471268080092726805551 := by
  unfold tailWord_4698271
  simp only [CollatzResearch.WordTrace]
  refine ⟨171360021161974042649518667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114240014107982695099679111 171360021161974042649518667)
  ·
    refine ⟨257040031742961063974278001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171360021161974042649518667 257040031742961063974278001)
    ·
      refine ⟨192780023807220797980708501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 257040031742961063974278001 192780023807220797980708501)
      ·
        refine ⟨9036563615963474905345711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 192780023807220797980708501 9036563615963474905345711)
        ·
          refine ⟨13554845423945212358018567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9036563615963474905345711 13554845423945212358018567)
          ·
            refine ⟨20332268135917818537027851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13554845423945212358018567 20332268135917818537027851)
            ·
              refine ⟨30498402203876727805541777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20332268135917818537027851 30498402203876727805541777)
              ·
                refine ⟨22873801652907545854156333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30498402203876727805541777 22873801652907545854156333)
                ·
                  refine ⟨8577675619840329695308625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22873801652907545854156333 8577675619840329695308625)
                  ·
                    refine ⟨6433256714880247271481469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8577675619840329695308625 6433256714880247271481469)
                    ·
                      refine ⟨2412471268080092726805551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6433256714880247271481469 2412471268080092726805551)
                      ·
                        rfl

theorem cell23_4698271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 2, 3, 2, 3].length) (baseStart_4698271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4698271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4698271 prefixEnd_4698271 := by exact prefixLift 4698271
  have htrace : WordTrace (prefixWord ++ tailWord_4698271) baseStart_4698271 baseEnd_4698271 := by
    simpa [prefixWord, tailWord_4698271, baseEnd_4698271] using wordTrace_append hprefix tailTrace_4698271
  have hstable : (prefixWord ++ tailWord_4698271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4698271).length < 2 ^ (prefixWord ++ tailWord_4698271).sum := by decide
  have hdescent : baseEnd_4698271 < baseStart_4698271 := by decide
  rcases family_descends (prefixWord ++ tailWord_4698271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4698285 : List Nat := [1, 5, 2, 1, 2, 2, 1, 2, 3, 2, 2]
def baseStart_4698285 : Nat := 118140960795 + 4698285 * 2 ^ 59
def prefixEnd_4698285 : Nat := 4983230072969 + 3 ^ 40 * 4698285 * 2
def baseEnd_4698285 : Nat := 2412478456809255672030487

theorem tailTrace_4698285 : CollatzResearch.WordTrace tailWord_4698285 prefixEnd_4698285 2412478456809255672030487 := by
  unfold tailWord_4698285
  simp only [CollatzResearch.WordTrace]
  refine ⟨171360531783923323040528309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114240354522615548693685539 171360531783923323040528309)
  ·
    refine ⟨16065049854742811535049529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 171360531783923323040528309 16065049854742811535049529)
    ·
      refine ⟨12048787391057108651287147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16065049854742811535049529 12048787391057108651287147)
      ·
        refine ⟨18073181086585662976930721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12048787391057108651287147 18073181086585662976930721)
        ·
          refine ⟨13554885814939247232698041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18073181086585662976930721 13554885814939247232698041)
          ·
            refine ⟨10166164361204435424523531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13554885814939247232698041 10166164361204435424523531)
            ·
              refine ⟨15249246541806653136785297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10166164361204435424523531 15249246541806653136785297)
              ·
                refine ⟨11436934906354989852588973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15249246541806653136785297 11436934906354989852588973)
                ·
                  refine ⟨4288850589883121194720865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11436934906354989852588973 4288850589883121194720865)
                  ·
                    refine ⟨3216637942412340896040649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4288850589883121194720865 3216637942412340896040649)
                    ·
                      refine ⟨2412478456809255672030487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3216637942412340896040649 2412478456809255672030487)
                      ·
                        rfl

theorem cell23_4698285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 2, 3, 2, 2].length) (baseStart_4698285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4698285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4698285 prefixEnd_4698285 := by exact prefixLift 4698285
  have htrace : WordTrace (prefixWord ++ tailWord_4698285) baseStart_4698285 baseEnd_4698285 := by
    simpa [prefixWord, tailWord_4698285, baseEnd_4698285] using wordTrace_append hprefix tailTrace_4698285
  have hstable : (prefixWord ++ tailWord_4698285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4698285).length < 2 ^ (prefixWord ++ tailWord_4698285).sum := by decide
  have hdescent : baseEnd_4698285 < baseStart_4698285 := by decide
  rcases family_descends (prefixWord ++ tailWord_4698285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4698287 : List Nat := [1, 1, 2, 1, 2, 3, 1, 1, 4, 7]
def baseStart_4698287 : Nat := 118140960795 + 4698287 * 2 ^ 59
def prefixEnd_4698287 : Nat := 4983230072969 + 3 ^ 40 * 4698287 * 2
def baseEnd_4698287 : Nat := 804159827923521554735159

theorem tailTrace_4698287 : CollatzResearch.WordTrace tailWord_4698287 prefixEnd_4698287 804159827923521554735159 := by
  unfold tailWord_4698287
  simp only [CollatzResearch.WordTrace]
  refine ⟨171360604729916077382101115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114240403153277384921400743 171360604729916077382101115)
  ·
    refine ⟨257040907094874116073151673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171360604729916077382101115 257040907094874116073151673)
    ·
      refine ⟨192780680321155587054863755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 257040907094874116073151673 192780680321155587054863755)
      ·
        refine ⟨289171020481733380582295633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192780680321155587054863755 289171020481733380582295633)
        ·
          refine ⟨216878265361300035436721725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 289171020481733380582295633 216878265361300035436721725)
          ·
            refine ⟨81329349510487513288770647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 216878265361300035436721725 81329349510487513288770647)
            ·
              refine ⟨121994024265731269933155971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81329349510487513288770647 121994024265731269933155971)
              ·
                refine ⟨182991036398596904899733957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 121994024265731269933155971 182991036398596904899733957)
                ·
                  refine ⟨34310819324736919668700117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 182991036398596904899733957 34310819324736919668700117)
                  ·
                    refine ⟨804159827923521554735159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34310819324736919668700117 804159827923521554735159)
                    ·
                      rfl

theorem cell23_4698287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 1, 4, 7].length) (baseStart_4698287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4698287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4698287 prefixEnd_4698287 := by exact prefixLift 4698287
  have htrace : WordTrace (prefixWord ++ tailWord_4698287) baseStart_4698287 baseEnd_4698287 := by
    simpa [prefixWord, tailWord_4698287, baseEnd_4698287] using wordTrace_append hprefix tailTrace_4698287
  have hstable : (prefixWord ++ tailWord_4698287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4698287).length < 2 ^ (prefixWord ++ tailWord_4698287).sum := by decide
  have hdescent : baseEnd_4698287 < baseStart_4698287 := by decide
  rcases family_descends (prefixWord ++ tailWord_4698287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4698301 : List Nat := [1, 4, 1, 2, 1, 1, 1, 4, 4, 1, 3]
def baseStart_4698301 : Nat := 118140960795 + 4698301 * 2 ^ 59
def prefixEnd_4698301 : Nat := 4983230072969 + 3 ^ 40 * 4698301 * 2
def baseEnd_4698301 : Nat := 2412486672499727609430413

theorem tailTrace_4698301 : CollatzResearch.WordTrace tailWord_4698301 prefixEnd_4698301 2412486672499727609430413 := by
  unfold tailWord_4698301
  simp only [CollatzResearch.WordTrace]
  refine ⟨171361115351865357773110757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114240743567910238515407171 171361115351865357773110757)
  ·
    refine ⟨32130209128474754582458267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 171361115351865357773110757 32130209128474754582458267)
    ·
      refine ⟨48195313692712131873687401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32130209128474754582458267 48195313692712131873687401)
      ·
        refine ⟨36146485269534098905265551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48195313692712131873687401 36146485269534098905265551)
        ·
          refine ⟨54219727904301148357898327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36146485269534098905265551 54219727904301148357898327)
          ·
            refine ⟨81329591856451722536847491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54219727904301148357898327 81329591856451722536847491)
            ·
              refine ⟨121994387784677583805271237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81329591856451722536847491 121994387784677583805271237)
              ·
                refine ⟨22873947709627046963488357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 121994387784677583805271237 22873947709627046963488357)
                ·
                  refine ⟨4288865195555071305654067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22873947709627046963488357 4288865195555071305654067)
                  ·
                    refine ⟨6433297793332606958481101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4288865195555071305654067 6433297793332606958481101)
                    ·
                      refine ⟨2412486672499727609430413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6433297793332606958481101 2412486672499727609430413)
                      ·
                        rfl

theorem cell23_4698301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 4, 4, 1, 3].length) (baseStart_4698301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4698301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4698301 prefixEnd_4698301 := by exact prefixLift 4698301
  have htrace : WordTrace (prefixWord ++ tailWord_4698301) baseStart_4698301 baseEnd_4698301 := by
    simpa [prefixWord, tailWord_4698301, baseEnd_4698301] using wordTrace_append hprefix tailTrace_4698301
  have hstable : (prefixWord ++ tailWord_4698301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4698301).length < 2 ^ (prefixWord ++ tailWord_4698301).sum := by decide
  have hdescent : baseEnd_4698301 < baseStart_4698301 := by decide
  rcases family_descends (prefixWord ++ tailWord_4698301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4698302 : List Nat := [4, 2, 1, 1, 5, 1, 2, 1, 1, 1, 4]
def baseStart_4698302 : Nat := 118140960795 + 4698302 * 2 ^ 59
def prefixEnd_4698302 : Nat := 4983230072969 + 3 ^ 40 * 4698302 * 2
def baseEnd_4698302 : Nat := 2412487185980382105517909

theorem tailTrace_4698302 : CollatzResearch.WordTrace tailWord_4698302 prefixEnd_4698302 2412487185980382105517909 := by
  unfold tailWord_4698302
  simp only [CollatzResearch.WordTrace]
  refine ⟨21420143978107716867987145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 114240767883241156629264773 21420143978107716867987145)
  ·
    refine ⟨16065107983580787650990359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21420143978107716867987145 16065107983580787650990359)
    ·
      refine ⟨24097661975371181476485539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16065107983580787650990359 24097661975371181476485539)
      ·
        refine ⟨36146492963056772214728309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24097661975371181476485539 36146492963056772214728309)
        ·
          refine ⟨3388733715286572395130779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 36146492963056772214728309 3388733715286572395130779)
          ·
            refine ⟨5083100572929858592696169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3388733715286572395130779 5083100572929858592696169)
            ·
              refine ⟨3812325429697393944522127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5083100572929858592696169 3812325429697393944522127)
              ·
                refine ⟨5718488144546090916783191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3812325429697393944522127 5718488144546090916783191)
                ·
                  refine ⟨8577732216819136375174787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5718488144546090916783191 8577732216819136375174787)
                  ·
                    refine ⟨12866598325228704562762181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8577732216819136375174787 12866598325228704562762181)
                    ·
                      refine ⟨2412487185980382105517909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12866598325228704562762181 2412487185980382105517909)
                      ·
                        rfl

theorem cell23_4698302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 2, 1, 1, 1, 4].length) (baseStart_4698302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4698302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4698302 prefixEnd_4698302 := by exact prefixLift 4698302
  have htrace : WordTrace (prefixWord ++ tailWord_4698302) baseStart_4698302 baseEnd_4698302 := by
    simpa [prefixWord, tailWord_4698302, baseEnd_4698302] using wordTrace_append hprefix tailTrace_4698302
  have hstable : (prefixWord ++ tailWord_4698302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4698302).length < 2 ^ (prefixWord ++ tailWord_4698302).sum := by decide
  have hdescent : baseEnd_4698302 < baseStart_4698302 := by decide
  rcases family_descends (prefixWord ++ tailWord_4698302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4698305 : List Nat := [1, 2, 6, 1, 2, 1, 1, 3, 1, 2, 3]
def baseStart_4698305 : Nat := 118140960795 + 4698305 * 2 ^ 59
def prefixEnd_4698305 : Nat := 4983230072969 + 3 ^ 40 * 4698305 * 2
def baseEnd_4698305 : Nat := 2412488726422345593780395

theorem tailTrace_4698305 : CollatzResearch.WordTrace tailWord_4698305 prefixEnd_4698305 2412488726422345593780395 := by
  unfold tailWord_4698305
  simp only [CollatzResearch.WordTrace]
  refine ⟨171361261243850866456256369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114240840829233910970837579 171361261243850866456256369)
  ·
    refine ⟨128520945932888149842192277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171361261243850866456256369 128520945932888149842192277)
    ·
      refine ⟨6024419340604132023852763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 128520945932888149842192277 6024419340604132023852763)
      ·
        refine ⟨9036629010906198035779145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6024419340604132023852763 9036629010906198035779145)
        ·
          refine ⟨6777471758179648526834359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9036629010906198035779145 6777471758179648526834359)
          ·
            refine ⟨10166207637269472790251539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6777471758179648526834359 10166207637269472790251539)
            ·
              refine ⟨15249311455904209185377309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10166207637269472790251539 15249311455904209185377309)
              ·
                refine ⟨5718491795964078444516491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15249311455904209185377309 5718491795964078444516491)
                ·
                  refine ⟨8577737693946117666774737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5718491795964078444516491 8577737693946117666774737)
                  ·
                    refine ⟨6433303270459588250081053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8577737693946117666774737 6433303270459588250081053)
                    ·
                      refine ⟨2412488726422345593780395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6433303270459588250081053 2412488726422345593780395)
                      ·
                        rfl

theorem cell23_4698305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 3, 1, 2, 3].length) (baseStart_4698305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4698305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4698305 prefixEnd_4698305 := by exact prefixLift 4698305
  have htrace : WordTrace (prefixWord ++ tailWord_4698305) baseStart_4698305 baseEnd_4698305 := by
    simpa [prefixWord, tailWord_4698305, baseEnd_4698305] using wordTrace_append hprefix tailTrace_4698305
  have hstable : (prefixWord ++ tailWord_4698305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4698305).length < 2 ^ (prefixWord ++ tailWord_4698305).sum := by decide
  have hdescent : baseEnd_4698305 < baseStart_4698305 := by decide
  rcases family_descends (prefixWord ++ tailWord_4698305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4698318 : List Nat := [4, 1, 1, 1, 4, 2, 1, 1, 4, 1, 3]
def baseStart_4698318 : Nat := 118140960795 + 4698318 * 2 ^ 59
def prefixEnd_4698318 : Nat := 4983230072969 + 3 ^ 40 * 4698318 * 2
def baseEnd_4698318 : Nat := 2412495401670854042917835

theorem tailTrace_4698318 : CollatzResearch.WordTrace tailWord_4698318 prefixEnd_4698318 2412495401670854042917835 := by
  unfold tailWord_4698318
  simp only [CollatzResearch.WordTrace]
  refine ⟨21420216924100471209559951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 114241156928535846450986405 21420216924100471209559951)
  ·
    refine ⟨32130325386150706814339927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21420216924100471209559951 32130325386150706814339927)
    ·
      refine ⟨48195488079226060221509891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32130325386150706814339927 48195488079226060221509891)
      ·
        refine ⟨72293232118839090332264837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48195488079226060221509891 72293232118839090332264837)
        ·
          refine ⟨13554981022282329437299657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 72293232118839090332264837 13554981022282329437299657)
          ·
            refine ⟨10166235766711747077974743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13554981022282329437299657 10166235766711747077974743)
            ·
              refine ⟨15249353650067620616962115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10166235766711747077974743 15249353650067620616962115)
              ·
                refine ⟨22874030475101430925443173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15249353650067620616962115 22874030475101430925443173)
                ·
                  refine ⟨4288880714081518298520595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22874030475101430925443173 4288880714081518298520595)
                  ·
                    refine ⟨6433321071122277447780893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4288880714081518298520595 6433321071122277447780893)
                    ·
                      refine ⟨2412495401670854042917835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6433321071122277447780893 2412495401670854042917835)
                      ·
                        rfl

theorem cell23_4698318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 1, 4, 1, 3].length) (baseStart_4698318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4698318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4698318 prefixEnd_4698318 := by exact prefixLift 4698318
  have htrace : WordTrace (prefixWord ++ tailWord_4698318) baseStart_4698318 baseEnd_4698318 := by
    simpa [prefixWord, tailWord_4698318, baseEnd_4698318] using wordTrace_append hprefix tailTrace_4698318
  have hstable : (prefixWord ++ tailWord_4698318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4698318).length < 2 ^ (prefixWord ++ tailWord_4698318).sum := by decide
  have hdescent : baseEnd_4698318 < baseStart_4698318 := by decide
  rcases family_descends (prefixWord ++ tailWord_4698318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4698332 : List Nat := [2, 2, 5, 2, 2, 1, 1, 1, 1, 2, 4]
def baseStart_4698332 : Nat := 118140960795 + 4698332 * 2 ^ 59
def prefixEnd_4698332 : Nat := 4983230072969 + 3 ^ 40 * 4698332 * 2
def baseEnd_4698332 : Nat := 2412502590400016988142771

theorem tailTrace_4698332 : CollatzResearch.WordTrace tailWord_4698332 prefixEnd_4698332 2412502590400016988142771 := by
  unfold tailWord_4698332
  simp only [CollatzResearch.WordTrace]
  refine ⟨85681123007376525033744625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114241497343168700044992833 85681123007376525033744625)
  ·
    refine ⟨64260842255532393775308469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85681123007376525033744625 64260842255532393775308469)
    ·
      refine ⟨6024453961456161916435169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 64260842255532393775308469 6024453961456161916435169)
      ·
        refine ⟨4518340471092121437326377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6024453961456161916435169 4518340471092121437326377)
        ·
          refine ⟨3388755353319091077994783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4518340471092121437326377 3388755353319091077994783)
          ·
            refine ⟨5083133029978636616992175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3388755353319091077994783 5083133029978636616992175)
            ·
              refine ⟨7624699544967954925488263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5083133029978636616992175 7624699544967954925488263)
              ·
                refine ⟨11437049317451932388232395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7624699544967954925488263 11437049317451932388232395)
                ·
                  refine ⟨17155573976177898582348593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11437049317451932388232395 17155573976177898582348593)
                  ·
                    refine ⟨12866680482133423936761445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17155573976177898582348593 12866680482133423936761445)
                    ·
                      refine ⟨2412502590400016988142771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12866680482133423936761445 2412502590400016988142771)
                      ·
                        rfl

theorem cell23_4698332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 1, 1, 1, 2, 4].length) (baseStart_4698332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4698332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4698332 prefixEnd_4698332 := by exact prefixLift 4698332
  have htrace : WordTrace (prefixWord ++ tailWord_4698332) baseStart_4698332 baseEnd_4698332 := by
    simpa [prefixWord, tailWord_4698332, baseEnd_4698332] using wordTrace_append hprefix tailTrace_4698332
  have hstable : (prefixWord ++ tailWord_4698332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4698332).length < 2 ^ (prefixWord ++ tailWord_4698332).sum := by decide
  have hdescent : baseEnd_4698332 < baseStart_4698332 := by decide
  rcases family_descends (prefixWord ++ tailWord_4698332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4698358 : List Nat := [5, 1, 1, 1, 1, 1, 2, 4, 1, 4, 2]
def baseStart_4698358 : Nat := 118140960795 + 4698358 * 2 ^ 59
def prefixEnd_4698358 : Nat := 4983230072969 + 3 ^ 40 * 4698358 * 2
def baseEnd_4698358 : Nat := 2412515940897033886417651

theorem tailTrace_4698358 : CollatzResearch.WordTrace tailWord_4698358 prefixEnd_4698358 2412515940897033886417651 := by
  unfold tailWord_4698358
  simp only [CollatzResearch.WordTrace]
  refine ⟨10710199644541178531745983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 114242129541772571005290485 10710199644541178531745983)
  ·
    refine ⟨16065299466811767797618975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10710199644541178531745983 16065299466811767797618975)
    ·
      refine ⟨24097949200217651696428463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16065299466811767797618975 24097949200217651696428463)
      ·
        refine ⟨36146923800326477544642695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24097949200217651696428463 36146923800326477544642695)
        ·
          refine ⟨54220385700489716316964043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36146923800326477544642695 54220385700489716316964043)
          ·
            refine ⟨81330578550734574475446065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54220385700489716316964043 81330578550734574475446065)
            ·
              refine ⟨60997933913050930856584549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81330578550734574475446065 60997933913050930856584549)
              ·
                refine ⟨11437112608697049535609603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 60997933913050930856584549 11437112608697049535609603)
                ·
                  refine ⟨17155668913045574303414405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11437112608697049535609603 17155668913045574303414405)
                  ·
                    refine ⟨3216687921196045181890201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17155668913045574303414405 3216687921196045181890201)
                    ·
                      refine ⟨2412515940897033886417651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3216687921196045181890201 2412515940897033886417651)
                      ·
                        rfl

theorem cell23_4698358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 4, 1, 4, 2].length) (baseStart_4698358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4698358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4698358 prefixEnd_4698358 := by exact prefixLift 4698358
  have htrace : WordTrace (prefixWord ++ tailWord_4698358) baseStart_4698358 baseEnd_4698358 := by
    simpa [prefixWord, tailWord_4698358, baseEnd_4698358] using wordTrace_append hprefix tailTrace_4698358
  have hstable : (prefixWord ++ tailWord_4698358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4698358).length < 2 ^ (prefixWord ++ tailWord_4698358).sum := by decide
  have hdescent : baseEnd_4698358 < baseStart_4698358 := by decide
  rcases family_descends (prefixWord ++ tailWord_4698358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4698431 : List Nat := [1, 1, 2, 2, 4, 1, 1, 4, 2, 1, 4]
def baseStart_4698431 : Nat := 118140960795 + 4698431 * 2 ^ 59
def prefixEnd_4698431 : Nat := 4983230072969 + 3 ^ 40 * 4698431 * 2
def baseEnd_4698431 : Nat := 2412553424984812100804815

theorem tailTrace_4698431 : CollatzResearch.WordTrace tailWord_4698431 prefixEnd_4698431 2412553424984812100804815 := by
  unfold tailWord_4698431
  simp only [CollatzResearch.WordTrace]
  refine ⟨171365856841394389975343147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114243904560929593316895431 171365856841394389975343147)
  ·
    refine ⟨257048785262091584963014721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171365856841394389975343147 257048785262091584963014721)
    ·
      refine ⟨192786588946568688722261041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 257048785262091584963014721 192786588946568688722261041)
      ·
        refine ⟨144589941709926516541695781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 192786588946568688722261041 144589941709926516541695781)
        ·
          refine ⟨27110614070611221851567959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 144589941709926516541695781 27110614070611221851567959)
          ·
            refine ⟨40665921105916832777351939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27110614070611221851567959 40665921105916832777351939)
            ·
              refine ⟨60998881658875249166027909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40665921105916832777351939 60998881658875249166027909)
              ·
                refine ⟨11437290311039109218630233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 60998881658875249166027909 11437290311039109218630233)
                ·
                  refine ⟨8577967733279331913972675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11437290311039109218630233 8577967733279331913972675)
                  ·
                    refine ⟨12866951599918997870959013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8577967733279331913972675 12866951599918997870959013)
                    ·
                      refine ⟨2412553424984812100804815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12866951599918997870959013 2412553424984812100804815)
                      ·
                        rfl

theorem cell23_4698431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 4, 2, 1, 4].length) (baseStart_4698431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4698431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4698431 prefixEnd_4698431 := by exact prefixLift 4698431
  have htrace : WordTrace (prefixWord ++ tailWord_4698431) baseStart_4698431 baseEnd_4698431 := by
    simpa [prefixWord, tailWord_4698431, baseEnd_4698431] using wordTrace_append hprefix tailTrace_4698431
  have hstable : (prefixWord ++ tailWord_4698431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4698431).length < 2 ^ (prefixWord ++ tailWord_4698431).sum := by decide
  have hdescent : baseEnd_4698431 < baseStart_4698431 := by decide
  rcases family_descends (prefixWord ++ tailWord_4698431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4698441 : List Nat := [1, 2, 1, 1, 2, 3, 1, 5, 3, 4]
def baseStart_4698441 : Nat := 118140960795 + 4698441 * 2 ^ 59
def prefixEnd_4698441 : Nat := 4983230072969 + 3 ^ 40 * 4698441 * 2
def baseEnd_4698441 : Nat := 804186186597119020559923

theorem tailTrace_4698441 : CollatzResearch.WordTrace tailWord_4698441 prefixEnd_4698441 804186186597119020559923 := by
  unfold tailWord_4698441
  simp only [CollatzResearch.WordTrace]
  refine ⟨171366221571358161683207177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114244147714238774455471451 171366221571358161683207177)
  ·
    refine ⟨128524666178518621262405383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171366221571358161683207177 128524666178518621262405383)
    ·
      refine ⟨192786999267777931893608075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128524666178518621262405383 192786999267777931893608075)
      ·
        refine ⟨289180498901666897840412113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192786999267777931893608075 289180498901666897840412113)
        ·
          refine ⟨216885374176250173380309085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 289180498901666897840412113 216885374176250173380309085)
          ·
            refine ⟨81332015316093815017615907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 216885374176250173380309085 81332015316093815017615907)
            ·
              refine ⟨121998022974140722526423861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81332015316093815017615907 121998022974140722526423861)
              ·
                refine ⟨11437314653825692736852237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 121998022974140722526423861 11437314653825692736852237)
                ·
                  refine ⟨4288992995184634776319589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11437314653825692736852237 4288992995184634776319589)
                  ·
                    refine ⟨804186186597119020559923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4288992995184634776319589 804186186597119020559923)
                    ·
                      rfl

theorem cell23_4698441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 5, 3, 4].length) (baseStart_4698441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4698441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4698441 prefixEnd_4698441 := by exact prefixLift 4698441
  have htrace : WordTrace (prefixWord ++ tailWord_4698441) baseStart_4698441 baseEnd_4698441 := by
    simpa [prefixWord, tailWord_4698441, baseEnd_4698441] using wordTrace_append hprefix tailTrace_4698441
  have hstable : (prefixWord ++ tailWord_4698441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4698441).length < 2 ^ (prefixWord ++ tailWord_4698441).sum := by decide
  have hdescent : baseEnd_4698441 < baseStart_4698441 := by decide
  rcases family_descends (prefixWord ++ tailWord_4698441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4698448 : List Nat := [2, 1, 1, 1, 1, 7, 1, 1, 2, 4, 2]
def baseStart_4698448 : Nat := 118140960795 + 4698448 * 2 ^ 59
def prefixEnd_4698448 : Nat := 4983230072969 + 3 ^ 40 * 4698448 * 2
def baseEnd_4698448 : Nat := 2412562154155938534292237

theorem tailTrace_4698448 : CollatzResearch.WordTrace tailWord_4698448 prefixEnd_4698448 2412562154155938534292237 := by
  unfold tailWord_4698448
  simp only [CollatzResearch.WordTrace]
  refine ⟨85683238441166400939355999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114244317921555201252474665 85683238441166400939355999)
  ·
    refine ⟨128524857661749601409033999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85683238441166400939355999 128524857661749601409033999)
    ·
      refine ⟨192787286492624402113550999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128524857661749601409033999 192787286492624402113550999)
      ·
        refine ⟨289180929738936603170326499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192787286492624402113550999 289180929738936603170326499)
        ·
          refine ⟨433771394608404904755489749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 289180929738936603170326499 433771394608404904755489749)
          ·
            refine ⟨10166517061134489955206791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 433771394608404904755489749 10166517061134489955206791)
            ·
              refine ⟨15249775591701734932810187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10166517061134489955206791 15249775591701734932810187)
              ·
                refine ⟨22874663387552602399215281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15249775591701734932810187 22874663387552602399215281)
                ·
                  refine ⟨17155997540664451799411461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22874663387552602399215281 17155997540664451799411461)
                  ·
                    refine ⟨3216749538874584712389649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17155997540664451799411461 3216749538874584712389649)
                    ·
                      refine ⟨2412562154155938534292237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3216749538874584712389649 2412562154155938534292237)
                      ·
                        rfl

theorem cell23_4698448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 1, 2, 4, 2].length) (baseStart_4698448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4698448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4698448 prefixEnd_4698448 := by exact prefixLift 4698448
  have htrace : WordTrace (prefixWord ++ tailWord_4698448) baseStart_4698448 baseEnd_4698448 := by
    simpa [prefixWord, tailWord_4698448, baseEnd_4698448] using wordTrace_append hprefix tailTrace_4698448
  have hstable : (prefixWord ++ tailWord_4698448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4698448).length < 2 ^ (prefixWord ++ tailWord_4698448).sum := by decide
  have hdescent : baseEnd_4698448 < baseStart_4698448 := by decide
  rcases family_descends (prefixWord ++ tailWord_4698448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4698508 : List Nat := [2, 2, 1, 2, 1, 4, 1, 2, 1, 5, 2]
def baseStart_4698508 : Nat := 118140960795 + 4698508 * 2 ^ 59
def prefixEnd_4698508 : Nat := 4983230072969 + 3 ^ 40 * 4698508 * 2
def baseEnd_4698508 : Nat := 2412592962995208299541961

theorem tailTrace_4698508 : CollatzResearch.WordTrace tailWord_4698508 prefixEnd_4698508 2412592962995208299541961 := by
  unfold tailWord_4698508
  simp only [CollatzResearch.WordTrace]
  refine ⟨85684332631057716062948089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114245776841410288083930785 85684332631057716062948089)
  ·
    refine ⟨64263249473293287047211067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85684332631057716062948089 64263249473293287047211067)
    ·
      refine ⟨96394874209939930570816601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64263249473293287047211067 96394874209939930570816601)
      ·
        refine ⟨72296155657454947928112451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96394874209939930570816601 72296155657454947928112451)
        ·
          refine ⟨108444233486182421892168677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72296155657454947928112451 108444233486182421892168677)
          ·
            refine ⟨20333293778659204104781627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 108444233486182421892168677 20333293778659204104781627)
            ·
              refine ⟨30499940667988806157172441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20333293778659204104781627 30499940667988806157172441)
              ·
                refine ⟨22874955500991604617879331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30499940667988806157172441 22874955500991604617879331)
                ·
                  refine ⟨34312433251487406926818997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22874955500991604617879331 34312433251487406926818997)
                  ·
                    refine ⟨3216790617326944399389281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34312433251487406926818997 3216790617326944399389281)
                    ·
                      refine ⟨2412592962995208299541961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3216790617326944399389281 2412592962995208299541961)
                      ·
                        rfl

theorem cell23_4698508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 2, 1, 5, 2].length) (baseStart_4698508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4698508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4698508 prefixEnd_4698508 := by exact prefixLift 4698508
  have htrace : WordTrace (prefixWord ++ tailWord_4698508) baseStart_4698508 baseEnd_4698508 := by
    simpa [prefixWord, tailWord_4698508, baseEnd_4698508] using wordTrace_append hprefix tailTrace_4698508
  have hstable : (prefixWord ++ tailWord_4698508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4698508).length < 2 ^ (prefixWord ++ tailWord_4698508).sum := by decide
  have hdescent : baseEnd_4698508 < baseStart_4698508 := by decide
  rcases family_descends (prefixWord ++ tailWord_4698508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4698532 : List Nat := [2, 3, 1, 2, 1, 1, 5, 3, 1, 1, 3]
def baseStart_4698532 : Nat := 118140960795 + 4698532 * 2 ^ 59
def prefixEnd_4698532 : Nat := 4983230072969 + 3 ^ 40 * 4698532 * 2
def baseEnd_4698532 : Nat := 2412605286530916205641851

theorem tailTrace_4698532 : CollatzResearch.WordTrace tailWord_4698532 prefixEnd_4698532 2412605286530916205641851 := by
  unfold tailWord_4698532
  simp only [CollatzResearch.WordTrace]
  refine ⟨85684770307014242112384925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114246360409352322816513233 85684770307014242112384925)
  ·
    refine ⟨32131788865130340792144347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85684770307014242112384925 32131788865130340792144347)
    ·
      refine ⟨48197683297695511188216521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32131788865130340792144347 48197683297695511188216521)
      ·
        refine ⟨36148262473271633391162391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48197683297695511188216521 36148262473271633391162391)
        ·
          refine ⟨54222393709907450086743587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36148262473271633391162391 54222393709907450086743587)
          ·
            refine ⟨81333590564861175130115381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54222393709907450086743587 81333590564861175130115381)
            ·
              refine ⟨7625024115455735168448317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 81333590564861175130115381 7625024115455735168448317)
              ·
                refine ⟨2859384043295900688168119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7625024115455735168448317 2859384043295900688168119)
                ·
                  refine ⟨4289076064943851032252179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2859384043295900688168119 4289076064943851032252179)
                  ·
                    refine ⟨6433614097415776548378269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4289076064943851032252179 6433614097415776548378269)
                    ·
                      refine ⟨2412605286530916205641851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6433614097415776548378269 2412605286530916205641851)
                      ·
                        rfl

theorem cell23_4698532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 5, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 5, 3, 1, 1, 3].length) (baseStart_4698532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4698532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4698532 prefixEnd_4698532 := by exact prefixLift 4698532
  have htrace : WordTrace (prefixWord ++ tailWord_4698532) baseStart_4698532 baseEnd_4698532 := by
    simpa [prefixWord, tailWord_4698532, baseEnd_4698532] using wordTrace_append hprefix tailTrace_4698532
  have hstable : (prefixWord ++ tailWord_4698532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4698532).length < 2 ^ (prefixWord ++ tailWord_4698532).sum := by decide
  have hdescent : baseEnd_4698532 < baseStart_4698532 := by decide
  rcases family_descends (prefixWord ++ tailWord_4698532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4698549 : List Nat := [1, 3, 3, 2, 4, 1, 1, 1, 3, 1, 3]
def baseStart_4698549 : Nat := 118140960795 + 4698549 * 2 ^ 59
def prefixEnd_4698549 : Nat := 4983230072969 + 3 ^ 40 * 4698549 * 2
def baseEnd_4698549 : Nat := 2412614015702042639129273

theorem tailTrace_4698549 : CollatzResearch.WordTrace tailWord_4698549 prefixEnd_4698549 2412614015702042639129273 := by
  unfold tailWord_4698549
  simp only [CollatzResearch.WordTrace]
  refine ⟨171370160654966896128138701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114246773769977930752092467 171370160654966896128138701)
  ·
    refine ⟨64263810245612586048052013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 171370160654966896128138701 64263810245612586048052013)
    ·
      refine ⟨24098928842104719768019505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64263810245612586048052013 24098928842104719768019505)
      ·
        refine ⟨18074196631578539826014629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24098928842104719768019505 18074196631578539826014629)
        ·
          refine ⟨3388911868420976217377743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18074196631578539826014629 3388911868420976217377743)
          ·
            refine ⟨5083367802631464326066615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3388911868420976217377743 5083367802631464326066615)
            ·
              refine ⟨7625051703947196489099923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5083367802631464326066615 7625051703947196489099923)
              ·
                refine ⟨11437577555920794733649885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7625051703947196489099923 11437577555920794733649885)
                ·
                  refine ⟨4289091583470298025118707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11437577555920794733649885 4289091583470298025118707)
                  ·
                    refine ⟨6433637375205447037678061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4289091583470298025118707 6433637375205447037678061)
                    ·
                      refine ⟨2412614015702042639129273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6433637375205447037678061 2412614015702042639129273)
                      ·
                        rfl

theorem cell23_4698549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 1, 1, 3, 1, 3].length) (baseStart_4698549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4698549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4698549 prefixEnd_4698549 := by exact prefixLift 4698549
  have htrace : WordTrace (prefixWord ++ tailWord_4698549) baseStart_4698549 baseEnd_4698549 := by
    simpa [prefixWord, tailWord_4698549, baseEnd_4698549] using wordTrace_append hprefix tailTrace_4698549
  have hstable : (prefixWord ++ tailWord_4698549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4698549).length < 2 ^ (prefixWord ++ tailWord_4698549).sum := by decide
  have hdescent : baseEnd_4698549 < baseStart_4698549 := by decide
  rcases family_descends (prefixWord ++ tailWord_4698549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4698551 : List Nat := [1, 1, 3, 1, 3, 3, 1, 2, 1, 1, 6]
def baseStart_4698551 : Nat := 118140960795 + 4698551 * 2 ^ 59
def prefixEnd_4698551 : Nat := 4983230072969 + 3 ^ 40 * 4698551 * 2
def baseEnd_4698551 : Nat := 2412615042663351631304263

theorem tailTrace_4698551 : CollatzResearch.WordTrace tailWord_4698551 prefixEnd_4698551 2412615042663351631304263 := by
  unfold tailWord_4698551
  simp only [CollatzResearch.WordTrace]
  refine ⟨171370233600959650469711507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114246822400639766979807671 171370233600959650469711507)
  ·
    refine ⟨257055350401439475704567261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171370233600959650469711507 257055350401439475704567261)
    ·
      refine ⟨96395756400539803389212723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 257055350401439475704567261 96395756400539803389212723)
      ·
        refine ⟨144593634600809705083819085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96395756400539803389212723 144593634600809705083819085)
        ·
          refine ⟨54222612975303639406432157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 144593634600809705083819085 54222612975303639406432157)
          ·
            refine ⟨20333479865738864777412059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54222612975303639406432157 20333479865738864777412059)
            ·
              refine ⟨30500219798608297166118089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20333479865738864777412059 30500219798608297166118089)
              ·
                refine ⟨22875164848956222874588567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30500219798608297166118089 22875164848956222874588567)
                ·
                  refine ⟨34312747273434334311882851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22875164848956222874588567 34312747273434334311882851)
                  ·
                    refine ⟨51469120910151501467824277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34312747273434334311882851 51469120910151501467824277)
                    ·
                      refine ⟨2412615042663351631304263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 51469120910151501467824277 2412615042663351631304263)
                      ·
                        rfl

theorem cell23_4698551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 2, 1, 1, 6].length) (baseStart_4698551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4698551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4698551 prefixEnd_4698551 := by exact prefixLift 4698551
  have htrace : WordTrace (prefixWord ++ tailWord_4698551) baseStart_4698551 baseEnd_4698551 := by
    simpa [prefixWord, tailWord_4698551, baseEnd_4698551] using wordTrace_append hprefix tailTrace_4698551
  have hstable : (prefixWord ++ tailWord_4698551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4698551).length < 2 ^ (prefixWord ++ tailWord_4698551).sum := by decide
  have hdescent : baseEnd_4698551 < baseStart_4698551 := by decide
  rcases family_descends (prefixWord ++ tailWord_4698551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4698558 : List Nat := [4, 2, 1, 1, 1, 1, 4, 2, 1, 1, 5]
def baseStart_4698558 : Nat := 118140960795 + 4698558 * 2 ^ 59
def prefixEnd_4698558 : Nat := 4983230072969 + 3 ^ 40 * 4698558 * 2
def baseEnd_4698558 : Nat := 2412618637027933103916731

theorem tailTrace_4698558 : CollatzResearch.WordTrace tailWord_4698558 prefixEnd_4698558 2412618637027933103916731 := by
  unfold tailWord_4698558
  simp only [CollatzResearch.WordTrace]
  refine ⟨21421311113991786333152041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 114246992607956193776810885 21421311113991786333152041)
  ·
    refine ⟨16065983335493839749864031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21421311113991786333152041 16065983335493839749864031)
    ·
      refine ⟨24098975003240759624796047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16065983335493839749864031 24098975003240759624796047)
      ·
        refine ⟨36148462504861139437194071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24098975003240759624796047 36148462504861139437194071)
        ·
          refine ⟨54222693757291709155791107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36148462504861139437194071 54222693757291709155791107)
          ·
            refine ⟨81334040635937563733686661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54222693757291709155791107 81334040635937563733686661)
            ·
              refine ⟨15250132619238293200066249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 81334040635937563733686661 15250132619238293200066249)
              ·
                refine ⟨11437599464428719900049687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15250132619238293200066249 11437599464428719900049687)
                ·
                  refine ⟨17156399196643079850074531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11437599464428719900049687 17156399196643079850074531)
                  ·
                    refine ⟨25734598794964619775111797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17156399196643079850074531 25734598794964619775111797)
                    ·
                      refine ⟨2412618637027933103916731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25734598794964619775111797 2412618637027933103916731)
                      ·
                        rfl

theorem cell23_4698558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 2, 1, 1, 5].length) (baseStart_4698558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4698558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4698558 prefixEnd_4698558 := by exact prefixLift 4698558
  have htrace : WordTrace (prefixWord ++ tailWord_4698558) baseStart_4698558 baseEnd_4698558 := by
    simpa [prefixWord, tailWord_4698558, baseEnd_4698558] using wordTrace_append hprefix tailTrace_4698558
  have hstable : (prefixWord ++ tailWord_4698558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4698558).length < 2 ^ (prefixWord ++ tailWord_4698558).sum := by decide
  have hdescent : baseEnd_4698558 < baseStart_4698558 := by decide
  rcases family_descends (prefixWord ++ tailWord_4698558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4698572 : List Nat := [2, 2, 1, 4, 3, 2, 1, 2, 1, 1, 4]
def baseStart_4698572 : Nat := 118140960795 + 4698572 * 2 ^ 59
def prefixEnd_4698572 : Nat := 4983230072969 + 3 ^ 40 * 4698572 * 2
def baseEnd_4698572 : Nat := 2412625825757096049141667

theorem tailTrace_4698572 : CollatzResearch.WordTrace tailWord_4698572 prefixEnd_4698572 2412625825757096049141667 := by
  unfold tailWord_4698572
  simp only [CollatzResearch.WordTrace]
  refine ⟨85685499766941785528112985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114247333022589047370817313 85685499766941785528112985)
  ·
    refine ⟨64264124825206339146084739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85685499766941785528112985 64264124825206339146084739)
    ·
      refine ⟨96396187237809508719127109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64264124825206339146084739 96396187237809508719127109)
      ·
        refine ⟨18074285107089282884836333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 96396187237809508719127109 18074285107089282884836333)
        ·
          refine ⟨6777856915158481081813625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18074285107089282884836333 6777856915158481081813625)
          ·
            refine ⟨5083392686368860811360219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6777856915158481081813625 5083392686368860811360219)
            ·
              refine ⟨7625089029553291217040329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5083392686368860811360219 7625089029553291217040329)
              ·
                refine ⟨5718816772164968412780247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7625089029553291217040329 5718816772164968412780247)
                ·
                  refine ⟨8578225158247452619170371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5718816772164968412780247 8578225158247452619170371)
                  ·
                    refine ⟨12867337737371178928755557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8578225158247452619170371 12867337737371178928755557)
                    ·
                      refine ⟨2412625825757096049141667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12867337737371178928755557 2412625825757096049141667)
                      ·
                        rfl

theorem cell23_4698572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 1, 2, 1, 1, 4].length) (baseStart_4698572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4698572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4698572 prefixEnd_4698572 := by exact prefixLift 4698572
  have htrace : WordTrace (prefixWord ++ tailWord_4698572) baseStart_4698572 baseEnd_4698572 := by
    simpa [prefixWord, tailWord_4698572, baseEnd_4698572] using wordTrace_append hprefix tailTrace_4698572
  have hstable : (prefixWord ++ tailWord_4698572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4698572).length < 2 ^ (prefixWord ++ tailWord_4698572).sum := by decide
  have hdescent : baseEnd_4698572 < baseStart_4698572 := by decide
  rcases family_descends (prefixWord ++ tailWord_4698572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4698589 : List Nat := [1, 4, 3, 1, 1, 1, 2, 5, 1, 2, 2]
def baseStart_4698589 : Nat := 118140960795 + 4698589 * 2 ^ 59
def prefixEnd_4698589 : Nat := 4983230072969 + 3 ^ 40 * 4698589 * 2
def baseEnd_4698589 : Nat := 2412634554928222482629089

theorem tailTrace_4698589 : CollatzResearch.WordTrace tailWord_4698589 prefixEnd_4698589 2412634554928222482629089 := by
  unfold tailWord_4698589
  simp only [CollatzResearch.WordTrace]
  refine ⟨171371619574821982959594821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114247746383214655306396547 171371619574821982959594821)
  ·
    refine ⟨32132178670279121804924029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 171371619574821982959594821 32132178670279121804924029)
    ·
      refine ⟨12049567001354670676846511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32132178670279121804924029 12049567001354670676846511)
      ·
        refine ⟨18074350502032006015269767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12049567001354670676846511 18074350502032006015269767)
        ·
          refine ⟨27111525753048009022904651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18074350502032006015269767 27111525753048009022904651)
          ·
            refine ⟨40667288629572013534356977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27111525753048009022904651 40667288629572013534356977)
            ·
              refine ⟨30500466472179010150767733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40667288629572013534356977 30500466472179010150767733)
              ·
                refine ⟨2859418731766782201634475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30500466472179010150767733 2859418731766782201634475)
                ·
                  refine ⟨4289128097650173302451713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2859418731766782201634475 4289128097650173302451713)
                  ·
                    refine ⟨3216846073237629976838785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4289128097650173302451713 3216846073237629976838785)
                    ·
                      refine ⟨2412634554928222482629089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3216846073237629976838785 2412634554928222482629089)
                      ·
                        rfl

theorem cell23_4698589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 5, 1, 2, 2].length) (baseStart_4698589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4698589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4698589 prefixEnd_4698589 := by exact prefixLift 4698589
  have htrace : WordTrace (prefixWord ++ tailWord_4698589) baseStart_4698589 baseEnd_4698589 := by
    simpa [prefixWord, tailWord_4698589, baseEnd_4698589] using wordTrace_append hprefix tailTrace_4698589
  have hstable : (prefixWord ++ tailWord_4698589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4698589).length < 2 ^ (prefixWord ++ tailWord_4698589).sum := by decide
  have hdescent : baseEnd_4698589 < baseStart_4698589 := by decide
  rcases family_descends (prefixWord ++ tailWord_4698589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4698606 : List Nat := [4, 1, 2, 1, 2, 2, 4, 2, 1, 2, 2]
def baseStart_4698606 : Nat := 118140960795 + 4698606 * 2 ^ 59
def prefixEnd_4698606 : Nat := 4983230072969 + 3 ^ 40 * 4698606 * 2
def baseEnd_4698606 : Nat := 2412643284099348916116511

theorem tailTrace_4698606 : CollatzResearch.WordTrace tailWord_4698606 prefixEnd_4698606 2412643284099348916116511 := by
  unfold tailWord_4698606
  simp only [CollatzResearch.WordTrace]
  refine ⟨21421529951970049357870459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 114248159743840263241975781 21421529951970049357870459)
  ·
    refine ⟨32132294927955074036805689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21421529951970049357870459 32132294927955074036805689)
    ·
      refine ⟨24099221195966305527604267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32132294927955074036805689 24099221195966305527604267)
      ·
        refine ⟨36148831793949458291406401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24099221195966305527604267 36148831793949458291406401)
        ·
          refine ⟨27111623845462093718554801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36148831793949458291406401 27111623845462093718554801)
          ·
            refine ⟨20333717884096570288916101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27111623845462093718554801 20333717884096570288916101)
            ·
              refine ⟨3812572103268106929171769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20333717884096570288916101 3812572103268106929171769)
              ·
                refine ⟨2859429077451080196878827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3812572103268106929171769 2859429077451080196878827)
                ·
                  refine ⟨4289143616176620295318241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2859429077451080196878827 4289143616176620295318241)
                  ·
                    refine ⟨3216857712132465221488681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4289143616176620295318241 3216857712132465221488681)
                    ·
                      refine ⟨2412643284099348916116511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3216857712132465221488681 2412643284099348916116511)
                      ·
                        rfl

theorem cell23_4698606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 4, 2, 1, 2, 2].length) (baseStart_4698606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4698606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4698606 prefixEnd_4698606 := by exact prefixLift 4698606
  have htrace : WordTrace (prefixWord ++ tailWord_4698606) baseStart_4698606 baseEnd_4698606 := by
    simpa [prefixWord, tailWord_4698606, baseEnd_4698606] using wordTrace_append hprefix tailTrace_4698606
  have hstable : (prefixWord ++ tailWord_4698606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4698606).length < 2 ^ (prefixWord ++ tailWord_4698606).sum := by decide
  have hdescent : baseEnd_4698606 < baseStart_4698606 := by decide
  rcases family_descends (prefixWord ++ tailWord_4698606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4698611 : List Nat := [1, 1, 1, 2, 2, 2, 3, 1, 1, 5, 4]
def baseStart_4698611 : Nat := 118140960795 + 4698611 * 2 ^ 59
def prefixEnd_4698611 : Nat := 4983230072969 + 3 ^ 40 * 4698611 * 2
def baseEnd_4698611 : Nat := 2412645851502621396553987

theorem tailTrace_4698611 : CollatzResearch.WordTrace tailWord_4698611 prefixEnd_4698611 2412645851502621396553987 := by
  unfold tailWord_4698611
  simp only [CollatzResearch.WordTrace]
  refine ⟨171372421980742280716895687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114248281320494853811263791 171372421980742280716895687)
  ·
    refine ⟨257058632971113421075343531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171372421980742280716895687 257058632971113421075343531)
    ·
      refine ⟨385587949456670131613015297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 257058632971113421075343531 385587949456670131613015297)
      ·
        refine ⟨289190962092502598709761473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 385587949456670131613015297 289190962092502598709761473)
        ·
          refine ⟨216893221569376949032321105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 289190962092502598709761473 216893221569376949032321105)
          ·
            refine ⟨162669916177032711774240829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 216893221569376949032321105 162669916177032711774240829)
            ·
              refine ⟨61001218566387266915340311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 162669916177032711774240829 61001218566387266915340311)
              ·
                refine ⟨91501827849580900373010467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61001218566387266915340311 91501827849580900373010467)
                ·
                  refine ⟨137252741774371350559515701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 91501827849580900373010467 137252741774371350559515701)
                  ·
                    refine ⟨12867444541347314114954597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 137252741774371350559515701 12867444541347314114954597)
                    ·
                      refine ⟨2412645851502621396553987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12867444541347314114954597 2412645851502621396553987)
                      ·
                        rfl

theorem cell23_4698611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 1, 1, 5, 4].length) (baseStart_4698611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4698611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4698611 prefixEnd_4698611 := by exact prefixLift 4698611
  have htrace : WordTrace (prefixWord ++ tailWord_4698611) baseStart_4698611 baseEnd_4698611 := by
    simpa [prefixWord, tailWord_4698611, baseEnd_4698611] using wordTrace_append hprefix tailTrace_4698611
  have hstable : (prefixWord ++ tailWord_4698611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4698611).length < 2 ^ (prefixWord ++ tailWord_4698611).sum := by decide
  have hdescent : baseEnd_4698611 < baseStart_4698611 := by decide
  rcases family_descends (prefixWord ++ tailWord_4698611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4698645 : List Nat := [1, 3, 2, 1, 3, 1, 1, 4, 1, 4, 2]
def baseStart_4698645 : Nat := 118140960795 + 4698645 * 2 ^ 59
def prefixEnd_4698645 : Nat := 4983230072969 + 3 ^ 40 * 4698645 * 2
def baseEnd_4698645 : Nat := 2412663309844874263528831

theorem tailTrace_4698645 : CollatzResearch.WordTrace tailWord_4698645 prefixEnd_4698645 2412663309844874263528831 := by
  unfold tailWord_4698645
  simp only [CollatzResearch.WordTrace]
  refine ⟨171373662062619104523633389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114249108041746069682422259 171373662062619104523633389)
  ·
    refine ⟨64265123273482164196362521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 171373662062619104523633389 64265123273482164196362521)
    ·
      refine ⟨48198842455111623147271891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64265123273482164196362521 48198842455111623147271891)
      ·
        refine ⟨72298263682667434720907837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48198842455111623147271891 72298263682667434720907837)
        ·
          refine ⟨27111848881000288020340439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72298263682667434720907837 27111848881000288020340439)
          ·
            refine ⟨40667773321500432030510659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27111848881000288020340439 40667773321500432030510659)
            ·
              refine ⟨61001659982250648045765989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40667773321500432030510659 61001659982250648045765989)
              ·
                refine ⟨11437811246671996508581123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 61001659982250648045765989 11437811246671996508581123)
                ·
                  refine ⟨17156716870007994762871685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11437811246671996508581123 17156716870007994762871685)
                  ·
                    refine ⟨3216884413126499018038441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17156716870007994762871685 3216884413126499018038441)
                    ·
                      refine ⟨2412663309844874263528831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3216884413126499018038441 2412663309844874263528831)
                      ·
                        rfl

theorem cell23_4698645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 4, 1, 4, 2].length) (baseStart_4698645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4698645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4698645 prefixEnd_4698645 := by exact prefixLift 4698645
  have htrace : WordTrace (prefixWord ++ tailWord_4698645) baseStart_4698645 baseEnd_4698645 := by
    simpa [prefixWord, tailWord_4698645, baseEnd_4698645] using wordTrace_append hprefix tailTrace_4698645
  have hstable : (prefixWord ++ tailWord_4698645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4698645).length < 2 ^ (prefixWord ++ tailWord_4698645).sum := by decide
  have hdescent : baseEnd_4698645 < baseStart_4698645 := by decide
  rcases family_descends (prefixWord ++ tailWord_4698645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4698656 : List Nat := [2, 1, 1, 6, 3, 1, 1, 2, 2, 1, 3]
def baseStart_4698656 : Nat := 118140960795 + 4698656 * 2 ^ 59
def prefixEnd_4698656 : Nat := 4983230072969 + 3 ^ 40 * 4698656 * 2
def baseEnd_4698656 : Nat := 2412668958132073720491281

theorem tailTrace_4698656 : CollatzResearch.WordTrace tailWord_4698656 prefixEnd_4698656 2412668958132073720491281 := by
  unfold tailWord_4698656
  simp only [CollatzResearch.WordTrace]
  refine ⟨85687031632789626701141911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114249375510386168934855881 85687031632789626701141911)
  ·
    refine ⟨128530547449184440051712867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85687031632789626701141911 128530547449184440051712867)
    ·
      refine ⟨192795821173776660077569301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128530547449184440051712867 192795821173776660077569301)
      ·
        refine ⟨9037304117520780941136061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 192795821173776660077569301 9037304117520780941136061)
        ·
          refine ⟨3388989044070292852926023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9037304117520780941136061 3388989044070292852926023)
          ·
            refine ⟨5083483566105439279389035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3388989044070292852926023 5083483566105439279389035)
            ·
              refine ⟨7625225349158158919083553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5083483566105439279389035 7625225349158158919083553)
              ·
                refine ⟨5718919011868619189312665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7625225349158158919083553 5718919011868619189312665)
                ·
                  refine ⟨4289189258901464391984499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5718919011868619189312665 4289189258901464391984499)
                  ·
                    refine ⟨6433783888352196587976749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4289189258901464391984499 6433783888352196587976749)
                    ·
                      refine ⟨2412668958132073720491281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6433783888352196587976749 2412668958132073720491281)
                      ·
                        rfl

theorem cell23_4698656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 1, 2, 2, 1, 3].length) (baseStart_4698656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4698656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4698656 prefixEnd_4698656 := by exact prefixLift 4698656
  have htrace : WordTrace (prefixWord ++ tailWord_4698656) baseStart_4698656 baseEnd_4698656 := by
    simpa [prefixWord, tailWord_4698656, baseEnd_4698656] using wordTrace_append hprefix tailTrace_4698656
  have hstable : (prefixWord ++ tailWord_4698656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4698656).length < 2 ^ (prefixWord ++ tailWord_4698656).sum := by decide
  have hdescent : baseEnd_4698656 < baseStart_4698656 := by decide
  rcases family_descends (prefixWord ++ tailWord_4698656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4698679 : List Nat := [1, 1, 3, 1, 2, 3, 5, 1, 2, 2, 2]
def baseStart_4698679 : Nat := 118140960795 + 4698679 * 2 ^ 59
def prefixEnd_4698679 : Nat := 4983230072969 + 3 ^ 40 * 4698679 * 2
def baseEnd_4698679 : Nat := 2412680768187127130503675

theorem tailTrace_4698679 : CollatzResearch.WordTrace tailWord_4698679 prefixEnd_4698679 2412680768187127130503675 := by
  unfold tailWord_4698679
  simp only [CollatzResearch.WordTrace]
  refine ⟨171374902144495928330371091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114249934762997285553580727 171374902144495928330371091)
  ·
    refine ⟨257062353216743892495556637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171374902144495928330371091 257062353216743892495556637)
    ·
      refine ⟨96398382456278959685833739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 257062353216743892495556637 96398382456278959685833739)
      ·
        refine ⟨144597573684418439528750609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96398382456278959685833739 144597573684418439528750609)
        ·
          refine ⟨108448180263313829646562957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 144597573684418439528750609 108448180263313829646562957)
          ·
            refine ⟨40668067598742686117461109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 108448180263313829646562957 40668067598742686117461109)
            ·
              refine ⟨3812631337382126823511979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 40668067598742686117461109 3812631337382126823511979)
              ·
                refine ⟨5718947006073190235267969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3812631337382126823511979 5718947006073190235267969)
                ·
                  refine ⟨4289210254554892676450977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5718947006073190235267969 4289210254554892676450977)
                  ·
                    refine ⟨3216907690916169507338233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4289210254554892676450977 3216907690916169507338233)
                    ·
                      refine ⟨2412680768187127130503675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3216907690916169507338233 2412680768187127130503675)
                      ·
                        rfl

theorem cell23_4698679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 5, 1, 2, 2, 2].length) (baseStart_4698679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4698679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4698679 prefixEnd_4698679 := by exact prefixLift 4698679
  have htrace : WordTrace (prefixWord ++ tailWord_4698679) baseStart_4698679 baseEnd_4698679 := by
    simpa [prefixWord, tailWord_4698679, baseEnd_4698679] using wordTrace_append hprefix tailTrace_4698679
  have hstable : (prefixWord ++ tailWord_4698679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4698679).length < 2 ^ (prefixWord ++ tailWord_4698679).sum := by decide
  have hdescent : baseEnd_4698679 < baseStart_4698679 := by decide
  rcases family_descends (prefixWord ++ tailWord_4698679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4698698 : List Nat := [3, 1, 2, 1, 1, 4, 2, 1, 1, 7]
def baseStart_4698698 : Nat := 118140960795 + 4698698 * 2 ^ 59
def prefixEnd_4698698 : Nat := 4983230072969 + 3 ^ 40 * 4698698 * 2
def baseEnd_4698698 : Nat := 804230174773187518722029

theorem tailTrace_4698698 : CollatzResearch.WordTrace tailWord_4698698 prefixEnd_4698698 804230174773187518722029 := by
  unfold tailWord_4698698
  simp only [CollatzResearch.WordTrace]
  refine ⟨42843898782856773643828187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114250396754284729716875165 42843898782856773643828187)
  ·
    refine ⟨64265848174285160465742281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42843898782856773643828187 64265848174285160465742281)
    ·
      refine ⟨48199386130713870349306711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64265848174285160465742281 48199386130713870349306711)
      ·
        refine ⟨72299079196070805523960067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48199386130713870349306711 72299079196070805523960067)
        ·
          refine ⟨108448618794106208285940101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72299079196070805523960067 108448618794106208285940101)
          ·
            refine ⟨20334116023894914053613769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 108448618794106208285940101 20334116023894914053613769)
            ·
              refine ⟨15250587017921185540210327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20334116023894914053613769 15250587017921185540210327)
              ·
                refine ⟨22875880526881778310315491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15250587017921185540210327 22875880526881778310315491)
                ·
                  refine ⟨34313820790322667465473237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22875880526881778310315491 34313820790322667465473237)
                  ·
                    refine ⟨804230174773187518722029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34313820790322667465473237 804230174773187518722029)
                    ·
                      rfl

theorem cell23_4698698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 1, 1, 7].length) (baseStart_4698698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4698698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4698698 prefixEnd_4698698 := by exact prefixLift 4698698
  have htrace : WordTrace (prefixWord ++ tailWord_4698698) baseStart_4698698 baseEnd_4698698 := by
    simpa [prefixWord, tailWord_4698698, baseEnd_4698698] using wordTrace_append hprefix tailTrace_4698698
  have hstable : (prefixWord ++ tailWord_4698698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4698698).length < 2 ^ (prefixWord ++ tailWord_4698698).sum := by decide
  have hdescent : baseEnd_4698698 < baseStart_4698698 := by decide
  rcases family_descends (prefixWord ++ tailWord_4698698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4698725 : List Nat := [1, 3, 1, 3, 4, 1, 1, 1, 1, 2, 5]
def baseStart_4698725 : Nat := 118140960795 + 4698725 * 2 ^ 59
def prefixEnd_4698725 : Nat := 4983230072969 + 3 ^ 40 * 4698725 * 2
def baseEnd_4698725 : Nat := 2412704388297233950528463

theorem tailTrace_4698725 : CollatzResearch.WordTrace tailWord_4698725 prefixEnd_4698725 2412704388297233950528463 := by
  unfold tailWord_4698725
  simp only [CollatzResearch.WordTrace]
  refine ⟨171376579902329278186545629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114251053268219518791030419 171376579902329278186545629)
  ·
    refine ⟨64266217463373479319954611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 171376579902329278186545629 64266217463373479319954611)
    ·
      refine ⟨96399326195060218979931917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64266217463373479319954611 96399326195060218979931917)
      ·
        refine ⟨36149747323147582117474469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96399326195060218979931917 36149747323147582117474469)
        ·
          refine ⟨6778077623090171647026463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36149747323147582117474469 6778077623090171647026463)
          ·
            refine ⟨10167116434635257470539695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6778077623090171647026463 10167116434635257470539695)
            ·
              refine ⟨15250674651952886205809543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10167116434635257470539695 15250674651952886205809543)
              ·
                refine ⟨22876011977929329308714315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15250674651952886205809543 22876011977929329308714315)
                ·
                  refine ⟨34314017966893993963071473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22876011977929329308714315 34314017966893993963071473)
                  ·
                    refine ⟨25735513475170495472303605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34314017966893993963071473 25735513475170495472303605)
                    ·
                      refine ⟨2412704388297233950528463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25735513475170495472303605 2412704388297233950528463)
                      ·
                        rfl

theorem cell23_4698725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 1, 1, 2, 5].length) (baseStart_4698725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4698725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4698725 prefixEnd_4698725 := by exact prefixLift 4698725
  have htrace : WordTrace (prefixWord ++ tailWord_4698725) baseStart_4698725 baseEnd_4698725 := by
    simpa [prefixWord, tailWord_4698725, baseEnd_4698725] using wordTrace_append hprefix tailTrace_4698725
  have hstable : (prefixWord ++ tailWord_4698725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4698725).length < 2 ^ (prefixWord ++ tailWord_4698725).sum := by decide
  have hdescent : baseEnd_4698725 < baseStart_4698725 := by decide
  rcases family_descends (prefixWord ++ tailWord_4698725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4698735 : List Nat := [1, 1, 2, 1, 3, 2, 2, 3, 2, 4, 2]
def baseStart_4698735 : Nat := 118140960795 + 4698735 * 2 ^ 59
def prefixEnd_4698735 : Nat := 4983230072969 + 3 ^ 40 * 4698735 * 2
def baseEnd_4698735 : Nat := 2412709523103778911403417

theorem tailTrace_4698735 : CollatzResearch.WordTrace tailWord_4698735 prefixEnd_4698735 2412709523103778911403417 := by
  unfold tailWord_4698735
  simp only [CollatzResearch.WordTrace]
  refine ⟨171376944632293049894409659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114251296421528699929606439 171376944632293049894409659)
  ·
    refine ⟨257065416948439574841614489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171376944632293049894409659 257065416948439574841614489)
    ·
      refine ⟨192799062711329681131210867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 257065416948439574841614489 192799062711329681131210867)
      ·
        refine ⟨289198594066994521696816301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192799062711329681131210867 289198594066994521696816301)
        ·
          refine ⟨108449472775122945636306113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 289198594066994521696816301 108449472775122945636306113)
          ·
            refine ⟨81337104581342209227229585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 108449472775122945636306113 81337104581342209227229585)
            ·
              refine ⟨61002828436006656920422189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81337104581342209227229585 61002828436006656920422189)
              ·
                refine ⟨22876060663502496345158321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61002828436006656920422189 22876060663502496345158321)
                ·
                  refine ⟨17157045497626872258868741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22876060663502496345158321 17157045497626872258868741)
                  ·
                    refine ⟨3216946030805038548537889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17157045497626872258868741 3216946030805038548537889)
                    ·
                      refine ⟨2412709523103778911403417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3216946030805038548537889 2412709523103778911403417)
                      ·
                        rfl

theorem cell23_4698735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 3, 2, 4, 2].length) (baseStart_4698735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4698735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4698735 prefixEnd_4698735 := by exact prefixLift 4698735
  have htrace : WordTrace (prefixWord ++ tailWord_4698735) baseStart_4698735 baseEnd_4698735 := by
    simpa [prefixWord, tailWord_4698735, baseEnd_4698735] using wordTrace_append hprefix tailTrace_4698735
  have hstable : (prefixWord ++ tailWord_4698735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4698735).length < 2 ^ (prefixWord ++ tailWord_4698735).sum := by decide
  have hdescent : baseEnd_4698735 < baseStart_4698735 := by decide
  rcases family_descends (prefixWord ++ tailWord_4698735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4698748 : List Nat := [2, 2, 2, 1, 1, 2, 2, 1, 2, 4, 4]
def baseStart_4698748 : Nat := 118140960795 + 4698748 * 2 ^ 59
def prefixEnd_4698748 : Nat := 4983230072969 + 3 ^ 40 * 4698748 * 2
def baseEnd_4698748 : Nat := 2412716198352287360540857

theorem tailTrace_4698748 : CollatzResearch.WordTrace tailWord_4698748 prefixEnd_4698748 2412716198352287360540857 := by
  unfold tailWord_4698748
  simp only [CollatzResearch.WordTrace]
  refine ⟨85688709390622976557316449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114251612520830635409755265 85688709390622976557316449)
  ·
    refine ⟨64266532042967232417987337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85688709390622976557316449 64266532042967232417987337)
    ·
      refine ⟨48199899032225424313490503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64266532042967232417987337 48199899032225424313490503)
      ·
        refine ⟨72299848548338136470235755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48199899032225424313490503 72299848548338136470235755)
        ·
          refine ⟨108449772822507204705353633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72299848548338136470235755 108449772822507204705353633)
          ·
            refine ⟨81337329616880403529015225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 108449772822507204705353633 81337329616880403529015225)
            ·
              refine ⟨61002997212660302646761419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81337329616880403529015225 61002997212660302646761419)
              ·
                refine ⟨91504495818990453970142129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61002997212660302646761419 91504495818990453970142129)
                ·
                  refine ⟨68628371864242840477606597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 91504495818990453970142129 68628371864242840477606597)
                  ·
                    refine ⟨12867819724545532589551237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 68628371864242840477606597 12867819724545532589551237)
                    ·
                      refine ⟨2412716198352287360540857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12867819724545532589551237 2412716198352287360540857)
                      ·
                        rfl

theorem cell23_4698748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 1, 2, 4, 4].length) (baseStart_4698748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4698748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4698748 prefixEnd_4698748 := by exact prefixLift 4698748
  have htrace : WordTrace (prefixWord ++ tailWord_4698748) baseStart_4698748 baseEnd_4698748 := by
    simpa [prefixWord, tailWord_4698748, baseEnd_4698748] using wordTrace_append hprefix tailTrace_4698748
  have hstable : (prefixWord ++ tailWord_4698748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4698748).length < 2 ^ (prefixWord ++ tailWord_4698748).sum := by decide
  have hdescent : baseEnd_4698748 < baseStart_4698748 := by decide
  rcases family_descends (prefixWord ++ tailWord_4698748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4698755 : List Nat := [1, 1, 1, 3, 3, 1, 3, 3, 2, 2, 3]
def baseStart_4698755 : Nat := 118140960795 + 4698755 * 2 ^ 59
def prefixEnd_4698755 : Nat := 4983230072969 + 3 ^ 40 * 4698755 * 2
def baseEnd_4698755 : Nat := 2412719792716868833153325

theorem tailTrace_4698755 : CollatzResearch.WordTrace tailWord_4698755 prefixEnd_4698755 2412719792716868833153325 := by
  unfold tailWord_4698755
  simp only [CollatzResearch.WordTrace]
  refine ⟨171377674092220593310137719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114251782728147062206758479 171377674092220593310137719)
  ·
    refine ⟨257066511138330889965206579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171377674092220593310137719 257066511138330889965206579)
    ·
      refine ⟨385599766707496334947809869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 257066511138330889965206579 385599766707496334947809869)
      ·
        refine ⟨144599912515311125605428701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 385599766707496334947809869 144599912515311125605428701)
        ·
          refine ⟨54224967193241672102035763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 144599912515311125605428701 54224967193241672102035763)
          ·
            refine ⟨81337450789862508153053645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54224967193241672102035763 81337450789862508153053645)
            ·
              refine ⟨30501544046198440557395117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 81337450789862508153053645 30501544046198440557395117)
              ·
                refine ⟨11438079017324415209023169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30501544046198440557395117 11438079017324415209023169)
                ·
                  refine ⟨8578559262993311406767377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11438079017324415209023169 8578559262993311406767377)
                  ·
                    refine ⟨6433919447244983555075533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8578559262993311406767377 6433919447244983555075533)
                    ·
                      refine ⟨2412719792716868833153325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6433919447244983555075533 2412719792716868833153325)
                      ·
                        rfl

theorem cell23_4698755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 3, 2, 2, 3].length) (baseStart_4698755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4698755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4698755 prefixEnd_4698755 := by exact prefixLift 4698755
  have htrace : WordTrace (prefixWord ++ tailWord_4698755) baseStart_4698755 baseEnd_4698755 := by
    simpa [prefixWord, tailWord_4698755, baseEnd_4698755] using wordTrace_append hprefix tailTrace_4698755
  have hstable : (prefixWord ++ tailWord_4698755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4698755).length < 2 ^ (prefixWord ++ tailWord_4698755).sum := by decide
  have hdescent : baseEnd_4698755 < baseStart_4698755 := by decide
  rcases family_descends (prefixWord ++ tailWord_4698755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4698775 : List Nat := [1, 1, 3, 3, 2, 1, 4, 2, 6]
def baseStart_4698775 : Nat := 118140960795 + 4698775 * 2 ^ 59
def prefixEnd_4698775 : Nat := 4983230072969 + 3 ^ 40 * 4698775 * 2
def baseEnd_4698775 : Nat := 268081118036662083878137

theorem tailTrace_4698775 : CollatzResearch.WordTrace tailWord_4698775 prefixEnd_4698775 268081118036662083878137 := by
  unfold tailWord_4698775
  simp only [CollatzResearch.WordTrace]
  refine ⟨171378403552148136725865779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114252269034765424483910519 171378403552148136725865779)
  ·
    refine ⟨257067605328222205088798669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171378403552148136725865779 257067605328222205088798669)
    ·
      refine ⟨96400351998083326908299501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 257067605328222205088798669 96400351998083326908299501)
      ·
        refine ⟨36150131999281247590612313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96400351998083326908299501 36150131999281247590612313)
        ·
          refine ⟨27112598999460935692959235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36150131999281247590612313 27112598999460935692959235)
          ·
            refine ⟨40668898499191403539438853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27112598999460935692959235 40668898499191403539438853)
            ·
              refine ⟨7625418468598388163644785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40668898499191403539438853 7625418468598388163644785)
              ·
                refine ⟨5719063851448791122733589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7625418468598388163644785 5719063851448791122733589)
                ·
                  refine ⟨268081118036662083878137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5719063851448791122733589 268081118036662083878137)
                  ·
                    rfl

theorem cell23_4698775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 4, 2, 6].length) (baseStart_4698775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4698775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4698775 prefixEnd_4698775 := by exact prefixLift 4698775
  have htrace : WordTrace (prefixWord ++ tailWord_4698775) baseStart_4698775 baseEnd_4698775 := by
    simpa [prefixWord, tailWord_4698775, baseEnd_4698775] using wordTrace_append hprefix tailTrace_4698775
  have hstable : (prefixWord ++ tailWord_4698775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4698775).length < 2 ^ (prefixWord ++ tailWord_4698775).sum := by decide
  have hdescent : baseEnd_4698775 < baseStart_4698775 := by decide
  rcases family_descends (prefixWord ++ tailWord_4698775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4698812 : List Nat := [2, 2, 2, 3, 1, 1, 3, 1, 1, 5, 2]
def baseStart_4698812 : Nat := 118140960795 + 4698812 * 2 ^ 59
def prefixEnd_4698812 : Nat := 4983230072969 + 3 ^ 40 * 4698812 * 2
def baseEnd_4698812 : Nat := 2412749061114175110140563

theorem tailTrace_4698812 : CollatzResearch.WordTrace tailWord_4698812 prefixEnd_4698812 2412749061114175110140563 := by
  unfold tailWord_4698812
  simp only [CollatzResearch.WordTrace]
  refine ⟨85689876526507046022481345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114253168702009394696641793 85689876526507046022481345)
  ·
    refine ⟨64267407394880284516861009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85689876526507046022481345 64267407394880284516861009)
    ·
      refine ⟨48200555546160213387645757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64267407394880284516861009 48200555546160213387645757)
      ·
        refine ⟨18075208329810080020367159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48200555546160213387645757 18075208329810080020367159)
        ·
          refine ⟨27112812494715120030550739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18075208329810080020367159 27112812494715120030550739)
          ·
            refine ⟨40669218742072680045826109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27112812494715120030550739 40669218742072680045826109)
            ·
              refine ⟨15250957028277255017184791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40669218742072680045826109 15250957028277255017184791)
              ·
                refine ⟨22876435542415882525777187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15250957028277255017184791 22876435542415882525777187)
                ·
                  refine ⟨34314653313623823788665781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22876435542415882525777187 34314653313623823788665781)
                  ·
                    refine ⟨3216998748152233480187417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34314653313623823788665781 3216998748152233480187417)
                    ·
                      refine ⟨2412749061114175110140563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3216998748152233480187417 2412749061114175110140563)
                      ·
                        rfl

theorem cell23_4698812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 1, 1, 5, 2].length) (baseStart_4698812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4698812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4698812 prefixEnd_4698812 := by exact prefixLift 4698812
  have htrace : WordTrace (prefixWord ++ tailWord_4698812) baseStart_4698812 baseEnd_4698812 := by
    simpa [prefixWord, tailWord_4698812, baseEnd_4698812] using wordTrace_append hprefix tailTrace_4698812
  have hstable : (prefixWord ++ tailWord_4698812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4698812).length < 2 ^ (prefixWord ++ tailWord_4698812).sum := by decide
  have hdescent : baseEnd_4698812 < baseStart_4698812 := by decide
  rcases family_descends (prefixWord ++ tailWord_4698812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4698825 : List Nat := [1, 2, 1, 1, 2, 1, 1, 1, 3, 8, 2]
def baseStart_4698825 : Nat := 118140960795 + 4698825 * 2 ^ 59
def prefixEnd_4698825 : Nat := 4983230072969 + 3 ^ 40 * 4698825 * 2
def baseEnd_4698825 : Nat := 2412755736362683559278003

theorem tailTrace_4698825 : CollatzResearch.WordTrace tailWord_4698825 prefixEnd_4698825 2412755736362683559278003 := by
  unfold tailWord_4698825
  simp only [CollatzResearch.WordTrace]
  refine ⟨171380227201966995265185929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114253484801311330176790619 171380227201966995265185929)
  ·
    refine ⟨128535170401475246448889447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171380227201966995265185929 128535170401475246448889447)
    ·
      refine ⟨192802755602212869673334171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128535170401475246448889447 192802755602212869673334171)
      ·
        refine ⟨289204133403319304510001257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192802755602212869673334171 289204133403319304510001257)
        ·
          refine ⟨216903100052489478382500943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 289204133403319304510001257 216903100052489478382500943)
          ·
            refine ⟨325354650078734217573751415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 216903100052489478382500943 325354650078734217573751415)
            ·
              refine ⟨488031975118101326360627123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 325354650078734217573751415 488031975118101326360627123)
              ·
                refine ⟨732047962677151989540940685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 488031975118101326360627123 732047962677151989540940685)
                ·
                  refine ⟨274517986003931996077852757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 732047962677151989540940685 274517986003931996077852757)
                  ·
                    refine ⟨3217007648483578079037337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 274517986003931996077852757 3217007648483578079037337)
                    ·
                      refine ⟨2412755736362683559278003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3217007648483578079037337 2412755736362683559278003)
                      ·
                        rfl

theorem cell23_4698825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 8, 2].length) (baseStart_4698825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4698825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4698825 prefixEnd_4698825 := by exact prefixLift 4698825
  have htrace : WordTrace (prefixWord ++ tailWord_4698825) baseStart_4698825 baseEnd_4698825 := by
    simpa [prefixWord, tailWord_4698825, baseEnd_4698825] using wordTrace_append hprefix tailTrace_4698825
  have hstable : (prefixWord ++ tailWord_4698825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4698825).length < 2 ^ (prefixWord ++ tailWord_4698825).sum := by decide
  have hdescent : baseEnd_4698825 < baseStart_4698825 := by decide
  rcases family_descends (prefixWord ++ tailWord_4698825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4698836 : List Nat := [2, 4, 1, 3, 2, 1, 2, 1, 3, 1, 3]
def baseStart_4698836 : Nat := 118140960795 + 4698836 * 2 ^ 59
def prefixEnd_4698836 : Nat := 4983230072969 + 3 ^ 40 * 4698836 * 2
def baseEnd_4698836 : Nat := 2412761384649883016240453

theorem tailTrace_4698836 : CollatzResearch.WordTrace tailWord_4698836 prefixEnd_4698836 2412761384649883016240453 := by
  unfold tailWord_4698836
  simp only [CollatzResearch.WordTrace]
  refine ⟨85690314202463572071918181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114253752269951429429224241 85690314202463572071918181)
  ·
    refine ⟨16066933912961919763484659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 85690314202463572071918181 16066933912961919763484659)
    ·
      refine ⟨24100400869442879645226989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16066933912961919763484659 24100400869442879645226989)
      ·
        refine ⟨9037650326041079866960121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24100400869442879645226989 9037650326041079866960121)
        ·
          refine ⟨6778237744530809900220091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9037650326041079866960121 6778237744530809900220091)
          ·
            refine ⟨10167356616796214850330137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6778237744530809900220091 10167356616796214850330137)
            ·
              refine ⟨7625517462597161137747603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10167356616796214850330137 7625517462597161137747603)
              ·
                refine ⟨11438276193895741706621405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7625517462597161137747603 11438276193895741706621405)
                ·
                  refine ⟨4289353572710903139983027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11438276193895741706621405 4289353572710903139983027)
                  ·
                    refine ⟨6434030359066354709974541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4289353572710903139983027 6434030359066354709974541)
                    ·
                      refine ⟨2412761384649883016240453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6434030359066354709974541 2412761384649883016240453)
                      ·
                        rfl

theorem cell23_4698836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 2, 1, 3, 1, 3].length) (baseStart_4698836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4698836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4698836 prefixEnd_4698836 := by exact prefixLift 4698836
  have htrace : WordTrace (prefixWord ++ tailWord_4698836) baseStart_4698836 baseEnd_4698836 := by
    simpa [prefixWord, tailWord_4698836, baseEnd_4698836] using wordTrace_append hprefix tailTrace_4698836
  have hstable : (prefixWord ++ tailWord_4698836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4698836).length < 2 ^ (prefixWord ++ tailWord_4698836).sum := by decide
  have hdescent : baseEnd_4698836 < baseStart_4698836 := by decide
  rcases family_descends (prefixWord ++ tailWord_4698836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4698848 : List Nat := [2, 1, 1, 3, 1, 2, 1, 12]
def baseStart_4698848 : Nat := 118140960795 + 4698848 * 2 ^ 59
def prefixEnd_4698848 : Nat := 4983230072969 + 3 ^ 40 * 4698848 * 2
def baseEnd_4698848 : Nat := 89361760978434702566311

theorem tailTrace_4698848 : CollatzResearch.WordTrace tailWord_4698848 prefixEnd_4698848 89361760978434702566311 := by
  unfold tailWord_4698848
  simp only [CollatzResearch.WordTrace]
  refine ⟨85690533040441835096636599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114254044053922446795515465 85690533040441835096636599)
  ·
    refine ⟨128535799560662752644954899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85690533040441835096636599 128535799560662752644954899)
    ·
      refine ⟨192803699340994128967432349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128535799560662752644954899 192803699340994128967432349)
      ·
        refine ⟨72301387252872798362787131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 192803699340994128967432349 72301387252872798362787131)
        ·
          refine ⟨108452080879309197544180697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72301387252872798362787131 108452080879309197544180697)
          ·
            refine ⟨81339060659481898158135523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 108452080879309197544180697 81339060659481898158135523)
            ·
              refine ⟨122008590989222847237203285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81339060659481898158135523 122008590989222847237203285)
              ·
                refine ⟨89361760978434702566311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 122008590989222847237203285 89361760978434702566311)
                ·
                  rfl

theorem cell23_4698848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 12].length) (baseStart_4698848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4698848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4698848 prefixEnd_4698848 := by exact prefixLift 4698848
  have htrace : WordTrace (prefixWord ++ tailWord_4698848) baseStart_4698848 baseEnd_4698848 := by
    simpa [prefixWord, tailWord_4698848, baseEnd_4698848] using wordTrace_append hprefix tailTrace_4698848
  have hstable : (prefixWord ++ tailWord_4698848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4698848).length < 2 ^ (prefixWord ++ tailWord_4698848).sum := by decide
  have hdescent : baseEnd_4698848 < baseStart_4698848 := by decide
  rcases family_descends (prefixWord ++ tailWord_4698848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4698852 : List Nat := [2, 3, 1, 1, 1, 6, 1, 1, 1, 6]
def baseStart_4698852 : Nat := 118140960795 + 4698852 * 2 ^ 59
def prefixEnd_4698852 : Nat := 4983230072969 + 3 ^ 40 * 4698852 * 2
def baseEnd_4698852 : Nat := 804256533446784984546793

theorem tailTrace_4698852 : CollatzResearch.WordTrace tailWord_4698852 prefixEnd_4698852 804256533446784984546793 := by
  unfold tailWord_4698852
  simp only [CollatzResearch.WordTrace]
  refine ⟨85690605986434589438209405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114254141315246119250945873 85690605986434589438209405)
  ·
    refine ⟨32133977244912971039328527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85690605986434589438209405 32133977244912971039328527)
    ·
      refine ⟨48200965867369456558992791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32133977244912971039328527 48200965867369456558992791)
      ·
        refine ⟨72301448801054184838489187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48200965867369456558992791 72301448801054184838489187)
        ·
          refine ⟨108452173201581277257733781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72301448801054184838489187 108452173201581277257733781)
          ·
            refine ⟨5083695618824122371456271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 108452173201581277257733781 5083695618824122371456271)
            ·
              refine ⟨7625543428236183557184407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5083695618824122371456271 7625543428236183557184407)
              ·
                refine ⟨11438315142354275335776611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7625543428236183557184407 11438315142354275335776611)
                ·
                  refine ⟨17157472713531413003664917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11438315142354275335776611 17157472713531413003664917)
                  ·
                    refine ⟨804256533446784984546793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17157472713531413003664917 804256533446784984546793)
                    ·
                      rfl

theorem cell23_4698852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 1, 1, 1, 6].length) (baseStart_4698852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4698852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4698852 prefixEnd_4698852 := by exact prefixLift 4698852
  have htrace : WordTrace (prefixWord ++ tailWord_4698852) baseStart_4698852 baseEnd_4698852 := by
    simpa [prefixWord, tailWord_4698852, baseEnd_4698852] using wordTrace_append hprefix tailTrace_4698852
  have hstable : (prefixWord ++ tailWord_4698852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4698852).length < 2 ^ (prefixWord ++ tailWord_4698852).sum := by decide
  have hdescent : baseEnd_4698852 < baseStart_4698852 := by decide
  rcases family_descends (prefixWord ++ tailWord_4698852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4698882 : List Nat := [3, 4, 1, 1, 1, 4, 9]
def baseStart_4698882 : Nat := 118140960795 + 4698882 * 2 ^ 59
def prefixEnd_4698882 : Nat := 4983230072969 + 3 ^ 40 * 4698882 * 2
def baseEnd_4698882 : Nat := 29787469194567775756361

theorem tailTrace_4698882 : CollatzResearch.WordTrace tailWord_4698882 prefixEnd_4698882 29787469194567775756361 := by
  unfold tailWord_4698882
  simp only [CollatzResearch.WordTrace]
  refine ⟨42845576540690123500002725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114254870775173662666673933 42845576540690123500002725)
  ·
    refine ⟨8033545601379398156250511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42845576540690123500002725 8033545601379398156250511)
    ·
      refine ⟨12050318402069097234375767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8033545601379398156250511 12050318402069097234375767)
      ·
        refine ⟨18075477603103645851563651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12050318402069097234375767 18075477603103645851563651)
        ·
          refine ⟨27113216404655468777345477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18075477603103645851563651 27113216404655468777345477)
          ·
            refine ⟨5083728075872900395752277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27113216404655468777345477 5083728075872900395752277)
            ·
              refine ⟨29787469194567775756361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5083728075872900395752277 29787469194567775756361)
              ·
                rfl

theorem cell23_4698882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 9].length) (baseStart_4698882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4698882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4698882 prefixEnd_4698882 := by exact prefixLift 4698882
  have htrace : WordTrace (prefixWord ++ tailWord_4698882) baseStart_4698882 baseEnd_4698882 := by
    simpa [prefixWord, tailWord_4698882, baseEnd_4698882] using wordTrace_append hprefix tailTrace_4698882
  have hstable : (prefixWord ++ tailWord_4698882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4698882).length < 2 ^ (prefixWord ++ tailWord_4698882).sum := by decide
  have hdescent : baseEnd_4698882 < baseStart_4698882 := by decide
  rcases family_descends (prefixWord ++ tailWord_4698882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4698903 : List Nat := [1, 1, 3, 4, 4, 1, 2, 1, 2, 4]
def baseStart_4698903 : Nat := 118140960795 + 4698903 * 2 ^ 59
def prefixEnd_4698903 : Nat := 4983230072969 + 3 ^ 40 * 4698903 * 2
def baseEnd_4698903 : Nat := 804265262617911418034215

theorem tailTrace_4698903 : CollatzResearch.WordTrace tailWord_4698903 prefixEnd_4698903 804265262617911418034215 := by
  unfold tailWord_4698903
  simp only [CollatzResearch.WordTrace]
  refine ⟨171383072095684414586525363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114255381397122943057683575 171383072095684414586525363)
  ·
    refine ⟨257074608143526621879788045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171383072095684414586525363 257074608143526621879788045)
    ·
      refine ⟨96402978053822483204920517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 257074608143526621879788045 96402978053822483204920517)
      ·
        refine ⟨18075558385091715600922597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 96402978053822483204920517 18075558385091715600922597)
        ·
          refine ⟨3389167197204696675172987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18075558385091715600922597 3389167197204696675172987)
          ·
            refine ⟨5083750795807045012759481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3389167197204696675172987 5083750795807045012759481)
            ·
              refine ⟨3812813096855283759569611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5083750795807045012759481 3812813096855283759569611)
              ·
                refine ⟨5719219645282925639354417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3812813096855283759569611 5719219645282925639354417)
                ·
                  refine ⟨4289414733962194229515813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5719219645282925639354417 4289414733962194229515813)
                  ·
                    refine ⟨804265262617911418034215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4289414733962194229515813 804265262617911418034215)
                    ·
                      rfl

theorem cell23_4698903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 2, 1, 2, 4].length) (baseStart_4698903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4698903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4698903 prefixEnd_4698903 := by exact prefixLift 4698903
  have htrace : WordTrace (prefixWord ++ tailWord_4698903) baseStart_4698903 baseEnd_4698903 := by
    simpa [prefixWord, tailWord_4698903, baseEnd_4698903] using wordTrace_append hprefix tailTrace_4698903
  have hstable : (prefixWord ++ tailWord_4698903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4698903).length < 2 ^ (prefixWord ++ tailWord_4698903).sum := by decide
  have hdescent : baseEnd_4698903 < baseStart_4698903 := by decide
  rcases family_descends (prefixWord ++ tailWord_4698903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4698935 : List Nat := [1, 1, 3, 1, 2, 1, 3, 3, 2, 1, 5]
def baseStart_4698935 : Nat := 118140960795 + 4698935 * 2 ^ 59
def prefixEnd_4698935 : Nat := 4983230072969 + 3 ^ 40 * 4698935 * 2
def baseEnd_4698935 : Nat := 2412812219234678128902497

theorem tailTrace_4698935 : CollatzResearch.WordTrace tailWord_4698935 prefixEnd_4698935 2412812219234678128902497 := by
  unfold tailWord_4698935
  simp only [CollatzResearch.WordTrace]
  refine ⟨171384239231568484051690259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114256159487712322701126839 171384239231568484051690259)
  ·
    refine ⟨257076358847352726077535389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171384239231568484051690259 257076358847352726077535389)
    ·
      refine ⟨96403634567757272279075771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 257076358847352726077535389 96403634567757272279075771)
      ·
        refine ⟨144605451851635908418613657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96403634567757272279075771 144605451851635908418613657)
        ·
          refine ⟨108454088888726931313960243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 144605451851635908418613657 108454088888726931313960243)
          ·
            refine ⟨162681133333090396970940365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108454088888726931313960243 162681133333090396970940365)
            ·
              refine ⟨61005424999908898864102637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 162681133333090396970940365 61005424999908898864102637)
              ·
                refine ⟨22877034374965837074038489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61005424999908898864102637 22877034374965837074038489)
                ·
                  refine ⟨17157775781224377805528867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22877034374965837074038489 17157775781224377805528867)
                  ·
                    refine ⟨25736663671836566708293301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17157775781224377805528867 25736663671836566708293301)
                    ·
                      refine ⟨2412812219234678128902497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25736663671836566708293301 2412812219234678128902497)
                      ·
                        rfl

theorem cell23_4698935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 3, 2, 1, 5].length) (baseStart_4698935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4698935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4698935 prefixEnd_4698935 := by exact prefixLift 4698935
  have htrace : WordTrace (prefixWord ++ tailWord_4698935) baseStart_4698935 baseEnd_4698935 := by
    simpa [prefixWord, tailWord_4698935, baseEnd_4698935] using wordTrace_append hprefix tailTrace_4698935
  have hstable : (prefixWord ++ tailWord_4698935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4698935).length < 2 ^ (prefixWord ++ tailWord_4698935).sum := by decide
  have hdescent : baseEnd_4698935 < baseStart_4698935 := by decide
  rcases family_descends (prefixWord ++ tailWord_4698935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4698936 : List Nat := [2, 1, 2, 1, 3, 2, 5, 1, 1, 3, 2]
def baseStart_4698936 : Nat := 118140960795 + 4698936 * 2 ^ 59
def prefixEnd_4698936 : Nat := 4983230072969 + 3 ^ 40 * 4698936 * 2
def baseEnd_4698936 : Nat := 2412812732715332624989993

theorem tailTrace_4698936 : CollatzResearch.WordTrace tailWord_4698936 prefixEnd_4698936 2412812732715332624989993 := by
  unfold tailWord_4698936
  simp only [CollatzResearch.WordTrace]
  refine ⟨85692137852282430611238331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114256183803043240814984441 85692137852282430611238331)
  ·
    refine ⟨128538206778423645916857497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85692137852282430611238331 128538206778423645916857497)
    ·
      refine ⟨96403655083817734437643123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128538206778423645916857497 96403655083817734437643123)
      ·
        refine ⟨144605482625726601656464685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96403655083817734437643123 144605482625726601656464685)
        ·
          refine ⟨54227055984647475621174257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 144605482625726601656464685 54227055984647475621174257)
          ·
            refine ⟨40670291988485606715880693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54227055984647475621174257 40670291988485606715880693)
            ·
              refine ⟨3812839873920525629613815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 40670291988485606715880693 3812839873920525629613815)
              ·
                refine ⟨5719259810880788444420723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3812839873920525629613815 5719259810880788444420723)
                ·
                  refine ⟨8578889716321182666631085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5719259810880788444420723 8578889716321182666631085)
                  ·
                    refine ⟨3217083643620443499986657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8578889716321182666631085 3217083643620443499986657)
                    ·
                      refine ⟨2412812732715332624989993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3217083643620443499986657 2412812732715332624989993)
                      ·
                        rfl

theorem cell23_4698936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 5, 1, 1, 3, 2].length) (baseStart_4698936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4698936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4698936 prefixEnd_4698936 := by exact prefixLift 4698936
  have htrace : WordTrace (prefixWord ++ tailWord_4698936) baseStart_4698936 baseEnd_4698936 := by
    simpa [prefixWord, tailWord_4698936, baseEnd_4698936] using wordTrace_append hprefix tailTrace_4698936
  have hstable : (prefixWord ++ tailWord_4698936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4698936).length < 2 ^ (prefixWord ++ tailWord_4698936).sum := by decide
  have hdescent : baseEnd_4698936 < baseStart_4698936 := by decide
  rcases family_descends (prefixWord ++ tailWord_4698936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4698962 : List Nat := [3, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4]
def baseStart_4698962 : Nat := 118140960795 + 4698962 * 2 ^ 59
def prefixEnd_4698962 : Nat := 4983230072969 + 3 ^ 40 * 4698962 * 2
def baseEnd_4698962 : Nat := 2412826083212349523264873

theorem tailTrace_4698962 : CollatzResearch.WordTrace tailWord_4698962 prefixEnd_4698962 2412826083212349523264873 := by
  unfold tailWord_4698962
  simp only [CollatzResearch.WordTrace]
  refine ⟨42846306000617666915730785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114256816001647111775282093 42846306000617666915730785)
  ·
    refine ⟨32134729500463250186798089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42846306000617666915730785 32134729500463250186798089)
    ·
      refine ⟨24101047125347437640098567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32134729500463250186798089 24101047125347437640098567)
      ·
        refine ⟨36151570688021156460147851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24101047125347437640098567 36151570688021156460147851)
        ·
          refine ⟨54227356032031734690221777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36151570688021156460147851 54227356032031734690221777)
          ·
            refine ⟨40670517024023801017666333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54227356032031734690221777 40670517024023801017666333)
            ·
              refine ⟨15251443884008925381624875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40670517024023801017666333 15251443884008925381624875)
              ·
                refine ⟨22877165826013388072437313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15251443884008925381624875 22877165826013388072437313)
                ·
                  refine ⟨17157874369510041054327985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22877165826013388072437313 17157874369510041054327985)
                  ·
                    refine ⟨12868405777132530790745989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17157874369510041054327985 12868405777132530790745989)
                    ·
                      refine ⟨2412826083212349523264873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12868405777132530790745989 2412826083212349523264873)
                      ·
                        rfl

theorem cell23_4698962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4].length) (baseStart_4698962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4698962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4698962 prefixEnd_4698962 := by exact prefixLift 4698962
  have htrace : WordTrace (prefixWord ++ tailWord_4698962) baseStart_4698962 baseEnd_4698962 := by
    simpa [prefixWord, tailWord_4698962, baseEnd_4698962] using wordTrace_append hprefix tailTrace_4698962
  have hstable : (prefixWord ++ tailWord_4698962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4698962).length < 2 ^ (prefixWord ++ tailWord_4698962).sum := by decide
  have hdescent : baseEnd_4698962 < baseStart_4698962 := by decide
  rcases family_descends (prefixWord ++ tailWord_4698962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4698972 : List Nat := [2, 2, 4, 2, 1, 1, 1, 1, 9]
def baseStart_4698972 : Nat := 118140960795 + 4698972 * 2 ^ 59
def prefixEnd_4698972 : Nat := 4983230072969 + 3 ^ 40 * 4698972 * 2
def baseEnd_4698972 : Nat := 268092357557654942682203

theorem tailTrace_4698972 : CollatzResearch.WordTrace tailWord_4698972 prefixEnd_4698972 268092357557654942682203 := by
  unfold tailWord_4698972
  simp only [CollatzResearch.WordTrace]
  refine ⟨85692794366217219685393585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114257059154956292913858113 85692794366217219685393585)
  ·
    refine ⟨64269595774662914764045189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85692794366217219685393585 64269595774662914764045189)
    ·
      refine ⟨12050549207749296518258473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64269595774662914764045189 12050549207749296518258473)
      ·
        refine ⟨9037911905811972388693855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12050549207749296518258473 9037911905811972388693855)
        ·
          refine ⟨13556867858717958583040783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9037911905811972388693855 13556867858717958583040783)
          ·
            refine ⟨20335301788076937874561175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13556867858717958583040783 20335301788076937874561175)
            ·
              refine ⟨30502952682115406811841763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20335301788076937874561175 30502952682115406811841763)
              ·
                refine ⟨45754429023173110217762645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30502952682115406811841763 45754429023173110217762645)
                ·
                  refine ⟨268092357557654942682203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 45754429023173110217762645 268092357557654942682203)
                  ·
                    rfl

theorem cell23_4698972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 1, 9].length) (baseStart_4698972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4698972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4698972 prefixEnd_4698972 := by exact prefixLift 4698972
  have htrace : WordTrace (prefixWord ++ tailWord_4698972) baseStart_4698972 baseEnd_4698972 := by
    simpa [prefixWord, tailWord_4698972, baseEnd_4698972] using wordTrace_append hprefix tailTrace_4698972
  have hstable : (prefixWord ++ tailWord_4698972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4698972).length < 2 ^ (prefixWord ++ tailWord_4698972).sum := by decide
  have hdescent : baseEnd_4698972 < baseStart_4698972 := by decide
  rcases family_descends (prefixWord ++ tailWord_4698972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4698995 : List Nat := [1, 1, 1, 2, 2, 1, 4, 1, 3, 2, 5]
def baseStart_4698995 : Nat := 118140960795 + 4698995 * 2 ^ 59
def prefixEnd_4698995 : Nat := 4983230072969 + 3 ^ 40 * 4698995 * 2
def baseEnd_4698995 : Nat := 2412843028073947894152221

theorem tailTrace_4698995 : CollatzResearch.WordTrace tailWord_4698995 prefixEnd_4698995 2412843028073947894152221 := by
  unfold tailWord_4698995
  simp only [CollatzResearch.WordTrace]
  refine ⟨171386427611351114298874439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114257618407567409532582959 171386427611351114298874439)
  ·
    refine ⟨257079641417026671448311659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171386427611351114298874439 257079641417026671448311659)
    ·
      refine ⟨385619462125540007172467489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 257079641417026671448311659 385619462125540007172467489)
      ·
        refine ⟨289214596594155005379350617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 385619462125540007172467489 289214596594155005379350617)
        ·
          refine ⟨216910947445616254034512963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 289214596594155005379350617 216910947445616254034512963)
          ·
            refine ⟨325366421168424381051769445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 216910947445616254034512963 325366421168424381051769445)
            ·
              refine ⟨61006203969079571447206771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 325366421168424381051769445 61006203969079571447206771)
              ·
                refine ⟨91509305953619357170810157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61006203969079571447206771 91509305953619357170810157)
                ·
                  refine ⟨34315989732607258939053809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 91509305953619357170810157 34315989732607258939053809)
                  ·
                    refine ⟨25736992299455444204290357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34315989732607258939053809 25736992299455444204290357)
                    ·
                      refine ⟨2412843028073947894152221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25736992299455444204290357 2412843028073947894152221)
                      ·
                        rfl

theorem cell23_4698995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 1, 3, 2, 5].length) (baseStart_4698995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4698995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4698995 prefixEnd_4698995 := by exact prefixLift 4698995
  have htrace : WordTrace (prefixWord ++ tailWord_4698995) baseStart_4698995 baseEnd_4698995 := by
    simpa [prefixWord, tailWord_4698995, baseEnd_4698995] using wordTrace_append hprefix tailTrace_4698995
  have hstable : (prefixWord ++ tailWord_4698995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4698995).length < 2 ^ (prefixWord ++ tailWord_4698995).sum := by decide
  have hdescent : baseEnd_4698995 < baseStart_4698995 := by decide
  rcases family_descends (prefixWord ++ tailWord_4698995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4699006 : List Nat := [4, 2, 3, 1, 2, 1, 2, 1, 7]
def baseStart_4699006 : Nat := 118140960795 + 4699006 * 2 ^ 59
def prefixEnd_4699006 : Nat := 4983230072969 + 3 ^ 40 * 4699006 * 2
def baseEnd_4699006 : Nat := 268094297373460816790519

theorem tailTrace_4699006 : CollatzResearch.WordTrace tailWord_4699006 prefixEnd_4699006 268094297373460816790519 := by
  unfold tailWord_4699006
  simp only [CollatzResearch.WordTrace]
  refine ⟨21423353601788907897190609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 114257885876207508785016581 21423353601788907897190609)
  ·
    refine ⟨16067515201341680922892957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21423353601788907897190609 16067515201341680922892957)
    ·
      refine ⟨6025318200503130346084859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16067515201341680922892957 6025318200503130346084859)
      ·
        refine ⟨9037977300754695519127289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6025318200503130346084859 9037977300754695519127289)
        ·
          refine ⟨6778482975566021639345467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9037977300754695519127289 6778482975566021639345467)
          ·
            refine ⟨10167724463349032459018201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6778482975566021639345467 10167724463349032459018201)
            ·
              refine ⟨7625793347511774344263651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10167724463349032459018201 7625793347511774344263651)
              ·
                refine ⟨11438690021267661516395477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7625793347511774344263651 11438690021267661516395477)
                ·
                  refine ⟨268094297373460816790519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11438690021267661516395477 268094297373460816790519)
                  ·
                    rfl

theorem cell23_4699006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 2, 1, 7].length) (baseStart_4699006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4699006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4699006 prefixEnd_4699006 := by exact prefixLift 4699006
  have htrace : WordTrace (prefixWord ++ tailWord_4699006) baseStart_4699006 baseEnd_4699006 := by
    simpa [prefixWord, tailWord_4699006, baseEnd_4699006] using wordTrace_append hprefix tailTrace_4699006
  have hstable : (prefixWord ++ tailWord_4699006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4699006).length < 2 ^ (prefixWord ++ tailWord_4699006).sum := by decide
  have hdescent : baseEnd_4699006 < baseStart_4699006 := by decide
  rcases family_descends (prefixWord ++ tailWord_4699006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4699079 : List Nat := [1, 1, 4, 1, 1, 2, 6, 1, 6]
def baseStart_4699079 : Nat := 118140960795 + 4699079 * 2 ^ 59
def prefixEnd_4699079 : Nat := 4983230072969 + 3 ^ 40 * 4699079 * 2
def baseEnd_4699079 : Nat := 268098462272102840611315

theorem tailTrace_4699079 : CollatzResearch.WordTrace tailWord_4699079 prefixEnd_4699079 268098462272102840611315 := by
  unfold tailWord_4699079
  simp only [CollatzResearch.WordTrace]
  refine ⟨171389491343046796644932291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114259660895364531096621527 171389491343046796644932291)
  ·
    refine ⟨257084237014570194967398437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171389491343046796644932291 257084237014570194967398437)
    ·
      refine ⟨48203294440231911556387207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 257084237014570194967398437 48203294440231911556387207)
      ·
        refine ⟨72304941660347867334580811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48203294440231911556387207 72304941660347867334580811)
        ·
          refine ⟨108457412490521801001871217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72304941660347867334580811 108457412490521801001871217)
          ·
            refine ⟨81343059367891350751403413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 108457412490521801001871217 81343059367891350751403413)
            ·
              refine ⟨3812955907869907066472035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 81343059367891350751403413 3812955907869907066472035)
              ·
                refine ⟨5719433861804860599708053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3812955907869907066472035 5719433861804860599708053)
                ·
                  refine ⟨268098462272102840611315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5719433861804860599708053 268098462272102840611315)
                  ·
                    rfl

theorem cell23_4699079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 6, 1, 6].length) (baseStart_4699079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4699079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4699079 prefixEnd_4699079 := by exact prefixLift 4699079
  have htrace : WordTrace (prefixWord ++ tailWord_4699079) baseStart_4699079 baseEnd_4699079 := by
    simpa [prefixWord, tailWord_4699079, baseEnd_4699079] using wordTrace_append hprefix tailTrace_4699079
  have hstable : (prefixWord ++ tailWord_4699079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4699079).length < 2 ^ (prefixWord ++ tailWord_4699079).sum := by decide
  have hdescent : baseEnd_4699079 < baseStart_4699079 := by decide
  rcases family_descends (prefixWord ++ tailWord_4699079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4699089 : List Nat := [1, 2, 2, 1, 2, 1, 4, 1, 5, 1, 3]
def baseStart_4699089 : Nat := 118140960795 + 4699089 * 2 ^ 59
def prefixEnd_4699089 : Nat := 4983230072969 + 3 ^ 40 * 4699089 * 2
def baseEnd_4699089 : Nat := 2412891295255470526376789

theorem tailTrace_4699089 : CollatzResearch.WordTrace tailWord_4699089 prefixEnd_4699089 2412891295255470526376789 := by
  unfold tailWord_4699089
  simp only [CollatzResearch.WordTrace]
  refine ⟨171389856073010568352796321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114259904048673712235197547 171389856073010568352796321)
  ·
    refine ⟨128542392054757926264597241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171389856073010568352796321 128542392054757926264597241)
    ·
      refine ⟨96406794041068444698447931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128542392054757926264597241 96406794041068444698447931)
      ·
        refine ⟨144610191061602667047671897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96406794041068444698447931 144610191061602667047671897)
        ·
          refine ⟨108457643296202000285753923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 144610191061602667047671897 108457643296202000285753923)
          ·
            refine ⟨162686464944303000428630885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108457643296202000285753923 162686464944303000428630885)
            ·
              refine ⟨30503712177056812580368291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 162686464944303000428630885 30503712177056812580368291)
              ·
                refine ⟨45755568265585218870552437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30503712177056812580368291 45755568265585218870552437)
                ·
                  refine ⟨4289584524898614269114291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 45755568265585218870552437 4289584524898614269114291)
                  ·
                    refine ⟨6434376787347921403671437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4289584524898614269114291 6434376787347921403671437)
                    ·
                      refine ⟨2412891295255470526376789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6434376787347921403671437 2412891295255470526376789)
                      ·
                        rfl

theorem cell23_4699089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 1, 5, 1, 3].length) (baseStart_4699089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4699089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4699089 prefixEnd_4699089 := by exact prefixLift 4699089
  have htrace : WordTrace (prefixWord ++ tailWord_4699089) baseStart_4699089 baseEnd_4699089 := by
    simpa [prefixWord, tailWord_4699089, baseEnd_4699089] using wordTrace_append hprefix tailTrace_4699089
  have hstable : (prefixWord ++ tailWord_4699089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4699089).length < 2 ^ (prefixWord ++ tailWord_4699089).sum := by decide
  have hdescent : baseEnd_4699089 < baseStart_4699089 := by decide
  rcases family_descends (prefixWord ++ tailWord_4699089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4699190 : List Nat := [5, 1, 2, 1, 1, 3, 3, 1, 2, 4]
def baseStart_4699190 : Nat := 118140960795 + 4699190 * 2 ^ 59
def prefixEnd_4699190 : Nat := 4983230072969 + 3 ^ 40 * 4699190 * 2
def baseEnd_4699190 : Nat := 804314385600524877071275

theorem tailTrace_4699190 : CollatzResearch.WordTrace tailWord_4699190 prefixEnd_4699190 804314385600524877071275 := by
  unfold tailWord_4699190
  simp only [CollatzResearch.WordTrace]
  refine ⟨10712096240352791412638939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 114262359897096441734815349 10712096240352791412638939)
  ·
    refine ⟨16068144360529187118958409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10712096240352791412638939 16068144360529187118958409)
    ·
      refine ⟨12051108270396890339218807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16068144360529187118958409 12051108270396890339218807)
      ·
        refine ⟨18076662405595335508828211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12051108270396890339218807 18076662405595335508828211)
        ·
          refine ⟨27114993608393003263242317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18076662405595335508828211 27114993608393003263242317)
          ·
            refine ⟨10168122603147376223715869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27114993608393003263242317 10168122603147376223715869)
            ·
              refine ⟨3813045976180266083893451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10168122603147376223715869 3813045976180266083893451)
              ·
                refine ⟨5719568964270399125840177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3813045976180266083893451 5719568964270399125840177)
                ·
                  refine ⟨4289676723202799344380133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5719568964270399125840177 4289676723202799344380133)
                  ·
                    refine ⟨804314385600524877071275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4289676723202799344380133 804314385600524877071275)
                    ·
                      rfl

theorem cell23_4699190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 3, 1, 2, 4].length) (baseStart_4699190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4699190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4699190 prefixEnd_4699190 := by exact prefixLift 4699190
  have htrace : WordTrace (prefixWord ++ tailWord_4699190) baseStart_4699190 baseEnd_4699190 := by
    simpa [prefixWord, tailWord_4699190, baseEnd_4699190] using wordTrace_append hprefix tailTrace_4699190
  have hstable : (prefixWord ++ tailWord_4699190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4699190).length < 2 ^ (prefixWord ++ tailWord_4699190).sum := by decide
  have hdescent : baseEnd_4699190 < baseStart_4699190 := by decide
  rcases family_descends (prefixWord ++ tailWord_4699190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4699196 : List Nat := [2, 2, 2, 2, 2, 2, 3, 1, 1, 3, 3]
def baseStart_4699196 : Nat := 118140960795 + 4699196 * 2 ^ 59
def prefixEnd_4699196 : Nat := 4983230072969 + 3 ^ 40 * 4699196 * 2
def baseEnd_4699196 : Nat := 2412946237685501607738797

theorem tailTrace_4699196 : CollatzResearch.WordTrace tailWord_4699196 prefixEnd_4699196 2412946237685501607738797 := by
  unfold tailWord_4699196
  simp only [CollatzResearch.WordTrace]
  refine ⟨85696879341811462813470721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114262505789081950417960961 85696879341811462813470721)
  ·
    refine ⟨64272659506358597110103041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85696879341811462813470721 64272659506358597110103041)
    ·
      refine ⟨48204494629768947832577281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64272659506358597110103041 48204494629768947832577281)
      ·
        refine ⟨36153370972326710874432961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48204494629768947832577281 36153370972326710874432961)
        ·
          refine ⟨27115028229245033155824721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36153370972326710874432961 27115028229245033155824721)
          ·
            refine ⟨20336271171933774866868541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27115028229245033155824721 20336271171933774866868541)
            ·
              refine ⟨7626101689475165575075703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20336271171933774866868541 7626101689475165575075703)
              ·
                refine ⟨11439152534212748362613555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7626101689475165575075703 11439152534212748362613555)
                ·
                  refine ⟨17158728801319122543920333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11439152534212748362613555 17158728801319122543920333)
                  ·
                    refine ⟨6434523300494670953970125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17158728801319122543920333 6434523300494670953970125)
                    ·
                      refine ⟨2412946237685501607738797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6434523300494670953970125 2412946237685501607738797)
                      ·
                        rfl

theorem cell23_4699196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 3, 1, 1, 3, 3].length) (baseStart_4699196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4699196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4699196 prefixEnd_4699196 := by exact prefixLift 4699196
  have htrace : WordTrace (prefixWord ++ tailWord_4699196) baseStart_4699196 baseEnd_4699196 := by
    simpa [prefixWord, tailWord_4699196, baseEnd_4699196] using wordTrace_append hprefix tailTrace_4699196
  have hstable : (prefixWord ++ tailWord_4699196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4699196).length < 2 ^ (prefixWord ++ tailWord_4699196).sum := by decide
  have hdescent : baseEnd_4699196 < baseStart_4699196 := by decide
  rcases family_descends (prefixWord ++ tailWord_4699196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4699213 : List Nat := [1, 6, 1, 1, 1, 2, 1, 2, 4, 1, 3]
def baseStart_4699213 : Nat := 118140960795 + 4699213 * 2 ^ 59
def prefixEnd_4699213 : Nat := 4983230072969 + 3 ^ 40 * 4699213 * 2
def baseEnd_4699213 : Nat := 2412954966856628041226219

theorem tailTrace_4699213 : CollatzResearch.WordTrace tailWord_4699213 prefixEnd_4699213 2412954966856628041226219 := by
  unfold tailWord_4699213
  simp only [CollatzResearch.WordTrace]
  refine ⟨171394378724561337530310293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114262919149707558353540195 171394378724561337530310293)
  ·
    refine ⟨8034111502713812696733295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 171394378724561337530310293 8034111502713812696733295)
    ·
      refine ⟨12051167254070719045099943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8034111502713812696733295 12051167254070719045099943)
      ·
        refine ⟨18076750881106078567649915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12051167254070719045099943 18076750881106078567649915)
        ·
          refine ⟨27115126321659117851474873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18076750881106078567649915 27115126321659117851474873)
          ·
            refine ⟨20336344741244338388606155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27115126321659117851474873 20336344741244338388606155)
            ·
              refine ⟨30504517111866507582909233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20336344741244338388606155 30504517111866507582909233)
              ·
                refine ⟨22878387833899880687181925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30504517111866507582909233 22878387833899880687181925)
                ·
                  refine ⟨4289697718856227628846611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22878387833899880687181925 4289697718856227628846611)
                  ·
                    refine ⟨6434546578284341443269917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4289697718856227628846611 6434546578284341443269917)
                    ·
                      refine ⟨2412954966856628041226219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6434546578284341443269917 2412954966856628041226219)
                      ·
                        rfl

theorem cell23_4699213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 2, 4, 1, 3].length) (baseStart_4699213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4699213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4699213 prefixEnd_4699213 := by exact prefixLift 4699213
  have htrace : WordTrace (prefixWord ++ tailWord_4699213) baseStart_4699213 baseEnd_4699213 := by
    simpa [prefixWord, tailWord_4699213, baseEnd_4699213] using wordTrace_append hprefix tailTrace_4699213
  have hstable : (prefixWord ++ tailWord_4699213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4699213).length < 2 ^ (prefixWord ++ tailWord_4699213).sum := by decide
  have hdescent : baseEnd_4699213 < baseStart_4699213 := by decide
  rcases family_descends (prefixWord ++ tailWord_4699213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4699257 : List Nat := [1, 2, 1, 3, 6, 1, 1, 2, 1, 3, 2]
def baseStart_4699257 : Nat := 118140960795 + 4699257 * 2 ^ 59
def prefixEnd_4699257 : Nat := 4983230072969 + 3 ^ 40 * 4699257 * 2
def baseEnd_4699257 : Nat := 2412977560005425869076017

theorem tailTrace_4699257 : CollatzResearch.WordTrace tailWord_4699257 prefixEnd_4699257 2412977560005425869076017 := by
  unfold tailWord_4699257
  simp only [CollatzResearch.WordTrace]
  refine ⟨171395983536401933044912025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114263989024267955363274683 171395983536401933044912025)
  ·
    refine ⟨128546987652301449783684019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171395983536401933044912025 128546987652301449783684019)
    ·
      refine ⟨192820481478452174675526029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128546987652301449783684019 192820481478452174675526029)
      ·
        refine ⟨72307680554419565503322261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 192820481478452174675526029 72307680554419565503322261)
        ·
          refine ⟨3389422525988417132968231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 72307680554419565503322261 3389422525988417132968231)
          ·
            refine ⟨5084133788982625699452347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3389422525988417132968231 5084133788982625699452347)
            ·
              refine ⟨7626200683473938549178521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5084133788982625699452347 7626200683473938549178521)
              ·
                refine ⟨5719650512605453911883891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7626200683473938549178521 5719650512605453911883891)
                ·
                  refine ⟨8579475768908180867825837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5719650512605453911883891 8579475768908180867825837)
                  ·
                    refine ⟨3217303413340567825434689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8579475768908180867825837 3217303413340567825434689)
                    ·
                      refine ⟨2412977560005425869076017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3217303413340567825434689 2412977560005425869076017)
                      ·
                        rfl

theorem cell23_4699257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 1, 2, 1, 3, 2].length) (baseStart_4699257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4699257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4699257 prefixEnd_4699257 := by exact prefixLift 4699257
  have htrace : WordTrace (prefixWord ++ tailWord_4699257) baseStart_4699257 baseEnd_4699257 := by
    simpa [prefixWord, tailWord_4699257, baseEnd_4699257] using wordTrace_append hprefix tailTrace_4699257
  have hstable : (prefixWord ++ tailWord_4699257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4699257).length < 2 ^ (prefixWord ++ tailWord_4699257).sum := by decide
  have hdescent : baseEnd_4699257 < baseStart_4699257 := by decide
  rcases family_descends (prefixWord ++ tailWord_4699257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4699296 : List Nat := [2, 1, 1, 4, 2, 1, 1, 1, 1, 7, 2]
def baseStart_4699296 : Nat := 118140960795 + 4699296 * 2 ^ 59
def prefixEnd_4699296 : Nat := 4983230072969 + 3 ^ 40 * 4699296 * 2
def baseEnd_4699296 : Nat := 2412997585750951216488337

theorem tailTrace_4699296 : CollatzResearch.WordTrace tailWord_4699296 prefixEnd_4699296 2412997585750951216488337 := by
  unfold tailWord_4699296
  simp only [CollatzResearch.WordTrace]
  refine ⟨85698702991630321352790871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114264937322173761803721161 85698702991630321352790871)
  ·
    refine ⟨128548054487445482029186307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85698702991630321352790871 128548054487445482029186307)
    ·
      refine ⟨192822081731168223043779461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128548054487445482029186307 192822081731168223043779461)
      ·
        refine ⟨36154140324594041820708649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 192822081731168223043779461 36154140324594041820708649)
        ·
          refine ⟨27115605243445531365531487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36154140324594041820708649 27115605243445531365531487)
          ·
            refine ⟨40673407865168297048297231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27115605243445531365531487 40673407865168297048297231)
            ·
              refine ⟨61010111797752445572445847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40673407865168297048297231 61010111797752445572445847)
              ·
                refine ⟨91515167696628668358668771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61010111797752445572445847 91515167696628668358668771)
                ·
                  refine ⟨137272751544943002538003157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 91515167696628668358668771 137272751544943002538003157)
                  ·
                    refine ⟨3217330114334601621984449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 137272751544943002538003157 3217330114334601621984449)
                    ·
                      refine ⟨2412997585750951216488337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3217330114334601621984449 2412997585750951216488337)
                      ·
                        rfl

theorem cell23_4699296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 1, 1, 7, 2].length) (baseStart_4699296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4699296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4699296 prefixEnd_4699296 := by exact prefixLift 4699296
  have htrace : WordTrace (prefixWord ++ tailWord_4699296) baseStart_4699296 baseEnd_4699296 := by
    simpa [prefixWord, tailWord_4699296, baseEnd_4699296] using wordTrace_append hprefix tailTrace_4699296
  have hstable : (prefixWord ++ tailWord_4699296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4699296).length < 2 ^ (prefixWord ++ tailWord_4699296).sum := by decide
  have hdescent : baseEnd_4699296 < baseStart_4699296 := by decide
  rcases family_descends (prefixWord ++ tailWord_4699296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4699303 : List Nat := [1, 1, 6, 2, 1, 2, 1, 1, 2, 3, 3]
def baseStart_4699303 : Nat := 118140960795 + 4699303 * 2 ^ 59
def prefixEnd_4699303 : Nat := 4983230072969 + 3 ^ 40 * 4699303 * 2
def baseEnd_4699303 : Nat := 2413001180115532689100805

theorem tailTrace_4699303 : CollatzResearch.WordTrace tailWord_4699303 prefixEnd_4699303 2413001180115532689100805 := by
  unfold tailWord_4699303
  simp only [CollatzResearch.WordTrace]
  refine ⟨171397661294235282901086563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114265107529490188600724375 171397661294235282901086563)
  ·
    refine ⟨257096491941352924351629845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171397661294235282901086563 257096491941352924351629845)
    ·
      refine ⟨12051398059750918328982649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 257096491941352924351629845 12051398059750918328982649)
      ·
        refine ⟨9038548544813188746736987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12051398059750918328982649 9038548544813188746736987)
        ·
          refine ⟨13557822817219783120105481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9038548544813188746736987 13557822817219783120105481)
          ·
            refine ⟨10168367112914837340079111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13557822817219783120105481 10168367112914837340079111)
            ·
              refine ⟨15252550669372256010118667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10168367112914837340079111 15252550669372256010118667)
              ·
                refine ⟨22878826004058384015178001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15252550669372256010118667 22878826004058384015178001)
                ·
                  refine ⟨17159119503043788011383501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22878826004058384015178001 17159119503043788011383501)
                  ·
                    refine ⟨6434669813641420504268813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17159119503043788011383501 6434669813641420504268813)
                    ·
                      refine ⟨2413001180115532689100805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6434669813641420504268813 2413001180115532689100805)
                      ·
                        rfl

theorem cell23_4699303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 1, 2, 3, 3].length) (baseStart_4699303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4699303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4699303 prefixEnd_4699303 := by exact prefixLift 4699303
  have htrace : WordTrace (prefixWord ++ tailWord_4699303) baseStart_4699303 baseEnd_4699303 := by
    simpa [prefixWord, tailWord_4699303, baseEnd_4699303] using wordTrace_append hprefix tailTrace_4699303
  have hstable : (prefixWord ++ tailWord_4699303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4699303).length < 2 ^ (prefixWord ++ tailWord_4699303).sum := by decide
  have hdescent : baseEnd_4699303 < baseStart_4699303 := by decide
  rcases family_descends (prefixWord ++ tailWord_4699303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4699403 : List Nat := [1, 1, 1, 1, 5, 3, 1, 1, 4, 3, 2]
def baseStart_4699403 : Nat := 118140960795 + 4699403 * 2 ^ 59
def prefixEnd_4699403 : Nat := 4983230072969 + 3 ^ 40 * 4699403 * 2
def baseEnd_4699403 : Nat := 2413052528180982297850345

theorem tailTrace_4699403 : CollatzResearch.WordTrace tailWord_4699403 prefixEnd_4699403 2413052528180982297850345 := by
  unfold tailWord_4699403
  simp only [CollatzResearch.WordTrace]
  refine ⟨171401308593872999979726863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114267539062581999986484575 171401308593872999979726863)
  ·
    refine ⟨257101962890809499969590295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171401308593872999979726863 257101962890809499969590295)
    ·
      refine ⟨385652944336214249954385443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 257101962890809499969590295 385652944336214249954385443)
      ·
        refine ⟨578479416504321374931578165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 385652944336214249954385443 578479416504321374931578165)
        ·
          refine ⟨54232445297280128899835453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 578479416504321374931578165 54232445297280128899835453)
          ·
            refine ⟨20337166986480048337438295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54232445297280128899835453 20337166986480048337438295)
            ·
              refine ⟨30505750479720072506157443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20337166986480048337438295 30505750479720072506157443)
              ·
                refine ⟨45758625719580108759236165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30505750479720072506157443 45758625719580108759236165)
                ·
                  refine ⟨8579742322421270392356781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45758625719580108759236165 8579742322421270392356781)
                  ·
                    refine ⟨3217403370907976397133793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8579742322421270392356781 3217403370907976397133793)
                    ·
                      refine ⟨2413052528180982297850345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3217403370907976397133793 2413052528180982297850345)
                      ·
                        rfl

theorem cell23_4699403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 1, 4, 3, 2].length) (baseStart_4699403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4699403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4699403 prefixEnd_4699403 := by exact prefixLift 4699403
  have htrace : WordTrace (prefixWord ++ tailWord_4699403) baseStart_4699403 baseEnd_4699403 := by
    simpa [prefixWord, tailWord_4699403, baseEnd_4699403] using wordTrace_append hprefix tailTrace_4699403
  have hstable : (prefixWord ++ tailWord_4699403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4699403).length < 2 ^ (prefixWord ++ tailWord_4699403).sum := by decide
  have hdescent : baseEnd_4699403 < baseStart_4699403 := by decide
  rcases family_descends (prefixWord ++ tailWord_4699403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4699437 : List Nat := [1, 5, 3, 1, 1, 1, 1, 3, 2, 3, 2]
def baseStart_4699437 : Nat := 118140960795 + 4699437 * 2 ^ 59
def prefixEnd_4699437 : Nat := 4983230072969 + 3 ^ 40 * 4699437 * 2
def baseEnd_4699437 : Nat := 2413069986523235164825189

theorem tailTrace_4699437 : CollatzResearch.WordTrace tailWord_4699437 prefixEnd_4699437 2413069986523235164825189 := by
  unfold tailWord_4699437
  simp only [CollatzResearch.WordTrace]
  refine ⟨171402548675749823786464565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114268365783833215857643043 171402548675749823786464565)
  ·
    refine ⟨16068988938351545979981053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 171402548675749823786464565 16068988938351545979981053)
    ·
      refine ⟨6025870851881829742492895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16068988938351545979981053 6025870851881829742492895)
      ·
        refine ⟨9038806277822744613739343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6025870851881829742492895 9038806277822744613739343)
        ·
          refine ⟨13558209416734116920609015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9038806277822744613739343 13558209416734116920609015)
          ·
            refine ⟨20337314125101175380913523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13558209416734116920609015 20337314125101175380913523)
            ·
              refine ⟨30505971187651763071370285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20337314125101175380913523 30505971187651763071370285)
              ·
                refine ⟨11439739195369411151763857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30505971187651763071370285 11439739195369411151763857)
                ·
                  refine ⟨8579804396527058363822893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11439739195369411151763857 8579804396527058363822893)
                  ·
                    refine ⟨3217426648697646886433585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8579804396527058363822893 3217426648697646886433585)
                    ·
                      refine ⟨2413069986523235164825189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3217426648697646886433585 2413069986523235164825189)
                      ·
                        rfl

theorem cell23_4699437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 3, 2, 3, 2].length) (baseStart_4699437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4699437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4699437 prefixEnd_4699437 := by exact prefixLift 4699437
  have htrace : WordTrace (prefixWord ++ tailWord_4699437) baseStart_4699437 baseEnd_4699437 := by
    simpa [prefixWord, tailWord_4699437, baseEnd_4699437] using wordTrace_append hprefix tailTrace_4699437
  have hstable : (prefixWord ++ tailWord_4699437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4699437).length < 2 ^ (prefixWord ++ tailWord_4699437).sum := by decide
  have hdescent : baseEnd_4699437 < baseStart_4699437 := by decide
  rcases family_descends (prefixWord ++ tailWord_4699437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4699450 : List Nat := [3, 1, 1, 1, 4, 1, 5, 1, 1, 1, 4]
def baseStart_4699450 : Nat := 118140960795 + 4699450 * 2 ^ 59
def prefixEnd_4699450 : Nat := 4983230072969 + 3 ^ 40 * 4699450 * 2
def baseEnd_4699450 : Nat := 2413076661771743613962629

theorem tailTrace_4699450 : CollatzResearch.WordTrace tailWord_4699450 prefixEnd_4699450 2413076661771743613962629 := by
  unfold tailWord_4699450
  simp only [CollatzResearch.WordTrace]
  refine ⟨42850755706175681751671951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114268681883135151337791869 42850755706175681751671951)
  ·
    refine ⟨64276133559263522627507927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42850755706175681751671951 64276133559263522627507927)
    ·
      refine ⟨96414200338895283941261891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64276133559263522627507927 96414200338895283941261891)
      ·
        refine ⟨144621300508342925911892837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96414200338895283941261891 144621300508342925911892837)
        ·
          refine ⟨27116493845314298608479907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 144621300508342925911892837 27116493845314298608479907)
          ·
            refine ⟨40674740767971447912719861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27116493845314298608479907 40674740767971447912719861)
            ·
              refine ⟨3813256946997323241817487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 40674740767971447912719861 3813256946997323241817487)
              ·
                refine ⟨5719885420495984862726231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3813256946997323241817487 5719885420495984862726231)
                ·
                  refine ⟨8579828130743977294089347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5719885420495984862726231 8579828130743977294089347)
                  ·
                    refine ⟨12869742196115965941134021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8579828130743977294089347 12869742196115965941134021)
                    ·
                      refine ⟨2413076661771743613962629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12869742196115965941134021 2413076661771743613962629)
                      ·
                        rfl

theorem cell23_4699450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 5, 1, 1, 1, 4].length) (baseStart_4699450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4699450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4699450 prefixEnd_4699450 := by exact prefixLift 4699450
  have htrace : WordTrace (prefixWord ++ tailWord_4699450) baseStart_4699450 baseEnd_4699450 := by
    simpa [prefixWord, tailWord_4699450, baseEnd_4699450] using wordTrace_append hprefix tailTrace_4699450
  have hstable : (prefixWord ++ tailWord_4699450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4699450).length < 2 ^ (prefixWord ++ tailWord_4699450).sum := by decide
  have hdescent : baseEnd_4699450 < baseStart_4699450 := by decide
  rcases family_descends (prefixWord ++ tailWord_4699450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4699516 : List Nat := [2, 2, 2, 1, 1, 1, 3, 1, 4, 6]
def baseStart_4699516 : Nat := 118140960795 + 4699516 * 2 ^ 59
def prefixEnd_4699516 : Nat := 4983230072969 + 3 ^ 40 * 4699516 * 2
def baseEnd_4699516 : Nat := 804370183831646785245775

theorem tailTrace_4699516 : CollatzResearch.WordTrace tailWord_4699516 prefixEnd_4699516 804370183831646785245775 := by
  unfold tailWord_4699516
  simp only [CollatzResearch.WordTrace]
  refine ⟨85702715021231810139295201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114270286694975746852393601 85702715021231810139295201)
  ·
    refine ⟨64277036265923857604471401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85702715021231810139295201 64277036265923857604471401)
    ·
      refine ⟨48207777199442893203353551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64277036265923857604471401 48207777199442893203353551)
      ·
        refine ⟨72311665799164339805030327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48207777199442893203353551 72311665799164339805030327)
        ·
          refine ⟨108467498698746509707545491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72311665799164339805030327 108467498698746509707545491)
          ·
            refine ⟨162701248048119764561318237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108467498698746509707545491 162701248048119764561318237)
            ·
              refine ⟨61012968018044911710494339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 162701248048119764561318237 61012968018044911710494339)
              ·
                refine ⟨91519452027067367565741509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61012968018044911710494339 91519452027067367565741509)
                ·
                  refine ⟨17159897255075131418576533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 91519452027067367565741509 17159897255075131418576533)
                  ·
                    refine ⟨804370183831646785245775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17159897255075131418576533 804370183831646785245775)
                    ·
                      rfl

theorem cell23_4699516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 1, 4, 6].length) (baseStart_4699516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4699516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4699516 prefixEnd_4699516 := by exact prefixLift 4699516
  have htrace : WordTrace (prefixWord ++ tailWord_4699516) baseStart_4699516 baseEnd_4699516 := by
    simpa [prefixWord, tailWord_4699516, baseEnd_4699516] using wordTrace_append hprefix tailTrace_4699516
  have hstable : (prefixWord ++ tailWord_4699516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4699516).length < 2 ^ (prefixWord ++ tailWord_4699516).sum := by decide
  have hdescent : baseEnd_4699516 < baseStart_4699516 := by decide
  rcases family_descends (prefixWord ++ tailWord_4699516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4699534 : List Nat := [4, 1, 1, 4, 3, 1, 1, 1, 1, 3, 3]
def baseStart_4699534 : Nat := 118140960795 + 4699534 * 2 ^ 59
def prefixEnd_4699534 : Nat := 4983230072969 + 3 ^ 40 * 4699534 * 2
def baseEnd_4699534 : Nat := 2413119794146721285312243

theorem tailTrace_4699534 : CollatzResearch.WordTrace tailWord_4699534 prefixEnd_4699534 2413119794146721285312243 := by
  unfold tailWord_4699534
  simp only [CollatzResearch.WordTrace]
  refine ⟨21425760819549801169093207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 114270724370932272901830437 21425760819549801169093207)
  ·
    refine ⟨32138641229324701753639811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21425760819549801169093207 32138641229324701753639811)
    ·
      refine ⟨48207961843987052630459717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32138641229324701753639811 48207961843987052630459717)
      ·
        refine ⟨9038992845747572368211197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48207961843987052630459717 9038992845747572368211197)
        ·
          refine ⟨3389622317155339638079199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9038992845747572368211197 3389622317155339638079199)
          ·
            refine ⟨5084433475733009457118799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3389622317155339638079199 5084433475733009457118799)
            ·
              refine ⟨7626650213599514185678199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5084433475733009457118799 7626650213599514185678199)
              ·
                refine ⟨11439975320399271278517299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7626650213599514185678199 11439975320399271278517299)
                ·
                  refine ⟨17159962980598906917775949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11439975320399271278517299 17159962980598906917775949)
                  ·
                    refine ⟨6434986117724590094165981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17159962980598906917775949 6434986117724590094165981)
                    ·
                      refine ⟨2413119794146721285312243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6434986117724590094165981 2413119794146721285312243)
                      ·
                        rfl

theorem cell23_4699534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 1, 1, 1, 3, 3].length) (baseStart_4699534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4699534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4699534 prefixEnd_4699534 := by exact prefixLift 4699534
  have htrace : WordTrace (prefixWord ++ tailWord_4699534) baseStart_4699534 baseEnd_4699534 := by
    simpa [prefixWord, tailWord_4699534, baseEnd_4699534] using wordTrace_append hprefix tailTrace_4699534
  have hstable : (prefixWord ++ tailWord_4699534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4699534).length < 2 ^ (prefixWord ++ tailWord_4699534).sum := by decide
  have hdescent : baseEnd_4699534 < baseStart_4699534 := by decide
  rcases family_descends (prefixWord ++ tailWord_4699534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4699544 : List Nat := [2, 1, 2, 5, 2, 1, 2, 2, 1, 3, 2]
def baseStart_4699544 : Nat := 118140960795 + 4699544 * 2 ^ 59
def prefixEnd_4699544 : Nat := 4983230072969 + 3 ^ 40 * 4699544 * 2
def baseEnd_4699544 : Nat := 2413124928953266246187197

theorem tailTrace_4699544 : CollatzResearch.WordTrace tailWord_4699544 prefixEnd_4699544 2413124928953266246187197 := by
  unfold tailWord_4699544
  simp only [CollatzResearch.WordTrace]
  refine ⟨85703225643181090530304843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114270967524241454040406457 85703225643181090530304843)
  ·
    refine ⟨128554838464771635795457265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85703225643181090530304843 128554838464771635795457265)
    ·
      refine ⟨96416128848578726846592949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128554838464771635795457265 96416128848578726846592949)
      ·
        refine ⟨9039012079554255641868089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 96416128848578726846592949 9039012079554255641868089)
        ·
          refine ⟨6779259059665691731401067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9039012079554255641868089 6779259059665691731401067)
          ·
            refine ⟨10168888589498537597101601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6779259059665691731401067 10168888589498537597101601)
            ·
              refine ⟨7626666442123903197826201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10168888589498537597101601 7626666442123903197826201)
              ·
                refine ⟨5719999831592927398369651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7626666442123903197826201 5719999831592927398369651)
                ·
                  refine ⟨8579999747389391097554477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5719999831592927398369651 8579999747389391097554477)
                  ·
                    refine ⟨3217499905271021661582929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8579999747389391097554477 3217499905271021661582929)
                    ·
                      refine ⟨2413124928953266246187197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3217499905271021661582929 2413124928953266246187197)
                      ·
                        rfl

theorem cell23_4699544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 2, 2, 1, 3, 2].length) (baseStart_4699544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4699544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4699544 prefixEnd_4699544 := by exact prefixLift 4699544
  have htrace : WordTrace (prefixWord ++ tailWord_4699544) baseStart_4699544 baseEnd_4699544 := by
    simpa [prefixWord, tailWord_4699544, baseEnd_4699544] using wordTrace_append hprefix tailTrace_4699544
  have hstable : (prefixWord ++ tailWord_4699544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4699544).length < 2 ^ (prefixWord ++ tailWord_4699544).sum := by decide
  have hdescent : baseEnd_4699544 < baseStart_4699544 := by decide
  rcases family_descends (prefixWord ++ tailWord_4699544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4699610 : List Nat := [3, 1, 1, 2, 3, 3, 2, 1, 2, 5]
def baseStart_4699610 : Nat := 118140960795 + 4699610 * 2 ^ 59
def prefixEnd_4699610 : Nat := 4983230072969 + 3 ^ 40 * 4699610 * 2
def baseEnd_4699610 : Nat := 804386272892154329320631

theorem tailTrace_4699610 : CollatzResearch.WordTrace tailWord_4699610 prefixEnd_4699610 804386272892154329320631 := by
  unfold tailWord_4699610
  simp only [CollatzResearch.WordTrace]
  refine ⟨42852214626030768583128071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114272572336082049555008189 42852214626030768583128071)
  ·
    refine ⟨64278321939046152874692107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42852214626030768583128071 64278321939046152874692107)
    ·
      refine ⟨96417482908569229312038161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64278321939046152874692107 96417482908569229312038161)
      ·
        refine ⟨72313112181426921984028621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96417482908569229312038161 72313112181426921984028621)
        ·
          refine ⟨27117417068035095744010733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72313112181426921984028621 27117417068035095744010733)
          ·
            refine ⟨10169031400513160904004025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27117417068035095744010733 10169031400513160904004025)
            ·
              refine ⟨7626773550384870678003019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10169031400513160904004025 7626773550384870678003019)
              ·
                refine ⟨11440160325577306017004529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7626773550384870678003019 11440160325577306017004529)
                ·
                  refine ⟨8580120244182979512753397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11440160325577306017004529 8580120244182979512753397)
                  ·
                    refine ⟨804386272892154329320631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8580120244182979512753397 804386272892154329320631)
                    ·
                      rfl

theorem cell23_4699610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 2, 1, 2, 5].length) (baseStart_4699610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4699610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4699610 prefixEnd_4699610 := by exact prefixLift 4699610
  have htrace : WordTrace (prefixWord ++ tailWord_4699610) baseStart_4699610 baseEnd_4699610 := by
    simpa [prefixWord, tailWord_4699610, baseEnd_4699610] using wordTrace_append hprefix tailTrace_4699610
  have hstable : (prefixWord ++ tailWord_4699610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4699610).length < 2 ^ (prefixWord ++ tailWord_4699610).sum := by decide
  have hdescent : baseEnd_4699610 < baseStart_4699610 := by decide
  rcases family_descends (prefixWord ++ tailWord_4699610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4699630 : List Nat := [4, 1, 2, 1, 2, 1, 1, 4, 2, 1, 4]
def baseStart_4699630 : Nat := 118140960795 + 4699630 * 2 ^ 59
def prefixEnd_4699630 : Nat := 4983230072969 + 3 ^ 40 * 4699630 * 2
def baseEnd_4699630 : Nat := 2413169088289552909711801

theorem tailTrace_4699630 : CollatzResearch.WordTrace tailWord_4699630 prefixEnd_4699630 2413169088289552909711801 := by
  unfold tailWord_4699630
  simp only [CollatzResearch.WordTrace]
  refine ⟨21426198495506327218530043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 114273058642700411832160229 21426198495506327218530043)
  ·
    refine ⟨32139297743259490827795065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21426198495506327218530043 32139297743259490827795065)
    ·
      refine ⟨24104473307444618120846299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32139297743259490827795065 24104473307444618120846299)
      ·
        refine ⟨36156709961166927181269449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24104473307444618120846299 36156709961166927181269449)
        ·
          refine ⟨27117532470875195385952087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36156709961166927181269449 27117532470875195385952087)
          ·
            refine ⟨40676298706312793078928131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27117532470875195385952087 40676298706312793078928131)
            ·
              refine ⟨61014448059469189618392197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40676298706312793078928131 61014448059469189618392197)
              ·
                refine ⟨11440209011150473053448537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 61014448059469189618392197 11440209011150473053448537)
                ·
                  refine ⟨8580156758362854790086403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11440209011150473053448537 8580156758362854790086403)
                  ·
                    refine ⟨12870235137544282185129605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8580156758362854790086403 12870235137544282185129605)
                    ·
                      refine ⟨2413169088289552909711801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12870235137544282185129605 2413169088289552909711801)
                      ·
                        rfl

theorem cell23_4699630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 4, 2, 1, 4].length) (baseStart_4699630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4699630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4699630 prefixEnd_4699630 := by exact prefixLift 4699630
  have htrace : WordTrace (prefixWord ++ tailWord_4699630) baseStart_4699630 baseEnd_4699630 := by
    simpa [prefixWord, tailWord_4699630, baseEnd_4699630] using wordTrace_append hprefix tailTrace_4699630
  have hstable : (prefixWord ++ tailWord_4699630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4699630).length < 2 ^ (prefixWord ++ tailWord_4699630).sum := by decide
  have hdescent : baseEnd_4699630 < baseStart_4699630 := by decide
  rcases family_descends (prefixWord ++ tailWord_4699630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4699661 : List Nat := [1, 7, 1, 1, 2, 2, 1, 1, 2, 5]
def baseStart_4699661 : Nat := 118140960795 + 4699661 * 2 ^ 59
def prefixEnd_4699661 : Nat := 4983230072969 + 3 ^ 40 * 4699661 * 2
def baseEnd_4699661 : Nat := 804395002063280762808053

theorem tailTrace_4699661 : CollatzResearch.WordTrace tailWord_4699661 prefixEnd_4699661 804395002063280762808053 := by
  unfold tailWord_4699661
  simp only [CollatzResearch.WordTrace]
  refine ⟨171410718626938310042618837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114273812417958873361745891 171410718626938310042618837)
  ·
    refine ⟨4017438717818866641623879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 171410718626938310042618837 4017438717818866641623879)
    ·
      refine ⟨6026158076728299962435819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4017438717818866641623879 6026158076728299962435819)
      ·
        refine ⟨9039237115092449943653729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6026158076728299962435819 9039237115092449943653729)
        ·
          refine ⟨6779427836319337457740297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9039237115092449943653729 6779427836319337457740297)
          ·
            refine ⟨5084570877239503093305223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6779427836319337457740297 5084570877239503093305223)
            ·
              refine ⟨7626856315859254639957835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5084570877239503093305223 7626856315859254639957835)
              ·
                refine ⟨11440284473788881959936753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7626856315859254639957835 11440284473788881959936753)
                ·
                  refine ⟨8580213355341661469952565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11440284473788881959936753 8580213355341661469952565)
                  ·
                    refine ⟨804395002063280762808053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8580213355341661469952565 804395002063280762808053)
                    ·
                      rfl

theorem cell23_4699661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 1, 1, 2, 5].length) (baseStart_4699661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4699661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4699661 prefixEnd_4699661 := by exact prefixLift 4699661
  have htrace : WordTrace (prefixWord ++ tailWord_4699661) baseStart_4699661 baseEnd_4699661 := by
    simpa [prefixWord, tailWord_4699661, baseEnd_4699661] using wordTrace_append hprefix tailTrace_4699661
  have hstable : (prefixWord ++ tailWord_4699661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4699661).length < 2 ^ (prefixWord ++ tailWord_4699661).sum := by decide
  have hdescent : baseEnd_4699661 < baseStart_4699661 := by decide
  rcases family_descends (prefixWord ++ tailWord_4699661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4699667 : List Nat := [1, 1, 1, 2, 1, 8, 1, 1, 2, 2, 3]
def baseStart_4699667 : Nat := 118140960795 + 4699667 * 2 ^ 59
def prefixEnd_4699667 : Nat := 4983230072969 + 3 ^ 40 * 4699667 * 2
def baseEnd_4699667 : Nat := 2413188087073769264949131

theorem tailTrace_4699667 : CollatzResearch.WordTrace tailWord_4699667 prefixEnd_4699667 2413188087073769264949131 := by
  unfold tailWord_4699667
  simp only [CollatzResearch.WordTrace]
  refine ⟨171410937464916573067337255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114273958309944382044891503 171410937464916573067337255)
  ·
    refine ⟨257116406197374859601005883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171410937464916573067337255 257116406197374859601005883)
    ·
      refine ⟨385674609296062289401508825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 257116406197374859601005883 385674609296062289401508825)
      ·
        refine ⟨289255956972046717051131619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 385674609296062289401508825 289255956972046717051131619)
        ·
          refine ⟨433883935458070075576697429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 289255956972046717051131619 433883935458070075576697429)
          ·
            refine ⟨5084577368649258698164423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 433883935458070075576697429 5084577368649258698164423)
            ·
              refine ⟨7626866052973888047246635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5084577368649258698164423 7626866052973888047246635)
              ·
                refine ⟨11440299079460832070869953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7626866052973888047246635 11440299079460832070869953)
                ·
                  refine ⟨8580224309595624053152465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11440299079460832070869953 8580224309595624053152465)
                  ·
                    refine ⟨6435168232196718039864349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8580224309595624053152465 6435168232196718039864349)
                    ·
                      refine ⟨2413188087073769264949131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6435168232196718039864349 2413188087073769264949131)
                      ·
                        rfl

theorem cell23_4699667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 1, 1, 2, 2, 3].length) (baseStart_4699667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4699667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4699667 prefixEnd_4699667 := by exact prefixLift 4699667
  have htrace : WordTrace (prefixWord ++ tailWord_4699667) baseStart_4699667 baseEnd_4699667 := by
    simpa [prefixWord, tailWord_4699667, baseEnd_4699667] using wordTrace_append hprefix tailTrace_4699667
  have hstable : (prefixWord ++ tailWord_4699667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4699667).length < 2 ^ (prefixWord ++ tailWord_4699667).sum := by decide
  have hdescent : baseEnd_4699667 < baseStart_4699667 := by decide
  rcases family_descends (prefixWord ++ tailWord_4699667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4699723 : List Nat := [1, 1, 1, 1, 3, 1, 3, 1, 5, 1, 5]
def baseStart_4699723 : Nat := 118140960795 + 4699723 * 2 ^ 59
def prefixEnd_4699723 : Nat := 4983230072969 + 3 ^ 40 * 4699723 * 2
def baseEnd_4699723 : Nat := 2413216841990421045848873

theorem tailTrace_4699723 : CollatzResearch.WordTrace tailWord_4699723 prefixEnd_4699723 2413216841990421045848873 := by
  unfold tailWord_4699723
  simp only [CollatzResearch.WordTrace]
  refine ⟨171412979952713694631375823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114275319968475796420917215 171412979952713694631375823)
  ·
    refine ⟨257119469929070541947063735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171412979952713694631375823 257119469929070541947063735)
    ·
      refine ⟨385679204893605812920595603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 257119469929070541947063735 385679204893605812920595603)
      ·
        refine ⟨578518807340408719380893405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 385679204893605812920595603 578518807340408719380893405)
        ·
          refine ⟨216944552752653269767835027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 578518807340408719380893405 216944552752653269767835027)
          ·
            refine ⟨325416829128979904651752541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 216944552752653269767835027 325416829128979904651752541)
            ·
              refine ⟨122031310923367464244407203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 325416829128979904651752541 122031310923367464244407203)
              ·
                refine ⟨183046966385051196366610805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 122031310923367464244407203 183046966385051196366610805)
                ·
                  refine ⟨17160653098598549659369763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 183046966385051196366610805 17160653098598549659369763)
                  ·
                    refine ⟨25740979647897824489054645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17160653098598549659369763 25740979647897824489054645)
                    ·
                      refine ⟨2413216841990421045848873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25740979647897824489054645 2413216841990421045848873)
                      ·
                        rfl

theorem cell23_4699723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 5, 1, 5].length) (baseStart_4699723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4699723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4699723 prefixEnd_4699723 := by exact prefixLift 4699723
  have htrace : WordTrace (prefixWord ++ tailWord_4699723) baseStart_4699723 baseEnd_4699723 := by
    simpa [prefixWord, tailWord_4699723, baseEnd_4699723] using wordTrace_append hprefix tailTrace_4699723
  have hstable : (prefixWord ++ tailWord_4699723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4699723).length < 2 ^ (prefixWord ++ tailWord_4699723).sum := by decide
  have hdescent : baseEnd_4699723 < baseStart_4699723 := by decide
  rcases family_descends (prefixWord ++ tailWord_4699723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4699737 : List Nat := [1, 2, 1, 2, 2, 1, 1, 4, 5, 2, 2]
def baseStart_4699737 : Nat := 118140960795 + 4699737 * 2 ^ 59
def prefixEnd_4699737 : Nat := 4983230072969 + 3 ^ 40 * 4699737 * 2
def baseEnd_4699737 : Nat := 2413224030719583991073809

theorem tailTrace_4699737 : CollatzResearch.WordTrace tailWord_4699737 prefixEnd_4699737 2413224030719583991073809 := by
  unfold tailWord_4699737
  simp only [CollatzResearch.WordTrace]
  refine ⟨171413490574662975022385465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114275660383108650014923643 171413490574662975022385465)
  ·
    refine ⟨128560117930997231266789099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171413490574662975022385465 128560117930997231266789099)
    ·
      refine ⟨192840176896495846900183649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128560117930997231266789099 192840176896495846900183649)
      ·
        refine ⟨144630132672371885175137737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 192840176896495846900183649 144630132672371885175137737)
        ·
          refine ⟨108472599504278913881353303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 144630132672371885175137737 108472599504278913881353303)
          ·
            refine ⟨162708899256418370822029955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108472599504278913881353303 162708899256418370822029955)
            ·
              refine ⟨244063348884627556233044933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 162708899256418370822029955 244063348884627556233044933)
              ·
                refine ⟨45761877915867666793695925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 244063348884627556233044933 45761877915867666793695925)
                ·
                  refine ⟨4290176054612593761908993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 45761877915867666793695925 4290176054612593761908993)
                  ·
                    refine ⟨3217632040959445321431745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4290176054612593761908993 3217632040959445321431745)
                    ·
                      refine ⟨2413224030719583991073809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3217632040959445321431745 2413224030719583991073809)
                      ·
                        rfl

theorem cell23_4699737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 4, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 4, 5, 2, 2].length) (baseStart_4699737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4699737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4699737 prefixEnd_4699737 := by exact prefixLift 4699737
  have htrace : WordTrace (prefixWord ++ tailWord_4699737) baseStart_4699737 baseEnd_4699737 := by
    simpa [prefixWord, tailWord_4699737, baseEnd_4699737] using wordTrace_append hprefix tailTrace_4699737
  have hstable : (prefixWord ++ tailWord_4699737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4699737).length < 2 ^ (prefixWord ++ tailWord_4699737).sum := by decide
  have hdescent : baseEnd_4699737 < baseStart_4699737 := by decide
  rcases family_descends (prefixWord ++ tailWord_4699737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4699760 : List Nat := [2, 1, 1, 1, 6, 2, 2, 8]
def baseStart_4699760 : Nat := 118140960795 + 4699760 * 2 ^ 59
def prefixEnd_4699760 : Nat := 4983230072969 + 3 ^ 40 * 4699760 * 2
def baseEnd_4699760 : Nat := 89379105213875459299489

theorem tailTrace_4699760 : CollatzResearch.WordTrace tailWord_4699760 prefixEnd_4699760 89379105213875459299489 := by
  unfold tailWord_4699760
  simp only [CollatzResearch.WordTrace]
  refine ⟨85707164726789824975236367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114276219635719766633648489 85707164726789824975236367)
  ·
    refine ⟨128560747090184737462854551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85707164726789824975236367 128560747090184737462854551)
    ·
      refine ⟨192841120635277106194281827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128560747090184737462854551 192841120635277106194281827)
      ·
        refine ⟨289261680952915659291422741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192841120635277106194281827 289261680952915659291422741)
        ·
          refine ⟨13559141294667921529285441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 289261680952915659291422741 13559141294667921529285441)
          ·
            refine ⟨10169355971000941146964081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13559141294667921529285441 10169355971000941146964081)
            ·
              refine ⟨7627016978250705860223061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10169355971000941146964081 7627016978250705860223061)
              ·
                refine ⟨89379105213875459299489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7627016978250705860223061 89379105213875459299489)
                ·
                  rfl

theorem cell23_4699760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 2, 8].length) (baseStart_4699760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4699760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4699760 prefixEnd_4699760 := by exact prefixLift 4699760
  have htrace : WordTrace (prefixWord ++ tailWord_4699760) baseStart_4699760 baseEnd_4699760 := by
    simpa [prefixWord, tailWord_4699760, baseEnd_4699760] using wordTrace_append hprefix tailTrace_4699760
  have hstable : (prefixWord ++ tailWord_4699760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4699760).length < 2 ^ (prefixWord ++ tailWord_4699760).sum := by decide
  have hdescent : baseEnd_4699760 < baseStart_4699760 := by decide
  rcases family_descends (prefixWord ++ tailWord_4699760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4699784 : List Nat := [2, 1, 3, 5, 1, 1, 1, 2, 1, 2, 4]
def baseStart_4699784 : Nat := 118140960795 + 4699784 * 2 ^ 59
def prefixEnd_4699784 : Nat := 4983230072969 + 3 ^ 40 * 4699784 * 2
def baseEnd_4699784 : Nat := 2413248164310345307186093

theorem tailTrace_4699784 : CollatzResearch.WordTrace tailWord_4699784 prefixEnd_4699784 2413248164310345307186093 := by
  unfold tailWord_4699784
  simp only [CollatzResearch.WordTrace]
  refine ⟨85707602402746351024673203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114276803203661801366230937 85707602402746351024673203)
  ·
    refine ⟨128561403604119526537009805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85707602402746351024673203 128561403604119526537009805)
    ·
      refine ⟨48210526351544822451378677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 128561403604119526537009805 48210526351544822451378677)
      ·
        refine ⟨4519736845457327104816751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 48210526351544822451378677 4519736845457327104816751)
        ·
          refine ⟨6779605268185990657225127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4519736845457327104816751 6779605268185990657225127)
          ·
            refine ⟨10169407902278985985837691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6779605268185990657225127 10169407902278985985837691)
            ·
              refine ⟨15254111853418478978756537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10169407902278985985837691 15254111853418478978756537)
              ·
                refine ⟨11440583890063859234067403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15254111853418478978756537 11440583890063859234067403)
                ·
                  refine ⟨17160875835095788851101105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11440583890063859234067403 17160875835095788851101105)
                  ·
                    refine ⟨12870656876321841638325829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17160875835095788851101105 12870656876321841638325829)
                    ·
                      refine ⟨2413248164310345307186093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12870656876321841638325829 2413248164310345307186093)
                      ·
                        rfl

theorem cell23_4699784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_4699784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4699784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4699784 prefixEnd_4699784 := by exact prefixLift 4699784
  have htrace : WordTrace (prefixWord ++ tailWord_4699784) baseStart_4699784 baseEnd_4699784 := by
    simpa [prefixWord, tailWord_4699784, baseEnd_4699784] using wordTrace_append hprefix tailTrace_4699784
  have hstable : (prefixWord ++ tailWord_4699784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4699784).length < 2 ^ (prefixWord ++ tailWord_4699784).sum := by decide
  have hdescent : baseEnd_4699784 < baseStart_4699784 := by decide
  rcases family_descends (prefixWord ++ tailWord_4699784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4699840 : List Nat := [2, 1, 1, 2, 4, 1, 1, 2, 1, 4, 4]
def baseStart_4699840 : Nat := 118140960795 + 4699840 * 2 ^ 59
def prefixEnd_4699840 : Nat := 4983230072969 + 3 ^ 40 * 4699840 * 2
def baseEnd_4699840 : Nat := 2413276919226997088085835

theorem tailTrace_4699840 : CollatzResearch.WordTrace tailWord_4699840 prefixEnd_4699840 2413276919226997088085835 := by
  unfold tailWord_4699840
  simp only [CollatzResearch.WordTrace]
  refine ⟨85708623646644911806692487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114278164862193215742256649 85708623646644911806692487)
  ·
    refine ⟨128562935469967367710038731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85708623646644911806692487 128562935469967367710038731)
    ·
      refine ⟨192844403204951051565058097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128562935469967367710038731 192844403204951051565058097)
      ·
        refine ⟨144633302403713288673793573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 192844403204951051565058097 144633302403713288673793573)
        ·
          refine ⟨27118744200696241626336295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 144633302403713288673793573 27118744200696241626336295)
          ·
            refine ⟨40678116301044362439504443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27118744200696241626336295 40678116301044362439504443)
            ·
              refine ⟨61017174451566543659256665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40678116301044362439504443 61017174451566543659256665)
              ·
                refine ⟨45762880838674907744442499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61017174451566543659256665 45762880838674907744442499)
                ·
                  refine ⟨68644321258012361616663749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45762880838674907744442499 68644321258012361616663749)
                  ·
                    refine ⟨12870810235877317803124453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 68644321258012361616663749 12870810235877317803124453)
                    ·
                      refine ⟨2413276919226997088085835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12870810235877317803124453 2413276919226997088085835)
                      ·
                        rfl

theorem cell23_4699840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 4, 4].length) (baseStart_4699840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4699840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4699840 prefixEnd_4699840 := by exact prefixLift 4699840
  have htrace : WordTrace (prefixWord ++ tailWord_4699840) baseStart_4699840 baseEnd_4699840 := by
    simpa [prefixWord, tailWord_4699840, baseEnd_4699840] using wordTrace_append hprefix tailTrace_4699840
  have hstable : (prefixWord ++ tailWord_4699840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4699840).length < 2 ^ (prefixWord ++ tailWord_4699840).sum := by decide
  have hdescent : baseEnd_4699840 < baseStart_4699840 := by decide
  rcases family_descends (prefixWord ++ tailWord_4699840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4699842 : List Nat := [3, 5, 1, 2, 1, 2, 2, 1, 1, 2, 3]
def baseStart_4699842 : Nat := 118140960795 + 4699842 * 2 ^ 59
def prefixEnd_4699842 : Nat := 4983230072969 + 3 ^ 40 * 4699842 * 2
def baseEnd_4699842 : Nat := 2413277946188306080260827

theorem tailTrace_4699842 : CollatzResearch.WordTrace tailWord_4699842 prefixEnd_4699842 2413277946188306080260827 := by
  unfold tailWord_4699842
  simp only [CollatzResearch.WordTrace]
  refine ⟨42854330059820644488739445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114278213492855051969971853 42854330059820644488739445)
  ·
    refine ⟨4017593443108185420819323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 42854330059820644488739445 4017593443108185420819323)
    ·
      refine ⟨6026390164662278131228985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4017593443108185420819323 6026390164662278131228985)
      ·
        refine ⟨4519792623496708598421739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6026390164662278131228985 4519792623496708598421739)
        ·
          refine ⟨6779688935245062897632609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4519792623496708598421739 6779688935245062897632609)
          ·
            refine ⟨5084766701433797173224457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6779688935245062897632609 5084766701433797173224457)
            ·
              refine ⟨3813575026075347879918343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5084766701433797173224457 3813575026075347879918343)
              ·
                refine ⟨5720362539113021819877515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3813575026075347879918343 5720362539113021819877515)
                ·
                  refine ⟨8580543808669532729816273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5720362539113021819877515 8580543808669532729816273)
                  ·
                    refine ⟨6435407856502149547362205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8580543808669532729816273 6435407856502149547362205)
                    ·
                      refine ⟨2413277946188306080260827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6435407856502149547362205 2413277946188306080260827)
                      ·
                        rfl

theorem cell23_4699842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 2, 1, 1, 2, 3].length) (baseStart_4699842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4699842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4699842 prefixEnd_4699842 := by exact prefixLift 4699842
  have htrace : WordTrace (prefixWord ++ tailWord_4699842) baseStart_4699842 baseEnd_4699842 := by
    simpa [prefixWord, tailWord_4699842, baseEnd_4699842] using wordTrace_append hprefix tailTrace_4699842
  have hstable : (prefixWord ++ tailWord_4699842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4699842).length < 2 ^ (prefixWord ++ tailWord_4699842).sum := by decide
  have hdescent : baseEnd_4699842 < baseStart_4699842 := by decide
  rcases family_descends (prefixWord ++ tailWord_4699842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4699844 : List Nat := [2, 3, 3, 1, 1, 1, 1, 4, 1, 4, 2]
def baseStart_4699844 : Nat := 118140960795 + 4699844 * 2 ^ 59
def prefixEnd_4699844 : Nat := 4983230072969 + 3 ^ 40 * 4699844 * 2
def baseEnd_4699844 : Nat := 2413278973149615072435817

theorem tailTrace_4699844 : CollatzResearch.WordTrace tailWord_4699844 prefixEnd_4699844 2413278973149615072435817 := by
  unfold tailWord_4699844
  simp only [CollatzResearch.WordTrace]
  refine ⟨85708696592637666148265293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114278262123516888197687057 85708696592637666148265293)
  ·
    refine ⟨32140761222239124805599485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85708696592637666148265293 32140761222239124805599485)
    ·
      refine ⟨12052785458339671802099807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32140761222239124805599485 12052785458339671802099807)
      ·
        refine ⟨18079178187509507703149711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12052785458339671802099807 18079178187509507703149711)
        ·
          refine ⟨27118767281264261554724567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18079178187509507703149711 27118767281264261554724567)
          ·
            refine ⟨40678150921896392332086851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27118767281264261554724567 40678150921896392332086851)
            ·
              refine ⟨61017226382844588498130277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40678150921896392332086851 61017226382844588498130277)
              ·
                refine ⟨11440729946783360343399427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 61017226382844588498130277 11440729946783360343399427)
                ·
                  refine ⟨17161094920175040515099141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11440729946783360343399427 17161094920175040515099141)
                  ·
                    refine ⟨3217705297532820096581089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17161094920175040515099141 3217705297532820096581089)
                    ·
                      refine ⟨2413278973149615072435817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3217705297532820096581089 2413278973149615072435817)
                      ·
                        rfl

theorem cell23_4699844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 4, 1, 4, 2].length) (baseStart_4699844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4699844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4699844 prefixEnd_4699844 := by exact prefixLift 4699844
  have htrace : WordTrace (prefixWord ++ tailWord_4699844) baseStart_4699844 baseEnd_4699844 := by
    simpa [prefixWord, tailWord_4699844, baseEnd_4699844] using wordTrace_append hprefix tailTrace_4699844
  have hstable : (prefixWord ++ tailWord_4699844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4699844).length < 2 ^ (prefixWord ++ tailWord_4699844).sum := by decide
  have hdescent : baseEnd_4699844 < baseStart_4699844 := by decide
  rcases family_descends (prefixWord ++ tailWord_4699844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4699877 : List Nat := [1, 3, 1, 4, 1, 1, 1, 3, 2, 3, 3]
def baseStart_4699877 : Nat := 118140960795 + 4699877 * 2 ^ 59
def prefixEnd_4699877 : Nat := 4983230072969 + 3 ^ 40 * 4699877 * 2
def baseEnd_4699877 : Nat := 2413295918011213443323165

theorem tailTrace_4699877 : CollatzResearch.WordTrace tailWord_4699877 prefixEnd_4699877 2413295918011213443323165 := by
  unfold tailWord_4699877
  simp only [CollatzResearch.WordTrace]
  refine ⟨171418596794155778932481885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114279064529437185954987923 171418596794155778932481885)
  ·
    refine ⟨64281973797808417099680707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 171418596794155778932481885 64281973797808417099680707)
    ·
      refine ⟨96422960696712625649521061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64281973797808417099680707 96422960696712625649521061)
      ·
        refine ⟨18079305130633617309285199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 96422960696712625649521061 18079305130633617309285199)
        ·
          refine ⟨27118957695950425963927799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18079305130633617309285199 27118957695950425963927799)
          ·
            refine ⟨40678436543925638945891699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27118957695950425963927799 40678436543925638945891699)
            ·
              refine ⟨61017654815888458418837549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40678436543925638945891699 61017654815888458418837549)
              ·
                refine ⟨22881620555958171907064081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61017654815888458418837549 22881620555958171907064081)
                ·
                  refine ⟨17161215416968628930298061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22881620555958171907064081 17161215416968628930298061)
                  ·
                    refine ⟨6435455781363235848861773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17161215416968628930298061 6435455781363235848861773)
                    ·
                      refine ⟨2413295918011213443323165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6435455781363235848861773 2413295918011213443323165)
                      ·
                        rfl

theorem cell23_4699877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 3, 2, 3, 3].length) (baseStart_4699877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4699877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4699877 prefixEnd_4699877 := by exact prefixLift 4699877
  have htrace : WordTrace (prefixWord ++ tailWord_4699877) baseStart_4699877 baseEnd_4699877 := by
    simpa [prefixWord, tailWord_4699877, baseEnd_4699877] using wordTrace_append hprefix tailTrace_4699877
  have hstable : (prefixWord ++ tailWord_4699877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4699877).length < 2 ^ (prefixWord ++ tailWord_4699877).sum := by decide
  have hdescent : baseEnd_4699877 < baseStart_4699877 := by decide
  rcases family_descends (prefixWord ++ tailWord_4699877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4699954 : List Nat := [3, 2, 1, 1, 3, 2, 1, 3, 2, 2, 3]
def baseStart_4699954 : Nat := 118140960795 + 4699954 * 2 ^ 59
def prefixEnd_4699954 : Nat := 4983230072969 + 3 ^ 40 * 4699954 * 2
def baseEnd_4699954 : Nat := 2413335456021609642060311

theorem tailTrace_4699954 : CollatzResearch.WordTrace tailWord_4699954 prefixEnd_4699954 2413335456021609642060311 := by
  unfold tailWord_4699954
  simp only [CollatzResearch.WordTrace]
  refine ⟨42855351303719205270758729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114280936809917880722023277 42855351303719205270758729)
  ·
    refine ⟨32141513477789403953069047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42855351303719205270758729 32141513477789403953069047)
    ·
      refine ⟨48212270216684105929603571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32141513477789403953069047 48212270216684105929603571)
      ·
        refine ⟨72318405325026158894405357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48212270216684105929603571 72318405325026158894405357)
        ·
          refine ⟨27119401996884809585402009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72318405325026158894405357 27119401996884809585402009)
          ·
            refine ⟨20339551497663607189051507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27119401996884809585402009 20339551497663607189051507)
            ·
              refine ⟨30509327246495410783577261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20339551497663607189051507 30509327246495410783577261)
              ·
                refine ⟨11440997717435779043841473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30509327246495410783577261 11440997717435779043841473)
                ·
                  refine ⟨8580748288076834282881105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11440997717435779043841473 8580748288076834282881105)
                  ·
                    refine ⟨6435561216057625712160829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8580748288076834282881105 6435561216057625712160829)
                    ·
                      refine ⟨2413335456021609642060311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6435561216057625712160829 2413335456021609642060311)
                      ·
                        rfl

theorem cell23_4699954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 3, 2, 2, 3].length) (baseStart_4699954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4699954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4699954 prefixEnd_4699954 := by exact prefixLift 4699954
  have htrace : WordTrace (prefixWord ++ tailWord_4699954) baseStart_4699954 baseEnd_4699954 := by
    simpa [prefixWord, tailWord_4699954, baseEnd_4699954] using wordTrace_append hprefix tailTrace_4699954
  have hstable : (prefixWord ++ tailWord_4699954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4699954).length < 2 ^ (prefixWord ++ tailWord_4699954).sum := by decide
  have hdescent : baseEnd_4699954 < baseStart_4699954 := by decide
  rcases family_descends (prefixWord ++ tailWord_4699954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4699984 : List Nat := [2, 1, 1, 1, 1, 4, 1, 5, 3, 1, 3]
def baseStart_4699984 : Nat := 118140960795 + 4699984 * 2 ^ 59
def prefixEnd_4699984 : Nat := 4983230072969 + 3 ^ 40 * 4699984 * 2
def baseEnd_4699984 : Nat := 2413350860441244524685173

theorem tailTrace_4699984 : CollatzResearch.WordTrace tailWord_4699984 prefixEnd_4699984 2413350860441244524685173 := by
  unfold tailWord_4699984
  simp only [CollatzResearch.WordTrace]
  refine ⟨85711249702384068103313503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114281666269845424137751337 85711249702384068103313503)
  ·
    refine ⟨128566874553576102154970255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85711249702384068103313503 128566874553576102154970255)
    ·
      refine ⟨192850311830364153232455383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128566874553576102154970255 192850311830364153232455383)
      ·
        refine ⟨289275467745546229848683075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192850311830364153232455383 289275467745546229848683075)
        ·
          refine ⟨433913201618319344773024613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 289275467745546229848683075 433913201618319344773024613)
          ·
            refine ⟨81358725303434877144942115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 433913201618319344773024613 81358725303434877144942115)
            ·
              refine ⟨122038087955152315717413173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81358725303434877144942115 122038087955152315717413173)
              ·
                refine ⟨11441070745795529598507485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 122038087955152315717413173 11441070745795529598507485)
                ·
                  refine ⟨4290401529673323599440307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11441070745795529598507485 4290401529673323599440307)
                  ·
                    refine ⟨6435602294509985399160461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4290401529673323599440307 6435602294509985399160461)
                    ·
                      refine ⟨2413350860441244524685173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6435602294509985399160461 2413350860441244524685173)
                      ·
                        rfl

theorem cell23_4699984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 5, 3, 1, 3].length) (baseStart_4699984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4699984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4699984 prefixEnd_4699984 := by exact prefixLift 4699984
  have htrace : WordTrace (prefixWord ++ tailWord_4699984) baseStart_4699984 baseEnd_4699984 := by
    simpa [prefixWord, tailWord_4699984, baseEnd_4699984] using wordTrace_append hprefix tailTrace_4699984
  have hstable : (prefixWord ++ tailWord_4699984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4699984).length < 2 ^ (prefixWord ++ tailWord_4699984).sum := by decide
  have hdescent : baseEnd_4699984 < baseStart_4699984 := by decide
  rcases family_descends (prefixWord ++ tailWord_4699984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4699994 : List Nat := [3, 1, 1, 2, 1, 3, 2, 2, 1, 5, 2]
def baseStart_4699994 : Nat := 118140960795 + 4699994 * 2 ^ 59
def prefixEnd_4699994 : Nat := 4983230072969 + 3 ^ 40 * 4699994 * 2
def baseEnd_4699994 : Nat := 2413355995247789485560127

theorem tailTrace_4699994 : CollatzResearch.WordTrace tailWord_4699994 prefixEnd_4699994 2413355995247789485560127 := by
  unfold tailWord_4699994
  simp only [CollatzResearch.WordTrace]
  refine ⟨42855716033682976978622759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114281909423154605276327357 42855716033682976978622759)
  ·
    refine ⟨64283574050524465467934139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42855716033682976978622759 64283574050524465467934139)
    ·
      refine ⟨96425361075786698201901209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64283574050524465467934139 96425361075786698201901209)
      ·
        refine ⟨72319020806840023651425907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96425361075786698201901209 72319020806840023651425907)
        ·
          refine ⟨108478531210260035477138861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72319020806840023651425907 108478531210260035477138861)
          ·
            refine ⟨40679449203847513303927073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 108478531210260035477138861 40679449203847513303927073)
            ·
              refine ⟨30509586902885634977945305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40679449203847513303927073 30509586902885634977945305)
              ·
                refine ⟨22882190177164226233458979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30509586902885634977945305 22882190177164226233458979)
                ·
                  refine ⟨34323285265746339350188469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22882190177164226233458979 34323285265746339350188469)
                  ·
                    refine ⟨3217807993663719314080169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34323285265746339350188469 3217807993663719314080169)
                    ·
                      refine ⟨2413355995247789485560127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3217807993663719314080169 2413355995247789485560127)
                      ·
                        rfl

theorem cell23_4699994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 2, 1, 5, 2].length) (baseStart_4699994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4699994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4699994 prefixEnd_4699994 := by exact prefixLift 4699994
  have htrace : WordTrace (prefixWord ++ tailWord_4699994) baseStart_4699994 baseEnd_4699994 := by
    simpa [prefixWord, tailWord_4699994, baseEnd_4699994] using wordTrace_append hprefix tailTrace_4699994
  have hstable : (prefixWord ++ tailWord_4699994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4699994).length < 2 ^ (prefixWord ++ tailWord_4699994).sum := by decide
  have hdescent : baseEnd_4699994 < baseStart_4699994 := by decide
  rcases family_descends (prefixWord ++ tailWord_4699994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4700017 : List Nat := [1, 2, 2, 2, 1, 3, 1, 4, 1, 6]
def baseStart_4700017 : Nat := 118140960795 + 4700017 * 2 ^ 59
def prefixEnd_4700017 : Nat := 4983230072969 + 3 ^ 40 * 4700017 * 2
def baseEnd_4700017 : Nat := 804455935100947631857507

theorem tailTrace_4700017 : CollatzResearch.WordTrace tailWord_4700017 prefixEnd_4700017 804455935100947631857507 := by
  unfold tailWord_4700017
  simp only [CollatzResearch.WordTrace]
  refine ⟨171423703013648582842578305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114282468675765721895052203 171423703013648582842578305)
  ·
    refine ⟨128567777260236437131933729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171423703013648582842578305 128567777260236437131933729)
    ·
      refine ⟨96425832945177327848950297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128567777260236437131933729 96425832945177327848950297)
      ·
        refine ⟨72319374708882995886712723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96425832945177327848950297 72319374708882995886712723)
        ·
          refine ⟨108479062063324493830069085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72319374708882995886712723 108479062063324493830069085)
          ·
            refine ⟨40679648273746685186275907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 108479062063324493830069085 40679648273746685186275907)
            ·
              refine ⟨61019472410620027779413861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40679648273746685186275907 61019472410620027779413861)
              ·
                refine ⟨11441151076991255208640099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 61019472410620027779413861 11441151076991255208640099)
                ·
                  refine ⟨17161726615486882812960149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11441151076991255208640099 17161726615486882812960149)
                  ·
                    refine ⟨804455935100947631857507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17161726615486882812960149 804455935100947631857507)
                    ·
                      rfl

theorem cell23_4700017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 4, 1, 6].length) (baseStart_4700017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4700017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4700017 prefixEnd_4700017 := by exact prefixLift 4700017
  have htrace : WordTrace (prefixWord ++ tailWord_4700017) baseStart_4700017 baseEnd_4700017 := by
    simpa [prefixWord, tailWord_4700017, baseEnd_4700017] using wordTrace_append hprefix tailTrace_4700017
  have hstable : (prefixWord ++ tailWord_4700017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4700017).length < 2 ^ (prefixWord ++ tailWord_4700017).sum := by decide
  have hdescent : baseEnd_4700017 < baseStart_4700017 := by decide
  rcases family_descends (prefixWord ++ tailWord_4700017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4700027 : List Nat := [1, 1, 1, 1, 1, 5, 1, 5, 1, 1, 5]
def baseStart_4700027 : Nat := 118140960795 + 4700027 * 2 ^ 59
def prefixEnd_4700027 : Nat := 4983230072969 + 3 ^ 40 * 4700027 * 2
def baseEnd_4700027 : Nat := 2413372940109387856447475

theorem tailTrace_4700027 : CollatzResearch.WordTrace tailWord_4700027 prefixEnd_4700027 2413372940109387856447475 := by
  unfold tailWord_4700027
  simp only [CollatzResearch.WordTrace]
  refine ⟨171424067743612354550442335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114282711829074903033628223 171424067743612354550442335)
  ·
    refine ⟨257136101615418531825663503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171424067743612354550442335 257136101615418531825663503)
    ·
      refine ⟨385704152423127797738495255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 257136101615418531825663503 385704152423127797738495255)
      ·
        refine ⟨578556228634691696607742883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 385704152423127797738495255 578556228634691696607742883)
        ·
          refine ⟨867834342952037544911614325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 578556228634691696607742883 867834342952037544911614325)
          ·
            refine ⟨81359469651753519835463843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 867834342952037544911614325 81359469651753519835463843)
            ·
              refine ⟨122039204477630279753195765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81359469651753519835463843 122039204477630279753195765)
              ·
                refine ⟨11441175419777838726862103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 122039204477630279753195765 11441175419777838726862103)
                ·
                  refine ⟨17161763129666758090293155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11441175419777838726862103 17161763129666758090293155)
                  ·
                    refine ⟨25742644694500137135439733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17161763129666758090293155 25742644694500137135439733)
                    ·
                      refine ⟨2413372940109387856447475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25742644694500137135439733 2413372940109387856447475)
                      ·
                        rfl

theorem cell23_4700027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 5, 1, 1, 5].length) (baseStart_4700027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4700027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4700027 prefixEnd_4700027 := by exact prefixLift 4700027
  have htrace : WordTrace (prefixWord ++ tailWord_4700027) baseStart_4700027 baseEnd_4700027 := by
    simpa [prefixWord, tailWord_4700027, baseEnd_4700027] using wordTrace_append hprefix tailTrace_4700027
  have hstable : (prefixWord ++ tailWord_4700027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4700027).length < 2 ^ (prefixWord ++ tailWord_4700027).sum := by decide
  have hdescent : baseEnd_4700027 < baseStart_4700027 := by decide
  rcases family_descends (prefixWord ++ tailWord_4700027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4700037 : List Nat := [1, 3, 1, 1, 3, 2, 2, 2, 1, 1, 6]
def baseStart_4700037 : Nat := 118140960795 + 4700037 * 2 ^ 59
def prefixEnd_4700037 : Nat := 4983230072969 + 3 ^ 40 * 4700037 * 2
def baseEnd_4700037 : Nat := 2413378074915932817322429

theorem tailTrace_4700037 : CollatzResearch.WordTrace tailWord_4700037 prefixEnd_4700037 2413378074915932817322429 := by
  unfold tailWord_4700037
  simp only [CollatzResearch.WordTrace]
  refine ⟨171424432473576126258306365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114282954982384084172204243 171424432473576126258306365)
  ·
    refine ⟨64284162177591047346864887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 171424432473576126258306365 64284162177591047346864887)
    ·
      refine ⟨96426243266386571020297331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64284162177591047346864887 96426243266386571020297331)
      ·
        refine ⟨144639364899579856530445997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96426243266386571020297331 144639364899579856530445997)
        ·
          refine ⟨54239761837342446198917249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 144639364899579856530445997 54239761837342446198917249)
          ·
            refine ⟨40679821378006834649187937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54239761837342446198917249 40679821378006834649187937)
            ·
              refine ⟨30509866033505125986890953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40679821378006834649187937 30509866033505125986890953)
              ·
                refine ⟨22882399525128844490168215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30509866033505125986890953 22882399525128844490168215)
                ·
                  refine ⟨34323599287693266735252323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22882399525128844490168215 34323599287693266735252323)
                  ·
                    refine ⟨51485398931539900102878485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34323599287693266735252323 51485398931539900102878485)
                    ·
                      refine ⟨2413378074915932817322429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 51485398931539900102878485 2413378074915932817322429)
                      ·
                        rfl

theorem cell23_4700037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 2, 1, 1, 6].length) (baseStart_4700037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4700037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4700037 prefixEnd_4700037 := by exact prefixLift 4700037
  have htrace : WordTrace (prefixWord ++ tailWord_4700037) baseStart_4700037 baseEnd_4700037 := by
    simpa [prefixWord, tailWord_4700037, baseEnd_4700037] using wordTrace_append hprefix tailTrace_4700037
  have hstable : (prefixWord ++ tailWord_4700037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4700037).length < 2 ^ (prefixWord ++ tailWord_4700037).sum := by decide
  have hdescent : baseEnd_4700037 < baseStart_4700037 := by decide
  rcases family_descends (prefixWord ++ tailWord_4700037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4700058 : List Nat := [3, 1, 1, 4, 2, 1, 2, 2, 3, 2, 2]
def baseStart_4700058 : Nat := 118140960795 + 4700058 * 2 ^ 59
def prefixEnd_4700058 : Nat := 4983230072969 + 3 ^ 40 * 4700058 * 2
def baseEnd_4700058 : Nat := 2413388858009677235159833

theorem tailTrace_4700058 : CollatzResearch.WordTrace tailWord_4700058 prefixEnd_4700058 2413388858009677235159833 := by
  unfold tailWord_4700058
  simp only [CollatzResearch.WordTrace]
  refine ⟨42856299601625011711205207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114283465604333364563213885 42856299601625011711205207)
  ·
    refine ⟨64284449402437517566807811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42856299601625011711205207 64284449402437517566807811)
    ·
      refine ⟨96426674103656276350211717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64284449402437517566807811 96426674103656276350211717)
      ·
        refine ⟨18080001394435551815664697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 96426674103656276350211717 18080001394435551815664697)
        ·
          refine ⟨13560001045826663861748523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18080001394435551815664697 13560001045826663861748523)
          ·
            refine ⟨20340001568739995792622785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13560001045826663861748523 20340001568739995792622785)
            ·
              refine ⟨15255001176554996844467089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20340001568739995792622785 15255001176554996844467089)
              ·
                refine ⟨11441250882416247633350317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15255001176554996844467089 11441250882416247633350317)
                ·
                  refine ⟨4290469080906092862506369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11441250882416247633350317 4290469080906092862506369)
                  ·
                    refine ⟨3217851810679569646879777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4290469080906092862506369 3217851810679569646879777)
                    ·
                      refine ⟨2413388858009677235159833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3217851810679569646879777 2413388858009677235159833)
                      ·
                        rfl

theorem cell23_4700058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 2, 3, 2, 2].length) (baseStart_4700058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4700058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4700058 prefixEnd_4700058 := by exact prefixLift 4700058
  have htrace : WordTrace (prefixWord ++ tailWord_4700058) baseStart_4700058 baseEnd_4700058 := by
    simpa [prefixWord, tailWord_4700058, baseEnd_4700058] using wordTrace_append hprefix tailTrace_4700058
  have hstable : (prefixWord ++ tailWord_4700058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4700058).length < 2 ^ (prefixWord ++ tailWord_4700058).sum := by decide
  have hdescent : baseEnd_4700058 < baseStart_4700058 := by decide
  rcases family_descends (prefixWord ++ tailWord_4700058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4700061 : List Nat := [1, 4, 2, 1, 2, 2, 1, 4, 1, 2, 3]
def baseStart_4700061 : Nat := 118140960795 + 4700061 * 2 ^ 59
def prefixEnd_4700061 : Nat := 4983230072969 + 3 ^ 40 * 4700061 * 2
def baseEnd_4700061 : Nat := 2413390398451640723422319

theorem tailTrace_4700061 : CollatzResearch.WordTrace tailWord_4700061 prefixEnd_4700061 2413390398451640723422319 := by
  unfold tailWord_4700061
  simp only [CollatzResearch.WordTrace]
  refine ⟨171425307825489178357180037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114283538550326118904786691 171425307825489178357180037)
  ·
    refine ⟨32142245217279220941971257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 171425307825489178357180037 32142245217279220941971257)
    ·
      refine ⟨24106683912959415706478443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32142245217279220941971257 24106683912959415706478443)
      ·
        refine ⟨36160025869439123559717665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24106683912959415706478443 36160025869439123559717665)
        ·
          refine ⟨27120019402079342669788249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36160025869439123559717665 27120019402079342669788249)
          ·
            refine ⟨20340014551559507002341187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27120019402079342669788249 20340014551559507002341187)
            ·
              refine ⟨30510021827339260503511781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20340014551559507002341187 30510021827339260503511781)
              ·
                refine ⟨5720629092626111344408459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30510021827339260503511781 5720629092626111344408459)
                ·
                  refine ⟨8580943638939167016612689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5720629092626111344408459 8580943638939167016612689)
                  ·
                    refine ⟨6435707729204375262459517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8580943638939167016612689 6435707729204375262459517)
                    ·
                      refine ⟨2413390398451640723422319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6435707729204375262459517 2413390398451640723422319)
                      ·
                        rfl

theorem cell23_4700061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 4, 1, 2, 3].length) (baseStart_4700061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4700061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4700061 prefixEnd_4700061 := by exact prefixLift 4700061
  have htrace : WordTrace (prefixWord ++ tailWord_4700061) baseStart_4700061 baseEnd_4700061 := by
    simpa [prefixWord, tailWord_4700061, baseEnd_4700061] using wordTrace_append hprefix tailTrace_4700061
  have hstable : (prefixWord ++ tailWord_4700061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4700061).length < 2 ^ (prefixWord ++ tailWord_4700061).sum := by decide
  have hdescent : baseEnd_4700061 < baseStart_4700061 := by decide
  rcases family_descends (prefixWord ++ tailWord_4700061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4700087 : List Nat := [1, 1, 3, 1, 3, 1, 1, 1, 4, 2, 5]
def baseStart_4700087 : Nat := 118140960795 + 4700087 * 2 ^ 59
def prefixEnd_4700087 : Nat := 4983230072969 + 3 ^ 40 * 4700087 * 2
def baseEnd_4700087 : Nat := 2413403748948657621697199

theorem tailTrace_4700087 : CollatzResearch.WordTrace tailWord_4700087 prefixEnd_4700087 2413403748948657621697199 := by
  unfold tailWord_4700087
  simp only [CollatzResearch.WordTrace]
  refine ⟨171426256123394984797626515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114284170748929989865084343 171426256123394984797626515)
  ·
    refine ⟨257139384185092477196439773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171426256123394984797626515 257139384185092477196439773)
    ·
      refine ⟨96427269069409678948664915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 257139384185092477196439773 96427269069409678948664915)
      ·
        refine ⟨144640903604114518422997373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96427269069409678948664915 144640903604114518422997373)
        ·
          refine ⟨54240338851542944408624015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 144640903604114518422997373 54240338851542944408624015)
          ·
            refine ⟨81360508277314416612936023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54240338851542944408624015 81360508277314416612936023)
            ·
              refine ⟨122040762415971624919404035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81360508277314416612936023 122040762415971624919404035)
              ·
                refine ⟨183061143623957437379106053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 122040762415971624919404035 183061143623957437379106053)
                ·
                  refine ⟨34323964429492019508582385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 183061143623957437379106053 34323964429492019508582385)
                  ·
                    refine ⟨25742973322119014631436789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34323964429492019508582385 25742973322119014631436789)
                    ·
                      refine ⟨2413403748948657621697199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25742973322119014631436789 2413403748948657621697199)
                      ·
                        rfl

theorem cell23_4700087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 4, 2, 5].length) (baseStart_4700087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4700087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4700087 prefixEnd_4700087 := by exact prefixLift 4700087
  have htrace : WordTrace (prefixWord ++ tailWord_4700087) baseStart_4700087 baseEnd_4700087 := by
    simpa [prefixWord, tailWord_4700087, baseEnd_4700087] using wordTrace_append hprefix tailTrace_4700087
  have hstable : (prefixWord ++ tailWord_4700087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4700087).length < 2 ^ (prefixWord ++ tailWord_4700087).sum := by decide
  have hdescent : baseEnd_4700087 < baseStart_4700087 := by decide
  rcases family_descends (prefixWord ++ tailWord_4700087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4700092 : List Nat := [2, 2, 2, 5, 1, 2, 1, 1, 3, 2, 2]
def baseStart_4700092 : Nat := 118140960795 + 4700092 * 2 ^ 59
def prefixEnd_4700092 : Nat := 4983230072969 + 3 ^ 40 * 4700092 * 2
def baseEnd_4700092 : Nat := 2413406316351930102134677

theorem tailTrace_4700092 : CollatzResearch.WordTrace tailWord_4700092 prefixEnd_4700092 2413406316351930102134677 := by
  unfold tailWord_4700092
  simp only [CollatzResearch.WordTrace]
  refine ⟨85713219244188435325779265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114284292325584580434372353 85713219244188435325779265)
  ·
    refine ⟨64284914433141326494334449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85713219244188435325779265 64284914433141326494334449)
    ·
      refine ⟨48213685824855994870750837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64284914433141326494334449 48213685824855994870750837)
      ·
        refine ⟨4520033046080249519132891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 48213685824855994870750837 4520033046080249519132891)
        ·
          refine ⟨6780049569120374278699337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4520033046080249519132891 6780049569120374278699337)
          ·
            refine ⟨5085037176840280709024503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6780049569120374278699337 5085037176840280709024503)
            ·
              refine ⟨7627555765260421063536755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5085037176840280709024503 7627555765260421063536755)
              ·
                refine ⟨11441333647890631595305133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7627555765260421063536755 11441333647890631595305133)
                ·
                  refine ⟨4290500117958986848239425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11441333647890631595305133 4290500117958986848239425)
                  ·
                    refine ⟨3217875088469240136179569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4290500117958986848239425 3217875088469240136179569)
                    ·
                      refine ⟨2413406316351930102134677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3217875088469240136179569 2413406316351930102134677)
                      ·
                        rfl

theorem cell23_4700092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 1, 1, 3, 2, 2].length) (baseStart_4700092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4700092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4700092 prefixEnd_4700092 := by exact prefixLift 4700092
  have htrace : WordTrace (prefixWord ++ tailWord_4700092) baseStart_4700092 baseEnd_4700092 := by
    simpa [prefixWord, tailWord_4700092, baseEnd_4700092] using wordTrace_append hprefix tailTrace_4700092
  have hstable : (prefixWord ++ tailWord_4700092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4700092).length < 2 ^ (prefixWord ++ tailWord_4700092).sum := by decide
  have hdescent : baseEnd_4700092 < baseStart_4700092 := by decide
  rcases family_descends (prefixWord ++ tailWord_4700092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4700107 : List Nat := [1, 1, 1, 1, 3, 4, 2, 1, 1, 8]
def baseStart_4700107 : Nat := 118140960795 + 4700107 * 2 ^ 59
def prefixEnd_4700107 : Nat := 4983230072969 + 3 ^ 40 * 4700107 * 2
def baseEnd_4700107 : Nat := 804471339520582514482369

theorem tailTrace_4700107 : CollatzResearch.WordTrace tailWord_4700107 prefixEnd_4700107 804471339520582514482369 := by
  unfold tailWord_4700107
  simp only [CollatzResearch.WordTrace]
  refine ⟨171426985583322528213354575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114284657055548352142236383 171426985583322528213354575)
  ·
    refine ⟨257140478374983792320031863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171426985583322528213354575 257140478374983792320031863)
    ·
      refine ⟨385710717562475688480047795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 257140478374983792320031863 385710717562475688480047795)
      ·
        refine ⟨578566076343713532720071693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 385710717562475688480047795 578566076343713532720071693)
        ·
          refine ⟨216962278628892574770026885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 578566076343713532720071693 216962278628892574770026885)
          ·
            refine ⟨40680427242917357769380041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 216962278628892574770026885 40680427242917357769380041)
            ·
              refine ⟨30510320432188018327035031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40680427242917357769380041 30510320432188018327035031)
              ·
                refine ⟨45765480648282027490552547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30510320432188018327035031 45765480648282027490552547)
                ·
                  refine ⟨68648220972423041235828821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45765480648282027490552547 68648220972423041235828821)
                  ·
                    refine ⟨804471339520582514482369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 68648220972423041235828821 804471339520582514482369)
                    ·
                      rfl

theorem cell23_4700107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 1, 1, 8].length) (baseStart_4700107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4700107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4700107 prefixEnd_4700107 := by exact prefixLift 4700107
  have htrace : WordTrace (prefixWord ++ tailWord_4700107) baseStart_4700107 baseEnd_4700107 := by
    simpa [prefixWord, tailWord_4700107, baseEnd_4700107] using wordTrace_append hprefix tailTrace_4700107
  have hstable : (prefixWord ++ tailWord_4700107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4700107).length < 2 ^ (prefixWord ++ tailWord_4700107).sum := by decide
  have hdescent : baseEnd_4700107 < baseStart_4700107 := by decide
  rcases family_descends (prefixWord ++ tailWord_4700107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4700108 : List Nat := [2, 2, 1, 4, 1, 3, 1, 3, 2, 1, 3]
def baseStart_4700108 : Nat := 118140960795 + 4700108 * 2 ^ 59
def prefixEnd_4700108 : Nat := 4983230072969 + 3 ^ 40 * 4700108 * 2
def baseEnd_4700108 : Nat := 2413414532042402039534603

theorem tailTrace_4700108 : CollatzResearch.WordTrace tailWord_4700108 prefixEnd_4700108 2413414532042402039534603 := by
  unfold tailWord_4700108
  simp only [CollatzResearch.WordTrace]
  refine ⟨85713511028159452692070489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114284681370879270256093985 85713511028159452692070489)
  ·
    refine ⟨64285133271119589519052867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85713511028159452692070489 64285133271119589519052867)
    ·
      refine ⟨96427699906679384278579301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64285133271119589519052867 96427699906679384278579301)
      ·
        refine ⟨18080193732502384552233619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 96427699906679384278579301 18080193732502384552233619)
        ·
          refine ⟨27120290598753576828350429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18080193732502384552233619 27120290598753576828350429)
          ·
            refine ⟨10170108974532591310631411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27120290598753576828350429 10170108974532591310631411)
            ·
              refine ⟨15255163461798886965947117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10170108974532591310631411 15255163461798886965947117)
              ·
                refine ⟨5720686298174582612230169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15255163461798886965947117 5720686298174582612230169)
                ·
                  refine ⟨4290514723630936959172627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5720686298174582612230169 4290514723630936959172627)
                  ·
                    refine ⟨6435772085446405438758941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4290514723630936959172627 6435772085446405438758941)
                    ·
                      refine ⟨2413414532042402039534603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6435772085446405438758941 2413414532042402039534603)
                      ·
                        rfl

theorem cell23_4700108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 3, 2, 1, 3].length) (baseStart_4700108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4700108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4700108 prefixEnd_4700108 := by exact prefixLift 4700108
  have htrace : WordTrace (prefixWord ++ tailWord_4700108) baseStart_4700108 baseEnd_4700108 := by
    simpa [prefixWord, tailWord_4700108, baseEnd_4700108] using wordTrace_append hprefix tailTrace_4700108
  have hstable : (prefixWord ++ tailWord_4700108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4700108).length < 2 ^ (prefixWord ++ tailWord_4700108).sum := by decide
  have hdescent : baseEnd_4700108 < baseStart_4700108 := by decide
  rcases family_descends (prefixWord ++ tailWord_4700108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4700131 : List Nat := [1, 1, 1, 6, 1, 2, 1, 1, 3, 4, 2]
def baseStart_4700131 : Nat := 118140960795 + 4700131 * 2 ^ 59
def prefixEnd_4700131 : Nat := 4983230072969 + 3 ^ 40 * 4700131 * 2
def baseEnd_4700131 : Nat := 2413426342097455449546997

theorem tailTrace_4700131 : CollatzResearch.WordTrace tailWord_4700131 prefixEnd_4700131 2413426342097455449546997 := by
  unfold tailWord_4700131
  simp only [CollatzResearch.WordTrace]
  refine ⟨171427860935235580312228247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114285240623490386874818831 171427860935235580312228247)
  ·
    refine ⟨257141791402853370468342371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171427860935235580312228247 257141791402853370468342371)
    ·
      refine ⟨385712687104280055702513557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 257141791402853370468342371 385712687104280055702513557)
      ·
        refine ⟨18080282208013127611055323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 385712687104280055702513557 18080282208013127611055323)
        ·
          refine ⟨27120423312019691416582985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18080282208013127611055323 27120423312019691416582985)
          ·
            refine ⟨20340317484014768562437239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27120423312019691416582985 20340317484014768562437239)
            ·
              refine ⟨30510476226022152843655859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20340317484014768562437239 30510476226022152843655859)
              ·
                refine ⟨45765714339033229265483789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30510476226022152843655859 45765714339033229265483789)
                ·
                  refine ⟨17162142877137460974556421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45765714339033229265483789 17162142877137460974556421)
                  ·
                    refine ⟨3217901789463273932729329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17162142877137460974556421 3217901789463273932729329)
                    ·
                      refine ⟨2413426342097455449546997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3217901789463273932729329 2413426342097455449546997)
                      ·
                        rfl

theorem cell23_4700131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 1, 3, 4, 2].length) (baseStart_4700131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4700131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4700131 prefixEnd_4700131 := by exact prefixLift 4700131
  have htrace : WordTrace (prefixWord ++ tailWord_4700131) baseStart_4700131 baseEnd_4700131 := by
    simpa [prefixWord, tailWord_4700131, baseEnd_4700131] using wordTrace_append hprefix tailTrace_4700131
  have hstable : (prefixWord ++ tailWord_4700131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4700131).length < 2 ^ (prefixWord ++ tailWord_4700131).sum := by decide
  have hdescent : baseEnd_4700131 < baseStart_4700131 := by decide
  rcases family_descends (prefixWord ++ tailWord_4700131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4700147 : List Nat := [1, 1, 1, 2, 2, 2, 1, 3, 1, 2, 7]
def baseStart_4700147 : Nat := 118140960795 + 4700147 * 2 ^ 59
def prefixEnd_4700147 : Nat := 4983230072969 + 3 ^ 40 * 4700147 * 2
def baseEnd_4700147 : Nat := 2413434557787927386946923

theorem tailTrace_4700147 : CollatzResearch.WordTrace tailWord_4700147 prefixEnd_4700147 2413434557787927386946923 := by
  unfold tailWord_4700147
  simp only [CollatzResearch.WordTrace]
  refine ⟨171428444503177615044810695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114285629668785076696540463 171428444503177615044810695)
  ·
    refine ⟨257142666754766422567216043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171428444503177615044810695 257142666754766422567216043)
    ·
      refine ⟨385714000132149633850824065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 257142666754766422567216043 385714000132149633850824065)
      ·
        refine ⟨289285500099112225388118049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 385714000132149633850824065 289285500099112225388118049)
        ·
          refine ⟨216964125074334169041088537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 289285500099112225388118049 216964125074334169041088537)
          ·
            refine ⟨162723093805750626780816403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 216964125074334169041088537 162723093805750626780816403)
            ·
              refine ⟨244084640708625940171224605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 162723093805750626780816403 244084640708625940171224605)
              ·
                refine ⟨91531740265734727564209227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 244084640708625940171224605 91531740265734727564209227)
                ·
                  refine ⟨137297610398602091346313841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 91531740265734727564209227 137297610398602091346313841)
                  ·
                    refine ⟨102973207798951568509735381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 137297610398602091346313841 102973207798951568509735381)
                    ·
                      refine ⟨2413434557787927386946923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 102973207798951568509735381 2413434557787927386946923)
                      ·
                        rfl

theorem cell23_4700147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 3, 1, 2, 7].length) (baseStart_4700147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4700147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4700147 prefixEnd_4700147 := by exact prefixLift 4700147
  have htrace : WordTrace (prefixWord ++ tailWord_4700147) baseStart_4700147 baseEnd_4700147 := by
    simpa [prefixWord, tailWord_4700147, baseEnd_4700147] using wordTrace_append hprefix tailTrace_4700147
  have hstable : (prefixWord ++ tailWord_4700147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4700147).length < 2 ^ (prefixWord ++ tailWord_4700147).sum := by decide
  have hdescent : baseEnd_4700147 < baseStart_4700147 := by decide
  rcases family_descends (prefixWord ++ tailWord_4700147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4700184 : List Nat := [2, 1, 2, 3, 2, 1, 3, 1, 1, 7]
def baseStart_4700184 : Nat := 118140960795 + 4700184 * 2 ^ 59
def prefixEnd_4700184 : Nat := 4983230072969 + 3 ^ 40 * 4700184 * 2
def baseEnd_4700184 : Nat := 804484518857381247394751

theorem tailTrace_4700184 : CollatzResearch.WordTrace tailWord_4700184 prefixEnd_4700184 804484518857381247394751 := by
  unfold tailWord_4700184
  simp only [CollatzResearch.WordTrace]
  refine ⟨85714897002021785181953803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114286529336029046909271737 85714897002021785181953803)
  ·
    refine ⟨128572345503032677772930705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85714897002021785181953803 128572345503032677772930705)
    ·
      refine ⟨96429259127274508329698029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128572345503032677772930705 96429259127274508329698029)
      ·
        refine ⟨36160972172727940623636761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96429259127274508329698029 36160972172727940623636761)
        ·
          refine ⟨27120729129545955467727571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36160972172727940623636761 27120729129545955467727571)
          ·
            refine ⟨40681093694318933201591357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27120729129545955467727571 40681093694318933201591357)
            ·
              refine ⟨15255410135369599950596759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40681093694318933201591357 15255410135369599950596759)
              ·
                refine ⟨22883115203054399925895139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15255410135369599950596759 22883115203054399925895139)
                ·
                  refine ⟨34324672804581599888842709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22883115203054399925895139 34324672804581599888842709)
                  ·
                    refine ⟨804484518857381247394751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34324672804581599888842709 804484518857381247394751)
                    ·
                      rfl

theorem cell23_4700184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 1, 1, 7].length) (baseStart_4700184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4700184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4700184 prefixEnd_4700184 := by exact prefixLift 4700184
  have htrace : WordTrace (prefixWord ++ tailWord_4700184) baseStart_4700184 baseEnd_4700184 := by
    simpa [prefixWord, tailWord_4700184, baseEnd_4700184] using wordTrace_append hprefix tailTrace_4700184
  have hstable : (prefixWord ++ tailWord_4700184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4700184).length < 2 ^ (prefixWord ++ tailWord_4700184).sum := by decide
  have hdescent : baseEnd_4700184 < baseStart_4700184 := by decide
  rcases family_descends (prefixWord ++ tailWord_4700184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4700188 : List Nat := [2, 2, 3, 1, 3, 2, 2, 3, 5]
def baseStart_4700188 : Nat := 118140960795 + 4700188 * 2 ^ 59
def prefixEnd_4700188 : Nat := 4983230072969 + 3 ^ 40 * 4700188 * 2
def baseEnd_4700188 : Nat := 268161734499417969614915

theorem tailTrace_4700188 : CollatzResearch.WordTrace tailWord_4700188 prefixEnd_4700188 268161734499417969614915 := by
  unfold tailWord_4700188
  simp only [CollatzResearch.WordTrace]
  refine ⟨85714969948014539523526609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114286626597352719364702145 85714969948014539523526609)
  ·
    refine ⟨64286227461010904642644957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85714969948014539523526609 64286227461010904642644957)
    ·
      refine ⟨24107335297879089240991859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64286227461010904642644957 24107335297879089240991859)
      ·
        refine ⟨36161002946818633861487789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24107335297879089240991859 36161002946818633861487789)
        ·
          refine ⟨13560376105056987698057921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36161002946818633861487789 13560376105056987698057921)
          ·
            refine ⟨10170282078792740773543441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13560376105056987698057921 10170282078792740773543441)
            ·
              refine ⟨7627711559094555580157581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10170282078792740773543441 7627711559094555580157581)
              ·
                refine ⟨2860391834660458342559093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7627711559094555580157581 2860391834660458342559093)
                ·
                  refine ⟨268161734499417969614915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2860391834660458342559093 268161734499417969614915)
                  ·
                    rfl

theorem cell23_4700188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 2, 3, 5].length) (baseStart_4700188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4700188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4700188 prefixEnd_4700188 := by exact prefixLift 4700188
  have htrace : WordTrace (prefixWord ++ tailWord_4700188) baseStart_4700188 baseEnd_4700188 := by
    simpa [prefixWord, tailWord_4700188, baseEnd_4700188] using wordTrace_append hprefix tailTrace_4700188
  have hstable : (prefixWord ++ tailWord_4700188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4700188).length < 2 ^ (prefixWord ++ tailWord_4700188).sum := by decide
  have hdescent : baseEnd_4700188 < baseStart_4700188 := by decide
  rcases family_descends (prefixWord ++ tailWord_4700188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4700199 : List Nat := [1, 1, 7, 1, 2, 2, 1, 2, 2, 2, 2]
def baseStart_4700199 : Nat := 118140960795 + 4700199 * 2 ^ 59
def prefixEnd_4700199 : Nat := 4983230072969 + 3 ^ 40 * 4700199 * 2
def baseEnd_4700199 : Nat := 2413461258781961183496685

theorem tailTrace_4700199 : CollatzResearch.WordTrace tailWord_4700199 prefixEnd_4700199 2413461258781961183496685 := by
  unfold tailWord_4700199
  simp only [CollatzResearch.WordTrace]
  refine ⟨171430341098989227925703651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114286894065992818617135767 171430341098989227925703651)
  ·
    refine ⟨257145511648483841888555477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171430341098989227925703651 257145511648483841888555477)
    ·
      refine ⟨6026847929261340044263019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 257145511648483841888555477 6026847929261340044263019)
      ·
        refine ⟨9040271893892010066394529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6026847929261340044263019 9040271893892010066394529)
        ·
          refine ⟨6780203920419007549795897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9040271893892010066394529 6780203920419007549795897)
          ·
            refine ⟨5085152940314255662346923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6780203920419007549795897 5085152940314255662346923)
            ·
              refine ⟨7627729410471383493520385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5085152940314255662346923 7627729410471383493520385)
              ·
                refine ⟨5720797057853537620140289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7627729410471383493520385 5720797057853537620140289)
                ·
                  refine ⟨4290597793390153215105217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5720797057853537620140289 4290597793390153215105217)
                  ·
                    refine ⟨3217948345042614911328913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4290597793390153215105217 3217948345042614911328913)
                    ·
                      refine ⟨2413461258781961183496685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3217948345042614911328913 2413461258781961183496685)
                      ·
                        rfl

theorem cell23_4700199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 1, 2, 2, 2, 2].length) (baseStart_4700199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4700199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4700199 prefixEnd_4700199 := by exact prefixLift 4700199
  have htrace : WordTrace (prefixWord ++ tailWord_4700199) baseStart_4700199 baseEnd_4700199 := by
    simpa [prefixWord, tailWord_4700199, baseEnd_4700199] using wordTrace_append hprefix tailTrace_4700199
  have hstable : (prefixWord ++ tailWord_4700199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4700199).length < 2 ^ (prefixWord ++ tailWord_4700199).sum := by decide
  have hdescent : baseEnd_4700199 < baseStart_4700199 := by decide
  rcases family_descends (prefixWord ++ tailWord_4700199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4700231 : List Nat := [1, 1, 4, 1, 3, 1, 1, 4, 3, 4]
def baseStart_4700231 : Nat := 118140960795 + 4700231 * 2 ^ 59
def prefixEnd_4700231 : Nat := 4983230072969 + 3 ^ 40 * 4700231 * 2
def baseEnd_4700231 : Nat := 804492563387635019432179

theorem tailTrace_4700231 : CollatzResearch.WordTrace tailWord_4700231 prefixEnd_4700231 804492563387635019432179 := by
  unfold tailWord_4700231
  simp only [CollatzResearch.WordTrace]
  refine ⟨171431508234873297390868547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114287672156582198260579031 171431508234873297390868547)
  ·
    refine ⟨257147262352309946086302821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171431508234873297390868547 257147262352309946086302821)
    ·
      refine ⟨48215111691058114891181779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 257147262352309946086302821 48215111691058114891181779)
      ·
        refine ⟨72322667536587172336772669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48215111691058114891181779 72322667536587172336772669)
        ·
          refine ⟨27121000326220189626289751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72322667536587172336772669 27121000326220189626289751)
          ·
            refine ⟨40681500489330284439434627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27121000326220189626289751 40681500489330284439434627)
            ·
              refine ⟨61022250733995426659151941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40681500489330284439434627 61022250733995426659151941)
              ·
                refine ⟨11441672012624142498590989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 61022250733995426659151941 11441672012624142498590989)
                ·
                  refine ⟨4290627004734053436971621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11441672012624142498590989 4290627004734053436971621)
                  ·
                    refine ⟨804492563387635019432179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4290627004734053436971621 804492563387635019432179)
                    ·
                      rfl

theorem cell23_4700231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 4, 3, 4].length) (baseStart_4700231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4700231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4700231 prefixEnd_4700231 := by exact prefixLift 4700231
  have htrace : WordTrace (prefixWord ++ tailWord_4700231) baseStart_4700231 baseEnd_4700231 := by
    simpa [prefixWord, tailWord_4700231, baseEnd_4700231] using wordTrace_append hprefix tailTrace_4700231
  have hstable : (prefixWord ++ tailWord_4700231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4700231).length < 2 ^ (prefixWord ++ tailWord_4700231).sum := by decide
  have hdescent : baseEnd_4700231 < baseStart_4700231 := by decide
  rcases family_descends (prefixWord ++ tailWord_4700231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4700234 : List Nat := [3, 1, 2, 1, 1, 2, 1, 1, 1, 6, 4]
def baseStart_4700234 : Nat := 118140960795 + 4700234 * 2 ^ 59
def prefixEnd_4700234 : Nat := 4983230072969 + 3 ^ 40 * 4700234 * 2
def baseEnd_4700234 : Nat := 2413479230604868546559023

theorem tailTrace_4700234 : CollatzResearch.WordTrace tailWord_4700234 prefixEnd_4700234 2413479230604868546559023 := by
  unfold tailWord_4700234
  simp only [CollatzResearch.WordTrace]
  refine ⟨42857904413465607225806939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114287745102574952602151837 42857904413465607225806939)
  ·
    refine ⟨64286856620198410838710409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42857904413465607225806939 64286856620198410838710409)
    ·
      refine ⟨48215142465148808129032807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64286856620198410838710409 48215142465148808129032807)
      ·
        refine ⟨72322713697723212193549211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48215142465148808129032807 72322713697723212193549211)
        ·
          refine ⟨108484070546584818290323817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72322713697723212193549211 108484070546584818290323817)
          ·
            refine ⟨81363052909938613717742863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 108484070546584818290323817 81363052909938613717742863)
            ·
              refine ⟨122044579364907920576614295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81363052909938613717742863 122044579364907920576614295)
              ·
                refine ⟨183066869047361880864921443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 122044579364907920576614295 183066869047361880864921443)
                ·
                  refine ⟨274600303571042821297382165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 183066869047361880864921443 274600303571042821297382165)
                  ·
                    refine ⟨12871889229892632248314789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 274600303571042821297382165 12871889229892632248314789)
                    ·
                      refine ⟨2413479230604868546559023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12871889229892632248314789 2413479230604868546559023)
                      ·
                        rfl

theorem cell23_4700234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 1, 1, 6, 4].length) (baseStart_4700234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4700234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4700234 prefixEnd_4700234 := by exact prefixLift 4700234
  have htrace : WordTrace (prefixWord ++ tailWord_4700234) baseStart_4700234 baseEnd_4700234 := by
    simpa [prefixWord, tailWord_4700234, baseEnd_4700234] using wordTrace_append hprefix tailTrace_4700234
  have hstable : (prefixWord ++ tailWord_4700234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4700234).length < 2 ^ (prefixWord ++ tailWord_4700234).sum := by decide
  have hdescent : baseEnd_4700234 < baseStart_4700234 := by decide
  rcases family_descends (prefixWord ++ tailWord_4700234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4700241 : List Nat := [1, 2, 2, 1, 3, 1, 1, 5, 2, 2, 3]
def baseStart_4700241 : Nat := 118140960795 + 4700241 * 2 ^ 59
def prefixEnd_4700241 : Nat := 4983230072969 + 3 ^ 40 * 4700241 * 2
def baseEnd_4700241 : Nat := 2413482824969450019171491

theorem tailTrace_4700241 : CollatzResearch.WordTrace tailWord_4700241 prefixEnd_4700241 2413482824969450019171491 := by
  unfold tailWord_4700241
  simp only [CollatzResearch.WordTrace]
  refine ⟨171431872964837069098732577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114287915309891379399155051 171431872964837069098732577)
  ·
    refine ⟨128573904723627801824049433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171431872964837069098732577 128573904723627801824049433)
    ·
      refine ⟨96430428542720851368037075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128573904723627801824049433 96430428542720851368037075)
      ·
        refine ⟨144645642814081277052055613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96430428542720851368037075 144645642814081277052055613)
        ·
          refine ⟨54242116055280478894520855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 144645642814081277052055613 54242116055280478894520855)
          ·
            refine ⟨81363174082920718341781283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54242116055280478894520855 81363174082920718341781283)
            ·
              refine ⟨122044761124381077512671925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81363174082920718341781283 122044761124381077512671925)
              ·
                refine ⟨11441696355410726016812993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 122044761124381077512671925 11441696355410726016812993)
                ·
                  refine ⟨8581272266558044512609745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11441696355410726016812993 8581272266558044512609745)
                  ·
                    refine ⟨6435954199918533384457309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8581272266558044512609745 6435954199918533384457309)
                    ·
                      refine ⟨2413482824969450019171491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6435954199918533384457309 2413482824969450019171491)
                      ·
                        rfl

theorem cell23_4700241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 5, 2, 2, 3].length) (baseStart_4700241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4700241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4700241 prefixEnd_4700241 := by exact prefixLift 4700241
  have htrace : WordTrace (prefixWord ++ tailWord_4700241) baseStart_4700241 baseEnd_4700241 := by
    simpa [prefixWord, tailWord_4700241, baseEnd_4700241] using wordTrace_append hprefix tailTrace_4700241
  have hstable : (prefixWord ++ tailWord_4700241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4700241).length < 2 ^ (prefixWord ++ tailWord_4700241).sum := by decide
  have hdescent : baseEnd_4700241 < baseStart_4700241 := by decide
  rcases family_descends (prefixWord ++ tailWord_4700241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4700265 : List Nat := [1, 2, 1, 1, 1, 5, 5, 2, 1, 4]
def baseStart_4700265 : Nat := 118140960795 + 4700265 * 2 ^ 59
def prefixEnd_4700265 : Nat := 4983230072969 + 3 ^ 40 * 4700265 * 2
def baseEnd_4700265 : Nat := 804498382835052641757127

theorem tailTrace_4700265 : CollatzResearch.WordTrace tailWord_4700265 prefixEnd_4700265 804498382835052641757127 := by
  unfold tailWord_4700265
  simp only [CollatzResearch.WordTrace]
  refine ⟨171432748316750121197606249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114288498877833414131737499 171432748316750121197606249)
  ·
    refine ⟨128574561237562590898204687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171432748316750121197606249 128574561237562590898204687)
    ·
      refine ⟨192861841856343886347307031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128574561237562590898204687 192861841856343886347307031)
      ·
        refine ⟨289292762784515829520960547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192861841856343886347307031 289292762784515829520960547)
        ·
          refine ⟨433939144176773744281440821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 289292762784515829520960547 433939144176773744281440821)
          ·
            refine ⟨40681794766572538526385077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 433939144176773744281440821 40681794766572538526385077)
            ·
              refine ⟨3813918259366175486848601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 40681794766572538526385077 3813918259366175486848601)
              ·
                refine ⟨2860438694524631615136451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3813918259366175486848601 2860438694524631615136451)
                ·
                  refine ⟨4290658041786947422704677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2860438694524631615136451 4290658041786947422704677)
                  ·
                    refine ⟨804498382835052641757127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4290658041786947422704677 804498382835052641757127)
                    ·
                      rfl

theorem cell23_4700265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 5, 2, 1, 4].length) (baseStart_4700265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4700265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4700265 prefixEnd_4700265 := by exact prefixLift 4700265
  have htrace : WordTrace (prefixWord ++ tailWord_4700265) baseStart_4700265 baseEnd_4700265 := by
    simpa [prefixWord, tailWord_4700265, baseEnd_4700265] using wordTrace_append hprefix tailTrace_4700265
  have hstable : (prefixWord ++ tailWord_4700265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4700265).length < 2 ^ (prefixWord ++ tailWord_4700265).sum := by decide
  have hdescent : baseEnd_4700265 < baseStart_4700265 := by decide
  rcases family_descends (prefixWord ++ tailWord_4700265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4700278 : List Nat := [5, 1, 1, 2, 1, 3, 1, 3, 6]
def baseStart_4700278 : Nat := 118140960795 + 4700278 * 2 ^ 59
def prefixEnd_4700278 : Nat := 4983230072969 + 3 ^ 40 * 4700278 * 2
def baseEnd_4700278 : Nat := 268166869305962930489869

theorem tailTrace_4700278 : CollatzResearch.WordTrace tailWord_4700278 prefixEnd_4700278 268166869305962930489869 := by
  unfold tailWord_4700278
  simp only [CollatzResearch.WordTrace]
  refine ⟨10714576404106439026114343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 114288814977135349611886325 10714576404106439026114343)
  ·
    refine ⟨16071864606159658539171515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10714576404106439026114343 16071864606159658539171515)
    ·
      refine ⟨24107796909239487808757273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16071864606159658539171515 24107796909239487808757273)
      ·
        refine ⟨18080847681929615856567955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24107796909239487808757273 18080847681929615856567955)
        ·
          refine ⟨27121271522894423784851933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18080847681929615856567955 27121271522894423784851933)
          ·
            refine ⟨10170476821085408919319475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27121271522894423784851933 10170476821085408919319475)
            ·
              refine ⟨15255715231628113378979213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10170476821085408919319475 15255715231628113378979213)
              ·
                refine ⟨5720893211860542517117205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15255715231628113378979213 5720893211860542517117205)
                ·
                  refine ⟨268166869305962930489869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5720893211860542517117205 268166869305962930489869)
                  ·
                    rfl

theorem cell23_4700278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 3, 6].length) (baseStart_4700278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4700278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4700278 prefixEnd_4700278 := by exact prefixLift 4700278
  have htrace : WordTrace (prefixWord ++ tailWord_4700278) baseStart_4700278 baseEnd_4700278 := by
    simpa [prefixWord, tailWord_4700278, baseEnd_4700278] using wordTrace_append hprefix tailTrace_4700278
  have hstable : (prefixWord ++ tailWord_4700278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4700278).length < 2 ^ (prefixWord ++ tailWord_4700278).sum := by decide
  have hdescent : baseEnd_4700278 < baseStart_4700278 := by decide
  rcases family_descends (prefixWord ++ tailWord_4700278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4700291 : List Nat := [1, 1, 1, 3, 3, 4, 1, 1, 3, 5]
def baseStart_4700291 : Nat := 118140960795 + 4700291 * 2 ^ 59
def prefixEnd_4700291 : Nat := 4983230072969 + 3 ^ 40 * 4700291 * 2
def baseEnd_4700291 : Nat := 804502833000724941182087

theorem tailTrace_4700291 : CollatzResearch.WordTrace tailWord_4700291 prefixEnd_4700291 804502833000724941182087 := by
  unfold tailWord_4700291
  simp only [CollatzResearch.WordTrace]
  refine ⟨171433696614655927638052727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114289131076437285092035151 171433696614655927638052727)
  ·
    refine ⟨257150544921983891457079091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171433696614655927638052727 257150544921983891457079091)
    ·
      refine ⟨385725817382975837185618637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 257150544921983891457079091 385725817382975837185618637)
      ·
        refine ⟨144647181518615938944606989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 385725817382975837185618637 144647181518615938944606989)
        ·
          refine ⟨54242693069480977104227621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 144647181518615938944606989 54242693069480977104227621)
          ·
            refine ⟨10170504950527683207042679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 54242693069480977104227621 10170504950527683207042679)
            ·
              refine ⟨15255757425791524810564019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10170504950527683207042679 15255757425791524810564019)
              ·
                refine ⟨22883636138687287215846029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15255757425791524810564019 22883636138687287215846029)
                ·
                  refine ⟨8581363552007732705942261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22883636138687287215846029 8581363552007732705942261)
                  ·
                    refine ⟨804502833000724941182087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8581363552007732705942261 804502833000724941182087)
                    ·
                      rfl

theorem cell23_4700291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 1, 3, 5].length) (baseStart_4700291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4700291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4700291 prefixEnd_4700291 := by exact prefixLift 4700291
  have htrace : WordTrace (prefixWord ++ tailWord_4700291) baseStart_4700291 baseEnd_4700291 := by
    simpa [prefixWord, tailWord_4700291, baseEnd_4700291] using wordTrace_append hprefix tailTrace_4700291
  have hstable : (prefixWord ++ tailWord_4700291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4700291).length < 2 ^ (prefixWord ++ tailWord_4700291).sum := by decide
  have hdescent : baseEnd_4700291 < baseStart_4700291 := by decide
  rcases family_descends (prefixWord ++ tailWord_4700291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4700338 : List Nat := [3, 2, 1, 1, 1, 3, 1, 5, 2, 4]
def baseStart_4700338 : Nat := 118140960795 + 4700338 * 2 ^ 59
def prefixEnd_4700338 : Nat := 4983230072969 + 3 ^ 40 * 4700338 * 2
def baseEnd_4700338 : Nat := 804510877530978713219515

theorem tailTrace_4700338 : CollatzResearch.WordTrace tailWord_4700338 prefixEnd_4700338 804510877530978713219515 := by
  unfold tailWord_4700338
  simp only [CollatzResearch.WordTrace]
  refine ⟨42858852711371413666253417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114290273896990436443342445 42858852711371413666253417)
  ·
    refine ⟨32144139533528560249690063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42858852711371413666253417 32144139533528560249690063)
    ·
      refine ⟨48216209300292840374535095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32144139533528560249690063 48216209300292840374535095)
      ·
        refine ⟨72324313950439260561802643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48216209300292840374535095 72324313950439260561802643)
        ·
          refine ⟨108486470925658890842703965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72324313950439260561802643 108486470925658890842703965)
          ·
            refine ⟨40682426597122084066013987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 108486470925658890842703965 40682426597122084066013987)
            ·
              refine ⟨61023639895683126099020981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40682426597122084066013987 61023639895683126099020981)
              ·
                refine ⟨5720966240220293071783217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 61023639895683126099020981 5720966240220293071783217)
                ·
                  refine ⟨4290724680165219803837413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5720966240220293071783217 4290724680165219803837413)
                  ·
                    refine ⟨804510877530978713219515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4290724680165219803837413 804510877530978713219515)
                    ·
                      rfl

theorem cell23_4700338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 5, 2, 4].length) (baseStart_4700338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4700338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4700338 prefixEnd_4700338 := by exact prefixLift 4700338
  have htrace : WordTrace (prefixWord ++ tailWord_4700338) baseStart_4700338 baseEnd_4700338 := by
    simpa [prefixWord, tailWord_4700338, baseEnd_4700338] using wordTrace_append hprefix tailTrace_4700338
  have hstable : (prefixWord ++ tailWord_4700338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4700338).length < 2 ^ (prefixWord ++ tailWord_4700338).sum := by decide
  have hdescent : baseEnd_4700338 < baseStart_4700338 := by decide
  rcases family_descends (prefixWord ++ tailWord_4700338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4700345 : List Nat := [1, 2, 1, 4, 1, 2, 3, 2, 3, 2, 2]
def baseStart_4700345 : Nat := 118140960795 + 4700345 * 2 ^ 59
def prefixEnd_4700345 : Nat := 4983230072969 + 3 ^ 40 * 4700345 * 2
def baseEnd_4700345 : Nat := 2413536226957517612271013

theorem tailTrace_4700345 : CollatzResearch.WordTrace tailWord_4700345 prefixEnd_4700345 2413536226957517612271013 := by
  unfold tailWord_4700345
  simp only [CollatzResearch.WordTrace]
  refine ⟨171435666156460294860518489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114290444104306863240345659 171435666156460294860518489)
  ·
    refine ⟨128576749617345221145388867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171435666156460294860518489 128576749617345221145388867)
    ·
      refine ⟨192865124426017831718083301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128576749617345221145388867 192865124426017831718083301)
      ·
        refine ⟨36162210829878343447140619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 192865124426017831718083301 36162210829878343447140619)
        ·
          refine ⟨54243316244817515170710929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36162210829878343447140619 54243316244817515170710929)
          ·
            refine ⟨40682487183613136378033197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54243316244817515170710929 40682487183613136378033197)
            ·
              refine ⟨15255932693854926141762449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40682487183613136378033197 15255932693854926141762449)
              ·
                refine ⟨11441949520391194606321837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15255932693854926141762449 11441949520391194606321837)
                ·
                  refine ⟨4290731070146697977370689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11441949520391194606321837 4290731070146697977370689)
                  ·
                    refine ⟨3218048302610023483028017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4290731070146697977370689 3218048302610023483028017)
                    ·
                      refine ⟨2413536226957517612271013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3218048302610023483028017 2413536226957517612271013)
                      ·
                        rfl

theorem cell23_4700345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 2, 3, 2, 2].length) (baseStart_4700345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4700345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4700345 prefixEnd_4700345 := by exact prefixLift 4700345
  have htrace : WordTrace (prefixWord ++ tailWord_4700345) baseStart_4700345 baseEnd_4700345 := by
    simpa [prefixWord, tailWord_4700345, baseEnd_4700345] using wordTrace_append hprefix tailTrace_4700345
  have hstable : (prefixWord ++ tailWord_4700345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4700345).length < 2 ^ (prefixWord ++ tailWord_4700345).sum := by decide
  have hdescent : baseEnd_4700345 < baseStart_4700345 := by decide
  rcases family_descends (prefixWord ++ tailWord_4700345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4700361 : List Nat := [1, 2, 1, 1, 2, 1, 1, 5, 3, 3, 3]
def baseStart_4700361 : Nat := 118140960795 + 4700361 * 2 ^ 59
def prefixEnd_4700361 : Nat := 4983230072969 + 3 ^ 40 * 4700361 * 2
def baseEnd_4700361 : Nat := 2413544442647989549670939

theorem tailTrace_4700361 : CollatzResearch.WordTrace tailWord_4700361 prefixEnd_4700361 2413544442647989549670939 := by
  unfold tailWord_4700361
  simp only [CollatzResearch.WordTrace]
  refine ⟨171436249724402329593100937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114290833149601553062067291 171436249724402329593100937)
  ·
    refine ⟨128577187293301747194825703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171436249724402329593100937 128577187293301747194825703)
    ·
      refine ⟨192865780939952620792238555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128577187293301747194825703 192865780939952620792238555)
      ·
        refine ⟨289298671409928931188357833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192865780939952620792238555 289298671409928931188357833)
        ·
          refine ⟨216974003557446698391268375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 289298671409928931188357833 216974003557446698391268375)
          ·
            refine ⟨325461005336170047586902563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 216974003557446698391268375 325461005336170047586902563)
            ·
              refine ⟨488191508004255071380353845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 325461005336170047586902563 488191508004255071380353845)
              ·
                refine ⟨45767953875398912941908173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 488191508004255071380353845 45767953875398912941908173)
                ·
                  refine ⟨17162982703274592353215565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45767953875398912941908173 17162982703274592353215565)
                  ·
                    refine ⟨6436118513727972132455837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17162982703274592353215565 6436118513727972132455837)
                    ·
                      refine ⟨2413544442647989549670939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6436118513727972132455837 2413544442647989549670939)
                      ·
                        rfl

theorem cell23_4700361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 5, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 5, 3, 3, 3].length) (baseStart_4700361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4700361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4700361 prefixEnd_4700361 := by exact prefixLift 4700361
  have htrace : WordTrace (prefixWord ++ tailWord_4700361) baseStart_4700361 baseEnd_4700361 := by
    simpa [prefixWord, tailWord_4700361, baseEnd_4700361] using wordTrace_append hprefix tailTrace_4700361
  have hstable : (prefixWord ++ tailWord_4700361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4700361).length < 2 ^ (prefixWord ++ tailWord_4700361).sum := by decide
  have hdescent : baseEnd_4700361 < baseStart_4700361 := by decide
  rcases family_descends (prefixWord ++ tailWord_4700361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4700401 : List Nat := [1, 2, 2, 2, 2, 1, 2, 2, 2, 3, 4]
def baseStart_4700401 : Nat := 118140960795 + 4700401 * 2 ^ 59
def prefixEnd_4700401 : Nat := 4983230072969 + 3 ^ 40 * 4700401 * 2
def baseEnd_4700401 : Nat := 2413564981874169393170755

theorem tailTrace_4700401 : CollatzResearch.WordTrace tailWord_4700401 prefixEnd_4700401 2413564981874169393170755 := by
  unfold tailWord_4700401
  simp only [CollatzResearch.WordTrace]
  refine ⟨171437708644257416424557057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114291805762838277616371371 171437708644257416424557057)
  ·
    refine ⟨128578281483193062318417793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171437708644257416424557057 128578281483193062318417793)
    ·
      refine ⟨96433711112394796738813345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128578281483193062318417793 96433711112394796738813345)
      ·
        refine ⟨72325283334296097554110009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96433711112394796738813345 72325283334296097554110009)
        ·
          refine ⟨54243962500722073165582507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72325283334296097554110009 54243962500722073165582507)
          ·
            refine ⟨81365943751083109748373761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54243962500722073165582507 81365943751083109748373761)
            ·
              refine ⟨61024457813312332311280321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81365943751083109748373761 61024457813312332311280321)
              ·
                refine ⟨45768343359984249233460241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61024457813312332311280321 45768343359984249233460241)
                ·
                  refine ⟨34326257519988186925095181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45768343359984249233460241 34326257519988186925095181)
                  ·
                    refine ⟨12872346569995570096910693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34326257519988186925095181 12872346569995570096910693)
                    ·
                      refine ⟨2413564981874169393170755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12872346569995570096910693 2413564981874169393170755)
                      ·
                        rfl

theorem cell23_4700401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 2, 2, 3, 4].length) (baseStart_4700401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4700401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4700401 prefixEnd_4700401 := by exact prefixLift 4700401
  have htrace : WordTrace (prefixWord ++ tailWord_4700401) baseStart_4700401 baseEnd_4700401 := by
    simpa [prefixWord, tailWord_4700401, baseEnd_4700401] using wordTrace_append hprefix tailTrace_4700401
  have hstable : (prefixWord ++ tailWord_4700401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4700401).length < 2 ^ (prefixWord ++ tailWord_4700401).sum := by decide
  have hdescent : baseEnd_4700401 < baseStart_4700401 := by decide
  rcases family_descends (prefixWord ++ tailWord_4700401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4700431 : List Nat := [1, 1, 2, 1, 1, 1, 3, 3, 4, 2, 4]
def baseStart_4700431 : Nat := 118140960795 + 4700431 * 2 ^ 59
def prefixEnd_4700431 : Nat := 4983230072969 + 3 ^ 40 * 4700431 * 2
def baseEnd_4700431 : Nat := 2413580386293804275795617

theorem tailTrace_4700431 : CollatzResearch.WordTrace tailWord_4700431 prefixEnd_4700431 2413580386293804275795617 := by
  unfold tailWord_4700431
  simp only [CollatzResearch.WordTrace]
  refine ⟨171438802834148731548149147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114292535222765821032099431 171438802834148731548149147)
  ·
    refine ⟨257158204251223097322223721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171438802834148731548149147 257158204251223097322223721)
    ·
      refine ⟨192868653188417322991667791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 257158204251223097322223721 192868653188417322991667791)
      ·
        refine ⟨289302979782625984487501687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192868653188417322991667791 289302979782625984487501687)
        ·
          refine ⟨433954469673938976731252531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 289302979782625984487501687 433954469673938976731252531)
          ·
            refine ⟨650931704510908465096878797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 433954469673938976731252531 650931704510908465096878797)
            ·
              refine ⟨244099389191590674411329549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 650931704510908465096878797 244099389191590674411329549)
              ·
                refine ⟨91537270946846502904248581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 244099389191590674411329549 91537270946846502904248581)
                ·
                  refine ⟨17163238302533719294546609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 91537270946846502904248581 17163238302533719294546609)
                  ·
                    refine ⟨12872428726900289470909957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17163238302533719294546609 12872428726900289470909957)
                    ·
                      refine ⟨2413580386293804275795617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12872428726900289470909957 2413580386293804275795617)
                      ·
                        rfl

theorem cell23_4700431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 3, 4, 2, 4].length) (baseStart_4700431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4700431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4700431 prefixEnd_4700431 := by exact prefixLift 4700431
  have htrace : WordTrace (prefixWord ++ tailWord_4700431) baseStart_4700431 baseEnd_4700431 := by
    simpa [prefixWord, tailWord_4700431, baseEnd_4700431] using wordTrace_append hprefix tailTrace_4700431
  have hstable : (prefixWord ++ tailWord_4700431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4700431).length < 2 ^ (prefixWord ++ tailWord_4700431).sum := by decide
  have hdescent : baseEnd_4700431 < baseStart_4700431 := by decide
  rcases family_descends (prefixWord ++ tailWord_4700431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4700446 : List Nat := [4, 3, 2, 1, 1, 1, 4, 1, 2, 1, 3]
def baseStart_4700446 : Nat := 118140960795 + 4700446 * 2 ^ 59
def prefixEnd_4700446 : Nat := 4983230072969 + 3 ^ 40 * 4700446 * 2
def baseEnd_4700446 : Nat := 2413588088503621717108049

theorem tailTrace_4700446 : CollatzResearch.WordTrace tailWord_4700446 prefixEnd_4700446 2413588088503621717108049 := by
  unfold tailWord_4700446
  simp only [CollatzResearch.WordTrace]
  refine ⟨21429918741136798638743149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 114292899952729592739963461 21429918741136798638743149)
  ·
    refine ⟨8036219527926299489528681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21429918741136798638743149 8036219527926299489528681)
    ·
      refine ⟨6027164645944724617146511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8036219527926299489528681 6027164645944724617146511)
      ·
        refine ⟨9040746968917086925719767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6027164645944724617146511 9040746968917086925719767)
        ·
          refine ⟨13561120453375630388579651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9040746968917086925719767 13561120453375630388579651)
          ·
            refine ⟨20341680680063445582869477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13561120453375630388579651 20341680680063445582869477)
            ·
              refine ⟨3814065127511896046788027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20341680680063445582869477 3814065127511896046788027)
              ·
                refine ⟨5721097691267844070182041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3814065127511896046788027 5721097691267844070182041)
                ·
                  refine ⟨4290823268450883052636531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5721097691267844070182041 4290823268450883052636531)
                  ·
                    refine ⟨6436234902676324578954797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4290823268450883052636531 6436234902676324578954797)
                    ·
                      refine ⟨2413588088503621717108049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6436234902676324578954797 2413588088503621717108049)
                      ·
                        rfl

theorem cell23_4700446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 4, 1, 2, 1, 3].length) (baseStart_4700446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4700446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4700446 prefixEnd_4700446 := by exact prefixLift 4700446
  have htrace : WordTrace (prefixWord ++ tailWord_4700446) baseStart_4700446 baseEnd_4700446 := by
    simpa [prefixWord, tailWord_4700446, baseEnd_4700446] using wordTrace_append hprefix tailTrace_4700446
  have hstable : (prefixWord ++ tailWord_4700446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4700446).length < 2 ^ (prefixWord ++ tailWord_4700446).sum := by decide
  have hdescent : baseEnd_4700446 < baseStart_4700446 := by decide
  rcases family_descends (prefixWord ++ tailWord_4700446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4700456 : List Nat := [2, 1, 5, 1, 4, 1, 1, 2, 1, 3, 2]
def baseStart_4700456 : Nat := 118140960795 + 4700456 * 2 ^ 59
def prefixEnd_4700456 : Nat := 4983230072969 + 3 ^ 40 * 4700456 * 2
def baseEnd_4700456 : Nat := 2413593223310166677983003

theorem tailTrace_4700456 : CollatzResearch.WordTrace tailWord_4700456 prefixEnd_4700456 2413593223310166677983003 := by
  unfold tailWord_4700456
  simp only [CollatzResearch.WordTrace]
  refine ⟨85719857329529080408904611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114293143106038773878539481 85719857329529080408904611)
  ·
    refine ⟨128579785994293620613356917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85719857329529080408904611 128579785994293620613356917)
    ·
      refine ⟨12054354936965026932502211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 128579785994293620613356917 12054354936965026932502211)
      ·
        refine ⟨18081532405447540398753317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12054354936965026932502211 18081532405447540398753317)
        ·
          refine ⟨3390287326021413824766247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18081532405447540398753317 3390287326021413824766247)
          ·
            refine ⟨5085430989032120737149371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3390287326021413824766247 5085430989032120737149371)
            ·
              refine ⟨7628146483548181105724057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5085430989032120737149371 7628146483548181105724057)
              ·
                refine ⟨5721109862661135829293043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7628146483548181105724057 5721109862661135829293043)
                ·
                  refine ⟨8581664793991703743939565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5721109862661135829293043 8581664793991703743939565)
                  ·
                    refine ⟨3218124297746888903977337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8581664793991703743939565 3218124297746888903977337)
                    ·
                      refine ⟨2413593223310166677983003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3218124297746888903977337 2413593223310166677983003)
                      ·
                        rfl

theorem cell23_4700456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 1, 2, 1, 3, 2].length) (baseStart_4700456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4700456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4700456 prefixEnd_4700456 := by exact prefixLift 4700456
  have htrace : WordTrace (prefixWord ++ tailWord_4700456) baseStart_4700456 baseEnd_4700456 := by
    simpa [prefixWord, tailWord_4700456, baseEnd_4700456] using wordTrace_append hprefix tailTrace_4700456
  have hstable : (prefixWord ++ tailWord_4700456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4700456).length < 2 ^ (prefixWord ++ tailWord_4700456).sum := by decide
  have hdescent : baseEnd_4700456 < baseStart_4700456 := by decide
  rcases family_descends (prefixWord ++ tailWord_4700456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4700471 : List Nat := [1, 1, 3, 1, 2, 1, 1, 5, 1, 7]
def baseStart_4700471 : Nat := 118140960795 + 4700471 * 2 ^ 59
def prefixEnd_4700471 : Nat := 4983230072969 + 3 ^ 40 * 4700471 * 2
def baseEnd_4700471 : Nat := 804533641839994706431811

theorem tailTrace_4700471 : CollatzResearch.WordTrace tailWord_4700471 prefixEnd_4700471 804533641839994706431811 := by
  unfold tailWord_4700471
  simp only [CollatzResearch.WordTrace]
  refine ⟨171440261754003818379605267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114293507836002545586403511 171440261754003818379605267)
  ·
    refine ⟨257160392631005727569407901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171440261754003818379605267 257160392631005727569407901)
    ·
      refine ⟨96435147236627147838527963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 257160392631005727569407901 96435147236627147838527963)
      ·
        refine ⟨144652720854940721757791945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96435147236627147838527963 144652720854940721757791945)
        ·
          refine ⟨108489540641205541318343959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 144652720854940721757791945 108489540641205541318343959)
          ·
            refine ⟨162734310961808311977515939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108489540641205541318343959 162734310961808311977515939)
            ·
              refine ⟨244101466442712467966273909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 162734310961808311977515939 244101466442712467966273909)
              ·
                refine ⟨22884512479004293871838179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 244101466442712467966273909 22884512479004293871838179)
                ·
                  refine ⟨34326768718506440807757269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22884512479004293871838179 34326768718506440807757269)
                  ·
                    refine ⟨804533641839994706431811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34326768718506440807757269 804533641839994706431811)
                    ·
                      rfl

theorem cell23_4700471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 5, 1, 7].length) (baseStart_4700471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4700471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4700471 prefixEnd_4700471 := by exact prefixLift 4700471
  have htrace : WordTrace (prefixWord ++ tailWord_4700471) baseStart_4700471 baseEnd_4700471 := by
    simpa [prefixWord, tailWord_4700471, baseEnd_4700471] using wordTrace_append hprefix tailTrace_4700471
  have hstable : (prefixWord ++ tailWord_4700471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4700471).length < 2 ^ (prefixWord ++ tailWord_4700471).sum := by decide
  have hdescent : baseEnd_4700471 < baseStart_4700471 := by decide
  rcases family_descends (prefixWord ++ tailWord_4700471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4700488 : List Nat := [2, 1, 3, 1, 1, 2, 4, 2, 2, 5]
def baseStart_4700488 : Nat := 118140960795 + 4700488 * 2 ^ 59
def prefixEnd_4700488 : Nat := 4983230072969 + 3 ^ 40 * 4700488 * 2
def baseEnd_4700488 : Nat := 804536551563703517594285

theorem tailTrace_4700488 : CollatzResearch.WordTrace tailWord_4700488 prefixEnd_4700488 804536551563703517594285 := by
  unfold tailWord_4700488
  simp only [CollatzResearch.WordTrace]
  refine ⟨85720440897471115141487059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114293921196628153521982745 85720440897471115141487059)
  ·
    refine ⟨128580661346206672712230589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85720440897471115141487059 128580661346206672712230589)
    ·
      refine ⟨48217748004827502267086471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 128580661346206672712230589 48217748004827502267086471)
      ·
        refine ⟨72326622007241253400629707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48217748004827502267086471 72326622007241253400629707)
        ·
          refine ⟨108489933010861880100944561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72326622007241253400629707 108489933010861880100944561)
          ·
            refine ⟨81367449758146410075708421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 108489933010861880100944561 81367449758146410075708421)
            ·
              refine ⟨15256396829652451889195329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 81367449758146410075708421 15256396829652451889195329)
              ·
                refine ⟨11442297622239338916896497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15256396829652451889195329 11442297622239338916896497)
                ·
                  refine ⟨8581723216679504187672373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11442297622239338916896497 8581723216679504187672373)
                  ·
                    refine ⟨804536551563703517594285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8581723216679504187672373 804536551563703517594285)
                    ·
                      rfl

theorem cell23_4700488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 2, 2, 5].length) (baseStart_4700488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4700488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4700488 prefixEnd_4700488 := by exact prefixLift 4700488
  have htrace : WordTrace (prefixWord ++ tailWord_4700488) baseStart_4700488 baseEnd_4700488 := by
    simpa [prefixWord, tailWord_4700488, baseEnd_4700488] using wordTrace_append hprefix tailTrace_4700488
  have hstable : (prefixWord ++ tailWord_4700488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4700488).length < 2 ^ (prefixWord ++ tailWord_4700488).sum := by decide
  have hdescent : baseEnd_4700488 < baseStart_4700488 := by decide
  rcases family_descends (prefixWord ++ tailWord_4700488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4700498 : List Nat := [3, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5]
def baseStart_4700498 : Nat := 118140960795 + 4700498 * 2 ^ 59
def prefixEnd_4700498 : Nat := 4983230072969 + 3 ^ 40 * 4700498 * 2
def baseEnd_4700498 : Nat := 2413614789497655513657809

theorem tailTrace_4700498 : CollatzResearch.WordTrace tailWord_4700498 prefixEnd_4700498 2413614789497655513657809 := by
  unfold tailWord_4700498
  simp only [CollatzResearch.WordTrace]
  refine ⟨42860311631226500497709537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114294164349937334660558765 42860311631226500497709537)
  ·
    refine ⟨32145233723419875373282153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42860311631226500497709537 32145233723419875373282153)
    ·
      refine ⟨24108925292564906529961615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32145233723419875373282153 24108925292564906529961615)
      ·
        refine ⟨36163387938847359794942423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24108925292564906529961615 36163387938847359794942423)
        ·
          refine ⟨54245081908271039692413635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36163387938847359794942423 54245081908271039692413635)
          ·
            refine ⟨81367622862406559538620453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54245081908271039692413635 81367622862406559538620453)
            ·
              refine ⟨15256429286701229913491335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 81367622862406559538620453 15256429286701229913491335)
              ·
                refine ⟨22884643930051844870237003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15256429286701229913491335 22884643930051844870237003)
                ·
                  refine ⟨34326965895077767305355505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22884643930051844870237003 34326965895077767305355505)
                  ·
                    refine ⟨25745224421308325479016629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34326965895077767305355505 25745224421308325479016629)
                    ·
                      refine ⟨2413614789497655513657809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25745224421308325479016629 2413614789497655513657809)
                      ·
                        rfl

theorem cell23_4700498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5].length) (baseStart_4700498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4700498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4700498 prefixEnd_4700498 := by exact prefixLift 4700498
  have htrace : WordTrace (prefixWord ++ tailWord_4700498) baseStart_4700498 baseEnd_4700498 := by
    simpa [prefixWord, tailWord_4700498, baseEnd_4700498] using wordTrace_append hprefix tailTrace_4700498
  have hstable : (prefixWord ++ tailWord_4700498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4700498).length < 2 ^ (prefixWord ++ tailWord_4700498).sum := by decide
  have hdescent : baseEnd_4700498 < baseStart_4700498 := by decide
  rcases family_descends (prefixWord ++ tailWord_4700498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4700522 : List Nat := [3, 1, 3, 3, 1, 3, 1, 1, 2, 5]
def baseStart_4700522 : Nat := 118140960795 + 4700522 * 2 ^ 59
def prefixEnd_4700522 : Nat := 4983230072969 + 3 ^ 40 * 4700522 * 2
def baseEnd_4700522 : Nat := 804542371011121139919233

theorem tailTrace_4700522 : CollatzResearch.WordTrace tailWord_4700522 prefixEnd_4700522 804542371011121139919233 := by
  unfold tailWord_4700522
  simp only [CollatzResearch.WordTrace]
  refine ⟨42860530469204763522427955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114294747917879369393141213 42860530469204763522427955)
  ·
    refine ⟨64290795703807145283641933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42860530469204763522427955 64290795703807145283641933)
    ·
      refine ⟨24109048388927679481365725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64290795703807145283641933 24109048388927679481365725)
      ·
        refine ⟨9040893145847879805512147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24109048388927679481365725 9040893145847879805512147)
        ·
          refine ⟨13561339718771819708268221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9040893145847879805512147 13561339718771819708268221)
          ·
            refine ⟨5085502394539432390600583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13561339718771819708268221 5085502394539432390600583)
            ·
              refine ⟨7628253591809148585900875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5085502394539432390600583 7628253591809148585900875)
              ·
                refine ⟨11442380387713722878851313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7628253591809148585900875 11442380387713722878851313)
                ·
                  refine ⟨8581785290785292159138485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11442380387713722878851313 8581785290785292159138485)
                  ·
                    refine ⟨804542371011121139919233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8581785290785292159138485 804542371011121139919233)
                    ·
                      rfl

theorem cell23_4700522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 1, 1, 2, 5].length) (baseStart_4700522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4700522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4700522 prefixEnd_4700522 := by exact prefixLift 4700522
  have htrace : WordTrace (prefixWord ++ tailWord_4700522) baseStart_4700522 baseEnd_4700522 := by
    simpa [prefixWord, tailWord_4700522, baseEnd_4700522] using wordTrace_append hprefix tailTrace_4700522
  have hstable : (prefixWord ++ tailWord_4700522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4700522).length < 2 ^ (prefixWord ++ tailWord_4700522).sum := by decide
  have hdescent : baseEnd_4700522 < baseStart_4700522 := by decide
  rcases family_descends (prefixWord ++ tailWord_4700522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4700525 : List Nat := [1, 5, 1, 1, 1, 2, 1, 2, 1, 6, 2]
def baseStart_4700525 : Nat := 118140960795 + 4700525 * 2 ^ 59
def prefixEnd_4700525 : Nat := 4983230072969 + 3 ^ 40 * 4700525 * 2
def baseEnd_4700525 : Nat := 2413628653475326908020185

theorem tailTrace_4700525 : CollatzResearch.WordTrace tailWord_4700525 prefixEnd_4700525 2413628653475326908020185 := by
  unfold tailWord_4700525
  simp only [CollatzResearch.WordTrace]
  refine ⟨171442231295808185602071029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114294820863872123734714019 171442231295808185602071029)
  ·
    refine ⟨16072709183982017400194159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 171442231295808185602071029 16072709183982017400194159)
    ·
      refine ⟨24109063775973026100291239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16072709183982017400194159 24109063775973026100291239)
      ·
        refine ⟨36163595663959539150436859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24109063775973026100291239 36163595663959539150436859)
        ·
          refine ⟨54245393495939308725655289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36163595663959539150436859 54245393495939308725655289)
          ·
            refine ⟨40684045121954481544241467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54245393495939308725655289 40684045121954481544241467)
            ·
              refine ⟨61026067682931722316362201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40684045121954481544241467 61026067682931722316362201)
              ·
                refine ⟨45769550762198791737271651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61026067682931722316362201 45769550762198791737271651)
                ·
                  refine ⟨68654326143298187605907477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45769550762198791737271651 68654326143298187605907477)
                  ·
                    refine ⟨3218171537967102544026913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 68654326143298187605907477 3218171537967102544026913)
                    ·
                      refine ⟨2413628653475326908020185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3218171537967102544026913 2413628653475326908020185)
                      ·
                        rfl

theorem cell23_4700525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 2, 1, 6, 2].length) (baseStart_4700525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4700525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4700525 prefixEnd_4700525 := by exact prefixLift 4700525
  have htrace : WordTrace (prefixWord ++ tailWord_4700525) baseStart_4700525 baseEnd_4700525 := by
    simpa [prefixWord, tailWord_4700525, baseEnd_4700525] using wordTrace_append hprefix tailTrace_4700525
  have hstable : (prefixWord ++ tailWord_4700525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4700525).length < 2 ^ (prefixWord ++ tailWord_4700525).sum := by decide
  have hdescent : baseEnd_4700525 < baseStart_4700525 := by decide
  rcases family_descends (prefixWord ++ tailWord_4700525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4700531 : List Nat := [1, 1, 1, 2, 2, 1, 2, 3, 10]
def baseStart_4700531 : Nat := 118140960795 + 4700531 * 2 ^ 59
def prefixEnd_4700531 : Nat := 4983230072969 + 3 ^ 40 * 4700531 * 2
def baseEnd_4700531 : Nat := 268181303817694876060573

theorem tailTrace_4700531 : CollatzResearch.WordTrace tailWord_4700531 prefixEnd_4700531 268181303817694876060573 := by
  unfold tailWord_4700531
  simp only [CollatzResearch.WordTrace]
  refine ⟨171442450133786448626789447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114294966755857632417859631 171442450133786448626789447)
  ·
    refine ⟨257163675200679672940184171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171442450133786448626789447 257163675200679672940184171)
    ·
      refine ⟨385745512801019509410276257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 257163675200679672940184171 385745512801019509410276257)
      ·
        refine ⟨289309134600764632057707193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 385745512801019509410276257 289309134600764632057707193)
        ·
          refine ⟨216981850950573474043280395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 289309134600764632057707193 216981850950573474043280395)
          ·
            refine ⟨325472776425860211064920593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 216981850950573474043280395 325472776425860211064920593)
            ·
              refine ⟨244104582319395158298690445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 325472776425860211064920593 244104582319395158298690445)
              ·
                refine ⟨91539218369773184362008917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 244104582319395158298690445 91539218369773184362008917)
                ·
                  refine ⟨268181303817694876060573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 91539218369773184362008917 268181303817694876060573)
                  ·
                    rfl

theorem cell23_4700531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 3, 10].length) (baseStart_4700531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4700531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4700531 prefixEnd_4700531 := by exact prefixLift 4700531
  have htrace : WordTrace (prefixWord ++ tailWord_4700531) baseStart_4700531 baseEnd_4700531 := by
    simpa [prefixWord, tailWord_4700531, baseEnd_4700531] using wordTrace_append hprefix tailTrace_4700531
  have hstable : (prefixWord ++ tailWord_4700531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4700531).length < 2 ^ (prefixWord ++ tailWord_4700531).sum := by decide
  have hdescent : baseEnd_4700531 < baseStart_4700531 := by decide
  rcases family_descends (prefixWord ++ tailWord_4700531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4700548 : List Nat := [2, 3, 2, 1, 1, 2, 3, 1, 8]
def baseStart_4700548 : Nat := 118140960795 + 4700548 * 2 ^ 59
def prefixEnd_4700548 : Nat := 4983230072969 + 3 ^ 40 * 4700548 * 2
def baseEnd_4700548 : Nat := 268182273725597813114731

theorem tailTrace_4700548 : CollatzResearch.WordTrace tailWord_4700548 prefixEnd_4700548 268182273725597813114731 := by
  unfold tailWord_4700548
  simp only [CollatzResearch.WordTrace]
  refine ⟨85721535087362430265079149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114295380116483240353438865 85721535087362430265079149)
  ·
    refine ⟨32145575657760911349404681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85721535087362430265079149 32145575657760911349404681)
    ·
      refine ⟨24109181743320683512053511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32145575657760911349404681 24109181743320683512053511)
      ·
        refine ⟨36163772614981025268080267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24109181743320683512053511 36163772614981025268080267)
        ·
          refine ⟨54245658922471537902120401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36163772614981025268080267 54245658922471537902120401)
          ·
            refine ⟨40684244191853653426590301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54245658922471537902120401 40684244191853653426590301)
            ·
              refine ⟨15256591571945120034971363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40684244191853653426590301 15256591571945120034971363)
              ·
                refine ⟨22884887357917680052457045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15256591571945120034971363 22884887357917680052457045)
                ·
                  refine ⟨268182273725597813114731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22884887357917680052457045 268182273725597813114731)
                  ·
                    rfl

theorem cell23_4700548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 1, 8].length) (baseStart_4700548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4700548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4700548 prefixEnd_4700548 := by exact prefixLift 4700548
  have htrace : WordTrace (prefixWord ++ tailWord_4700548) baseStart_4700548 baseEnd_4700548 := by
    simpa [prefixWord, tailWord_4700548, baseEnd_4700548] using wordTrace_append hprefix tailTrace_4700548
  have hstable : (prefixWord ++ tailWord_4700548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4700548).length < 2 ^ (prefixWord ++ tailWord_4700548).sum := by decide
  have hdescent : baseEnd_4700548 < baseStart_4700548 := by decide
  rcases family_descends (prefixWord ++ tailWord_4700548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4700552 : List Nat := [2, 1, 3, 3, 1, 1, 1, 6, 1, 4]
def baseStart_4700552 : Nat := 118140960795 + 4700552 * 2 ^ 59
def prefixEnd_4700552 : Nat := 4983230072969 + 3 ^ 40 * 4700552 * 2
def baseEnd_4700552 : Nat := 804547505817666100794187

theorem tailTrace_4700552 : CollatzResearch.WordTrace tailWord_4700552 prefixEnd_4700552 804547505817666100794187 := by
  unfold tailWord_4700552
  simp only [CollatzResearch.WordTrace]
  refine ⟨85721608033355184606651955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114295477377806912808869273 85721608033355184606651955)
  ·
    refine ⟨128582412050032776909977933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85721608033355184606651955 128582412050032776909977933)
    ·
      refine ⟨48218404518762291341241725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 128582412050032776909977933 48218404518762291341241725)
      ·
        refine ⟨18081901694535859252965647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48218404518762291341241725 18081901694535859252965647)
        ·
          refine ⟨27122852541803788879448471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18081901694535859252965647 27122852541803788879448471)
          ·
            refine ⟨40684278812705683319172707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27122852541803788879448471 40684278812705683319172707)
            ·
              refine ⟨61026418219058524978759061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40684278812705683319172707 61026418219058524978759061)
              ·
                refine ⟨2860613354018368358379331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 61026418219058524978759061 2860613354018368358379331)
                ·
                  refine ⟨4290920031027552537568997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2860613354018368358379331 4290920031027552537568997)
                  ·
                    refine ⟨804547505817666100794187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4290920031027552537568997 804547505817666100794187)
                    ·
                      rfl

theorem cell23_4700552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 6, 1, 4].length) (baseStart_4700552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4700552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4700552 prefixEnd_4700552 := by exact prefixLift 4700552
  have htrace : WordTrace (prefixWord ++ tailWord_4700552) baseStart_4700552 baseEnd_4700552 := by
    simpa [prefixWord, tailWord_4700552, baseEnd_4700552] using wordTrace_append hprefix tailTrace_4700552
  have hstable : (prefixWord ++ tailWord_4700552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4700552).length < 2 ^ (prefixWord ++ tailWord_4700552).sum := by decide
  have hdescent : baseEnd_4700552 < baseStart_4700552 := by decide
  rcases family_descends (prefixWord ++ tailWord_4700552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4700585 : List Nat := [1, 2, 1, 1, 1, 1, 3, 2, 6, 3, 2]
def baseStart_4700585 : Nat := 118140960795 + 4700585 * 2 ^ 59
def prefixEnd_4700585 : Nat := 4983230072969 + 3 ^ 40 * 4700585 * 2
def baseEnd_4700585 : Nat := 2413659462314596673269909

theorem tailTrace_4700585 : CollatzResearch.WordTrace tailWord_4700585 prefixEnd_4700585 2413659462314596673269909 := by
  unfold tailWord_4700585
  simp only [CollatzResearch.WordTrace]
  refine ⟨171444419675590815849255209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114296279783727210566170139 171444419675590815849255209)
  ·
    refine ⟨128583314756693111886941407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171444419675590815849255209 128583314756693111886941407)
    ·
      refine ⟨192874972135039667830412111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128583314756693111886941407 192874972135039667830412111)
      ·
        refine ⟨289312458202559501745618167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192874972135039667830412111 289312458202559501745618167)
        ·
          refine ⟨433968687303839252618427251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 289312458202559501745618167 433968687303839252618427251)
          ·
            refine ⟨650953030955758878927640877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 433968687303839252618427251 650953030955758878927640877)
            ·
              refine ⟨244107386608409579597865329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 650953030955758878927640877 244107386608409579597865329)
              ·
                refine ⟨183080539956307184698398997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 244107386608409579597865329 183080539956307184698398997)
                ·
                  refine ⟨8581900310451899282737453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 183080539956307184698398997 8581900310451899282737453)
                  ·
                    refine ⟨3218212616419462231026545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8581900310451899282737453 3218212616419462231026545)
                    ·
                      refine ⟨2413659462314596673269909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3218212616419462231026545 2413659462314596673269909)
                      ·
                        rfl

theorem cell23_4700585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 2, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 2, 6, 3, 2].length) (baseStart_4700585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4700585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4700585 prefixEnd_4700585 := by exact prefixLift 4700585
  have htrace : WordTrace (prefixWord ++ tailWord_4700585) baseStart_4700585 baseEnd_4700585 := by
    simpa [prefixWord, tailWord_4700585, baseEnd_4700585] using wordTrace_append hprefix tailTrace_4700585
  have hstable : (prefixWord ++ tailWord_4700585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4700585).length < 2 ^ (prefixWord ++ tailWord_4700585).sum := by decide
  have hdescent : baseEnd_4700585 < baseStart_4700585 := by decide
  rcases family_descends (prefixWord ++ tailWord_4700585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4700596 : List Nat := [2, 5, 2, 2, 1, 1, 1, 2, 2, 2, 3]
def baseStart_4700596 : Nat := 118140960795 + 4700596 * 2 ^ 59
def prefixEnd_4700596 : Nat := 4983230072969 + 3 ^ 40 * 4700596 * 2
def baseEnd_4700596 : Nat := 2413665110601796130232359

theorem tailTrace_4700596 : CollatzResearch.WordTrace tailWord_4700596 prefixEnd_4700596 2413665110601796130232359 := by
  unfold tailWord_4700596
  simp only [CollatzResearch.WordTrace]
  refine ⟨85722410439275482363952821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114296547252367309818603761 85722410439275482363952821)
  ·
    refine ⟨8036475978682076471620577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 85722410439275482363952821 8036475978682076471620577)
    ·
      refine ⟨6027356984011557353715433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8036475978682076471620577 6027356984011557353715433)
      ·
        refine ⟨4520517738008668015286575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6027356984011557353715433 4520517738008668015286575)
        ·
          refine ⟨6780776607013002022929863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4520517738008668015286575 6780776607013002022929863)
          ·
            refine ⟨10171164910519503034394795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6780776607013002022929863 10171164910519503034394795)
            ·
              refine ⟨15256747365779254551592193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10171164910519503034394795 15256747365779254551592193)
              ·
                refine ⟨11442560524334440913694145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15256747365779254551592193 11442560524334440913694145)
                ·
                  refine ⟨8581920393250830685270609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11442560524334440913694145 8581920393250830685270609)
                  ·
                    refine ⟨6436440294938123013952957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8581920393250830685270609 6436440294938123013952957)
                    ·
                      refine ⟨2413665110601796130232359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6436440294938123013952957 2413665110601796130232359)
                      ·
                        rfl

theorem cell23_4700596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_4700596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4700596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4700596 prefixEnd_4700596 := by exact prefixLift 4700596
  have htrace : WordTrace (prefixWord ++ tailWord_4700596) baseStart_4700596 baseEnd_4700596 := by
    simpa [prefixWord, tailWord_4700596, baseEnd_4700596] using wordTrace_append hprefix tailTrace_4700596
  have hstable : (prefixWord ++ tailWord_4700596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4700596).length < 2 ^ (prefixWord ++ tailWord_4700596).sum := by decide
  have hdescent : baseEnd_4700596 < baseStart_4700596 := by decide
  rcases family_descends (prefixWord ++ tailWord_4700596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4700632 : List Nat := [2, 1, 2, 2, 2, 1, 1, 3, 5, 2, 2]
def baseStart_4700632 : Nat := 118140960795 + 4700632 * 2 ^ 59
def prefixEnd_4700632 : Nat := 4983230072969 + 3 ^ 40 * 4700632 * 2
def baseEnd_4700632 : Nat := 2413683595905357989382193

theorem tailTrace_4700632 : CollatzResearch.WordTrace tailWord_4700632 prefixEnd_4700632 2413683595905357989382193 := by
  unfold tailWord_4700632
  simp only [CollatzResearch.WordTrace]
  refine ⟨85723066953210271438108075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114297422604280361917477433 85723066953210271438108075)
  ·
    refine ⟨128584600429815407157162113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85723066953210271438108075 128584600429815407157162113)
    ·
      refine ⟨96438450322361555367871585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128584600429815407157162113 96438450322361555367871585)
      ·
        refine ⟨72328837741771166525903689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96438450322361555367871585 72328837741771166525903689)
        ·
          refine ⟨54246628306328374894427767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72328837741771166525903689 54246628306328374894427767)
          ·
            refine ⟨81369942459492562341641651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54246628306328374894427767 81369942459492562341641651)
            ·
              refine ⟨122054913689238843512462477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81369942459492562341641651 122054913689238843512462477)
              ·
                refine ⟨45770592633464566317173429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 122054913689238843512462477 45770592633464566317173429)
                ·
                  refine ⟨4290993059387303092235009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 45770592633464566317173429 4290993059387303092235009)
                  ·
                    refine ⟨3218244794540477319176257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4290993059387303092235009 3218244794540477319176257)
                    ·
                      refine ⟨2413683595905357989382193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3218244794540477319176257 2413683595905357989382193)
                      ·
                        rfl

theorem cell23_4700632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 3, 5, 2, 2].length) (baseStart_4700632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4700632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4700632 prefixEnd_4700632 := by exact prefixLift 4700632
  have htrace : WordTrace (prefixWord ++ tailWord_4700632) baseStart_4700632 baseEnd_4700632 := by
    simpa [prefixWord, tailWord_4700632, baseEnd_4700632] using wordTrace_append hprefix tailTrace_4700632
  have hstable : (prefixWord ++ tailWord_4700632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4700632).length < 2 ^ (prefixWord ++ tailWord_4700632).sum := by decide
  have hdescent : baseEnd_4700632 < baseStart_4700632 := by decide
  rcases family_descends (prefixWord ++ tailWord_4700632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4700682 : List Nat := [3, 1, 2, 2, 2, 1, 4, 1, 1, 3, 3]
def baseStart_4700682 : Nat := 118140960795 + 4700682 * 2 ^ 59
def prefixEnd_4700682 : Nat := 4983230072969 + 3 ^ 40 * 4700682 * 2
def baseEnd_4700682 : Nat := 2413709269938082793756963

theorem tailTrace_4700682 : CollatzResearch.WordTrace tailWord_4700682 prefixEnd_4700682 2413709269938082793756963 := by
  unfold tailWord_4700682
  simp only [CollatzResearch.WordTrace]
  refine ⟨42861989389059850353884075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114298638370826267610357533 42861989389059850353884075)
  ·
    refine ⟨64292984083589775530826113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42861989389059850353884075 64292984083589775530826113)
    ·
      refine ⟨48219738062692331648119585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64292984083589775530826113 48219738062692331648119585)
      ·
        refine ⟨36164803547019248736089689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48219738062692331648119585 36164803547019248736089689)
        ·
          refine ⟨27123602660264436552067267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36164803547019248736089689 27123602660264436552067267)
          ·
            refine ⟨40685403990396654828100901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27123602660264436552067267 40685403990396654828100901)
            ·
              refine ⟨7628513248199372780268919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40685403990396654828100901 7628513248199372780268919)
              ·
                refine ⟨11442769872299059170403379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7628513248199372780268919 11442769872299059170403379)
                ·
                  refine ⟨17164154808448588755605069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11442769872299059170403379 17164154808448588755605069)
                  ·
                    refine ⟨6436558053168220783351901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17164154808448588755605069 6436558053168220783351901)
                    ·
                      refine ⟨2413709269938082793756963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6436558053168220783351901 2413709269938082793756963)
                      ·
                        rfl

theorem cell23_4700682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 4, 1, 1, 3, 3].length) (baseStart_4700682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4700682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4700682 prefixEnd_4700682 := by exact prefixLift 4700682
  have htrace : WordTrace (prefixWord ++ tailWord_4700682) baseStart_4700682 baseEnd_4700682 := by
    simpa [prefixWord, tailWord_4700682, baseEnd_4700682] using wordTrace_append hprefix tailTrace_4700682
  have hstable : (prefixWord ++ tailWord_4700682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4700682).length < 2 ^ (prefixWord ++ tailWord_4700682).sum := by decide
  have hdescent : baseEnd_4700682 < baseStart_4700682 := by decide
  rcases family_descends (prefixWord ++ tailWord_4700682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4700722 : List Nat := [3, 2, 1, 1, 2, 1, 2, 2, 3, 4, 2]
def baseStart_4700722 : Nat := 118140960795 + 4700722 * 2 ^ 59
def prefixEnd_4700722 : Nat := 4983230072969 + 3 ^ 40 * 4700722 * 2
def baseEnd_4700722 : Nat := 2413729809164262637256779

theorem tailTrace_4700722 : CollatzResearch.WordTrace tailWord_4700722 prefixEnd_4700722 2413729809164262637256779 := by
  unfold tailWord_4700722
  simp only [CollatzResearch.WordTrace]
  refine ⟨42862354119023622061748105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114299610984062992164661613 42862354119023622061748105)
  ·
    refine ⟨32146765589267716546311079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42862354119023622061748105 32146765589267716546311079)
    ·
      refine ⟨48220148383901574819466619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32146765589267716546311079 48220148383901574819466619)
      ·
        refine ⟨72330222575852362229199929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48220148383901574819466619 72330222575852362229199929)
        ·
          refine ⟨54247666931889271671899947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72330222575852362229199929 54247666931889271671899947)
          ·
            refine ⟨81371500397833907507849921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54247666931889271671899947 81371500397833907507849921)
            ·
              refine ⟨61028625298375430630887441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81371500397833907507849921 61028625298375430630887441)
              ·
                refine ⟨45771468973781572973165581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61028625298375430630887441 45771468973781572973165581)
                ·
                  refine ⟨17164300865168089864937093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45771468973781572973165581 17164300865168089864937093)
                  ·
                    refine ⟨3218306412219016849675705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17164300865168089864937093 3218306412219016849675705)
                    ·
                      refine ⟨2413729809164262637256779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3218306412219016849675705 2413729809164262637256779)
                      ·
                        rfl

theorem cell23_4700722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 2, 3, 4, 2].length) (baseStart_4700722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4700722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4700722 prefixEnd_4700722 := by exact prefixLift 4700722
  have htrace : WordTrace (prefixWord ++ tailWord_4700722) baseStart_4700722 baseEnd_4700722 := by
    simpa [prefixWord, tailWord_4700722, baseEnd_4700722] using wordTrace_append hprefix tailTrace_4700722
  have hstable : (prefixWord ++ tailWord_4700722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4700722).length < 2 ^ (prefixWord ++ tailWord_4700722).sum := by decide
  have hdescent : baseEnd_4700722 < baseStart_4700722 := by decide
  rcases family_descends (prefixWord ++ tailWord_4700722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4700735 : List Nat := [1, 1, 2, 2, 3, 2, 1, 3, 2, 2, 4]
def baseStart_4700735 : Nat := 118140960795 + 4700735 * 2 ^ 59
def prefixEnd_4700735 : Nat := 4983230072969 + 3 ^ 40 * 4700735 * 2
def baseEnd_4700735 : Nat := 2413736484412771086394219

theorem tailTrace_4700735 : CollatzResearch.WordTrace tailWord_4700735 prefixEnd_4700735 2413736484412771086394219 := by
  unfold tailWord_4700735
  simp only [CollatzResearch.WordTrace]
  refine ⟨171449890625047391467215659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114299927083364927644810439 171449890625047391467215659)
  ·
    refine ⟨257174835937571087200823489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171449890625047391467215659 257174835937571087200823489)
    ·
      refine ⟨192881126953178315400617617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 257174835937571087200823489 192881126953178315400617617)
      ·
        refine ⟨144660845214883736550463213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 192881126953178315400617617 144660845214883736550463213)
        ·
          refine ⟨54247816955581401206423705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 144660845214883736550463213 54247816955581401206423705)
          ·
            refine ⟨40685862716686050904817779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54247816955581401206423705 40685862716686050904817779)
            ·
              refine ⟨61028794075029076357226669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40685862716686050904817779 61028794075029076357226669)
              ·
                refine ⟨22885797778135903633960001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61028794075029076357226669 22885797778135903633960001)
                ·
                  refine ⟨17164348333601927725470001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22885797778135903633960001 17164348333601927725470001)
                  ·
                    refine ⟨12873261250201445794102501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17164348333601927725470001 12873261250201445794102501)
                    ·
                      refine ⟨2413736484412771086394219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12873261250201445794102501 2413736484412771086394219)
                      ·
                        rfl

theorem cell23_4700735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 3, 2, 2, 4].length) (baseStart_4700735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4700735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4700735 prefixEnd_4700735 := by exact prefixLift 4700735
  have htrace : WordTrace (prefixWord ++ tailWord_4700735) baseStart_4700735 baseEnd_4700735 := by
    simpa [prefixWord, tailWord_4700735, baseEnd_4700735] using wordTrace_append hprefix tailTrace_4700735
  have hstable : (prefixWord ++ tailWord_4700735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4700735).length < 2 ^ (prefixWord ++ tailWord_4700735).sum := by decide
  have hdescent : baseEnd_4700735 < baseStart_4700735 := by decide
  rcases family_descends (prefixWord ++ tailWord_4700735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4700739 : List Nat := [1, 1, 1, 3, 1, 2, 1, 7, 2, 2, 2]
def baseStart_4700739 : Nat := 118140960795 + 4700739 * 2 ^ 59
def prefixEnd_4700739 : Nat := 4983230072969 + 3 ^ 40 * 4700739 * 2
def baseEnd_4700739 : Nat := 2413738538335389070744201

theorem tailTrace_4700739 : CollatzResearch.WordTrace tailWord_4700739 prefixEnd_4700739 2413738538335389070744201 := by
  unfold tailWord_4700739
  simp only [CollatzResearch.WordTrace]
  refine ⟨171450036517032900150361271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114300024344688600100240847 171450036517032900150361271)
  ·
    refine ⟨257175054775549350225541907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171450036517032900150361271 257175054775549350225541907)
    ·
      refine ⟨385762582163324025338312861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 257175054775549350225541907 385762582163324025338312861)
      ·
        refine ⟨144660968311246509501867323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 385762582163324025338312861 144660968311246509501867323)
        ·
          refine ⟨216991452466869764252800985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144660968311246509501867323 216991452466869764252800985)
          ·
            refine ⟨162743589350152323189600739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 216991452466869764252800985 162743589350152323189600739)
            ·
              refine ⟨244115384025228484784401109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 162743589350152323189600739 244115384025228484784401109)
              ·
                refine ⟨5721454313091292612134401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 244115384025228484784401109 5721454313091292612134401)
                ·
                  refine ⟨4291090734818469459100801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5721454313091292612134401 4291090734818469459100801)
                  ·
                    refine ⟨3218318051113852094325601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4291090734818469459100801 3218318051113852094325601)
                    ·
                      refine ⟨2413738538335389070744201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3218318051113852094325601 2413738538335389070744201)
                      ·
                        rfl

theorem cell23_4700739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 7, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 7, 2, 2, 2].length) (baseStart_4700739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4700739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4700739 prefixEnd_4700739 := by exact prefixLift 4700739
  have htrace : WordTrace (prefixWord ++ tailWord_4700739) baseStart_4700739 baseEnd_4700739 := by
    simpa [prefixWord, tailWord_4700739, baseEnd_4700739] using wordTrace_append hprefix tailTrace_4700739
  have hstable : (prefixWord ++ tailWord_4700739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4700739).length < 2 ^ (prefixWord ++ tailWord_4700739).sum := by decide
  have hdescent : baseEnd_4700739 < baseStart_4700739 := by decide
  rcases family_descends (prefixWord ++ tailWord_4700739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4700795 : List Nat := [1, 1, 1, 1, 1, 4, 2, 4, 1, 3, 4]
def baseStart_4700795 : Nat := 118140960795 + 4700795 * 2 ^ 59
def prefixEnd_4700795 : Nat := 4983230072969 + 3 ^ 40 * 4700795 * 2
def baseEnd_4700795 : Nat := 2413767293252040851643943

theorem tailTrace_4700795 : CollatzResearch.WordTrace tailWord_4700795 prefixEnd_4700795 2413767293252040851643943 := by
  unfold tailWord_4700795
  simp only [CollatzResearch.WordTrace]
  refine ⟨171452079004830021714399839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114301386003220014476266559 171452079004830021714399839)
  ·
    refine ⟨257178118507245032571599759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171452079004830021714399839 257178118507245032571599759)
    ·
      refine ⟨385767177760867548857399639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 257178118507245032571599759 385767177760867548857399639)
      ·
        refine ⟨578650766641301323286099459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 385767177760867548857399639 578650766641301323286099459)
        ·
          refine ⟨867976149961951984929149189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 578650766641301323286099459 867976149961951984929149189)
          ·
            refine ⟨162745528117865997174215473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 867976149961951984929149189 162745528117865997174215473)
            ·
              refine ⟨122059146088399497880661605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 162745528117865997174215473 122059146088399497880661605)
              ·
                refine ⟨22886089891574905852624051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 122059146088399497880661605 22886089891574905852624051)
                ·
                  refine ⟨34329134837362358778936077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22886089891574905852624051 34329134837362358778936077)
                  ·
                    refine ⟨12873425564010884542101029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34329134837362358778936077 12873425564010884542101029)
                    ·
                      refine ⟨2413767293252040851643943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12873425564010884542101029 2413767293252040851643943)
                      ·
                        rfl

theorem cell23_4700795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 4, 1, 3, 4].length) (baseStart_4700795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4700795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4700795 prefixEnd_4700795 := by exact prefixLift 4700795
  have htrace : WordTrace (prefixWord ++ tailWord_4700795) baseStart_4700795 baseEnd_4700795 := by
    simpa [prefixWord, tailWord_4700795, baseEnd_4700795] using wordTrace_append hprefix tailTrace_4700795
  have hstable : (prefixWord ++ tailWord_4700795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4700795).length < 2 ^ (prefixWord ++ tailWord_4700795).sum := by decide
  have hdescent : baseEnd_4700795 < baseStart_4700795 := by decide
  rcases family_descends (prefixWord ++ tailWord_4700795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4700812 : List Nat := [2, 2, 1, 2, 1, 1, 2, 1, 3, 6, 2]
def baseStart_4700812 : Nat := 118140960795 + 4700812 * 2 ^ 59
def prefixEnd_4700812 : Nat := 4983230072969 + 3 ^ 40 * 4700812 * 2
def baseEnd_4700812 : Nat := 2413776022423167285131365

theorem tailTrace_4700812 : CollatzResearch.WordTrace tailWord_4700812 prefixEnd_4700812 2413776022423167285131365 := by
  unfold tailWord_4700812
  simp only [CollatzResearch.WordTrace]
  refine ⟨85726349522884216808884345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114301799363845622411845793 85726349522884216808884345)
  ·
    refine ⟨64294762142163162606663259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85726349522884216808884345 64294762142163162606663259)
    ·
      refine ⟨96442143213244743909994889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64294762142163162606663259 96442143213244743909994889)
      ·
        refine ⟨72331607409933557932496167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96442143213244743909994889 72331607409933557932496167)
        ·
          refine ⟨108497411114900336898744251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72331607409933557932496167 108497411114900336898744251)
          ·
            refine ⟨162746116672350505348116377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108497411114900336898744251 162746116672350505348116377)
            ·
              refine ⟨122059587504262879011087283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 162746116672350505348116377 122059587504262879011087283)
              ·
                refine ⟨183089381256394318516630925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 122059587504262879011087283 183089381256394318516630925)
                ·
                  refine ⟨68658517971147869443736597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 183089381256394318516630925 68658517971147869443736597)
                  ·
                    refine ⟨3218368029897556380175153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 68658517971147869443736597 3218368029897556380175153)
                    ·
                      refine ⟨2413776022423167285131365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3218368029897556380175153 2413776022423167285131365)
                      ·
                        rfl

theorem cell23_4700812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 3, 6, 2].length) (baseStart_4700812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4700812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4700812 prefixEnd_4700812 := by exact prefixLift 4700812
  have htrace : WordTrace (prefixWord ++ tailWord_4700812) baseStart_4700812 baseEnd_4700812 := by
    simpa [prefixWord, tailWord_4700812, baseEnd_4700812] using wordTrace_append hprefix tailTrace_4700812
  have hstable : (prefixWord ++ tailWord_4700812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4700812).length < 2 ^ (prefixWord ++ tailWord_4700812).sum := by decide
  have hdescent : baseEnd_4700812 < baseStart_4700812 := by decide
  rcases family_descends (prefixWord ++ tailWord_4700812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4700825 : List Nat := [1, 2, 1, 2, 1, 2, 4, 1, 2, 1, 6]
def baseStart_4700825 : Nat := 118140960795 + 4700825 * 2 ^ 59
def prefixEnd_4700825 : Nat := 4983230072969 + 3 ^ 40 * 4700825 * 2
def baseEnd_4700825 : Nat := 2413782697671675734268805

theorem tailTrace_4700825 : CollatzResearch.WordTrace tailWord_4700825 prefixEnd_4700825 2413782697671675734268805 := by
  unfold tailWord_4700825
  simp only [CollatzResearch.WordTrace]
  refine ⟨171453173194721336837991929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114302115463147557891994619 171453173194721336837991929)
  ·
    refine ⟨128589879896041002628493947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171453173194721336837991929 128589879896041002628493947)
    ·
      refine ⟨192884819844061503942740921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128589879896041002628493947 192884819844061503942740921)
      ·
        refine ⟨144663614883046127957055691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 192884819844061503942740921 144663614883046127957055691)
        ·
          refine ⟨216995422324569191935583537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144663614883046127957055691 216995422324569191935583537)
          ·
            refine ⟨162746566743426893951687653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 216995422324569191935583537 162746566743426893951687653)
            ·
              refine ⟨30514981264392542615941435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 162746566743426893951687653 30514981264392542615941435)
              ·
                refine ⟨45772471896588813923912153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30514981264392542615941435 45772471896588813923912153)
                ·
                  refine ⟨34329353922441610442934115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45772471896588813923912153 34329353922441610442934115)
                  ·
                    refine ⟨51494030883662415664401173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34329353922441610442934115 51494030883662415664401173)
                    ·
                      refine ⟨2413782697671675734268805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 51494030883662415664401173 2413782697671675734268805)
                      ·
                        rfl

theorem cell23_4700825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 1, 2, 1, 6].length) (baseStart_4700825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4700825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4700825 prefixEnd_4700825 := by exact prefixLift 4700825
  have htrace : WordTrace (prefixWord ++ tailWord_4700825) baseStart_4700825 baseEnd_4700825 := by
    simpa [prefixWord, tailWord_4700825, baseEnd_4700825] using wordTrace_append hprefix tailTrace_4700825
  have hstable : (prefixWord ++ tailWord_4700825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4700825).length < 2 ^ (prefixWord ++ tailWord_4700825).sum := by decide
  have hdescent : baseEnd_4700825 < baseStart_4700825 := by decide
  rcases family_descends (prefixWord ++ tailWord_4700825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4700846 : List Nat := [4, 1, 4, 1, 1, 1, 1, 1, 1, 6, 2]
def baseStart_4700846 : Nat := 118140960795 + 4700846 * 2 ^ 59
def prefixEnd_4700846 : Nat := 4983230072969 + 3 ^ 40 * 4700846 * 2
def baseEnd_4700846 : Nat := 2413793480765420152106209

theorem tailTrace_4700846 : CollatzResearch.WordTrace tailWord_4700846 prefixEnd_4700846 2413793480765420152106209 := by
  unfold tailWord_4700846
  simp only [CollatzResearch.WordTrace]
  refine ⟨21431742390955657178063299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 114302626085096838283004261 21431742390955657178063299)
  ·
    refine ⟨32147613586433485767094949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21431742390955657178063299 32147613586433485767094949)
    ·
      refine ⟨6027677547456278581330303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32147613586433485767094949 6027677547456278581330303)
      ·
        refine ⟨9041516321184417871995455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6027677547456278581330303 9041516321184417871995455)
        ·
          refine ⟨13562274481776626807993183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9041516321184417871995455 13562274481776626807993183)
          ·
            refine ⟨20343411722664940211989775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13562274481776626807993183 20343411722664940211989775)
            ·
              refine ⟨30515117583997410317984663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20343411722664940211989775 30515117583997410317984663)
              ·
                refine ⟨45772676375996115476976995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30515117583997410317984663 45772676375996115476976995)
                ·
                  refine ⟨68659014563994173215465493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45772676375996115476976995 68659014563994173215465493)
                  ·
                    refine ⟨3218391307687226869474945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 68659014563994173215465493 3218391307687226869474945)
                    ·
                      refine ⟨2413793480765420152106209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3218391307687226869474945 2413793480765420152106209)
                      ·
                        rfl

theorem cell23_4700846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 1, 1, 6, 2].length) (baseStart_4700846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4700846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4700846 prefixEnd_4700846 := by exact prefixLift 4700846
  have htrace : WordTrace (prefixWord ++ tailWord_4700846) baseStart_4700846 baseEnd_4700846 := by
    simpa [prefixWord, tailWord_4700846, baseEnd_4700846] using wordTrace_append hprefix tailTrace_4700846
  have hstable : (prefixWord ++ tailWord_4700846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4700846).length < 2 ^ (prefixWord ++ tailWord_4700846).sum := by decide
  have hdescent : baseEnd_4700846 < baseStart_4700846 := by decide
  rcases family_descends (prefixWord ++ tailWord_4700846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4700875 : List Nat := [1, 1, 1, 1, 3, 2, 1, 1, 1, 6, 5]
def baseStart_4700875 : Nat := 118140960795 + 4700875 * 2 ^ 59
def prefixEnd_4700875 : Nat := 4983230072969 + 3 ^ 40 * 4700875 * 2
def baseEnd_4700875 : Nat := 2413808371704400538643575

theorem tailTrace_4700875 : CollatzResearch.WordTrace tailWord_4700875 prefixEnd_4700875 2413808371704400538643575 := by
  unfold tailWord_4700875
  simp only [CollatzResearch.WordTrace]
  refine ⟨171454996844540195377312079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114303331229693463584874719 171454996844540195377312079)
  ·
    refine ⟨257182495266810293065968119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171454996844540195377312079 257182495266810293065968119)
    ·
      refine ⟨385773742900215439598952179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 257182495266810293065968119 385773742900215439598952179)
      ·
        refine ⟨578660614350323159398428269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 385773742900215439598952179 578660614350323159398428269)
        ·
          refine ⟨216997730381371184774410601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 578660614350323159398428269 216997730381371184774410601)
          ·
            refine ⟨162748297786028388580807951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 216997730381371184774410601 162748297786028388580807951)
            ·
              refine ⟨244122446679042582871211927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 162748297786028388580807951 244122446679042582871211927)
              ·
                refine ⟨366183670018563874306817891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 244122446679042582871211927 366183670018563874306817891)
                ·
                  refine ⟨549275505027845811460226837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 366183670018563874306817891 549275505027845811460226837)
                  ·
                    refine ⟨25747289298180272412198133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 549275505027845811460226837 25747289298180272412198133)
                    ·
                      refine ⟨2413808371704400538643575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25747289298180272412198133 2413808371704400538643575)
                      ·
                        rfl

theorem cell23_4700875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 6, 5].length) (baseStart_4700875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4700875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4700875 prefixEnd_4700875 := by exact prefixLift 4700875
  have htrace : WordTrace (prefixWord ++ tailWord_4700875) baseStart_4700875 baseEnd_4700875 := by
    simpa [prefixWord, tailWord_4700875, baseEnd_4700875] using wordTrace_append hprefix tailTrace_4700875
  have hstable : (prefixWord ++ tailWord_4700875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4700875).length < 2 ^ (prefixWord ++ tailWord_4700875).sum := by decide
  have hdescent : baseEnd_4700875 < baseStart_4700875 := by decide
  rcases family_descends (prefixWord ++ tailWord_4700875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4700889 : List Nat := [1, 2, 1, 2, 3, 2, 2, 1, 4, 3, 2]
def baseStart_4700889 : Nat := 118140960795 + 4700889 * 2 ^ 59
def prefixEnd_4700889 : Nat := 4983230072969 + 3 ^ 40 * 4700889 * 2
def baseEnd_4700889 : Nat := 2413815560433563483868511

theorem tailTrace_4700889 : CollatzResearch.WordTrace tailWord_4700889 prefixEnd_4700889 2413815560433563483868511 := by
  unfold tailWord_4700889
  simp only [CollatzResearch.WordTrace]
  refine ⟨171455507466489475768321721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114303671644326317178881147 171455507466489475768321721)
  ·
    refine ⟨128591630599867106826241291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171455507466489475768321721 128591630599867106826241291)
    ·
      refine ⟨192887445899800660239361937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128591630599867106826241291 192887445899800660239361937)
      ·
        refine ⟨144665584424850495179521453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 192887445899800660239361937 144665584424850495179521453)
        ·
          refine ⟨54249594159318935692320545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 144665584424850495179521453 54249594159318935692320545)
          ·
            refine ⟨40687195619489201769240409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54249594159318935692320545 40687195619489201769240409)
            ·
              refine ⟨30515396714616901326930307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40687195619489201769240409 30515396714616901326930307)
              ·
                refine ⟨45773095071925351990395461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30515396714616901326930307 45773095071925351990395461)
                ·
                  refine ⟨8582455325986003498199149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45773095071925351990395461 8582455325986003498199149)
                  ·
                    refine ⟨3218420747244751311824681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8582455325986003498199149 3218420747244751311824681)
                    ·
                      refine ⟨2413815560433563483868511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3218420747244751311824681 2413815560433563483868511)
                      ·
                        rfl

theorem cell23_4700889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 1, 4, 3, 2].length) (baseStart_4700889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4700889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4700889 prefixEnd_4700889 := by exact prefixLift 4700889
  have htrace : WordTrace (prefixWord ++ tailWord_4700889) baseStart_4700889 baseEnd_4700889 := by
    simpa [prefixWord, tailWord_4700889, baseEnd_4700889] using wordTrace_append hprefix tailTrace_4700889
  have hstable : (prefixWord ++ tailWord_4700889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4700889).length < 2 ^ (prefixWord ++ tailWord_4700889).sum := by decide
  have hdescent : baseEnd_4700889 < baseStart_4700889 := by decide
  rcases family_descends (prefixWord ++ tailWord_4700889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4700930 : List Nat := [3, 4, 1, 1, 1, 2, 3, 3, 1, 1, 3]
def baseStart_4700930 : Nat := 118140960795 + 4700930 * 2 ^ 59
def prefixEnd_4700930 : Nat := 4983230072969 + 3 ^ 40 * 4700930 * 2
def baseEnd_4700930 : Nat := 2413836613140397823455823

theorem tailTrace_4700930 : CollatzResearch.WordTrace tailWord_4700930 prefixEnd_4700930 2413836613140397823455823 := by
  unfold tailWord_4700930
  simp only [CollatzResearch.WordTrace]
  refine ⟨42864250714835234942641061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114304668572893959847042829 42864250714835234942641061)
  ·
    refine ⟨8037047009031606551745199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42864250714835234942641061 8037047009031606551745199)
    ·
      refine ⟨12055570513547409827617799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8037047009031606551745199 12055570513547409827617799)
      ·
        refine ⟨18083355770321114741426699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12055570513547409827617799 18083355770321114741426699)
        ·
          refine ⟨27125033655481672112140049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18083355770321114741426699 27125033655481672112140049)
          ·
            refine ⟨20343775241611254084105037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27125033655481672112140049 20343775241611254084105037)
            ·
              refine ⟨7628915715604220281539389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20343775241611254084105037 7628915715604220281539389)
              ·
                refine ⟨2860843393351582605577271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7628915715604220281539389 2860843393351582605577271)
                ·
                  refine ⟨4291265090027373908365907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2860843393351582605577271 4291265090027373908365907)
                  ·
                    refine ⟨6436897635041060862548861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4291265090027373908365907 6436897635041060862548861)
                    ·
                      refine ⟨2413836613140397823455823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6436897635041060862548861 2413836613140397823455823)
                      ·
                        rfl

theorem cell23_4700930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 3, 3, 1, 1, 3].length) (baseStart_4700930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4700930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4700930 prefixEnd_4700930 := by exact prefixLift 4700930
  have htrace : WordTrace (prefixWord ++ tailWord_4700930) baseStart_4700930 baseEnd_4700930 := by
    simpa [prefixWord, tailWord_4700930, baseEnd_4700930] using wordTrace_append hprefix tailTrace_4700930
  have hstable : (prefixWord ++ tailWord_4700930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4700930).length < 2 ^ (prefixWord ++ tailWord_4700930).sum := by decide
  have hdescent : baseEnd_4700930 < baseStart_4700930 := by decide
  rcases family_descends (prefixWord ++ tailWord_4700930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4700970 : List Nat := [3, 1, 4, 3, 1, 2, 1, 2, 1, 1, 4]
def baseStart_4700970 : Nat := 118140960795 + 4700970 * 2 ^ 59
def prefixEnd_4700970 : Nat := 4983230072969 + 3 ^ 40 * 4700970 * 2
def baseEnd_4700970 : Nat := 2413857152366577666955639

theorem tailTrace_4700970 : CollatzResearch.WordTrace tailWord_4700970 prefixEnd_4700970 2413857152366577666955639 := by
  unfold tailWord_4700970
  simp only [CollatzResearch.WordTrace]
  refine ⟨42864615444799006650505091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114305641186130684401346909 42864615444799006650505091)
  ·
    refine ⟨64296923167198509975757637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42864615444799006650505091 64296923167198509975757637)
    ·
      refine ⟨12055673093849720620454557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64296923167198509975757637 12055673093849720620454557)
      ·
        refine ⟨4520877410193645232670459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12055673093849720620454557 4520877410193645232670459)
        ·
          refine ⟨6781316115290467849005689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4520877410193645232670459 6781316115290467849005689)
          ·
            refine ⟨5085987086467850886754267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6781316115290467849005689 5085987086467850886754267)
            ·
              refine ⟨7628980629701776330131401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5085987086467850886754267 7628980629701776330131401)
              ·
                refine ⟨5721735472276332247598551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7628980629701776330131401 5721735472276332247598551)
                ·
                  refine ⟨8582603208414498371397827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5721735472276332247598551 8582603208414498371397827)
                  ·
                    refine ⟨12873904812621747557096741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8582603208414498371397827 12873904812621747557096741)
                    ·
                      refine ⟨2413857152366577666955639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12873904812621747557096741 2413857152366577666955639)
                      ·
                        rfl

theorem cell23_4700970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_4700970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4700970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4700970 prefixEnd_4700970 := by exact prefixLift 4700970
  have htrace : WordTrace (prefixWord ++ tailWord_4700970) baseStart_4700970 baseEnd_4700970 := by
    simpa [prefixWord, tailWord_4700970, baseEnd_4700970] using wordTrace_append hprefix tailTrace_4700970
  have hstable : (prefixWord ++ tailWord_4700970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4700970).length < 2 ^ (prefixWord ++ tailWord_4700970).sum := by decide
  have hdescent : baseEnd_4700970 < baseStart_4700970 := by decide
  rcases family_descends (prefixWord ++ tailWord_4700970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4700986 : List Nat := [3, 1, 1, 1, 6, 1, 1, 2, 1, 3, 3]
def baseStart_4700986 : Nat := 118140960795 + 4700986 * 2 ^ 59
def prefixEnd_4700986 : Nat := 4983230072969 + 3 ^ 40 * 4700986 * 2
def baseEnd_4700986 : Nat := 2413865368057049604355565

theorem tailTrace_4700986 : CollatzResearch.WordTrace tailWord_4700986 prefixEnd_4700986 2413865368057049604355565 := by
  unfold tailWord_4700986
  simp only [CollatzResearch.WordTrace]
  refine ⟨42864761336784515333650703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114306030231425374223068541 42864761336784515333650703)
  ·
    refine ⟨64297142005176773000476055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42864761336784515333650703 64297142005176773000476055)
    ·
      refine ⟨96445713007765159500714083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64297142005176773000476055 96445713007765159500714083)
      ·
        refine ⟨144668569511647739251071125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96445713007765159500714083 144668569511647739251071125)
        ·
          refine ⟨6781339195858487777393959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 144668569511647739251071125 6781339195858487777393959)
          ·
            refine ⟨10172008793787731666090939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6781339195858487777393959 10172008793787731666090939)
            ·
              refine ⟨15258013190681597499136409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10172008793787731666090939 15258013190681597499136409)
              ·
                refine ⟨11443509893011198124352307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15258013190681597499136409 11443509893011198124352307)
                ·
                  refine ⟨17165264839516797186528461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11443509893011198124352307 17165264839516797186528461)
                  ·
                    refine ⟨6436974314818798944948173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17165264839516797186528461 6436974314818798944948173)
                    ·
                      refine ⟨2413865368057049604355565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6436974314818798944948173 2413865368057049604355565)
                      ·
                        rfl

theorem cell23_4700986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 2, 1, 3, 3].length) (baseStart_4700986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4700986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4700986 prefixEnd_4700986 := by exact prefixLift 4700986
  have htrace : WordTrace (prefixWord ++ tailWord_4700986) baseStart_4700986 baseEnd_4700986 := by
    simpa [prefixWord, tailWord_4700986, baseEnd_4700986] using wordTrace_append hprefix tailTrace_4700986
  have hstable : (prefixWord ++ tailWord_4700986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4700986).length < 2 ^ (prefixWord ++ tailWord_4700986).sum := by decide
  have hdescent : baseEnd_4700986 < baseStart_4700986 := by decide
  rcases family_descends (prefixWord ++ tailWord_4700986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4700990 : List Nat := [4, 2, 1, 2, 3, 1, 3, 1, 1, 2, 3]
def baseStart_4700990 : Nat := 118140960795 + 4700990 * 2 ^ 59
def prefixEnd_4700990 : Nat := 4983230072969 + 3 ^ 40 * 4700990 * 2
def baseEnd_4700990 : Nat := 2413867421979667588705547

theorem tailTrace_4700990 : CollatzResearch.WordTrace tailWord_4700990 prefixEnd_4700990 2413867421979667588705547 := by
  unfold tailWord_4700990
  simp only [CollatzResearch.WordTrace]
  refine ⟨21432398904890446252218553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 114306127492749046678498949 21432398904890446252218553)
  ·
    refine ⟨16074299178667834689163915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21432398904890446252218553 16074299178667834689163915)
    ·
      refine ⟨24111448768001752033745873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16074299178667834689163915 24111448768001752033745873)
      ·
        refine ⟨18083586576001314025309405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24111448768001752033745873 18083586576001314025309405)
        ·
          refine ⟨6781344966000492759491027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18083586576001314025309405 6781344966000492759491027)
          ·
            refine ⟨10172017449000739139236541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6781344966000492759491027 10172017449000739139236541)
            ·
              refine ⟨3814506543375277177213703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10172017449000739139236541 3814506543375277177213703)
              ·
                refine ⟨5721759815062915765820555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3814506543375277177213703 5721759815062915765820555)
                ·
                  refine ⟨8582639722594373648730833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5721759815062915765820555 8582639722594373648730833)
                  ·
                    refine ⟨6436979791945780236548125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8582639722594373648730833 6436979791945780236548125)
                    ·
                      refine ⟨2413867421979667588705547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6436979791945780236548125 2413867421979667588705547)
                      ·
                        rfl

theorem cell23_4700990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 3, 1, 1, 2, 3].length) (baseStart_4700990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4700990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4700990 prefixEnd_4700990 := by exact prefixLift 4700990
  have htrace : WordTrace (prefixWord ++ tailWord_4700990) baseStart_4700990 baseEnd_4700990 := by
    simpa [prefixWord, tailWord_4700990, baseEnd_4700990] using wordTrace_append hprefix tailTrace_4700990
  have hstable : (prefixWord ++ tailWord_4700990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4700990).length < 2 ^ (prefixWord ++ tailWord_4700990).sum := by decide
  have hdescent : baseEnd_4700990 < baseStart_4700990 := by decide
  rcases family_descends (prefixWord ++ tailWord_4700990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4700992 : List Nat := [2, 1, 1, 2, 2, 1, 1, 2, 4, 3, 4]
def baseStart_4700992 : Nat := 118140960795 + 4700992 * 2 ^ 59
def prefixEnd_4700992 : Nat := 4983230072969 + 3 ^ 40 * 4700992 * 2
def baseEnd_4700992 : Nat := 2413868448940976580880537

theorem tailTrace_4700992 : CollatzResearch.WordTrace tailWord_4700992 prefixEnd_4700992 2413868448940976580880537 := by
  unfold tailWord_4700992
  simp only [CollatzResearch.WordTrace]
  refine ⟨85729632092558162179660615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114306176123410882906214153 85729632092558162179660615)
  ·
    refine ⟨128594448138837243269490923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85729632092558162179660615 128594448138837243269490923)
    ·
      refine ⟨192891672208255864904236385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128594448138837243269490923 192891672208255864904236385)
      ·
        refine ⟨144668754156191898678177289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 192891672208255864904236385 144668754156191898678177289)
        ·
          refine ⟨108501565617143924008632967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 144668754156191898678177289 108501565617143924008632967)
          ·
            refine ⟨162752348425715886012949451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108501565617143924008632967 162752348425715886012949451)
            ·
              refine ⟨244128522638573829019424177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 162752348425715886012949451 244128522638573829019424177)
              ·
                refine ⟨183096391978930371764568133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 244128522638573829019424177 183096391978930371764568133)
                ·
                  refine ⟨34330573496049444705856525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 183096391978930371764568133 34330573496049444705856525)
                  ·
                    refine ⟨12873965061018541764696197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34330573496049444705856525 12873965061018541764696197)
                    ·
                      refine ⟨2413868448940976580880537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12873965061018541764696197 2413868448940976580880537)
                      ·
                        rfl

theorem cell23_4700992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 4, 3, 4].length) (baseStart_4700992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4700992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4700992 prefixEnd_4700992 := by exact prefixLift 4700992
  have htrace : WordTrace (prefixWord ++ tailWord_4700992) baseStart_4700992 baseEnd_4700992 := by
    simpa [prefixWord, tailWord_4700992, baseEnd_4700992] using wordTrace_append hprefix tailTrace_4700992
  have hstable : (prefixWord ++ tailWord_4700992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4700992).length < 2 ^ (prefixWord ++ tailWord_4700992).sum := by decide
  have hdescent : baseEnd_4700992 < baseStart_4700992 := by decide
  rcases family_descends (prefixWord ++ tailWord_4700992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4701054 : List Nat := [4, 2, 3, 1, 3, 1, 1, 2, 2, 1, 3]
def baseStart_4701054 : Nat := 118140960795 + 4701054 * 2 ^ 59
def prefixEnd_4701054 : Nat := 4983230072969 + 3 ^ 40 * 4701054 * 2
def baseEnd_4701054 : Nat := 2413900284741555338305253

theorem tailTrace_4701054 : CollatzResearch.WordTrace tailWord_4701054 prefixEnd_4701054 2413900284741555338305253 := by
  unfold tailWord_4701054
  simp only [CollatzResearch.WordTrace]
  refine ⟨21432690688861463618509777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 114307683673927805965385477 21432690688861463618509777)
  ·
    refine ⟨16074518016646097713882333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21432690688861463618509777 16074518016646097713882333)
    ·
      refine ⟨6027944256242286642705875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16074518016646097713882333 6027944256242286642705875)
      ·
        refine ⟨9041916384363429964058813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6027944256242286642705875 9041916384363429964058813)
        ·
          refine ⟨3390718644136286236522055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9041916384363429964058813 3390718644136286236522055)
          ·
            refine ⟨5086077966204429354783083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3390718644136286236522055 5086077966204429354783083)
            ·
              refine ⟨7629116949306644032174625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5086077966204429354783083 7629116949306644032174625)
              ·
                refine ⟨5721837711979983024130969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7629116949306644032174625 5721837711979983024130969)
                ·
                  refine ⟨4291378283984987268098227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5721837711979983024130969 4291378283984987268098227)
                  ·
                    refine ⟨6437067425977480902147341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4291378283984987268098227 6437067425977480902147341)
                    ·
                      refine ⟨2413900284741555338305253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6437067425977480902147341 2413900284741555338305253)
                      ·
                        rfl

theorem cell23_4701054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 1, 2, 2, 1, 3].length) (baseStart_4701054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4701054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4701054 prefixEnd_4701054 := by exact prefixLift 4701054
  have htrace : WordTrace (prefixWord ++ tailWord_4701054) baseStart_4701054 baseEnd_4701054 := by
    simpa [prefixWord, tailWord_4701054, baseEnd_4701054] using wordTrace_append hprefix tailTrace_4701054
  have hstable : (prefixWord ++ tailWord_4701054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4701054).length < 2 ^ (prefixWord ++ tailWord_4701054).sum := by decide
  have hdescent : baseEnd_4701054 < baseStart_4701054 := by decide
  rcases family_descends (prefixWord ++ tailWord_4701054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4701059 : List Nat := [1, 1, 1, 3, 4, 1, 1, 1, 4, 3, 3]
def baseStart_4701059 : Nat := 118140960795 + 4701059 * 2 ^ 59
def prefixEnd_4701059 : Nat := 4983230072969 + 3 ^ 40 * 4701059 * 2
def baseEnd_4701059 : Nat := 2413902852144827818742729

theorem tailTrace_4701059 : CollatzResearch.WordTrace tailWord_4701059 prefixEnd_4701059 2413902852144827818742729 := by
  unfold tailWord_4701059
  simp only [CollatzResearch.WordTrace]
  refine ⟨171461707875873594802010231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114307805250582396534673487 171461707875873594802010231)
  ·
    refine ⟨257192561813810392203015347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171461707875873594802010231 257192561813810392203015347)
    ·
      refine ⟨385788842720715588304523021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 257192561813810392203015347 385788842720715588304523021)
      ·
        refine ⟨144670816020268345614196133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 385788842720715588304523021 144670816020268345614196133)
        ·
          refine ⟨27125778003800314802661775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 144670816020268345614196133 27125778003800314802661775)
          ·
            refine ⟨40688667005700472203992663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27125778003800314802661775 40688667005700472203992663)
            ·
              refine ⟨61033000508550708305988995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40688667005700472203992663 61033000508550708305988995)
              ·
                refine ⟨91549500762826062458983493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61033000508550708305988995 91549500762826062458983493)
                ·
                  refine ⟨17165531393029886711059405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 91549500762826062458983493 17165531393029886711059405)
                  ·
                    refine ⟨6437074272386207516647277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17165531393029886711059405 6437074272386207516647277)
                    ·
                      refine ⟨2413902852144827818742729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6437074272386207516647277 2413902852144827818742729)
                      ·
                        rfl

theorem cell23_4701059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 1, 4, 3, 3].length) (baseStart_4701059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4701059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4701059 prefixEnd_4701059 := by exact prefixLift 4701059
  have htrace : WordTrace (prefixWord ++ tailWord_4701059) baseStart_4701059 baseEnd_4701059 := by
    simpa [prefixWord, tailWord_4701059, baseEnd_4701059] using wordTrace_append hprefix tailTrace_4701059
  have hstable : (prefixWord ++ tailWord_4701059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4701059).length < 2 ^ (prefixWord ++ tailWord_4701059).sum := by decide
  have hdescent : baseEnd_4701059 < baseStart_4701059 := by decide
  rcases family_descends (prefixWord ++ tailWord_4701059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4701066 : List Nat := [3, 1, 2, 4, 1, 2, 2, 1, 7]
def baseStart_4701066 : Nat := 118140960795 + 4701066 * 2 ^ 59
def prefixEnd_4701066 : Nat := 4983230072969 + 3 ^ 40 * 4701066 * 2
def baseEnd_4701066 : Nat := 268211827389934365706133

theorem tailTrace_4701066 : CollatzResearch.WordTrace tailWord_4701066 prefixEnd_4701066 268211827389934365706133 := by
  unfold tailWord_4701066
  simp only [CollatzResearch.WordTrace]
  refine ⟨42865490796712058749378763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114307975457898823331676701 42865490796712058749378763)
  ·
    refine ⟨64298236195068088124068145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42865490796712058749378763 64298236195068088124068145)
    ·
      refine ⟨48223677146301066093051109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64298236195068088124068145 48223677146301066093051109)
      ·
        refine ⟨9041939464931449892447083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48223677146301066093051109 9041939464931449892447083)
        ·
          refine ⟨13562909197397174838670625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9041939464931449892447083 13562909197397174838670625)
          ·
            refine ⟨10172181898047881129002969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13562909197397174838670625 10172181898047881129002969)
            ·
              refine ⟨7629136423535910846752227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10172181898047881129002969 7629136423535910846752227)
              ·
                refine ⟨11443704635303866270128341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7629136423535910846752227 11443704635303866270128341)
                ·
                  refine ⟨268211827389934365706133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11443704635303866270128341 268211827389934365706133)
                  ·
                    rfl

theorem cell23_4701066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 2, 1, 7].length) (baseStart_4701066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4701066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4701066 prefixEnd_4701066 := by exact prefixLift 4701066
  have htrace : WordTrace (prefixWord ++ tailWord_4701066) baseStart_4701066 baseEnd_4701066 := by
    simpa [prefixWord, tailWord_4701066, baseEnd_4701066] using wordTrace_append hprefix tailTrace_4701066
  have hstable : (prefixWord ++ tailWord_4701066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4701066).length < 2 ^ (prefixWord ++ tailWord_4701066).sum := by decide
  have hdescent : baseEnd_4701066 < baseStart_4701066 := by decide
  rcases family_descends (prefixWord ++ tailWord_4701066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4701076 : List Nat := [2, 4, 2, 1, 1, 1, 1, 3, 2, 3, 3]
def baseStart_4701076 : Nat := 118140960795 + 4701076 * 2 ^ 59
def prefixEnd_4701076 : Nat := 4983230072969 + 3 ^ 40 * 4701076 * 2
def baseEnd_4701076 : Nat := 2413911581315954252230151

theorem tailTrace_4701076 : CollatzResearch.WordTrace tailWord_4701076 prefixEnd_4701076 2413911581315954252230151 := by
  unfold tailWord_4701076
  simp only [CollatzResearch.WordTrace]
  refine ⟨85731163958406003352689541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114308218611208004470252721 85731163958406003352689541)
  ·
    refine ⟨16074593242201125628629289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 85731163958406003352689541 16074593242201125628629289)
    ·
      refine ⟨12055944931650844221471967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16074593242201125628629289 12055944931650844221471967)
      ·
        refine ⟨18083917397476266332207951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12055944931650844221471967 18083917397476266332207951)
        ·
          refine ⟨27125876096214399498311927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18083917397476266332207951 27125876096214399498311927)
          ·
            refine ⟨40688814144321599247467891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27125876096214399498311927 40688814144321599247467891)
            ·
              refine ⟨61033221216482398871201837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40688814144321599247467891 61033221216482398871201837)
              ·
                refine ⟨22887457956180899576700689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61033221216482398871201837 22887457956180899576700689)
                ·
                  refine ⟨17165593467135674682525517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22887457956180899576700689 17165593467135674682525517)
                  ·
                    refine ⟨6437097550175878005947069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17165593467135674682525517 6437097550175878005947069)
                    ·
                      refine ⟨2413911581315954252230151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6437097550175878005947069 2413911581315954252230151)
                      ·
                        rfl

theorem cell23_4701076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 3, 2, 3, 3].length) (baseStart_4701076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4701076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4701076 prefixEnd_4701076 := by exact prefixLift 4701076
  have htrace : WordTrace (prefixWord ++ tailWord_4701076) baseStart_4701076 baseEnd_4701076 := by
    simpa [prefixWord, tailWord_4701076, baseEnd_4701076] using wordTrace_append hprefix tailTrace_4701076
  have hstable : (prefixWord ++ tailWord_4701076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4701076).length < 2 ^ (prefixWord ++ tailWord_4701076).sum := by decide
  have hdescent : baseEnd_4701076 < baseStart_4701076 := by decide
  rcases family_descends (prefixWord ++ tailWord_4701076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4701119 : List Nat := [1, 1, 2, 2, 2, 1, 2, 2, 3, 4, 3]
def baseStart_4701119 : Nat := 118140960795 + 4701119 * 2 ^ 59
def prefixEnd_4701119 : Nat := 4983230072969 + 3 ^ 40 * 4701119 * 2
def baseEnd_4701119 : Nat := 2413933660984097583992453

theorem tailTrace_4701119 : CollatzResearch.WordTrace tailWord_4701119 prefixEnd_4701119 2413933660984097583992453 := by
  unfold tailWord_4701119
  simp only [CollatzResearch.WordTrace]
  refine ⟨171463896255656225049194411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114309264170437483366129607 171463896255656225049194411)
  ·
    refine ⟨257195844383484337573791617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171463896255656225049194411 257195844383484337573791617)
    ·
      refine ⟨192896883287613253180343713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 257195844383484337573791617 192896883287613253180343713)
      ·
        refine ⟨144672662465709939885257785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 192896883287613253180343713 144672662465709939885257785)
        ·
          refine ⟨108504496849282454913943339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 144672662465709939885257785 108504496849282454913943339)
          ·
            refine ⟨162756745273923682370915009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108504496849282454913943339 162756745273923682370915009)
            ·
              refine ⟨122067558955442761778186257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 162756745273923682370915009 122067558955442761778186257)
              ·
                refine ⟨91550669216582071333639693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 122067558955442761778186257 91550669216582071333639693)
                ·
                  refine ⟨34331500956218276750114885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 91550669216582071333639693 34331500956218276750114885)
                  ·
                    refine ⟨6437156429290926890646541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34331500956218276750114885 6437156429290926890646541)
                    ·
                      refine ⟨2413933660984097583992453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6437156429290926890646541 2413933660984097583992453)
                      ·
                        rfl

theorem cell23_4701119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 2, 3, 4, 3].length) (baseStart_4701119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4701119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4701119 prefixEnd_4701119 := by exact prefixLift 4701119
  have htrace : WordTrace (prefixWord ++ tailWord_4701119) baseStart_4701119 baseEnd_4701119 := by
    simpa [prefixWord, tailWord_4701119, baseEnd_4701119] using wordTrace_append hprefix tailTrace_4701119
  have hstable : (prefixWord ++ tailWord_4701119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4701119).length < 2 ^ (prefixWord ++ tailWord_4701119).sum := by decide
  have hdescent : baseEnd_4701119 < baseStart_4701119 := by decide
  rcases family_descends (prefixWord ++ tailWord_4701119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4701176 : List Nat := [2, 1, 2, 1, 1, 3, 1, 2, 3, 5, 2]
def baseStart_4701176 : Nat := 118140960795 + 4701176 * 2 ^ 59
def prefixEnd_4701176 : Nat := 4983230072969 + 3 ^ 40 * 4701176 * 2
def baseEnd_4701176 : Nat := 2413962929381403860979691

theorem tailTrace_4701176 : CollatzResearch.WordTrace tailWord_4701176 prefixEnd_4701176 2413962929381403860979691 := by
  unfold tailWord_4701176
  simp only [CollatzResearch.WordTrace]
  refine ⟨85732987608224861892009691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114310650144299815856012921 85732987608224861892009691)
  ·
    refine ⟨128599481412337292838014537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85732987608224861892009691 128599481412337292838014537)
    ·
      refine ⟨96449611059252969628510903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128599481412337292838014537 96449611059252969628510903)
      ·
        refine ⟨144674416588879454442766355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96449611059252969628510903 144674416588879454442766355)
        ·
          refine ⟨217011624883319181664149533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144674416588879454442766355 217011624883319181664149533)
          ·
            refine ⟨81379359331244693124056075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 217011624883319181664149533 81379359331244693124056075)
            ·
              refine ⟨122069038996867039686084113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81379359331244693124056075 122069038996867039686084113)
              ·
                refine ⟨91551779247650279764563085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 122069038996867039686084113 91551779247650279764563085)
                ·
                  refine ⟨34331917217868854911711157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 91551779247650279764563085 34331917217868854911711157)
                  ·
                    refine ⟨3218617239175205147972921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34331917217868854911711157 3218617239175205147972921)
                    ·
                      refine ⟨2413962929381403860979691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3218617239175205147972921 2413962929381403860979691)
                      ·
                        rfl

theorem cell23_4701176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 2, 3, 5, 2].length) (baseStart_4701176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4701176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4701176 prefixEnd_4701176 := by exact prefixLift 4701176
  have htrace : WordTrace (prefixWord ++ tailWord_4701176) baseStart_4701176 baseEnd_4701176 := by
    simpa [prefixWord, tailWord_4701176, baseEnd_4701176] using wordTrace_append hprefix tailTrace_4701176
  have hstable : (prefixWord ++ tailWord_4701176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4701176).length < 2 ^ (prefixWord ++ tailWord_4701176).sum := by decide
  have hdescent : baseEnd_4701176 < baseStart_4701176 := by decide
  rcases family_descends (prefixWord ++ tailWord_4701176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4701217 : List Nat := [1, 2, 3, 2, 3, 2, 2, 3, 1, 1, 3]
def baseStart_4701217 : Nat := 118140960795 + 4701217 * 2 ^ 59
def prefixEnd_4701217 : Nat := 4983230072969 + 3 ^ 40 * 4701217 * 2
def baseEnd_4701217 : Nat := 2413983982088238200567003

theorem tailTrace_4701217 : CollatzResearch.WordTrace tailWord_4701217 prefixEnd_4701217 2413983982088238200567003 := by
  unfold tailWord_4701217
  simp only [CollatzResearch.WordTrace]
  refine ⟨171467470609301187786261905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114311647072867458524174603 171467470609301187786261905)
  ·
    refine ⟨128600602956975890839696429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171467470609301187786261905 128600602956975890839696429)
    ·
      refine ⟨48225226108865959064886161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 128600602956975890839696429 48225226108865959064886161)
      ·
        refine ⟨36168919581649469298664621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48225226108865959064886161 36168919581649469298664621)
        ·
          refine ⟨13563344843118550986999233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36168919581649469298664621 13563344843118550986999233)
          ·
            refine ⟨10172508632338913240249425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13563344843118550986999233 10172508632338913240249425)
            ·
              refine ⟨7629381474254184930187069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10172508632338913240249425 7629381474254184930187069)
              ·
                refine ⟨2861018052845319348820151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7629381474254184930187069 2861018052845319348820151)
                ·
                  refine ⟨4291527079267979023230227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2861018052845319348820151 4291527079267979023230227)
                  ·
                    refine ⟨6437290618901968534845341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4291527079267979023230227 6437290618901968534845341)
                    ·
                      refine ⟨2413983982088238200567003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6437290618901968534845341 2413983982088238200567003)
                      ·
                        rfl

theorem cell23_4701217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 2, 3, 1, 1, 3].length) (baseStart_4701217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4701217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4701217 prefixEnd_4701217 := by exact prefixLift 4701217
  have htrace : WordTrace (prefixWord ++ tailWord_4701217) baseStart_4701217 baseEnd_4701217 := by
    simpa [prefixWord, tailWord_4701217, baseEnd_4701217] using wordTrace_append hprefix tailTrace_4701217
  have hstable : (prefixWord ++ tailWord_4701217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4701217).length < 2 ^ (prefixWord ++ tailWord_4701217).sum := by decide
  have hdescent : baseEnd_4701217 < baseStart_4701217 := by decide
  rcases family_descends (prefixWord ++ tailWord_4701217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4701220 : List Nat := [2, 3, 1, 4, 1, 1, 4, 1, 1, 5]
def baseStart_4701220 : Nat := 118140960795 + 4701220 * 2 ^ 59
def prefixEnd_4701220 : Nat := 4983230072969 + 3 ^ 40 * 4701220 * 2
def baseEnd_4701220 : Nat := 804661840843400562943163

theorem tailTrace_4701220 : CollatzResearch.WordTrace tailWord_4701220 prefixEnd_4701220 804661840843400562943163 := by
  unfold tailWord_4701220
  simp only [CollatzResearch.WordTrace]
  refine ⟨85733790014145159649310557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114311720018860212865747409 85733790014145159649310557)
  ·
    refine ⟨32150171255304434868491459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85733790014145159649310557 32150171255304434868491459)
    ·
      refine ⟨48225256882956652302737189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32150171255304434868491459 48225256882956652302737189)
      ·
        refine ⟨9042235665554372306763223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48225256882956652302737189 9042235665554372306763223)
        ·
          refine ⟨13563353498331558460144835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9042235665554372306763223 13563353498331558460144835)
          ·
            refine ⟨20345030247497337690217253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13563353498331558460144835 20345030247497337690217253)
            ·
              refine ⟨3814693171405750816915735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20345030247497337690217253 3814693171405750816915735)
              ·
                refine ⟨5722039757108626225373603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3814693171405750816915735 5722039757108626225373603)
                ·
                  refine ⟨8583059635662939338060405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5722039757108626225373603 8583059635662939338060405)
                  ·
                    refine ⟨804661840843400562943163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8583059635662939338060405 804661840843400562943163)
                    ·
                      rfl

theorem cell23_4701220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 4, 1, 1, 5].length) (baseStart_4701220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4701220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4701220 prefixEnd_4701220 := by exact prefixLift 4701220
  have htrace : WordTrace (prefixWord ++ tailWord_4701220) baseStart_4701220 baseEnd_4701220 := by
    simpa [prefixWord, tailWord_4701220, baseEnd_4701220] using wordTrace_append hprefix tailTrace_4701220
  have hstable : (prefixWord ++ tailWord_4701220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4701220).length < 2 ^ (prefixWord ++ tailWord_4701220).sum := by decide
  have hdescent : baseEnd_4701220 < baseStart_4701220 := by decide
  rcases family_descends (prefixWord ++ tailWord_4701220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4701239 : List Nat := [1, 1, 3, 1, 2, 2, 1, 1, 2, 2, 7]
def baseStart_4701239 : Nat := 118140960795 + 4701239 * 2 ^ 59
def prefixEnd_4701239 : Nat := 4983230072969 + 3 ^ 40 * 4701239 * 2
def baseEnd_4701239 : Nat := 2413995278662637114491901

theorem tailTrace_4701239 : CollatzResearch.WordTrace tailWord_4701239 prefixEnd_4701239 2413995278662637114491901 := by
  unfold tailWord_4701239
  simp only [CollatzResearch.WordTrace]
  refine ⟨171468273015221485543562771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114312182010147657029041847 171468273015221485543562771)
  ·
    refine ⟨257202409522832228315344157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171468273015221485543562771 257202409522832228315344157)
    ·
      refine ⟨96450903571062085618254059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 257202409522832228315344157 96450903571062085618254059)
      ·
        refine ⟨144676355356593128427381089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96450903571062085618254059 144676355356593128427381089)
        ·
          refine ⟨108507266517444846320535817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 144676355356593128427381089 108507266517444846320535817)
          ·
            refine ⟨81380449888083634740401863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 108507266517444846320535817 81380449888083634740401863)
            ·
              refine ⟨122070674832125452110602795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81380449888083634740401863 122070674832125452110602795)
              ·
                refine ⟨183106012248188178165904193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 122070674832125452110602795 183106012248188178165904193)
                ·
                  refine ⟨137329509186141133624428145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 183106012248188178165904193 137329509186141133624428145)
                  ·
                    refine ⟨102997131889605850218321109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 137329509186141133624428145 102997131889605850218321109)
                    ·
                      refine ⟨2413995278662637114491901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 102997131889605850218321109 2413995278662637114491901)
                      ·
                        rfl

theorem cell23_4701239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 1, 2, 2, 7].length) (baseStart_4701239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4701239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4701239 prefixEnd_4701239 := by exact prefixLift 4701239
  have htrace : WordTrace (prefixWord ++ tailWord_4701239) baseStart_4701239 baseEnd_4701239 := by
    simpa [prefixWord, tailWord_4701239, baseEnd_4701239] using wordTrace_append hprefix tailTrace_4701239
  have hstable : (prefixWord ++ tailWord_4701239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4701239).length < 2 ^ (prefixWord ++ tailWord_4701239).sum := by decide
  have hdescent : baseEnd_4701239 < baseStart_4701239 := by decide
  rcases family_descends (prefixWord ++ tailWord_4701239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4701240 : List Nat := [2, 1, 2, 1, 5, 1, 1, 3, 3, 2, 2]
def baseStart_4701240 : Nat := 118140960795 + 4701240 * 2 ^ 59
def prefixEnd_4701240 : Nat := 4983230072969 + 3 ^ 40 * 4701240 * 2
def baseEnd_4701240 : Nat := 2413995792143291610579397

theorem tailTrace_4701240 : CollatzResearch.WordTrace tailWord_4701240 prefixEnd_4701240 2413995792143291610579397 := by
  unfold tailWord_4701240
  simp only [CollatzResearch.WordTrace]
  refine ⟨85734154744108931357174587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114312206325478575142899449 85734154744108931357174587)
  ·
    refine ⟨128601232116163397035761881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85734154744108931357174587 128601232116163397035761881)
    ·
      refine ⟨96450924087122547776821411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128601232116163397035761881 96450924087122547776821411)
      ·
        refine ⟨144676386130683821665232117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96450924087122547776821411 144676386130683821665232117)
        ·
          refine ⟨13563411199751608281115511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 144676386130683821665232117 13563411199751608281115511)
          ·
            refine ⟨20345116799627412421673267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13563411199751608281115511 20345116799627412421673267)
            ·
              refine ⟨30517675199441118632509901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20345116799627412421673267 30517675199441118632509901)
              ·
                refine ⟨11444128199790419487191213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30517675199441118632509901 11444128199790419487191213)
                ·
                  refine ⟨4291548074921407307696705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11444128199790419487191213 4291548074921407307696705)
                  ·
                    refine ⟨3218661056191055480772529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4291548074921407307696705 3218661056191055480772529)
                    ·
                      refine ⟨2413995792143291610579397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3218661056191055480772529 2413995792143291610579397)
                      ·
                        rfl

theorem cell23_4701240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 3, 3, 2, 2].length) (baseStart_4701240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4701240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4701240 prefixEnd_4701240 := by exact prefixLift 4701240
  have htrace : WordTrace (prefixWord ++ tailWord_4701240) baseStart_4701240 baseEnd_4701240 := by
    simpa [prefixWord, tailWord_4701240, baseEnd_4701240] using wordTrace_append hprefix tailTrace_4701240
  have hstable : (prefixWord ++ tailWord_4701240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4701240).length < 2 ^ (prefixWord ++ tailWord_4701240).sum := by decide
  have hdescent : baseEnd_4701240 < baseStart_4701240 := by decide
  rcases family_descends (prefixWord ++ tailWord_4701240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4701283 : List Nat := [1, 1, 1, 5, 1, 1, 1, 2, 5, 3, 2]
def baseStart_4701283 : Nat := 118140960795 + 4701283 * 2 ^ 59
def prefixEnd_4701283 : Nat := 4983230072969 + 3 ^ 40 * 4701283 * 2
def baseEnd_4701283 : Nat := 2414017871811434942341699

theorem tailTrace_4701283 : CollatzResearch.WordTrace tailWord_4701283 prefixEnd_4701283 2414017871811434942341699 := by
  unfold tailWord_4701283
  simp only [CollatzResearch.WordTrace]
  refine ⟨171469877827062081058164503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114313251884708054038776335 171469877827062081058164503)
  ·
    refine ⟨257204816740593121587246755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171469877827062081058164503 257204816740593121587246755)
    ·
      refine ⟨385807225110889682380870133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 257204816740593121587246755 385807225110889682380870133)
      ·
        refine ⟨36169427354145907723206575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 385807225110889682380870133 36169427354145907723206575)
        ·
          refine ⟨54254141031218861584809863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36169427354145907723206575 54254141031218861584809863)
          ·
            refine ⟨81381211546828292377214795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54254141031218861584809863 81381211546828292377214795)
            ·
              refine ⟨122071817320242438565822193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81381211546828292377214795 122071817320242438565822193)
              ·
                refine ⟨91553862990181828924366645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 122071817320242438565822193 91553862990181828924366645)
                ·
                  refine ⟨8583174655329546461659373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 91553862990181828924366645 8583174655329546461659373)
                  ·
                    refine ⟨3218690495748579923122265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8583174655329546461659373 3218690495748579923122265)
                    ·
                      refine ⟨2414017871811434942341699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3218690495748579923122265 2414017871811434942341699)
                      ·
                        rfl

theorem cell23_4701283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 2, 5, 3, 2].length) (baseStart_4701283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4701283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4701283 prefixEnd_4701283 := by exact prefixLift 4701283
  have htrace : WordTrace (prefixWord ++ tailWord_4701283) baseStart_4701283 baseEnd_4701283 := by
    simpa [prefixWord, tailWord_4701283, baseEnd_4701283] using wordTrace_append hprefix tailTrace_4701283
  have hstable : (prefixWord ++ tailWord_4701283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4701283).length < 2 ^ (prefixWord ++ tailWord_4701283).sum := by decide
  have hdescent : baseEnd_4701283 < baseStart_4701283 := by decide
  rcases family_descends (prefixWord ++ tailWord_4701283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4701290 : List Nat := [3, 1, 3, 2, 2, 1, 2, 1, 4, 1, 3]
def baseStart_4701290 : Nat := 118140960795 + 4701290 * 2 ^ 59
def prefixEnd_4701290 : Nat := 4983230072969 + 3 ^ 40 * 4701290 * 2
def baseEnd_4701290 : Nat := 2414021466176016414954167

theorem tailTrace_4701290 : CollatzResearch.WordTrace tailWord_4701290 prefixEnd_4701290 2414021466176016414954167 := by
  unfold tailWord_4701290
  simp only [CollatzResearch.WordTrace]
  refine ⟨42867533284509180313417331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114313422092024480835779549 42867533284509180313417331)
  ·
    refine ⟨64301299926763770470125997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42867533284509180313417331 64301299926763770470125997)
    ·
      refine ⟨24112987472536413926297249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64301299926763770470125997 24112987472536413926297249)
      ·
        refine ⟨18084740604402310444722937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24112987472536413926297249 18084740604402310444722937)
        ·
          refine ⟨13563555453301732833542203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18084740604402310444722937 13563555453301732833542203)
          ·
            refine ⟨20345333179952599250313305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13563555453301732833542203 20345333179952599250313305)
            ·
              refine ⟨15258999884964449437734979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20345333179952599250313305 15258999884964449437734979)
              ·
                refine ⟨22888499827446674156602469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15258999884964449437734979 22888499827446674156602469)
                ·
                  refine ⟨4291593717646251404362963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22888499827446674156602469 4291593717646251404362963)
                  ·
                    refine ⟨6437390576469377106544445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4291593717646251404362963 6437390576469377106544445)
                    ·
                      refine ⟨2414021466176016414954167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6437390576469377106544445 2414021466176016414954167)
                      ·
                        rfl

theorem cell23_4701290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 1, 4, 1, 3].length) (baseStart_4701290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4701290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4701290 prefixEnd_4701290 := by exact prefixLift 4701290
  have htrace : WordTrace (prefixWord ++ tailWord_4701290) baseStart_4701290 baseEnd_4701290 := by
    simpa [prefixWord, tailWord_4701290, baseEnd_4701290] using wordTrace_append hprefix tailTrace_4701290
  have hstable : (prefixWord ++ tailWord_4701290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4701290).length < 2 ^ (prefixWord ++ tailWord_4701290).sum := by decide
  have hdescent : baseEnd_4701290 < baseStart_4701290 := by decide
  rcases family_descends (prefixWord ++ tailWord_4701290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4701296 : List Nat := [2, 1, 1, 1, 5, 1, 2, 1, 2, 3, 4]
def baseStart_4701296 : Nat := 118140960795 + 4701296 * 2 ^ 59
def prefixEnd_4701296 : Nat := 4983230072969 + 3 ^ 40 * 4701296 * 2
def baseEnd_4701296 : Nat := 2414024547059943391479139

theorem tailTrace_4701296 : CollatzResearch.WordTrace tailWord_4701296 prefixEnd_4701296 2414024547059943391479139 := by
  unfold tailWord_4701296
  simp only [CollatzResearch.WordTrace]
  refine ⟨85735175988007492139193871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114313567984009989518925161 85735175988007492139193871)
  ·
    refine ⟨128602763982011238208790807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85735175988007492139193871 128602763982011238208790807)
    ·
      refine ⟨192904145973016857313186211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128602763982011238208790807 192904145973016857313186211)
      ·
        refine ⟨289356218959525285969779317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192904145973016857313186211 289356218959525285969779317)
        ·
          refine ⟨27127145527455495559666811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 289356218959525285969779317 27127145527455495559666811)
          ·
            refine ⟨40690718291183243339500217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27127145527455495559666811 40690718291183243339500217)
            ·
              refine ⟨30518038718387432504625163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40690718291183243339500217 30518038718387432504625163)
              ·
                refine ⟨45777058077581148756937745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30518038718387432504625163 45777058077581148756937745)
                ·
                  refine ⟨34332793558185861567703309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45777058077581148756937745 34332793558185861567703309)
                  ·
                    refine ⟨12874797584319698087888741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34332793558185861567703309 12874797584319698087888741)
                    ·
                      refine ⟨2414024547059943391479139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12874797584319698087888741 2414024547059943391479139)
                      ·
                        rfl

theorem cell23_4701296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 1, 2, 3, 4].length) (baseStart_4701296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4701296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4701296 prefixEnd_4701296 := by exact prefixLift 4701296
  have htrace : WordTrace (prefixWord ++ tailWord_4701296) baseStart_4701296 baseEnd_4701296 := by
    simpa [prefixWord, tailWord_4701296, baseEnd_4701296] using wordTrace_append hprefix tailTrace_4701296
  have hstable : (prefixWord ++ tailWord_4701296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4701296).length < 2 ^ (prefixWord ++ tailWord_4701296).sum := by decide
  have hdescent : baseEnd_4701296 < baseStart_4701296 := by decide
  rcases family_descends (prefixWord ++ tailWord_4701296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4701301 : List Nat := [1, 3, 4, 3, 2, 1, 2, 1, 2, 4]
def baseStart_4701301 : Nat := 118140960795 + 4701301 * 2 ^ 59
def prefixEnd_4701301 : Nat := 4983230072969 + 3 ^ 40 * 4701301 * 2
def baseEnd_4701301 : Nat := 804675704821071957305539

theorem tailTrace_4701301 : CollatzResearch.WordTrace tailWord_4701301 prefixEnd_4701301 804675704821071957305539 := by
  unfold tailWord_4701301
  simp only [CollatzResearch.WordTrace]
  refine ⟨171470534340996870132319757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114313689560664580088213171 171470534340996870132319757)
  ·
    refine ⟨64301450377873826299619909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 171470534340996870132319757 64301450377873826299619909)
    ·
      refine ⟨12056521945851342431178733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64301450377873826299619909 12056521945851342431178733)
      ·
        refine ⟨4521195729694253411692025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12056521945851342431178733 4521195729694253411692025)
        ·
          refine ⟨3390896797270690058769019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4521195729694253411692025 3390896797270690058769019)
          ·
            refine ⟨5086345195906035088153529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3390896797270690058769019 5086345195906035088153529)
            ·
              refine ⟨3814758896929526316115147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5086345195906035088153529 3814758896929526316115147)
              ·
                refine ⟨5722138345394289474172721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3814758896929526316115147 5722138345394289474172721)
                ·
                  refine ⟨4291603759045717105629541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5722138345394289474172721 4291603759045717105629541)
                  ·
                    refine ⟨804675704821071957305539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4291603759045717105629541 804675704821071957305539)
                    ·
                      rfl

theorem cell23_4701301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 2, 1, 2, 4].length) (baseStart_4701301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4701301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4701301 prefixEnd_4701301 := by exact prefixLift 4701301
  have htrace : WordTrace (prefixWord ++ tailWord_4701301) baseStart_4701301 baseEnd_4701301 := by
    simpa [prefixWord, tailWord_4701301, baseEnd_4701301] using wordTrace_append hprefix tailTrace_4701301
  have hstable : (prefixWord ++ tailWord_4701301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4701301).length < 2 ^ (prefixWord ++ tailWord_4701301).sum := by decide
  have hdescent : baseEnd_4701301 < baseStart_4701301 := by decide
  rcases family_descends (prefixWord ++ tailWord_4701301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4701330 : List Nat := [3, 2, 3, 1, 1, 2, 1, 1, 3, 4, 2]
def baseStart_4701330 : Nat := 118140960795 + 4701330 * 2 ^ 59
def prefixEnd_4701330 : Nat := 4983230072969 + 3 ^ 40 * 4701330 * 2
def baseEnd_4701330 : Nat := 2414042005402196258453983

theorem tailTrace_4701330 : CollatzResearch.WordTrace tailWord_4701330 prefixEnd_4701330 2414042005402196258453983 := by
  unfold tailWord_4701330
  simp only [CollatzResearch.WordTrace]
  refine ⟨42867898014472952021281361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114314394705261205390083629 42867898014472952021281361)
  ·
    refine ⟨32150923510854714015961021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42867898014472952021281361 32150923510854714015961021)
    ·
      refine ⟨12056596316570517755985383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32150923510854714015961021 12056596316570517755985383)
      ·
        refine ⟨18084894474855776633978075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12056596316570517755985383 18084894474855776633978075)
        ·
          refine ⟨27127341712283664950967113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18084894474855776633978075 27127341712283664950967113)
          ·
            refine ⟨20345506284212748713225335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27127341712283664950967113 20345506284212748713225335)
            ·
              refine ⟨30518259426319123069838003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20345506284212748713225335 30518259426319123069838003)
              ·
                refine ⟨45777389139478684604757005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30518259426319123069838003 45777389139478684604757005)
                ·
                  refine ⟨17166520927304506726783877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45777389139478684604757005 17166520927304506726783877)
                  ·
                    refine ⟨3218722673869595011271977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17166520927304506726783877 3218722673869595011271977)
                    ·
                      refine ⟨2414042005402196258453983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3218722673869595011271977 2414042005402196258453983)
                      ·
                        rfl

theorem cell23_4701330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 1, 3, 4, 2].length) (baseStart_4701330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4701330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4701330 prefixEnd_4701330 := by exact prefixLift 4701330
  have htrace : WordTrace (prefixWord ++ tailWord_4701330) baseStart_4701330 baseEnd_4701330 := by
    simpa [prefixWord, tailWord_4701330, baseEnd_4701330] using wordTrace_append hprefix tailTrace_4701330
  have hstable : (prefixWord ++ tailWord_4701330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4701330).length < 2 ^ (prefixWord ++ tailWord_4701330).sum := by decide
  have hdescent : baseEnd_4701330 < baseStart_4701330 := by decide
  rcases family_descends (prefixWord ++ tailWord_4701330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4701398 : List Nat := [5, 2, 1, 2, 2, 2, 1, 2, 2, 2, 2]
def baseStart_4701398 : Nat := 118140960795 + 4701398 * 2 ^ 59
def prefixEnd_4701398 : Nat := 4983230072969 + 3 ^ 40 * 4701398 * 2
def baseEnd_4701398 : Nat := 2414076922086701992403671

theorem tailTrace_4701398 : CollatzResearch.WordTrace tailWord_4701398 prefixEnd_4701398 2414076922086701992403671 := by
  unfold tailWord_4701398
  simp only [CollatzResearch.WordTrace]
  refine ⟨10717129513852840981162553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 114316048147763637132400565 10717129513852840981162553)
  ·
    refine ⟨8037847135389630735871915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10717129513852840981162553 8037847135389630735871915)
    ·
      refine ⟨12056770703084446103807873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8037847135389630735871915 12056770703084446103807873)
      ·
        refine ⟨9042578027313334577855905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12056770703084446103807873 9042578027313334577855905)
        ·
          refine ⟨6781933520485000933391929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9042578027313334577855905 6781933520485000933391929)
          ·
            refine ⟨5086450140363750700043947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6781933520485000933391929 5086450140363750700043947)
            ·
              refine ⟨7629675210545626050065921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5086450140363750700043947 7629675210545626050065921)
              ·
                refine ⟨5722256407909219537549441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7629675210545626050065921 5722256407909219537549441)
                ·
                  refine ⟨4291692305931914653162081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5722256407909219537549441 4291692305931914653162081)
                  ·
                    refine ⟨3218769229448935989871561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4291692305931914653162081 3218769229448935989871561)
                    ·
                      refine ⟨2414076922086701992403671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3218769229448935989871561 2414076922086701992403671)
                      ·
                        rfl

theorem cell23_4701398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 1, 2, 2, 2, 2].length) (baseStart_4701398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4701398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4701398 prefixEnd_4701398 := by exact prefixLift 4701398
  have htrace : WordTrace (prefixWord ++ tailWord_4701398) baseStart_4701398 baseEnd_4701398 := by
    simpa [prefixWord, tailWord_4701398, baseEnd_4701398] using wordTrace_append hprefix tailTrace_4701398
  have hstable : (prefixWord ++ tailWord_4701398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4701398).length < 2 ^ (prefixWord ++ tailWord_4701398).sum := by decide
  have hdescent : baseEnd_4701398 < baseStart_4701398 := by decide
  rcases family_descends (prefixWord ++ tailWord_4701398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4701420 : List Nat := [2, 2, 1, 1, 2, 4, 2, 1, 2, 4, 2]
def baseStart_4701420 : Nat := 118140960795 + 4701420 * 2 ^ 59
def prefixEnd_4701420 : Nat := 4983230072969 + 3 ^ 40 * 4701420 * 2
def baseEnd_4701420 : Nat := 2414088218661100906328569

theorem tailTrace_4701420 : CollatzResearch.WordTrace tailWord_4701420 prefixEnd_4701420 2414088218661100906328569 := by
  unfold tailWord_4701420
  simp only [CollatzResearch.WordTrace]
  refine ⟨85737437313782876727950857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114316583085043835637267809 85737437313782876727950857)
  ·
    refine ⟨64303077985337157545963143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85737437313782876727950857 64303077985337157545963143)
    ·
      refine ⟨96454616978005736318944715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64303077985337157545963143 96454616978005736318944715)
      ·
        refine ⟨144681925467008604478417073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96454616978005736318944715 144681925467008604478417073)
        ·
          refine ⟨108511444100256453358812805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 144681925467008604478417073 108511444100256453358812805)
          ·
            refine ⟨20345895768798085004777401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 108511444100256453358812805 20345895768798085004777401)
            ·
              refine ⟨15259421826598563753583051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20345895768798085004777401 15259421826598563753583051)
              ·
                refine ⟨22889132739897845630374577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15259421826598563753583051 22889132739897845630374577)
                ·
                  refine ⟨17166849554923384222780933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22889132739897845630374577 17166849554923384222780933)
                  ·
                    refine ⟨3218784291548134541771425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17166849554923384222780933 3218784291548134541771425)
                    ·
                      refine ⟨2414088218661100906328569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3218784291548134541771425 2414088218661100906328569)
                      ·
                        rfl

theorem cell23_4701420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 4, 2].length) (baseStart_4701420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4701420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4701420 prefixEnd_4701420 := by exact prefixLift 4701420
  have htrace : WordTrace (prefixWord ++ tailWord_4701420) baseStart_4701420 baseEnd_4701420 := by
    simpa [prefixWord, tailWord_4701420, baseEnd_4701420] using wordTrace_append hprefix tailTrace_4701420
  have hstable : (prefixWord ++ tailWord_4701420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4701420).length < 2 ^ (prefixWord ++ tailWord_4701420).sum := by decide
  have hdescent : baseEnd_4701420 < baseStart_4701420 := by decide
  rcases family_descends (prefixWord ++ tailWord_4701420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4701456 : List Nat := [2, 1, 1, 1, 1, 1, 1, 1, 3, 11]
def baseStart_4701456 : Nat := 118140960795 + 4701456 * 2 ^ 59
def prefixEnd_4701456 : Nat := 4983230072969 + 3 ^ 40 * 4701456 * 2
def baseEnd_4701456 : Nat := 804702234654887588492801

theorem tailTrace_4701456 : CollatzResearch.WordTrace tailWord_4701456 prefixEnd_4701456 804702234654887588492801 := by
  unfold tailWord_4701456
  simp only [CollatzResearch.WordTrace]
  refine ⟨85738093827717665802106111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114317458436956887736141481 85738093827717665802106111)
  ·
    refine ⟨128607140741576498703159167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85738093827717665802106111 128607140741576498703159167)
    ·
      refine ⟨192910711112364748054738751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128607140741576498703159167 192910711112364748054738751)
      ·
        refine ⟨289366066668547122082108127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192910711112364748054738751 289366066668547122082108127)
        ·
          refine ⟨434049100002820683123162191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 289366066668547122082108127 434049100002820683123162191)
          ·
            refine ⟨651073650004231024684743287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 434049100002820683123162191 651073650004231024684743287)
            ·
              refine ⟨976610475006346537027114931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 651073650004231024684743287 976610475006346537027114931)
              ·
                refine ⟨1464915712509519805540672397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 976610475006346537027114931 1464915712509519805540672397)
                ·
                  refine ⟨549343392191069927077752149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1464915712509519805540672397 549343392191069927077752149)
                  ·
                    refine ⟨804702234654887588492801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 549343392191069927077752149 804702234654887588492801)
                    ·
                      rfl

theorem cell23_4701456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 11].length) (baseStart_4701456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4701456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4701456 prefixEnd_4701456 := by exact prefixLift 4701456
  have htrace : WordTrace (prefixWord ++ tailWord_4701456) baseStart_4701456 baseEnd_4701456 := by
    simpa [prefixWord, tailWord_4701456, baseEnd_4701456] using wordTrace_append hprefix tailTrace_4701456
  have hstable : (prefixWord ++ tailWord_4701456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4701456).length < 2 ^ (prefixWord ++ tailWord_4701456).sum := by decide
  have hdescent : baseEnd_4701456 < baseStart_4701456 := by decide
  rcases family_descends (prefixWord ++ tailWord_4701456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4701464 : List Nat := [2, 1, 2, 3, 1, 4, 3, 2, 1, 4]
def baseStart_4701464 : Nat := 118140960795 + 4701464 * 2 ^ 59
def prefixEnd_4701464 : Nat := 4983230072969 + 3 ^ 40 * 4701464 * 2
def baseEnd_4701464 : Nat := 804703603936632911392789

theorem tailTrace_4701464 : CollatzResearch.WordTrace tailWord_4701464 prefixEnd_4701464 804703603936632911392789 := by
  unfold tailWord_4701464
  simp only [CollatzResearch.WordTrace]
  refine ⟨85738239719703174485251723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114317652959604232647002297 85738239719703174485251723)
  ·
    refine ⟨128607359579554761727877585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85738239719703174485251723 128607359579554761727877585)
    ·
      refine ⟨96455519684666071295908189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128607359579554761727877585 96455519684666071295908189)
      ·
        refine ⟨36170819881749776735965571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96455519684666071295908189 36170819881749776735965571)
        ·
          refine ⟨54256229822624665103948357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36170819881749776735965571 54256229822624665103948357)
          ·
            refine ⟨10173043091742124706990317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 54256229822624665103948357 10173043091742124706990317)
            ·
              refine ⟨3814891159403296765121369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10173043091742124706990317 3814891159403296765121369)
              ·
                refine ⟨2861168369552472573841027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3814891159403296765121369 2861168369552472573841027)
                ·
                  refine ⟨4291752554328708860761541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2861168369552472573841027 4291752554328708860761541)
                  ·
                    refine ⟨804703603936632911392789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4291752554328708860761541 804703603936632911392789)
                    ·
                      rfl

theorem cell23_4701464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 3, 2, 1, 4].length) (baseStart_4701464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4701464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4701464 prefixEnd_4701464 := by exact prefixLift 4701464
  have htrace : WordTrace (prefixWord ++ tailWord_4701464) baseStart_4701464 baseEnd_4701464 := by
    simpa [prefixWord, tailWord_4701464, baseEnd_4701464] using wordTrace_append hprefix tailTrace_4701464
  have hstable : (prefixWord ++ tailWord_4701464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4701464).length < 2 ^ (prefixWord ++ tailWord_4701464).sum := by decide
  have hdescent : baseEnd_4701464 < baseStart_4701464 := by decide
  rcases family_descends (prefixWord ++ tailWord_4701464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4701473 : List Nat := [1, 2, 3, 2, 1, 1, 1, 4, 3, 5]
def baseStart_4701473 : Nat := 118140960795 + 4701473 * 2 ^ 59
def prefixEnd_4701473 : Nat := 4983230072969 + 3 ^ 40 * 4701473 * 2
def baseEnd_4701473 : Nat := 804705144378596399655275

theorem tailTrace_4701473 : CollatzResearch.WordTrace tailWord_4701473 prefixEnd_4701473 804705144378596399655275 := by
  unfold tailWord_4701473
  simp only [CollatzResearch.WordTrace]
  refine ⟨171476807696373743507581073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114317871797582495671720715 171476807696373743507581073)
  ·
    refine ⟨128607605772280307630685805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171476807696373743507581073 128607605772280307630685805)
    ·
      refine ⟨48227852164605115361507177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 128607605772280307630685805 48227852164605115361507177)
      ·
        refine ⟨36170889123453836521130383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48227852164605115361507177 36170889123453836521130383)
        ·
          refine ⟨54256333685180754781695575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36170889123453836521130383 54256333685180754781695575)
          ·
            refine ⟨81384500527771132172543363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54256333685180754781695575 81384500527771132172543363)
            ·
              refine ⟨122076750791656698258815045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81384500527771132172543363 122076750791656698258815045)
              ·
                refine ⟨22889390773435630923527821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 122076750791656698258815045 22889390773435630923527821)
                ·
                  refine ⟨8583521540038361596322933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22889390773435630923527821 8583521540038361596322933)
                  ·
                    refine ⟨804705144378596399655275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8583521540038361596322933 804705144378596399655275)
                    ·
                      rfl

theorem cell23_4701473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 4, 3, 5].length) (baseStart_4701473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4701473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4701473 prefixEnd_4701473 := by exact prefixLift 4701473
  have htrace : WordTrace (prefixWord ++ tailWord_4701473) baseStart_4701473 baseEnd_4701473 := by
    simpa [prefixWord, tailWord_4701473, baseEnd_4701473] using wordTrace_append hprefix tailTrace_4701473
  have hstable : (prefixWord ++ tailWord_4701473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4701473).length < 2 ^ (prefixWord ++ tailWord_4701473).sum := by decide
  have hdescent : baseEnd_4701473 < baseStart_4701473 := by decide
  rcases family_descends (prefixWord ++ tailWord_4701473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
