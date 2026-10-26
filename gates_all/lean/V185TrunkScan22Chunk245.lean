import V185TrunkScan22Chunk244

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_2185892 : List Nat := [2, 3, 1, 2, 2, 1, 1, 3, 3, 4]
def baseStart_2185892 : Nat := 118140960795 + 2185892 * 2 ^ 59
def prefixEnd_2185892 : Nat := 4983230072969 + 3 ^ 40 * 2185892 * 2
def baseEnd_2185892 : Nat := 748275503211911280798181

theorem tailTrace_2185892 : CollatzResearch.WordTrace tailWord_2185892 prefixEnd_2185892 748275503211911280798181 := by
  unfold tailWord_2185892
  simp only [CollatzResearch.WordTrace]
  refine ⟨39863015498447039738567965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53150687331262719651423953 39863015498447039738567965)
  ·
    refine ⟨14948630811917639901962987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39863015498447039738567965 14948630811917639901962987)
    ·
      refine ⟨22422946217876459852944481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14948630811917639901962987 22422946217876459852944481)
      ·
        refine ⟨16817209663407344889708361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22422946217876459852944481 16817209663407344889708361)
        ·
          refine ⟨12612907247555508667281271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16817209663407344889708361 12612907247555508667281271)
          ·
            refine ⟨18919360871333263000921907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12612907247555508667281271 18919360871333263000921907)
            ·
              refine ⟨28379041306999894501382861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18919360871333263000921907 28379041306999894501382861)
              ·
                refine ⟨10642140490124960438018573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28379041306999894501382861 10642140490124960438018573)
                ·
                  refine ⟨3990802683796860164256965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10642140490124960438018573 3990802683796860164256965)
                  ·
                    refine ⟨748275503211911280798181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3990802683796860164256965 748275503211911280798181)
                    ·
                      rfl

theorem cell22_2185892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 3, 3, 4].length) (baseStart_2185892 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2185892 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2185892 prefixEnd_2185892 := by exact prefixLift 2185892
  have htrace : WordTrace (prefixWord ++ tailWord_2185892) baseStart_2185892 baseEnd_2185892 := by
    simpa [prefixWord, tailWord_2185892, baseEnd_2185892] using wordTrace_append hprefix tailTrace_2185892
  have hstable : (prefixWord ++ tailWord_2185892).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2185892).length < 2 ^ (prefixWord ++ tailWord_2185892).sum := by decide
  have hdescent : baseEnd_2185892 < baseStart_2185892 := by decide
  rcases family_descends (prefixWord ++ tailWord_2185892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2185924 : List Nat := [2, 3, 3, 1, 1, 3, 2, 1, 6]
def baseStart_2185924 : Nat := 118140960795 + 2185924 * 2 ^ 59
def prefixEnd_2185924 : Nat := 4983230072969 + 3 ^ 40 * 2185924 * 2
def baseEnd_2185924 : Nat := 249428819155291287999361

theorem tailTrace_2185924 : CollatzResearch.WordTrace tailWord_2185924 prefixEnd_2185924 249428819155291287999361 := by
  unfold tailWord_2185924
  simp only [CollatzResearch.WordTrace]
  refine ⟨39863599066389074471150413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53151465421852099294867217 39863599066389074471150413)
  ·
    refine ⟨14948849649895902926681405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39863599066389074471150413 14948849649895902926681405)
    ·
      refine ⟨5605818618710963597505527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14948849649895902926681405 5605818618710963597505527)
      ·
        refine ⟨8408727928066445396258291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5605818618710963597505527 8408727928066445396258291)
        ·
          refine ⟨12613091892099668094387437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8408727928066445396258291 12613091892099668094387437)
          ·
            refine ⟨4729909459537375535395289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12613091892099668094387437 4729909459537375535395289)
            ·
              refine ⟨3547432094653031651546467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4729909459537375535395289 3547432094653031651546467)
              ·
                refine ⟨5321148141979547477319701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3547432094653031651546467 5321148141979547477319701)
                ·
                  refine ⟨249428819155291287999361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5321148141979547477319701 249428819155291287999361)
                  ·
                    rfl

theorem cell22_2185924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 2, 1, 6].length) (baseStart_2185924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2185924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2185924 prefixEnd_2185924 := by exact prefixLift 2185924
  have htrace : WordTrace (prefixWord ++ tailWord_2185924) baseStart_2185924 baseEnd_2185924 := by
    simpa [prefixWord, tailWord_2185924, baseEnd_2185924] using wordTrace_append hprefix tailTrace_2185924
  have hstable : (prefixWord ++ tailWord_2185924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2185924).length < 2 ^ (prefixWord ++ tailWord_2185924).sum := by decide
  have hdescent : baseEnd_2185924 < baseStart_2185924 := by decide
  rcases family_descends (prefixWord ++ tailWord_2185924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2186027 : List Nat := [1, 1, 1, 1, 2, 1, 2, 4, 5, 4]
def baseStart_2186027 : Nat := 118140960795 + 2186027 * 2 ^ 59
def prefixEnd_2186027 : Nat := 4983230072969 + 3 ^ 40 * 2186027 * 2
def baseEnd_2186027 : Nat := 748321716470815928672767

theorem tailTrace_2186027 : CollatzResearch.WordTrace tailWord_2186027 prefixEnd_2186027 748321716470815928672767 := by
  unfold tailWord_2186027
  simp only [CollatzResearch.WordTrace]
  refine ⟨79730954851404997533300335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53153969900936665022200223 79730954851404997533300335)
  ·
    refine ⟨119596432277107496299950503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79730954851404997533300335 119596432277107496299950503)
    ·
      refine ⟨179394648415661244449925755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119596432277107496299950503 179394648415661244449925755)
      ·
        refine ⟨269091972623491866674888633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 179394648415661244449925755 269091972623491866674888633)
        ·
          refine ⟨201818979467618900006166475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 269091972623491866674888633 201818979467618900006166475)
          ·
            refine ⟨302728469201428350009249713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 201818979467618900006166475 302728469201428350009249713)
            ·
              refine ⟨227046351901071262506937285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 302728469201428350009249713 227046351901071262506937285)
              ·
                refine ⟨42571190981450861720050741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 227046351901071262506937285 42571190981450861720050741)
                ·
                  refine ⟨3991049154511018286254757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 42571190981450861720050741 3991049154511018286254757)
                  ·
                    refine ⟨748321716470815928672767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3991049154511018286254757 748321716470815928672767)
                    ·
                      rfl

theorem cell22_2186027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 4, 5, 4].length) (baseStart_2186027 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2186027 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2186027 prefixEnd_2186027 := by exact prefixLift 2186027
  have htrace : WordTrace (prefixWord ++ tailWord_2186027) baseStart_2186027 baseEnd_2186027 := by
    simpa [prefixWord, tailWord_2186027, baseEnd_2186027] using wordTrace_append hprefix tailTrace_2186027
  have hstable : (prefixWord ++ tailWord_2186027).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2186027).length < 2 ^ (prefixWord ++ tailWord_2186027).sum := by decide
  have hdescent : baseEnd_2186027 < baseStart_2186027 := by decide
  rcases family_descends (prefixWord ++ tailWord_2186027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2186035 : List Nat := [1, 1, 1, 2, 6, 3, 2, 2, 1, 3]
def baseStart_2186035 : Nat := 118140960795 + 2186035 * 2 ^ 59
def prefixEnd_2186035 : Nat := 4983230072969 + 3 ^ 40 * 2186035 * 2
def baseEnd_2186035 : Nat := 748324455034306574472743

theorem tailTrace_2186035 : CollatzResearch.WordTrace tailWord_2186035 prefixEnd_2186035 748324455034306574472743 := by
  unfold tailWord_2186035
  simp only [CollatzResearch.WordTrace]
  refine ⟨79731246635376014899591559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53154164423584009933061039 79731246635376014899591559)
  ·
    refine ⟨119596869953064022349387339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79731246635376014899591559 119596869953064022349387339)
    ·
      refine ⟨179395304929596033524081009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119596869953064022349387339 179395304929596033524081009)
      ·
        refine ⟨134546478697197025143060757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 179395304929596033524081009 134546478697197025143060757)
        ·
          refine ⟨6306866188931110553580973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 134546478697197025143060757 6306866188931110553580973)
          ·
            refine ⟨2365074820849166457592865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6306866188931110553580973 2365074820849166457592865)
            ·
              refine ⟨1773806115636874843194649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2365074820849166457592865 1773806115636874843194649)
              ·
                refine ⟨1330354586727656132395987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1773806115636874843194649 1330354586727656132395987)
                ·
                  refine ⟨1995531880091484198593981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1330354586727656132395987 1995531880091484198593981)
                  ·
                    refine ⟨748324455034306574472743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1995531880091484198593981 748324455034306574472743)
                    ·
                      rfl

theorem cell22_2186035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 2, 2, 1, 3].length) (baseStart_2186035 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2186035 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2186035 prefixEnd_2186035 := by exact prefixLift 2186035
  have htrace : WordTrace (prefixWord ++ tailWord_2186035) baseStart_2186035 baseEnd_2186035 := by
    simpa [prefixWord, tailWord_2186035, baseEnd_2186035] using wordTrace_append hprefix tailTrace_2186035
  have hstable : (prefixWord ++ tailWord_2186035).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2186035).length < 2 ^ (prefixWord ++ tailWord_2186035).sum := by decide
  have hdescent : baseEnd_2186035 < baseStart_2186035 := by decide
  rcases family_descends (prefixWord ++ tailWord_2186035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2186046 : List Nat := [4, 2, 1, 2, 3, 1, 1, 1, 2, 5]
def baseStart_2186046 : Nat := 118140960795 + 2186046 * 2 ^ 59
def prefixEnd_2186046 : Nat := 4983230072969 + 3 ^ 40 * 2186046 * 2
def baseEnd_2186046 : Nat := 748328220559106212447709

theorem tailTrace_2186046 : CollatzResearch.WordTrace tailWord_2186046 prefixEnd_2186046 748328220559106212447709 := by
  unfold tailWord_2186046
  simp only [CollatzResearch.WordTrace]
  refine ⟨9966455979792020472280249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53154431892224109185494661 9966455979792020472280249)
  ·
    refine ⟨7474841984844015354210187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9966455979792020472280249 7474841984844015354210187)
    ·
      refine ⟨11212262977266023031315281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7474841984844015354210187 11212262977266023031315281)
      ·
        refine ⟨8409197232949517273486461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11212262977266023031315281 8409197232949517273486461)
        ·
          refine ⟨3153448962356068977557423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8409197232949517273486461 3153448962356068977557423)
          ·
            refine ⟨4730173443534103466336135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3153448962356068977557423 4730173443534103466336135)
            ·
              refine ⟨7095260165301155199504203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4730173443534103466336135 7095260165301155199504203)
              ·
                refine ⟨10642890247951732799256305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7095260165301155199504203 10642890247951732799256305)
                ·
                  refine ⟨7982167685963799599442229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10642890247951732799256305 7982167685963799599442229)
                  ·
                    refine ⟨748328220559106212447709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7982167685963799599442229 748328220559106212447709)
                    ·
                      rfl

theorem cell22_2186046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 1, 2, 5].length) (baseStart_2186046 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2186046 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2186046 prefixEnd_2186046 := by exact prefixLift 2186046
  have htrace : WordTrace (prefixWord ++ tailWord_2186046) baseStart_2186046 baseEnd_2186046 := by
    simpa [prefixWord, tailWord_2186046, baseEnd_2186046] using wordTrace_append hprefix tailTrace_2186046
  have hstable : (prefixWord ++ tailWord_2186046).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2186046).length < 2 ^ (prefixWord ++ tailWord_2186046).sum := by decide
  have hdescent : baseEnd_2186046 < baseStart_2186046 := by decide
  rcases family_descends (prefixWord ++ tailWord_2186046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2186074 : List Nat := [3, 1, 1, 2, 1, 4, 2, 2, 1, 5]
def baseStart_2186074 : Nat := 118140960795 + 2186074 * 2 ^ 59
def prefixEnd_2186074 : Nat := 4983230072969 + 3 ^ 40 * 2186074 * 2
def baseEnd_2186074 : Nat := 748337805531323472747623

theorem tailTrace_2186074 : CollatzResearch.WordTrace tailWord_2186074 prefixEnd_2186074 748337805531323472747623 := by
  unfold tailWord_2186074
  simp only [CollatzResearch.WordTrace]
  refine ⟨19933167270558681140065319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53155112721489816373507517 19933167270558681140065319)
  ·
    refine ⟨29899750905838021710097979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19933167270558681140065319 29899750905838021710097979)
    ·
      refine ⟨44849626358757032565146969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29899750905838021710097979 44849626358757032565146969)
      ·
        refine ⟨33637219769067774423860227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44849626358757032565146969 33637219769067774423860227)
        ·
          refine ⟨50455829653601661635790341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33637219769067774423860227 50455829653601661635790341)
          ·
            refine ⟨9460468060050311556710689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50455829653601661635790341 9460468060050311556710689)
            ·
              refine ⟨7095351045037733667533017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9460468060050311556710689 7095351045037733667533017)
              ·
                refine ⟨5321513283778300250649763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7095351045037733667533017 5321513283778300250649763)
                ·
                  refine ⟨7982269925667450375974645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5321513283778300250649763 7982269925667450375974645)
                  ·
                    refine ⟨748337805531323472747623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7982269925667450375974645 748337805531323472747623)
                    ·
                      rfl

theorem cell22_2186074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 2, 1, 5].length) (baseStart_2186074 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2186074 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2186074 prefixEnd_2186074 := by exact prefixLift 2186074
  have htrace : WordTrace (prefixWord ++ tailWord_2186074) baseStart_2186074 baseEnd_2186074 := by
    simpa [prefixWord, tailWord_2186074, baseEnd_2186074] using wordTrace_append hprefix tailTrace_2186074
  have hstable : (prefixWord ++ tailWord_2186074).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2186074).length < 2 ^ (prefixWord ++ tailWord_2186074).sum := by decide
  have hdescent : baseEnd_2186074 < baseStart_2186074 := by decide
  rcases family_descends (prefixWord ++ tailWord_2186074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2186091 : List Nat := [1, 1, 1, 1, 2, 2, 7, 2, 2, 3]
def baseStart_2186091 : Nat := 118140960795 + 2186091 * 2 ^ 59
def prefixEnd_2186091 : Nat := 4983230072969 + 3 ^ 40 * 2186091 * 2
def baseEnd_2186091 : Nat := 748343624978741095072571

theorem tailTrace_2186091 : CollatzResearch.WordTrace tailWord_2186091 prefixEnd_2186091 748343624978741095072571 := by
  unfold tailWord_2186091
  simp only [CollatzResearch.WordTrace]
  refine ⟨79733289123173136463630127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53155526082115424309086751 79733289123173136463630127)
  ·
    refine ⟨119599933684759704695445191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79733289123173136463630127 119599933684759704695445191)
    ·
      refine ⟨179399900527139557043167787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119599933684759704695445191 179399900527139557043167787)
      ·
        refine ⟨269099850790709335564751681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 179399900527139557043167787 269099850790709335564751681)
        ·
          refine ⟨201824888093032001673563761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 269099850790709335564751681 201824888093032001673563761)
          ·
            refine ⟨151368666069774001255172821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 201824888093032001673563761 151368666069774001255172821)
            ·
              refine ⟨3547703111010328154418113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 151368666069774001255172821 3547703111010328154418113)
              ·
                refine ⟨2660777333257746115813585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3547703111010328154418113 2660777333257746115813585)
                ·
                  refine ⟨1995582999943309586860189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2660777333257746115813585 1995582999943309586860189)
                  ·
                    refine ⟨748343624978741095072571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1995582999943309586860189 748343624978741095072571)
                    ·
                      rfl

theorem cell22_2186091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 7, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 7, 2, 2, 3].length) (baseStart_2186091 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2186091 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2186091 prefixEnd_2186091 := by exact prefixLift 2186091
  have htrace : WordTrace (prefixWord ++ tailWord_2186091) baseStart_2186091 baseEnd_2186091 := by
    simpa [prefixWord, tailWord_2186091, baseEnd_2186091] using wordTrace_append hprefix tailTrace_2186091
  have hstable : (prefixWord ++ tailWord_2186091).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2186091).length < 2 ^ (prefixWord ++ tailWord_2186091).sum := by decide
  have hdescent : baseEnd_2186091 < baseStart_2186091 := by decide
  rcases family_descends (prefixWord ++ tailWord_2186091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2186121 : List Nat := [1, 2, 1, 1, 5, 4, 2, 6]
def baseStart_2186121 : Nat := 118140960795 + 2186121 * 2 ^ 59
def prefixEnd_2186121 : Nat := 4983230072969 + 3 ^ 40 * 2186121 * 2
def baseEnd_2186121 : Nat := 83150432732425668535831

theorem tailTrace_2186121 : CollatzResearch.WordTrace tailWord_2186121 prefixEnd_2186121 83150432732425668535831 := by
  unfold tailWord_2186121
  simp only [CollatzResearch.WordTrace]
  refine ⟨79734383313064451587222217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53156255542042967724814811 79734383313064451587222217)
  ·
    refine ⟨59800787484798338690416663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79734383313064451587222217 59800787484798338690416663)
    ·
      refine ⟨89701181227197508035624995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59800787484798338690416663 89701181227197508035624995)
      ·
        refine ⟨134551771840796262053437493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89701181227197508035624995 134551771840796262053437493)
        ·
          refine ⟨12614228610074649567509765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 134551771840796262053437493 12614228610074649567509765)
          ·
            refine ⟨2365167864388996793908081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12614228610074649567509765 2365167864388996793908081)
            ·
              refine ⟨1773875898291747595431061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2365167864388996793908081 1773875898291747595431061)
              ·
                refine ⟨83150432732425668535831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1773875898291747595431061 83150432732425668535831)
                ·
                  rfl

theorem cell22_2186121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 2, 6].length) (baseStart_2186121 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2186121 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2186121 prefixEnd_2186121 := by exact prefixLift 2186121
  have htrace : WordTrace (prefixWord ++ tailWord_2186121) baseStart_2186121 baseEnd_2186121 := by
    simpa [prefixWord, tailWord_2186121, baseEnd_2186121] using wordTrace_append hprefix tailTrace_2186121
  have hstable : (prefixWord ++ tailWord_2186121).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2186121).length < 2 ^ (prefixWord ++ tailWord_2186121).sum := by decide
  have hdescent : baseEnd_2186121 < baseStart_2186121 := by decide
  rcases family_descends (prefixWord ++ tailWord_2186121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2186179 : List Nat := [1, 1, 1, 3, 1, 1, 2, 5, 3, 4]
def baseStart_2186179 : Nat := 118140960795 + 2186179 * 2 ^ 59
def prefixEnd_2186179 : Nat := 4983230072969 + 3 ^ 40 * 2186179 * 2
def baseEnd_2186179 : Nat := 748373749177138198872301

theorem tailTrace_2186179 : CollatzResearch.WordTrace tailWord_2186179 prefixEnd_2186179 748373749177138198872301 := by
  unfold tailWord_2186179
  simp only [CollatzResearch.WordTrace]
  refine ⟨79736498746854327492833591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53157665831236218328555727 79736498746854327492833591)
  ·
    refine ⟨119604748120281491239250387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79736498746854327492833591 119604748120281491239250387)
    ·
      refine ⟨179407122180422236858875581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119604748120281491239250387 179407122180422236858875581)
      ·
        refine ⟨67277670817658338822078343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 179407122180422236858875581 67277670817658338822078343)
        ·
          refine ⟨100916506226487508233117515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67277670817658338822078343 100916506226487508233117515)
          ·
            refine ⟨151374759339731262349676273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100916506226487508233117515 151374759339731262349676273)
            ·
              refine ⟨113531069504798446762257205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 151374759339731262349676273 113531069504798446762257205)
              ·
                refine ⟨10643537766074854383961613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 113531069504798446762257205 10643537766074854383961613)
                ·
                  refine ⟨3991326662278070393985605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10643537766074854383961613 3991326662278070393985605)
                  ·
                    refine ⟨748373749177138198872301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3991326662278070393985605 748373749177138198872301)
                    ·
                      rfl

theorem cell22_2186179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 5, 3, 4].length) (baseStart_2186179 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2186179 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2186179 prefixEnd_2186179 := by exact prefixLift 2186179
  have htrace : WordTrace (prefixWord ++ tailWord_2186179) baseStart_2186179 baseEnd_2186179 := by
    simpa [prefixWord, tailWord_2186179, baseEnd_2186179] using wordTrace_append hprefix tailTrace_2186179
  have hstable : (prefixWord ++ tailWord_2186179).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2186179).length < 2 ^ (prefixWord ++ tailWord_2186179).sum := by decide
  have hdescent : baseEnd_2186179 < baseStart_2186179 := by decide
  rcases family_descends (prefixWord ++ tailWord_2186179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2186209 : List Nat := [1, 2, 3, 1, 2, 1, 1, 1, 5, 5]
def baseStart_2186209 : Nat := 118140960795 + 2186209 * 2 ^ 59
def prefixEnd_2186209 : Nat := 4983230072969 + 3 ^ 40 * 2186209 * 2
def baseEnd_2186209 : Nat := 748384018790228120622209

theorem tailTrace_2186209 : CollatzResearch.WordTrace tailWord_2186209 prefixEnd_2186209 748384018790228120622209 := by
  unfold tailWord_2186209
  simp only [CollatzResearch.WordTrace]
  refine ⟨79737592936745642616425681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53158395291163761744283787 79737592936745642616425681)
  ·
    refine ⟨59803194702559231962319261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79737592936745642616425681 59803194702559231962319261)
    ·
      refine ⟨22426198013459711985869723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59803194702559231962319261 22426198013459711985869723)
      ·
        refine ⟨33639297020189567978804585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22426198013459711985869723 33639297020189567978804585)
        ·
          refine ⟨25229472765142175984103439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33639297020189567978804585 25229472765142175984103439)
          ·
            refine ⟨37844209147713263976155159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25229472765142175984103439 37844209147713263976155159)
            ·
              refine ⟨56766313721569895964232739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37844209147713263976155159 56766313721569895964232739)
              ·
                refine ⟨85149470582354843946349109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56766313721569895964232739 85149470582354843946349109)
                ·
                  refine ⟨7982762867095766619970229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 85149470582354843946349109 7982762867095766619970229)
                  ·
                    refine ⟨748384018790228120622209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7982762867095766619970229 748384018790228120622209)
                    ·
                      rfl

theorem cell22_2186209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 1, 5, 5].length) (baseStart_2186209 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2186209 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2186209 prefixEnd_2186209 := by exact prefixLift 2186209
  have htrace : WordTrace (prefixWord ++ tailWord_2186209) baseStart_2186209 baseEnd_2186209 := by
    simpa [prefixWord, tailWord_2186209, baseEnd_2186209] using wordTrace_append hprefix tailTrace_2186209
  have hstable : (prefixWord ++ tailWord_2186209).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2186209).length < 2 ^ (prefixWord ++ tailWord_2186209).sum := by decide
  have hdescent : baseEnd_2186209 < baseStart_2186209 := by decide
  rcases family_descends (prefixWord ++ tailWord_2186209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2186224 : List Nat := [2, 1, 1, 1, 3, 2, 1, 4, 1, 6]
def baseStart_2186224 : Nat := 118140960795 + 2186224 * 2 ^ 59
def prefixEnd_2186224 : Nat := 4983230072969 + 3 ^ 40 * 2186224 * 2
def baseEnd_2186224 : Nat := 748389153596773081497163

theorem tailTrace_2186224 : CollatzResearch.WordTrace tailWord_2186224 prefixEnd_2186224 748389153596773081497163 := by
  unfold tailWord_2186224
  simp only [CollatzResearch.WordTrace]
  refine ⟨39869070015845650089110863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53158760021127533452147817 39869070015845650089110863)
  ·
    refine ⟨59803605023768475133666295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39869070015845650089110863 59803605023768475133666295)
    ·
      refine ⟨89705407535652712700499443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59803605023768475133666295 89705407535652712700499443)
      ·
        refine ⟨134558111303479069050749165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89705407535652712700499443 134558111303479069050749165)
        ·
          refine ⟨50459291738804650894030937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 134558111303479069050749165 50459291738804650894030937)
          ·
            refine ⟨37844468804103488170523203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50459291738804650894030937 37844468804103488170523203)
            ·
              refine ⟨56766703206155232255784805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37844468804103488170523203 56766703206155232255784805)
              ·
                refine ⟨10643756851154106047959651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 56766703206155232255784805 10643756851154106047959651)
                ·
                  refine ⟨15965635276731159071939477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10643756851154106047959651 15965635276731159071939477)
                  ·
                    refine ⟨748389153596773081497163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15965635276731159071939477 748389153596773081497163)
                    ·
                      rfl

theorem cell22_2186224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 4, 1, 6].length) (baseStart_2186224 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2186224 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2186224 prefixEnd_2186224 := by exact prefixLift 2186224
  have htrace : WordTrace (prefixWord ++ tailWord_2186224) baseStart_2186224 baseEnd_2186224 := by
    simpa [prefixWord, tailWord_2186224, baseEnd_2186224] using wordTrace_append hprefix tailTrace_2186224
  have hstable : (prefixWord ++ tailWord_2186224).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2186224).length < 2 ^ (prefixWord ++ tailWord_2186224).sum := by decide
  have hdescent : baseEnd_2186224 < baseStart_2186224 := by decide
  rcases family_descends (prefixWord ++ tailWord_2186224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2186241 : List Nat := [1, 2, 4, 1, 2, 3, 1, 1, 1, 6]
def baseStart_2186241 : Nat := 118140960795 + 2186241 * 2 ^ 59
def prefixEnd_2186241 : Nat := 4983230072969 + 3 ^ 40 * 2186241 * 2
def baseEnd_2186241 : Nat := 748394973044190703822111

theorem tailTrace_2186241 : CollatzResearch.WordTrace tailWord_2186241 prefixEnd_2186241 748394973044190703822111 := by
  unfold tailWord_2186241
  simp only [CollatzResearch.WordTrace]
  refine ⟨79738760072629712081590577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53159173381753141387727051 79738760072629712081590577)
  ·
    refine ⟨59804070054472284061192933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79738760072629712081590577 59804070054472284061192933)
    ·
      refine ⟨11213263135213553261473675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 59804070054472284061192933 11213263135213553261473675)
      ·
        refine ⟨16819894702820329892210513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11213263135213553261473675 16819894702820329892210513)
        ·
          refine ⟨12614921027115247419157885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16819894702820329892210513 12614921027115247419157885)
          ·
            refine ⟨4730595385168217782184207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12614921027115247419157885 4730595385168217782184207)
            ·
              refine ⟨7095893077752326673276311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4730595385168217782184207 7095893077752326673276311)
              ·
                refine ⟨10643839616628490009914467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7095893077752326673276311 10643839616628490009914467)
                ·
                  refine ⟨15965759424942735014871701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10643839616628490009914467 15965759424942735014871701)
                  ·
                    refine ⟨748394973044190703822111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15965759424942735014871701 748394973044190703822111)
                    ·
                      rfl

theorem cell22_2186241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 1, 1, 6].length) (baseStart_2186241 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2186241 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2186241 prefixEnd_2186241 := by exact prefixLift 2186241
  have htrace : WordTrace (prefixWord ++ tailWord_2186241) baseStart_2186241 baseEnd_2186241 := by
    simpa [prefixWord, tailWord_2186241, baseEnd_2186241] using wordTrace_append hprefix tailTrace_2186241
  have hstable : (prefixWord ++ tailWord_2186241).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2186241).length < 2 ^ (prefixWord ++ tailWord_2186241).sum := by decide
  have hdescent : baseEnd_2186241 < baseStart_2186241 := by decide
  rcases family_descends (prefixWord ++ tailWord_2186241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2186301 : List Nat := [1, 4, 1, 3, 1, 2, 1, 2, 7]
def baseStart_2186301 : Nat := 118140960795 + 2186301 * 2 ^ 59
def prefixEnd_2186301 : Nat := 4983230072969 + 3 ^ 40 * 2186301 * 2
def baseEnd_2186301 : Nat := 249471837423456849107309

theorem tailTrace_2186301 : CollatzResearch.WordTrace tailWord_2186301 prefixEnd_2186301 249471837423456849107309 := by
  unfold tailWord_2186301
  simp only [CollatzResearch.WordTrace]
  refine ⟨79740948452412342328774757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53160632301608228219183171 79740948452412342328774757)
  ·
    refine ⟨14951427834827314186645267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 79740948452412342328774757 14951427834827314186645267)
    ·
      refine ⟨22427141752240971279967901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14951427834827314186645267 22427141752240971279967901)
      ·
        refine ⟨8410178157090364229987963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22427141752240971279967901 8410178157090364229987963)
        ·
          refine ⟨12615267235635546344981945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8410178157090364229987963 12615267235635546344981945)
          ·
            refine ⟨9461450426726659758736459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12615267235635546344981945 9461450426726659758736459)
            ·
              refine ⟨14192175640089989638104689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9461450426726659758736459 14192175640089989638104689)
              ·
                refine ⟨10644131730067492228578517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14192175640089989638104689 10644131730067492228578517)
                ·
                  refine ⟨249471837423456849107309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10644131730067492228578517 249471837423456849107309)
                  ·
                    rfl

theorem cell22_2186301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 2, 7].length) (baseStart_2186301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2186301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2186301 prefixEnd_2186301 := by exact prefixLift 2186301
  have htrace : WordTrace (prefixWord ++ tailWord_2186301) baseStart_2186301 baseEnd_2186301 := by
    simpa [prefixWord, tailWord_2186301, baseEnd_2186301] using wordTrace_append hprefix tailTrace_2186301
  have hstable : (prefixWord ++ tailWord_2186301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2186301).length < 2 ^ (prefixWord ++ tailWord_2186301).sum := by decide
  have hdescent : baseEnd_2186301 < baseStart_2186301 := by decide
  rcases family_descends (prefixWord ++ tailWord_2186301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2186365 : List Nat := [1, 4, 1, 1, 3, 1, 5, 1, 1, 4]
def baseStart_2186365 : Nat := 118140960795 + 2186365 * 2 ^ 59
def prefixEnd_2186365 : Nat := 4983230072969 + 3 ^ 40 * 2186365 * 2
def baseEnd_2186365 : Nat := 748437420778295713721731

theorem tailTrace_2186365 : CollatzResearch.WordTrace tailWord_2186365 prefixEnd_2186365 748437420778295713721731 := by
  unfold tailWord_2186365
  simp only [CollatzResearch.WordTrace]
  refine ⟨79743282724180481259104549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53162188482786987506069699 79743282724180481259104549)
  ·
    refine ⟨14951865510783840236082103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 79743282724180481259104549 14951865510783840236082103)
    ·
      refine ⟨22427798266175760354123155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14951865510783840236082103 22427798266175760354123155)
      ·
        refine ⟨33641697399263640531184733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22427798266175760354123155 33641697399263640531184733)
        ·
          refine ⟨12615636524723865199194275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33641697399263640531184733 12615636524723865199194275)
          ·
            refine ⟨18923454787085797798791413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12615636524723865199194275 18923454787085797798791413)
            ·
              refine ⟨1774073886289293543636695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18923454787085797798791413 1774073886289293543636695)
              ·
                refine ⟨2661110829433940315455043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1774073886289293543636695 2661110829433940315455043)
                ·
                  refine ⟨3991666244150910473182565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2661110829433940315455043 3991666244150910473182565)
                  ·
                    refine ⟨748437420778295713721731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3991666244150910473182565 748437420778295713721731)
                    ·
                      rfl

theorem cell22_2186365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 5, 1, 1, 4].length) (baseStart_2186365 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2186365 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2186365 prefixEnd_2186365 := by exact prefixLift 2186365
  have htrace : WordTrace (prefixWord ++ tailWord_2186365) baseStart_2186365 baseEnd_2186365 := by
    simpa [prefixWord, tailWord_2186365, baseEnd_2186365] using wordTrace_append hprefix tailTrace_2186365
  have hstable : (prefixWord ++ tailWord_2186365).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2186365).length < 2 ^ (prefixWord ++ tailWord_2186365).sum := by decide
  have hdescent : baseEnd_2186365 < baseStart_2186365 := by decide
  rcases family_descends (prefixWord ++ tailWord_2186365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2186410 : List Nat := [3, 1, 5, 1, 1, 2, 1, 1, 1, 6]
def baseStart_2186410 : Nat := 118140960795 + 2186410 * 2 ^ 59
def prefixEnd_2186410 : Nat := 4983230072969 + 3 ^ 40 * 2186410 * 2
def baseEnd_2186410 : Nat := 748452825197930596346593

theorem tailTrace_2186410 : CollatzResearch.WordTrace tailWord_2186410 prefixEnd_2186410 748452825197930596346593 := by
  unfold tailWord_2186410
  simp only [CollatzResearch.WordTrace]
  refine ⟨19936231002254363486123171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53163282672678302629661789 19936231002254363486123171)
  ·
    refine ⟨29904346503381545229184757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19936231002254363486123171 29904346503381545229184757)
    ·
      refine ⟨2803532484692019865236071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 29904346503381545229184757 2803532484692019865236071)
      ·
        refine ⟨4205298727038029797854107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2803532484692019865236071 4205298727038029797854107)
        ·
          refine ⟨6307948090557044696781161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4205298727038029797854107 6307948090557044696781161)
          ·
            refine ⟨4730961067917783522585871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6307948090557044696781161 4730961067917783522585871)
            ·
              refine ⟨7096441601876675283878807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4730961067917783522585871 7096441601876675283878807)
              ·
                refine ⟨10644662402815012925818211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7096441601876675283878807 10644662402815012925818211)
                ·
                  refine ⟨15966993604222519388727317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10644662402815012925818211 15966993604222519388727317)
                  ·
                    refine ⟨748452825197930596346593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15966993604222519388727317 748452825197930596346593)
                    ·
                      rfl

theorem cell22_2186410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_2186410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2186410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2186410 prefixEnd_2186410 := by exact prefixLift 2186410
  have htrace : WordTrace (prefixWord ++ tailWord_2186410) baseStart_2186410 baseEnd_2186410 := by
    simpa [prefixWord, tailWord_2186410, baseEnd_2186410] using wordTrace_append hprefix tailTrace_2186410
  have hstable : (prefixWord ++ tailWord_2186410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2186410).length < 2 ^ (prefixWord ++ tailWord_2186410).sum := by decide
  have hdescent : baseEnd_2186410 < baseStart_2186410 := by decide
  rcases family_descends (prefixWord ++ tailWord_2186410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2186423 : List Nat := [1, 1, 3, 1, 4, 1, 1, 2, 5, 3]
def baseStart_2186423 : Nat := 118140960795 + 2186423 * 2 ^ 59
def prefixEnd_2186423 : Nat := 4983230072969 + 3 ^ 40 * 2186423 * 2
def baseEnd_2186423 : Nat := 748457275363602895771553

theorem tailTrace_2186423 : CollatzResearch.WordTrace tailWord_2186423 prefixEnd_2186423 748457275363602895771553 := by
  unfold tailWord_2186423
  simp only [CollatzResearch.WordTrace]
  refine ⟨79745398157970357164715923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53163598771980238109810615 79745398157970357164715923)
  ·
    refine ⟨119618097236955535747073885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79745398157970357164715923 119618097236955535747073885)
    ·
      refine ⟨44856786463858325905152707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 119618097236955535747073885 44856786463858325905152707)
      ·
        refine ⟨67285179695787488857729061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44856786463858325905152707 67285179695787488857729061)
        ·
          refine ⟨12615971192960154160824199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 67285179695787488857729061 12615971192960154160824199)
          ·
            refine ⟨18923956789440231241236299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12615971192960154160824199 18923956789440231241236299)
            ·
              refine ⟨28385935184160346861854449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18923956789440231241236299 28385935184160346861854449)
              ·
                refine ⟨21289451388120260146390837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28385935184160346861854449 21289451388120260146390837)
                ·
                  refine ⟨1995886067636274388724141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21289451388120260146390837 1995886067636274388724141)
                  ·
                    refine ⟨748457275363602895771553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1995886067636274388724141 748457275363602895771553)
                    ·
                      rfl

theorem cell22_2186423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 2, 5, 3].length) (baseStart_2186423 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2186423 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2186423 prefixEnd_2186423 := by exact prefixLift 2186423
  have htrace : WordTrace (prefixWord ++ tailWord_2186423) baseStart_2186423 baseEnd_2186423 := by
    simpa [prefixWord, tailWord_2186423, baseEnd_2186423] using wordTrace_append hprefix tailTrace_2186423
  have hstable : (prefixWord ++ tailWord_2186423).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2186423).length < 2 ^ (prefixWord ++ tailWord_2186423).sum := by decide
  have hdescent : baseEnd_2186423 < baseStart_2186423 := by decide
  rcases family_descends (prefixWord ++ tailWord_2186423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2186474 : List Nat := [3, 1, 3, 1, 1, 5, 1, 3, 1, 3]
def baseStart_2186474 : Nat := 118140960795 + 2186474 * 2 ^ 59
def prefixEnd_2186474 : Nat := 4983230072969 + 3 ^ 40 * 2186474 * 2
def baseEnd_2186474 : Nat := 748474733705855762746397

theorem tailTrace_2186474 : CollatzResearch.WordTrace tailWord_2186474 prefixEnd_2186474 748474733705855762746397 := by
  unfold tailWord_2186474
  simp only [CollatzResearch.WordTrace]
  refine ⟨19936814570196398218705619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53164838853857061916548317 19936814570196398218705619)
  ·
    refine ⟨29905221855294597328058429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19936814570196398218705619 29905221855294597328058429)
    ·
      refine ⟨11214458195735473998021911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29905221855294597328058429 11214458195735473998021911)
      ·
        refine ⟨16821687293603210997032867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11214458195735473998021911 16821687293603210997032867)
        ·
          refine ⟨25232530940404816495549301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16821687293603210997032867 25232530940404816495549301)
          ·
            refine ⟨2365549775662951546457747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 25232530940404816495549301 2365549775662951546457747)
            ·
              refine ⟨3548324663494427319686621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2365549775662951546457747 3548324663494427319686621)
              ·
                refine ⟨1330621748810410244882483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3548324663494427319686621 1330621748810410244882483)
                ·
                  refine ⟨1995932623215615367323725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1330621748810410244882483 1995932623215615367323725)
                  ·
                    refine ⟨748474733705855762746397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1995932623215615367323725 748474733705855762746397)
                    ·
                      rfl

theorem cell22_2186474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 1, 3, 1, 3].length) (baseStart_2186474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2186474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2186474 prefixEnd_2186474 := by exact prefixLift 2186474
  have htrace : WordTrace (prefixWord ++ tailWord_2186474) baseStart_2186474 baseEnd_2186474 := by
    simpa [prefixWord, tailWord_2186474, baseEnd_2186474] using wordTrace_append hprefix tailTrace_2186474
  have hstable : (prefixWord ++ tailWord_2186474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2186474).length < 2 ^ (prefixWord ++ tailWord_2186474).sum := by decide
  have hdescent : baseEnd_2186474 < baseStart_2186474 := by decide
  rcases family_descends (prefixWord ++ tailWord_2186474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2186504 : List Nat := [2, 1, 3, 2, 5, 1, 2, 1, 5]
def baseStart_2186504 : Nat := 118140960795 + 2186504 * 2 ^ 59
def prefixEnd_2186504 : Nat := 4983230072969 + 3 ^ 40 * 2186504 * 2
def baseEnd_2186504 : Nat := 249495001106315228165435

theorem tailTrace_2186504 : CollatzResearch.WordTrace tailWord_2186504 prefixEnd_2186504 249495001106315228165435 := by
  unfold tailWord_2186504
  simp only [CollatzResearch.WordTrace]
  refine ⟨39874176235338453999207283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53165568313784605332276377 39874176235338453999207283)
  ·
    refine ⟨59811264353007680998810925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39874176235338453999207283 59811264353007680998810925)
    ·
      refine ⟨22429224132377880374554097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59811264353007680998810925 22429224132377880374554097)
      ·
        refine ⟨16821918099283410280915573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22429224132377880374554097 16821918099283410280915573)
        ·
          refine ⟨1577054821807819713835835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16821918099283410280915573 1577054821807819713835835)
          ·
            refine ⟨2365582232711729570753753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1577054821807819713835835 2365582232711729570753753)
            ·
              refine ⟨1774186674533797178065315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2365582232711729570753753 1774186674533797178065315)
              ·
                refine ⟨2661280011800695767097973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1774186674533797178065315 2661280011800695767097973)
                ·
                  refine ⟨249495001106315228165435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2661280011800695767097973 249495001106315228165435)
                  ·
                    rfl

theorem cell22_2186504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 2, 1, 5].length) (baseStart_2186504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2186504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2186504 prefixEnd_2186504 := by exact prefixLift 2186504
  have htrace : WordTrace (prefixWord ++ tailWord_2186504) baseStart_2186504 baseEnd_2186504 := by
    simpa [prefixWord, tailWord_2186504, baseEnd_2186504] using wordTrace_append hprefix tailTrace_2186504
  have hstable : (prefixWord ++ tailWord_2186504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2186504).length < 2 ^ (prefixWord ++ tailWord_2186504).sum := by decide
  have hdescent : baseEnd_2186504 < baseStart_2186504 := by decide
  rcases family_descends (prefixWord ++ tailWord_2186504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2186513 : List Nat := [1, 2, 2, 1, 1, 4, 2, 3, 1, 5]
def baseStart_2186513 : Nat := 118140960795 + 2186513 * 2 ^ 59
def prefixEnd_2186513 : Nat := 4983230072969 + 3 ^ 40 * 2186513 * 2
def baseEnd_2186513 : Nat := 748488084202872661021277

theorem tailTrace_2186513 : CollatzResearch.WordTrace tailWord_2186513 prefixEnd_2186513 748488084202872661021277 := by
  unfold tailWord_2186513
  simp only [CollatzResearch.WordTrace]
  refine ⟨79748680727644302535492193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53165787151762868356994795 79748680727644302535492193)
  ·
    refine ⟨59811510545733226901619145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79748680727644302535492193 59811510545733226901619145)
    ·
      refine ⟨44858632909299920176214359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59811510545733226901619145 44858632909299920176214359)
      ·
        refine ⟨67287949363949880264321539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44858632909299920176214359 67287949363949880264321539)
        ·
          refine ⟨100931924045924820396482309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67287949363949880264321539 100931924045924820396482309)
          ·
            refine ⟨18924735758610903824340433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 100931924045924820396482309 18924735758610903824340433)
            ·
              refine ⟨14193551818958177868255325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18924735758610903824340433 14193551818958177868255325)
              ·
                refine ⟨5322581932109316700595747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14193551818958177868255325 5322581932109316700595747)
                ·
                  refine ⟨7983872898163975050893621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5322581932109316700595747 7983872898163975050893621)
                  ·
                    refine ⟨748488084202872661021277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7983872898163975050893621 748488084202872661021277)
                    ·
                      rfl

theorem cell22_2186513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 5].length) (baseStart_2186513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2186513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2186513 prefixEnd_2186513 := by exact prefixLift 2186513
  have htrace : WordTrace (prefixWord ++ tailWord_2186513) baseStart_2186513 baseEnd_2186513 := by
    simpa [prefixWord, tailWord_2186513, baseEnd_2186513] using wordTrace_append hprefix tailTrace_2186513
  have hstable : (prefixWord ++ tailWord_2186513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2186513).length < 2 ^ (prefixWord ++ tailWord_2186513).sum := by decide
  have hdescent : baseEnd_2186513 < baseStart_2186513 := by decide
  rcases family_descends (prefixWord ++ tailWord_2186513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2186545 : List Nat := [1, 2, 2, 3, 3, 1, 2, 2, 2, 4]
def baseStart_2186545 : Nat := 118140960795 + 2186545 * 2 ^ 59
def prefixEnd_2186545 : Nat := 4983230072969 + 3 ^ 40 * 2186545 * 2
def baseEnd_2186545 : Nat := 748499038456835244221179

theorem tailTrace_2186545 : CollatzResearch.WordTrace tailWord_2186545 prefixEnd_2186545 748499038456835244221179 := by
  unfold tailWord_2186545
  simp only [CollatzResearch.WordTrace]
  refine ⟨79749847863528372000657089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53166565242352248000438059 79749847863528372000657089)
  ·
    refine ⟨59812385897646279000492817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79749847863528372000657089 59812385897646279000492817)
    ·
      refine ⟨44859289423234709250369613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59812385897646279000492817 44859289423234709250369613)
      ·
        refine ⟨16822233533713015968888605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44859289423234709250369613 16822233533713015968888605)
        ·
          refine ⟨6308337575142380988333227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16822233533713015968888605 6308337575142380988333227)
          ·
            refine ⟨9462506362713571482499841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6308337575142380988333227 9462506362713571482499841)
            ·
              refine ⟨7096879772035178611874881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9462506362713571482499841 7096879772035178611874881)
              ·
                refine ⟨5322659829026383958906161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7096879772035178611874881 5322659829026383958906161)
                ·
                  refine ⟨3991994871769787969179621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5322659829026383958906161 3991994871769787969179621)
                  ·
                    refine ⟨748499038456835244221179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3991994871769787969179621 748499038456835244221179)
                    ·
                      rfl

theorem cell22_2186545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 2, 2, 4].length) (baseStart_2186545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2186545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2186545 prefixEnd_2186545 := by exact prefixLift 2186545
  have htrace : WordTrace (prefixWord ++ tailWord_2186545) baseStart_2186545 baseEnd_2186545 := by
    simpa [prefixWord, tailWord_2186545, baseEnd_2186545] using wordTrace_append hprefix tailTrace_2186545
  have hstable : (prefixWord ++ tailWord_2186545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2186545).length < 2 ^ (prefixWord ++ tailWord_2186545).sum := by decide
  have hdescent : baseEnd_2186545 < baseStart_2186545 := by decide
  rcases family_descends (prefixWord ++ tailWord_2186545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2186547 : List Nat := [1, 1, 1, 2, 5, 3, 2, 2, 2, 3]
def baseStart_2186547 : Nat := 118140960795 + 2186547 * 2 ^ 59
def prefixEnd_2186547 : Nat := 4983230072969 + 3 ^ 40 * 2186547 * 2
def baseEnd_2186547 : Nat := 748499723097707905671173

theorem tailTrace_2186547 : CollatzResearch.WordTrace tailWord_2186547 prefixEnd_2186547 748499723097707905671173 := by
  unfold tailWord_2186547
  simp only [CollatzResearch.WordTrace]
  refine ⟨79749920809521126342229895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53166613873014084228153263 79749920809521126342229895)
  ·
    refine ⟨119624881214281689513344843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79749920809521126342229895 119624881214281689513344843)
    ·
      refine ⟨179437321821422534270017265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119624881214281689513344843 179437321821422534270017265)
      ·
        refine ⟨134577991366066900702512949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 179437321821422534270017265 134577991366066900702512949)
        ·
          refine ⟨12616686690568771940860589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 134577991366066900702512949 12616686690568771940860589)
          ·
            refine ⟨4731257508963289477822721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12616686690568771940860589 4731257508963289477822721)
            ·
              refine ⟨3548443131722467108367041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4731257508963289477822721 3548443131722467108367041)
              ·
                refine ⟨2661332348791850331275281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3548443131722467108367041 2661332348791850331275281)
                ·
                  refine ⟨1995999261593887748456461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2661332348791850331275281 1995999261593887748456461)
                  ·
                    refine ⟨748499723097707905671173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1995999261593887748456461 748499723097707905671173)
                    ·
                      rfl

theorem cell22_2186547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 2, 2, 2, 3].length) (baseStart_2186547 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2186547 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2186547 prefixEnd_2186547 := by exact prefixLift 2186547
  have htrace : WordTrace (prefixWord ++ tailWord_2186547) baseStart_2186547 baseEnd_2186547 := by
    simpa [prefixWord, tailWord_2186547, baseEnd_2186547] using wordTrace_append hprefix tailTrace_2186547
  have hstable : (prefixWord ++ tailWord_2186547).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2186547).length < 2 ^ (prefixWord ++ tailWord_2186547).sum := by decide
  have hdescent : baseEnd_2186547 < baseStart_2186547 := by decide
  rcases family_descends (prefixWord ++ tailWord_2186547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2186549 : List Nat := [1, 3, 3, 1, 2, 4, 2, 2, 4]
def baseStart_2186549 : Nat := 118140960795 + 2186549 * 2 ^ 59
def prefixEnd_2186549 : Nat := 4983230072969 + 3 ^ 40 * 2186549 * 2
def baseEnd_2186549 : Nat := 249500135912860189040389

theorem tailTrace_2186549 : CollatzResearch.WordTrace tailWord_2186549 prefixEnd_2186549 249500135912860189040389 := by
  unfold tailWord_2186549
  simp only [CollatzResearch.WordTrace]
  refine ⟨79749993755513880683802701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53166662503675920455868467 79749993755513880683802701)
  ·
    refine ⟨29906247658317705256426013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79749993755513880683802701 29906247658317705256426013)
    ·
      refine ⟨11214842871869139471159755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29906247658317705256426013 11214842871869139471159755)
      ·
        refine ⟨16822264307803709206739633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11214842871869139471159755 16822264307803709206739633)
        ·
          refine ⟨12616698230852781905054725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16822264307803709206739633 12616698230852781905054725)
          ·
            refine ⟨2365630918284896607197761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12616698230852781905054725 2365630918284896607197761)
            ·
              refine ⟨1774223188713672455398321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2365630918284896607197761 1774223188713672455398321)
              ·
                refine ⟨1330667391535254341548741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1774223188713672455398321 1330667391535254341548741)
                ·
                  refine ⟨249500135912860189040389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1330667391535254341548741 249500135912860189040389)
                  ·
                    rfl

theorem cell22_2186549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 2, 2, 4].length) (baseStart_2186549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2186549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2186549 prefixEnd_2186549 := by exact prefixLift 2186549
  have htrace : WordTrace (prefixWord ++ tailWord_2186549) baseStart_2186549 baseEnd_2186549 := by
    simpa [prefixWord, tailWord_2186549, baseEnd_2186549] using wordTrace_append hprefix tailTrace_2186549
  have hstable : (prefixWord ++ tailWord_2186549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2186549).length < 2 ^ (prefixWord ++ tailWord_2186549).sum := by decide
  have hdescent : baseEnd_2186549 < baseStart_2186549 := by decide
  rcases family_descends (prefixWord ++ tailWord_2186549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2186564 : List Nat := [2, 3, 4, 1, 1, 1, 2, 3, 2, 3]
def baseStart_2186564 : Nat := 118140960795 + 2186564 * 2 ^ 59
def prefixEnd_2186564 : Nat := 4983230072969 + 3 ^ 40 * 2186564 * 2
def baseEnd_2186564 : Nat := 748505542545125527996121

theorem tailTrace_2186564 : CollatzResearch.WordTrace tailWord_2186564 prefixEnd_2186564 748505542545125527996121 := by
  unfold tailWord_2186564
  simp only [CollatzResearch.WordTrace]
  refine ⟨39875270425229769122799373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53167027233639692163732497 39875270425229769122799373)
  ·
    refine ⟨14953226409461163421049765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39875270425229769122799373 14953226409461163421049765)
    ·
      refine ⟨2803729951773968141446831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14953226409461163421049765 2803729951773968141446831)
      ·
        refine ⟨4205594927660952212170247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2803729951773968141446831 4205594927660952212170247)
        ·
          refine ⟨6308392391491428318255371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4205594927660952212170247 6308392391491428318255371)
          ·
            refine ⟨9462588587237142477383057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6308392391491428318255371 9462588587237142477383057)
            ·
              refine ⟨7096941440427856858037293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9462588587237142477383057 7096941440427856858037293)
              ·
                refine ⟨2661353040160446321763985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7096941440427856858037293 2661353040160446321763985)
                ·
                  refine ⟨1996014780120334741322989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2661353040160446321763985 1996014780120334741322989)
                  ·
                    refine ⟨748505542545125527996121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1996014780120334741322989 748505542545125527996121)
                    ·
                      rfl

theorem cell22_2186564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 3, 2, 3].length) (baseStart_2186564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2186564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2186564 prefixEnd_2186564 := by exact prefixLift 2186564
  have htrace : WordTrace (prefixWord ++ tailWord_2186564) baseStart_2186564 baseEnd_2186564 := by
    simpa [prefixWord, tailWord_2186564, baseEnd_2186564] using wordTrace_append hprefix tailTrace_2186564
  have hstable : (prefixWord ++ tailWord_2186564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2186564).length < 2 ^ (prefixWord ++ tailWord_2186564).sum := by decide
  have hdescent : baseEnd_2186564 < baseStart_2186564 := by decide
  rcases family_descends (prefixWord ++ tailWord_2186564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2186605 : List Nat := [1, 5, 1, 1, 1, 4, 1, 1, 7]
def baseStart_2186605 : Nat := 118140960795 + 2186605 * 2 ^ 59
def prefixEnd_2186605 : Nat := 4983230072969 + 3 ^ 40 * 2186605 * 2
def baseEnd_2186605 : Nat := 249506525894338362573665

theorem tailTrace_2186605 : CollatzResearch.WordTrace tailWord_2186605 prefixEnd_2186605 249506525894338362573665 := by
  unfold tailWord_2186605
  simp only [CollatzResearch.WordTrace]
  refine ⟨79752036243311002247841269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53168024162207334831894179 79752036243311002247841269)
  ·
    refine ⟨7476753397810406460735119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 79752036243311002247841269 7476753397810406460735119)
    ·
      refine ⟨11215130096715609691102679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7476753397810406460735119 11215130096715609691102679)
      ·
        refine ⟨16822695145073414536654019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11215130096715609691102679 16822695145073414536654019)
        ·
          refine ⟨25234042717610121804981029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16822695145073414536654019 25234042717610121804981029)
          ·
            refine ⟨4731383009551897838433943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25234042717610121804981029 4731383009551897838433943)
            ·
              refine ⟨7097074514327846757650915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4731383009551897838433943 7097074514327846757650915)
              ·
                refine ⟨10645611771491770136476373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7097074514327846757650915 10645611771491770136476373)
                ·
                  refine ⟨249506525894338362573665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10645611771491770136476373 249506525894338362573665)
                  ·
                    rfl

theorem cell22_2186605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 1, 7].length) (baseStart_2186605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2186605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2186605 prefixEnd_2186605 := by exact prefixLift 2186605
  have htrace : WordTrace (prefixWord ++ tailWord_2186605) baseStart_2186605 baseEnd_2186605 := by
    simpa [prefixWord, tailWord_2186605, baseEnd_2186605] using wordTrace_append hprefix tailTrace_2186605
  have hstable : (prefixWord ++ tailWord_2186605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2186605).length < 2 ^ (prefixWord ++ tailWord_2186605).sum := by decide
  have hdescent : baseEnd_2186605 < baseStart_2186605 := by decide
  rcases family_descends (prefixWord ++ tailWord_2186605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2186817 : List Nat := [1, 2, 5, 1, 1, 1, 2, 1, 3, 5]
def baseStart_2186817 : Nat := 118140960795 + 2186817 * 2 ^ 59
def prefixEnd_2186817 : Nat := 4983230072969 + 3 ^ 40 * 2186817 * 2
def baseEnd_2186817 : Nat := 748592149615517201420345

theorem tailTrace_2186817 : CollatzResearch.WordTrace tailWord_2186817 prefixEnd_2186817 748592149615517201420345 := by
  unfold tailWord_2186817
  simp only [CollatzResearch.WordTrace]
  refine ⟨79759768518542962454558705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53173179012361974969705803 79759768518542962454558705)
  ·
    refine ⟨59819826388907221840919029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79759768518542962454558705 59819826388907221840919029)
    ·
      refine ⟨5608108723960052047586159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 59819826388907221840919029 5608108723960052047586159)
      ·
        refine ⟨8412163085940078071379239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5608108723960052047586159 8412163085940078071379239)
        ·
          refine ⟨12618244628910117107068859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8412163085940078071379239 12618244628910117107068859)
          ·
            refine ⟨18927366943365175660603289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12618244628910117107068859 18927366943365175660603289)
            ·
              refine ⟨14195525207523881745452467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18927366943365175660603289 14195525207523881745452467)
              ·
                refine ⟨21293287811285822618178701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14195525207523881745452467 21293287811285822618178701)
                ·
                  refine ⟨7984982929232183481817013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21293287811285822618178701 7984982929232183481817013)
                  ·
                    refine ⟨748592149615517201420345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7984982929232183481817013 748592149615517201420345)
                    ·
                      rfl

theorem cell22_2186817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 1, 3, 5].length) (baseStart_2186817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2186817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2186817 prefixEnd_2186817 := by exact prefixLift 2186817
  have htrace : WordTrace (prefixWord ++ tailWord_2186817) baseStart_2186817 baseEnd_2186817 := by
    simpa [prefixWord, tailWord_2186817, baseEnd_2186817] using wordTrace_append hprefix tailTrace_2186817
  have hstable : (prefixWord ++ tailWord_2186817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2186817).length < 2 ^ (prefixWord ++ tailWord_2186817).sum := by decide
  have hdescent : baseEnd_2186817 < baseStart_2186817 := by decide
  rcases family_descends (prefixWord ++ tailWord_2186817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2186832 : List Nat := [2, 1, 1, 1, 1, 3, 5, 2, 2, 4]
def baseStart_2186832 : Nat := 118140960795 + 2186832 * 2 ^ 59
def prefixEnd_2186832 : Nat := 4983230072969 + 3 ^ 40 * 2186832 * 2
def baseEnd_2186832 : Nat := 748597284422062162295299

theorem tailTrace_2186832 : CollatzResearch.WordTrace tailWord_2186832 prefixEnd_2186832 748597284422062162295299 := by
  unfold tailWord_2186832
  simp only [CollatzResearch.WordTrace]
  refine ⟨39880157806744310008177375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53173543742325746677569833 39880157806744310008177375)
  ·
    refine ⟨59820236710116465012266063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39880157806744310008177375 59820236710116465012266063)
    ·
      refine ⟨89730355065174697518399095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59820236710116465012266063 89730355065174697518399095)
      ·
        refine ⟨134595532597762046277598643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89730355065174697518399095 134595532597762046277598643)
        ·
          refine ⟨201893298896643069416397965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134595532597762046277598643 201893298896643069416397965)
          ·
            refine ⟨75709987086241151031149237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 201893298896643069416397965 75709987086241151031149237)
            ·
              refine ⟨7097811289335107909170241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 75709987086241151031149237 7097811289335107909170241)
              ·
                refine ⟨5323358467001330931877681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7097811289335107909170241 5323358467001330931877681)
                ·
                  refine ⟨3992518850250998198908261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5323358467001330931877681 3992518850250998198908261)
                  ·
                    refine ⟨748597284422062162295299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3992518850250998198908261 748597284422062162295299)
                    ·
                      rfl

theorem cell22_2186832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 2, 2, 4].length) (baseStart_2186832 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2186832 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2186832 prefixEnd_2186832 := by exact prefixLift 2186832
  have htrace : WordTrace (prefixWord ++ tailWord_2186832) baseStart_2186832 baseEnd_2186832 := by
    simpa [prefixWord, tailWord_2186832, baseEnd_2186832] using wordTrace_append hprefix tailTrace_2186832
  have hstable : (prefixWord ++ tailWord_2186832).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2186832).length < 2 ^ (prefixWord ++ tailWord_2186832).sum := by decide
  have hdescent : baseEnd_2186832 < baseStart_2186832 := by decide
  rcases family_descends (prefixWord ++ tailWord_2186832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2186834 : List Nat := [3, 2, 2, 1, 2, 2, 2, 1, 4, 3]
def baseStart_2186834 : Nat := 118140960795 + 2186834 * 2 ^ 59
def prefixEnd_2186834 : Nat := 4983230072969 + 3 ^ 40 * 2186834 * 2
def baseEnd_2186834 : Nat := 748597969062934823745293

theorem tailTrace_2186834 : CollatzResearch.WordTrace tailWord_2186834 prefixEnd_2186834 748597969062934823745293 := by
  unfold tailWord_2186834
  simp only [CollatzResearch.WordTrace]
  refine ⟨19940097139870343589481889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53173592372987582905285037 19940097139870343589481889)
  ·
    refine ⟨14955072854902757692111417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19940097139870343589481889 14955072854902757692111417)
    ·
      refine ⟨11216304641177068269083563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14955072854902757692111417 11216304641177068269083563)
      ·
        refine ⟨16824456961765602403625345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11216304641177068269083563 16824456961765602403625345)
        ·
          refine ⟨12618342721324201802719009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16824456961765602403625345 12618342721324201802719009)
          ·
            refine ⟨9463757040993151352039257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12618342721324201802719009 9463757040993151352039257)
            ·
              refine ⟨7097817780744863514029443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9463757040993151352039257 7097817780744863514029443)
              ·
                refine ⟨10646726671117295271044165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7097817780744863514029443 10646726671117295271044165)
                ·
                  refine ⟨1996261250834492863320781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10646726671117295271044165 1996261250834492863320781)
                  ·
                    refine ⟨748597969062934823745293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1996261250834492863320781 748597969062934823745293)
                    ·
                      rfl

theorem cell22_2186834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 1, 4, 3].length) (baseStart_2186834 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2186834 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2186834 prefixEnd_2186834 := by exact prefixLift 2186834
  have htrace : WordTrace (prefixWord ++ tailWord_2186834) baseStart_2186834 baseEnd_2186834 := by
    simpa [prefixWord, tailWord_2186834, baseEnd_2186834] using wordTrace_append hprefix tailTrace_2186834
  have hstable : (prefixWord ++ tailWord_2186834).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2186834).length < 2 ^ (prefixWord ++ tailWord_2186834).sum := by decide
  have hdescent : baseEnd_2186834 < baseStart_2186834 := by decide
  rcases family_descends (prefixWord ++ tailWord_2186834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2186836 : List Nat := [2, 4, 1, 1, 1, 2, 5, 2, 4]
def baseStart_2186836 : Nat := 118140960795 + 2186836 * 2 ^ 59
def prefixEnd_2186836 : Nat := 4983230072969 + 3 ^ 40 * 2186836 * 2
def baseEnd_2186836 : Nat := 249532884567935828398429

theorem tailTrace_2186836 : CollatzResearch.WordTrace tailWord_2186836 prefixEnd_2186836 249532884567935828398429 := by
  unfold tailWord_2186836
  simp only [CollatzResearch.WordTrace]
  refine ⟨39880230752737064349750181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53173641003649419133000241 39880230752737064349750181)
  ·
    refine ⟨7477543266138199565578159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39880230752737064349750181 7477543266138199565578159)
    ·
      refine ⟨11216314899207299348367239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7477543266138199565578159 11216314899207299348367239)
      ·
        refine ⟨16824472348810949022550859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11216314899207299348367239 16824472348810949022550859)
        ·
          refine ⟨25236708523216423533826289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16824472348810949022550859 25236708523216423533826289)
          ·
            refine ⟨18927531392412317650369717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25236708523216423533826289 18927531392412317650369717)
            ·
              refine ⟨1774456068038654779722161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18927531392412317650369717 1774456068038654779722161)
              ·
                refine ⟨1330842051028991084791621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1774456068038654779722161 1330842051028991084791621)
                ·
                  refine ⟨249532884567935828398429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1330842051028991084791621 249532884567935828398429)
                  ·
                    rfl

theorem cell22_2186836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 5, 2, 4].length) (baseStart_2186836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2186836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2186836 prefixEnd_2186836 := by exact prefixLift 2186836
  have htrace : WordTrace (prefixWord ++ tailWord_2186836) baseStart_2186836 baseEnd_2186836 := by
    simpa [prefixWord, tailWord_2186836, baseEnd_2186836] using wordTrace_append hprefix tailTrace_2186836
  have hstable : (prefixWord ++ tailWord_2186836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2186836).length < 2 ^ (prefixWord ++ tailWord_2186836).sum := by decide
  have hdescent : baseEnd_2186836 < baseStart_2186836 := by decide
  rcases family_descends (prefixWord ++ tailWord_2186836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2186851 : List Nat := [1, 1, 1, 5, 1, 3, 4, 1, 2, 3]
def baseStart_2186851 : Nat := 118140960795 + 2186851 * 2 ^ 59
def prefixEnd_2186851 : Nat := 4983230072969 + 3 ^ 40 * 2186851 * 2
def baseEnd_2186851 : Nat := 748603788510352446070241

theorem tailTrace_2186851 : CollatzResearch.WordTrace tailWord_2186851 prefixEnd_2186851 748603788510352446070241 := by
  unfold tailWord_2186851
  simp only [CollatzResearch.WordTrace]
  refine ⟨79761008600419786261296407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53174005733613190840864271 79761008600419786261296407)
  ·
    refine ⟨119641512900629679391944611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79761008600419786261296407 119641512900629679391944611)
    ·
      refine ⟨179462269350944519087916917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119641512900629679391944611 179462269350944519087916917)
      ·
        refine ⟨16824587751651048664492211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 179462269350944519087916917 16824587751651048664492211)
        ·
          refine ⟨25236881627476572996738317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16824587751651048664492211 25236881627476572996738317)
          ·
            refine ⟨9463830610303714873776869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25236881627476572996738317 9463830610303714873776869)
            ·
              refine ⟨1774468239431946538833163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9463830610303714873776869 1774468239431946538833163)
              ·
                refine ⟨2661702359147919808249745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1774468239431946538833163 2661702359147919808249745)
                ·
                  refine ⟨1996276769360939856187309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2661702359147919808249745 1996276769360939856187309)
                  ·
                    refine ⟨748603788510352446070241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1996276769360939856187309 748603788510352446070241)
                    ·
                      rfl

theorem cell22_2186851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 4, 1, 2, 3].length) (baseStart_2186851 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2186851 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2186851 prefixEnd_2186851 := by exact prefixLift 2186851
  have htrace : WordTrace (prefixWord ++ tailWord_2186851) baseStart_2186851 baseEnd_2186851 := by
    simpa [prefixWord, tailWord_2186851, baseEnd_2186851] using wordTrace_append hprefix tailTrace_2186851
  have hstable : (prefixWord ++ tailWord_2186851).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2186851).length < 2 ^ (prefixWord ++ tailWord_2186851).sum := by decide
  have hdescent : baseEnd_2186851 < baseStart_2186851 := by decide
  rcases family_descends (prefixWord ++ tailWord_2186851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2186967 : List Nat := [1, 1, 3, 2, 1, 3, 1, 1, 3, 6]
def baseStart_2186967 : Nat := 118140960795 + 2186967 * 2 ^ 59
def prefixEnd_2186967 : Nat := 4983230072969 + 3 ^ 40 * 2186967 * 2
def baseEnd_2186967 : Nat := 748643497680966810169885

theorem tailTrace_2186967 : CollatzResearch.WordTrace tailWord_2186967 prefixEnd_2186967 748643497680966810169885 := by
  unfold tailWord_2186967
  simp only [CollatzResearch.WordTrace]
  refine ⟨79765239467999538072519155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53176826311999692048346103 79765239467999538072519155)
  ·
    refine ⟨119647859201999307108778733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79765239467999538072519155 119647859201999307108778733)
    ·
      refine ⟨44867947200749740165792025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 119647859201999307108778733 44867947200749740165792025)
      ·
        refine ⟨33650960400562305124344019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44867947200749740165792025 33650960400562305124344019)
        ·
          refine ⟨50476440600843457686516029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33650960400562305124344019 50476440600843457686516029)
          ·
            refine ⟨18928665225316296632443511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50476440600843457686516029 18928665225316296632443511)
            ·
              refine ⟨28392997837974444948665267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18928665225316296632443511 28392997837974444948665267)
              ·
                refine ⟨42589496756961667422997901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28392997837974444948665267 42589496756961667422997901)
                ·
                  refine ⟨15971061283860625283624213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42589496756961667422997901 15971061283860625283624213)
                  ·
                    refine ⟨748643497680966810169885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15971061283860625283624213 748643497680966810169885)
                    ·
                      rfl

theorem cell22_2186967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 1, 3, 6].length) (baseStart_2186967 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2186967 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2186967 prefixEnd_2186967 := by exact prefixLift 2186967
  have htrace : WordTrace (prefixWord ++ tailWord_2186967) baseStart_2186967 baseEnd_2186967 := by
    simpa [prefixWord, tailWord_2186967, baseEnd_2186967] using wordTrace_append hprefix tailTrace_2186967
  have hstable : (prefixWord ++ tailWord_2186967).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2186967).length < 2 ^ (prefixWord ++ tailWord_2186967).sum := by decide
  have hdescent : baseEnd_2186967 < baseStart_2186967 := by decide
  rcases family_descends (prefixWord ++ tailWord_2186967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2186969 : List Nat := [1, 2, 1, 2, 3, 3, 3, 1, 1, 5]
def baseStart_2186969 : Nat := 118140960795 + 2186969 * 2 ^ 59
def prefixEnd_2186969 : Nat := 4983230072969 + 3 ^ 40 * 2186969 * 2
def baseEnd_2186969 : Nat := 748644182321839471619879

theorem tailTrace_2186969 : CollatzResearch.WordTrace tailWord_2186969 prefixEnd_2186969 748644182321839471619879 := by
  unfold tailWord_2186969
  simp only [CollatzResearch.WordTrace]
  refine ⟨79765312413992292414091961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53176874942661528276061307 79765312413992292414091961)
  ·
    refine ⟨59823984310494219310568971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79765312413992292414091961 59823984310494219310568971)
    ·
      refine ⟨89735976465741328965853457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59823984310494219310568971 89735976465741328965853457)
      ·
        refine ⟨67301982349305996724390093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89735976465741328965853457 67301982349305996724390093)
        ·
          refine ⟨25238243380989748771646285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67301982349305996724390093 25238243380989748771646285)
          ·
            refine ⟨9464341267871155789367357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25238243380989748771646285 9464341267871155789367357)
            ·
              refine ⟨3549127975451683421012759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9464341267871155789367357 3549127975451683421012759)
              ·
                refine ⟨5323691963177525131519139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3549127975451683421012759 5323691963177525131519139)
                ·
                  refine ⟨7985537944766287697278709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5323691963177525131519139 7985537944766287697278709)
                  ·
                    refine ⟨748644182321839471619879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7985537944766287697278709 748644182321839471619879)
                    ·
                      rfl

theorem cell22_2186969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 3, 1, 1, 5].length) (baseStart_2186969 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2186969 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2186969 prefixEnd_2186969 := by exact prefixLift 2186969
  have htrace : WordTrace (prefixWord ++ tailWord_2186969) baseStart_2186969 baseEnd_2186969 := by
    simpa [prefixWord, tailWord_2186969, baseEnd_2186969] using wordTrace_append hprefix tailTrace_2186969
  have hstable : (prefixWord ++ tailWord_2186969).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2186969).length < 2 ^ (prefixWord ++ tailWord_2186969).sum := by decide
  have hdescent : baseEnd_2186969 < baseStart_2186969 := by decide
  rcases family_descends (prefixWord ++ tailWord_2186969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2186984 : List Nat := [2, 1, 4, 1, 3, 1, 2, 1, 1, 6]
def baseStart_2186984 : Nat := 118140960795 + 2186984 * 2 ^ 59
def prefixEnd_2186984 : Nat := 4983230072969 + 3 ^ 40 * 2186984 * 2
def baseEnd_2186984 : Nat := 748649317128384432494833

theorem tailTrace_2186984 : CollatzResearch.WordTrace tailWord_2186984 prefixEnd_2186984 748649317128384432494833 := by
  unfold tailWord_2186984
  simp only [CollatzResearch.WordTrace]
  refine ⟨39882929754468974987944003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53177239672625299983925337 39882929754468974987944003)
  ·
    refine ⟨59824394631703462481916005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39882929754468974987944003 59824394631703462481916005)
    ·
      refine ⟨11217073993444399215359251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 59824394631703462481916005 11217073993444399215359251)
      ·
        refine ⟨16825610990166598823038877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11217073993444399215359251 16825610990166598823038877)
        ·
          refine ⟨6309604121312474558639579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16825610990166598823038877 6309604121312474558639579)
          ·
            refine ⟨9464406181968711837959369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6309604121312474558639579 9464406181968711837959369)
            ·
              refine ⟨7098304636476533878469527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9464406181968711837959369 7098304636476533878469527)
              ·
                refine ⟨10647456954714800817704291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7098304636476533878469527 10647456954714800817704291)
                ·
                  refine ⟨15971185432072201226556437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10647456954714800817704291 15971185432072201226556437)
                  ·
                    refine ⟨748649317128384432494833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15971185432072201226556437 748649317128384432494833)
                    ·
                      rfl

theorem cell22_2186984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 1, 1, 6].length) (baseStart_2186984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2186984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2186984 prefixEnd_2186984 := by exact prefixLift 2186984
  have htrace : WordTrace (prefixWord ++ tailWord_2186984) baseStart_2186984 baseEnd_2186984 := by
    simpa [prefixWord, tailWord_2186984, baseEnd_2186984] using wordTrace_append hprefix tailTrace_2186984
  have hstable : (prefixWord ++ tailWord_2186984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2186984).length < 2 ^ (prefixWord ++ tailWord_2186984).sum := by decide
  have hdescent : baseEnd_2186984 < baseStart_2186984 := by decide
  rcases family_descends (prefixWord ++ tailWord_2186984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2187027 : List Nat := [1, 1, 1, 2, 1, 3, 2, 2, 9]
def baseStart_2187027 : Nat := 118140960795 + 2187027 * 2 ^ 59
def prefixEnd_2187027 : Nat := 4983230072969 + 3 ^ 40 * 2187027 * 2
def baseEnd_2187027 : Nat := 249554678969048884556567

theorem tailTrace_2187027 : CollatzResearch.WordTrace tailWord_2187027 prefixEnd_2187027 249554678969048884556567 := by
  unfold tailWord_2187027
  simp only [CollatzResearch.WordTrace]
  refine ⟨79767427847782168319703335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53178285231854778879802223 79767427847782168319703335)
  ·
    refine ⟨119651141771673252479555003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79767427847782168319703335 119651141771673252479555003)
    ·
      refine ⟨179476712657509878719332505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119651141771673252479555003 179476712657509878719332505)
      ·
        refine ⟨134607534493132409039499379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 179476712657509878719332505 134607534493132409039499379)
        ·
          refine ⟨201911301739698613559249069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134607534493132409039499379 201911301739698613559249069)
          ·
            refine ⟨75716738152386980084718401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 201911301739698613559249069 75716738152386980084718401)
            ·
              refine ⟨56787553614290235063538801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75716738152386980084718401 56787553614290235063538801)
              ·
                refine ⟨42590665210717676297654101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56787553614290235063538801 42590665210717676297654101)
                ·
                  refine ⟨249554678969048884556567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 42590665210717676297654101 249554678969048884556567)
                  ·
                    rfl

theorem cell22_2187027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 2, 9].length) (baseStart_2187027 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2187027 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2187027 prefixEnd_2187027 := by exact prefixLift 2187027
  have htrace : WordTrace (prefixWord ++ tailWord_2187027) baseStart_2187027 baseEnd_2187027 := by
    simpa [prefixWord, tailWord_2187027, baseEnd_2187027] using wordTrace_append hprefix tailTrace_2187027
  have hstable : (prefixWord ++ tailWord_2187027).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2187027).length < 2 ^ (prefixWord ++ tailWord_2187027).sum := by decide
  have hdescent : baseEnd_2187027 < baseStart_2187027 := by decide
  rcases family_descends (prefixWord ++ tailWord_2187027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2187089 : List Nat := [1, 2, 2, 1, 5, 1, 1, 1, 8]
def baseStart_2187089 : Nat := 118140960795 + 2187089 * 2 ^ 59
def prefixEnd_2187089 : Nat := 4983230072969 + 3 ^ 40 * 2187089 * 2
def baseEnd_2187089 : Nat := 249561753591399719539837

theorem tailTrace_2187089 : CollatzResearch.WordTrace tailWord_2187089 prefixEnd_2187089 249561753591399719539837 := by
  unfold tailWord_2187089
  simp only [CollatzResearch.WordTrace]
  refine ⟨79769689173557552908460321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53179792782371701938973547 79769689173557552908460321)
  ·
    refine ⟨59827266880168164681345241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79769689173557552908460321 59827266880168164681345241)
    ·
      refine ⟨44870450160126123511008931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59827266880168164681345241 44870450160126123511008931)
      ·
        refine ⟨67305675240189185266513397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44870450160126123511008931 67305675240189185266513397)
        ·
          refine ⟨6309907053767736118735631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 67305675240189185266513397 6309907053767736118735631)
          ·
            refine ⟨9464860580651604178103447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6309907053767736118735631 9464860580651604178103447)
            ·
              refine ⟨14197290870977406267155171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9464860580651604178103447 14197290870977406267155171)
              ·
                refine ⟨21295936306466109400732757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14197290870977406267155171 21295936306466109400732757)
                ·
                  refine ⟨249561753591399719539837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21295936306466109400732757 249561753591399719539837)
                  ·
                    rfl

theorem cell22_2187089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 1, 8].length) (baseStart_2187089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2187089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2187089 prefixEnd_2187089 := by exact prefixLift 2187089
  have htrace : WordTrace (prefixWord ++ tailWord_2187089) baseStart_2187089 baseEnd_2187089 := by
    simpa [prefixWord, tailWord_2187089, baseEnd_2187089] using wordTrace_append hprefix tailTrace_2187089
  have hstable : (prefixWord ++ tailWord_2187089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2187089).length < 2 ^ (prefixWord ++ tailWord_2187089).sum := by decide
  have hdescent : baseEnd_2187089 < baseStart_2187089 := by decide
  rcases family_descends (prefixWord ++ tailWord_2187089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2187108 : List Nat := [2, 3, 1, 1, 5, 1, 1, 3, 1, 4]
def baseStart_2187108 : Nat := 118140960795 + 2187108 * 2 ^ 59
def prefixEnd_2187108 : Nat := 4983230072969 + 3 ^ 40 * 2187108 * 2
def baseEnd_2187108 : Nat := 748691764862489442394453

theorem tailTrace_2187108 : CollatzResearch.WordTrace tailWord_2187108 prefixEnd_2187108 748691764862489442394453 := by
  unfold tailWord_2187108
  simp only [CollatzResearch.WordTrace]
  refine ⟨39885191080244359576700989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53180254773659146102267985 39885191080244359576700989)
  ·
    refine ⟨14956946655091634841262871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39885191080244359576700989 14956946655091634841262871)
    ·
      refine ⟨22435419982637452261894307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14956946655091634841262871 22435419982637452261894307)
      ·
        refine ⟨33653129973956178392841461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22435419982637452261894307 33653129973956178392841461)
        ·
          refine ⟨3154980935058391724328887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 33653129973956178392841461 3154980935058391724328887)
          ·
            refine ⟨4732471402587587586493331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3154980935058391724328887 4732471402587587586493331)
            ·
              refine ⟨7098707103881381379739997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4732471402587587586493331 7098707103881381379739997)
              ·
                refine ⟨2662015163955518017402499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7098707103881381379739997 2662015163955518017402499)
                ·
                  refine ⟨3993022745933277026103749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2662015163955518017402499 3993022745933277026103749)
                  ·
                    refine ⟨748691764862489442394453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3993022745933277026103749 748691764862489442394453)
                    ·
                      rfl

theorem cell22_2187108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 3, 1, 4].length) (baseStart_2187108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2187108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2187108 prefixEnd_2187108 := by exact prefixLift 2187108
  have htrace : WordTrace (prefixWord ++ tailWord_2187108) baseStart_2187108 baseEnd_2187108 := by
    simpa [prefixWord, tailWord_2187108, baseEnd_2187108] using wordTrace_append hprefix tailTrace_2187108
  have hstable : (prefixWord ++ tailWord_2187108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2187108).length < 2 ^ (prefixWord ++ tailWord_2187108).sum := by decide
  have hdescent : baseEnd_2187108 < baseStart_2187108 := by decide
  rcases family_descends (prefixWord ++ tailWord_2187108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2187121 : List Nat := [1, 2, 2, 2, 1, 3, 3, 1, 4, 3]
def baseStart_2187121 : Nat := 118140960795 + 2187121 * 2 ^ 59
def prefixEnd_2187121 : Nat := 4983230072969 + 3 ^ 40 * 2187121 * 2
def baseEnd_2187121 : Nat := 748696215028161741819413

theorem tailTrace_2187121 : CollatzResearch.WordTrace tailWord_2187121 prefixEnd_2187121 748696215028161741819413 := by
  unfold tailWord_2187121
  simp only [CollatzResearch.WordTrace]
  refine ⟨79770856309441622373625217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53180570872961081582416811 79770856309441622373625217)
  ·
    refine ⟨59828142232081216780218913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79770856309441622373625217 59828142232081216780218913)
    ·
      refine ⟨44871106674060912585164185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59828142232081216780218913 44871106674060912585164185)
      ·
        refine ⟨33653330005545684438873139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44871106674060912585164185 33653330005545684438873139)
        ·
          refine ⟨50479995008318526658309709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33653330005545684438873139 50479995008318526658309709)
          ·
            refine ⟨18929998128119447496866141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50479995008318526658309709 18929998128119447496866141)
            ·
              refine ⟨7098749298044792811324803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18929998128119447496866141 7098749298044792811324803)
              ·
                refine ⟨10648123947067189216987205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7098749298044792811324803 10648123947067189216987205)
                ·
                  refine ⟨1996523240075097978185101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10648123947067189216987205 1996523240075097978185101)
                  ·
                    refine ⟨748696215028161741819413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1996523240075097978185101 748696215028161741819413)
                    ·
                      rfl

theorem cell22_2187121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 1, 4, 3].length) (baseStart_2187121 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2187121 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2187121 prefixEnd_2187121 := by exact prefixLift 2187121
  have htrace : WordTrace (prefixWord ++ tailWord_2187121) baseStart_2187121 baseEnd_2187121 := by
    simpa [prefixWord, tailWord_2187121, baseEnd_2187121] using wordTrace_append hprefix tailTrace_2187121
  have hstable : (prefixWord ++ tailWord_2187121).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2187121).length < 2 ^ (prefixWord ++ tailWord_2187121).sum := by decide
  have hdescent : baseEnd_2187121 < baseStart_2187121 := by decide
  rcases family_descends (prefixWord ++ tailWord_2187121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2187209 : List Nat := [1, 2, 1, 1, 2, 1, 2, 2, 2, 8]
def baseStart_2187209 : Nat := 118140960795 + 2187209 * 2 ^ 59
def prefixEnd_2187209 : Nat := 4983230072969 + 3 ^ 40 * 2187209 * 2
def baseEnd_2187209 : Nat := 748726339226558845619143

theorem tailTrace_2187209 : CollatzResearch.WordTrace tailWord_2187209 prefixEnd_2187209 748726339226558845619143 := by
  unfold tailWord_2187209
  simp only [CollatzResearch.WordTrace]
  refine ⟨79774065933122813402828681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53182710622081875601885787 79774065933122813402828681)
  ·
    refine ⟨59830549449842110052121511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79774065933122813402828681 59830549449842110052121511)
    ·
      refine ⟨89745824174763165078182267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59830549449842110052121511 89745824174763165078182267)
      ·
        refine ⟨134618736262144747617273401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89745824174763165078182267 134618736262144747617273401)
        ·
          refine ⟨100964052196608560712955051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 134618736262144747617273401 100964052196608560712955051)
          ·
            refine ⟨151446078294912841069432577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100964052196608560712955051 151446078294912841069432577)
            ·
              refine ⟨113584558721184630802074433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 151446078294912841069432577 113584558721184630802074433)
              ·
                refine ⟨85188419040888473101555825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 113584558721184630802074433 85188419040888473101555825)
                ·
                  refine ⟨63891314280666354826166869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 85188419040888473101555825 63891314280666354826166869)
                  ·
                    refine ⟨748726339226558845619143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 63891314280666354826166869 748726339226558845619143)
                    ·
                      rfl

theorem cell22_2187209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 2, 8].length) (baseStart_2187209 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2187209 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2187209 prefixEnd_2187209 := by exact prefixLift 2187209
  have htrace : WordTrace (prefixWord ++ tailWord_2187209) baseStart_2187209 baseEnd_2187209 := by
    simpa [prefixWord, tailWord_2187209, baseEnd_2187209] using wordTrace_append hprefix tailTrace_2187209
  have hstable : (prefixWord ++ tailWord_2187209).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2187209).length < 2 ^ (prefixWord ++ tailWord_2187209).sum := by decide
  have hdescent : baseEnd_2187209 < baseStart_2187209 := by decide
  rcases family_descends (prefixWord ++ tailWord_2187209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2187234 : List Nat := [3, 3, 3, 1, 2, 1, 1, 4, 1, 3]
def baseStart_2187234 : Nat := 118140960795 + 2187234 * 2 ^ 59
def prefixEnd_2187234 : Nat := 4983230072969 + 3 ^ 40 * 2187234 * 2
def baseEnd_2187234 : Nat := 748734897237467113744067

theorem tailTrace_2187234 : CollatzResearch.WordTrace tailWord_2187234 prefixEnd_2187234 748734897237467113744067 := by
  unfold tailWord_2187234
  simp only [CollatzResearch.WordTrace]
  refine ⟨19943744439508060668122189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53183318505354828448325837 19943744439508060668122189)
  ·
    refine ⟨7478904164815522750545821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19943744439508060668122189 7478904164815522750545821)
    ·
      refine ⟨2804589061805821031454683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7478904164815522750545821 2804589061805821031454683)
      ·
        refine ⟨4206883592708731547182025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2804589061805821031454683 4206883592708731547182025)
        ·
          refine ⟨3155162694531548660386519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4206883592708731547182025 3155162694531548660386519)
          ·
            refine ⟨4732744041797322990579779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3155162694531548660386519 4732744041797322990579779)
            ·
              refine ⟨7099116062695984485869669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4732744041797322990579779 7099116062695984485869669)
              ·
                refine ⟨1331084261755497091100563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7099116062695984485869669 1331084261755497091100563)
                ·
                  refine ⟨1996626392633245636650845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1331084261755497091100563 1996626392633245636650845)
                  ·
                    refine ⟨748734897237467113744067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1996626392633245636650845 748734897237467113744067)
                    ·
                      rfl

theorem cell22_2187234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 4, 1, 3].length) (baseStart_2187234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2187234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2187234 prefixEnd_2187234 := by exact prefixLift 2187234
  have htrace : WordTrace (prefixWord ++ tailWord_2187234) baseStart_2187234 baseEnd_2187234 := by
    simpa [prefixWord, tailWord_2187234, baseEnd_2187234] using wordTrace_append hprefix tailTrace_2187234
  have hstable : (prefixWord ++ tailWord_2187234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2187234).length < 2 ^ (prefixWord ++ tailWord_2187234).sum := by decide
  have hdescent : baseEnd_2187234 < baseStart_2187234 := by decide
  rcases family_descends (prefixWord ++ tailWord_2187234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2187245 : List Nat := [1, 5, 1, 4, 1, 1, 1, 1, 2, 5]
def baseStart_2187245 : Nat := 118140960795 + 2187245 * 2 ^ 59
def prefixEnd_2187245 : Nat := 4983230072969 + 3 ^ 40 * 2187245 * 2
def baseEnd_2187245 : Nat := 748738662762266751719033

theorem tailTrace_2187245 : CollatzResearch.WordTrace tailWord_2187245 prefixEnd_2187245 748738662762266751719033 := by
  unfold tailWord_2187245
  simp only [CollatzResearch.WordTrace]
  refine ⟨79775378960992391551139189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53183585973994927700759459 79775378960992391551139189)
  ·
    refine ⟨7478941777593036707919299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 79775378960992391551139189 7478941777593036707919299)
    ·
      refine ⟨11218412666389555061878949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7478941777593036707919299 11218412666389555061878949)
      ·
        refine ⟨2103452374948041574102303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11218412666389555061878949 2103452374948041574102303)
        ·
          refine ⟨3155178562422062361153455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2103452374948041574102303 3155178562422062361153455)
          ·
            refine ⟨4732767843633093541730183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3155178562422062361153455 4732767843633093541730183)
            ·
              refine ⟨7099151765449640312595275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4732767843633093541730183 7099151765449640312595275)
              ·
                refine ⟨10648727648174460468892913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7099151765449640312595275 10648727648174460468892913)
                ·
                  refine ⟨7986545736130845351669685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10648727648174460468892913 7986545736130845351669685)
                  ·
                    refine ⟨748738662762266751719033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7986545736130845351669685 748738662762266751719033)
                    ·
                      rfl

theorem cell22_2187245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 1, 2, 5].length) (baseStart_2187245 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2187245 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2187245 prefixEnd_2187245 := by exact prefixLift 2187245
  have htrace : WordTrace (prefixWord ++ tailWord_2187245) baseStart_2187245 baseEnd_2187245 := by
    simpa [prefixWord, tailWord_2187245, baseEnd_2187245] using wordTrace_append hprefix tailTrace_2187245
  have hstable : (prefixWord ++ tailWord_2187245).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2187245).length < 2 ^ (prefixWord ++ tailWord_2187245).sum := by decide
  have hdescent : baseEnd_2187245 < baseStart_2187245 := by decide
  rcases family_descends (prefixWord ++ tailWord_2187245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2187256 : List Nat := [2, 1, 2, 1, 1, 3, 3, 3, 1, 5]
def baseStart_2187256 : Nat := 118140960795 + 2187256 * 2 ^ 59
def prefixEnd_2187256 : Nat := 4983230072969 + 3 ^ 40 * 2187256 * 2
def baseEnd_2187256 : Nat := 748742428287066389693999

theorem tailTrace_2187256 : CollatzResearch.WordTrace tailWord_2187256 prefixEnd_2187256 748742428287066389693999 := by
  unfold tailWord_2187256
  simp only [CollatzResearch.WordTrace]
  refine ⟨39887890081976270214894811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53183853442635026953193081 39887890081976270214894811)
  ·
    refine ⟨59831835122964405322342217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39887890081976270214894811 59831835122964405322342217)
    ·
      refine ⟨44873876342223303991756663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59831835122964405322342217 44873876342223303991756663)
      ·
        refine ⟨67310814513334955987634995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44873876342223303991756663 67310814513334955987634995)
        ·
          refine ⟨100966221770002433981452493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67310814513334955987634995 100966221770002433981452493)
          ·
            refine ⟨37862333163750912743044685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 100966221770002433981452493 37862333163750912743044685)
            ·
              refine ⟨14198374936406592278641757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37862333163750912743044685 14198374936406592278641757)
              ·
                refine ⟨5324390601152472104490659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14198374936406592278641757 5324390601152472104490659)
                ·
                  refine ⟨7986585901728708156735989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5324390601152472104490659 7986585901728708156735989)
                  ·
                    refine ⟨748742428287066389693999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7986585901728708156735989 748742428287066389693999)
                    ·
                      rfl

theorem cell22_2187256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 3, 1, 5].length) (baseStart_2187256 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2187256 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2187256 prefixEnd_2187256 := by exact prefixLift 2187256
  have htrace : WordTrace (prefixWord ++ tailWord_2187256) baseStart_2187256 baseEnd_2187256 := by
    simpa [prefixWord, tailWord_2187256, baseEnd_2187256] using wordTrace_append hprefix tailTrace_2187256
  have hstable : (prefixWord ++ tailWord_2187256).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2187256).length < 2 ^ (prefixWord ++ tailWord_2187256).sum := by decide
  have hdescent : baseEnd_2187256 < baseStart_2187256 := by decide
  rcases family_descends (prefixWord ++ tailWord_2187256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2187290 : List Nat := [3, 1, 1, 3, 1, 3, 3, 2, 2, 3]
def baseStart_2187290 : Nat := 118140960795 + 2187290 * 2 ^ 59
def prefixEnd_2187290 : Nat := 4983230072969 + 3 ^ 40 * 2187290 * 2
def baseEnd_2187290 : Nat := 748754067181901634343895

theorem tailTrace_2187290 : CollatzResearch.WordTrace tailWord_2187290 prefixEnd_2187290 748754067181901634343895 := by
  unfold tailWord_2187290
  simp only [CollatzResearch.WordTrace]
  refine ⟨19944255061457341059131831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53184680163886242824351549 19944255061457341059131831)
  ·
    refine ⟨29916382592186011588697747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19944255061457341059131831 29916382592186011588697747)
    ·
      refine ⟨44874573888279017383046621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29916382592186011588697747 44874573888279017383046621)
      ·
        refine ⟨16827965208104631518642483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44874573888279017383046621 16827965208104631518642483)
        ·
          refine ⟨25241947812156947277963725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16827965208104631518642483 25241947812156947277963725)
          ·
            refine ⟨9465730429558855229236397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25241947812156947277963725 9465730429558855229236397)
            ·
              refine ⟨3549648911084570710963649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9465730429558855229236397 3549648911084570710963649)
              ·
                refine ⟨2662236683313428033222737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3549648911084570710963649 2662236683313428033222737)
                ·
                  refine ⟨1996677512485071024917053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2662236683313428033222737 1996677512485071024917053)
                  ·
                    refine ⟨748754067181901634343895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1996677512485071024917053 748754067181901634343895)
                    ·
                      rfl

theorem cell22_2187290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 3, 2, 2, 3].length) (baseStart_2187290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2187290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2187290 prefixEnd_2187290 := by exact prefixLift 2187290
  have htrace : WordTrace (prefixWord ++ tailWord_2187290) baseStart_2187290 baseEnd_2187290 := by
    simpa [prefixWord, tailWord_2187290, baseEnd_2187290] using wordTrace_append hprefix tailTrace_2187290
  have hstable : (prefixWord ++ tailWord_2187290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2187290).length < 2 ^ (prefixWord ++ tailWord_2187290).sum := by decide
  have hdescent : baseEnd_2187290 < baseStart_2187290 := by decide
  rcases family_descends (prefixWord ++ tailWord_2187290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2187318 : List Nat := [5, 1, 2, 1, 1, 1, 1, 1, 2, 7]
def baseStart_2187318 : Nat := 118140960795 + 2187318 * 2 ^ 59
def prefixEnd_2187318 : Nat := 4983230072969 + 3 ^ 40 * 2187318 * 2
def baseEnd_2187318 : Nat := 748763652154118894643809

theorem tailTrace_2187318 : CollatzResearch.WordTrace tailWord_2187318 prefixEnd_2187318 748763652154118894643809 := by
  unfold tailWord_2187318
  simp only [CollatzResearch.WordTrace]
  refine ⟨4986127593107995313659163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 53185360993151950012364405 4986127593107995313659163)
  ·
    refine ⟨7479191389661992970488745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4986127593107995313659163 7479191389661992970488745)
    ·
      refine ⟨5609393542246494727866559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7479191389661992970488745 5609393542246494727866559)
      ·
        refine ⟨8414090313369742091799839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5609393542246494727866559 8414090313369742091799839)
        ·
          refine ⟨12621135470054613137699759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8414090313369742091799839 12621135470054613137699759)
          ·
            refine ⟨18931703205081919706549639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12621135470054613137699759 18931703205081919706549639)
            ·
              refine ⟨28397554807622879559824459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18931703205081919706549639 28397554807622879559824459)
              ·
                refine ⟨42596332211434319339736689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28397554807622879559824459 42596332211434319339736689)
                ·
                  refine ⟨31947249158575739504802517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42596332211434319339736689 31947249158575739504802517)
                  ·
                    refine ⟨748763652154118894643809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31947249158575739504802517 748763652154118894643809)
                    ·
                      rfl

theorem cell22_2187318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 1, 2, 7].length) (baseStart_2187318 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2187318 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2187318 prefixEnd_2187318 := by exact prefixLift 2187318
  have htrace : WordTrace (prefixWord ++ tailWord_2187318) baseStart_2187318 baseEnd_2187318 := by
    simpa [prefixWord, tailWord_2187318, baseEnd_2187318] using wordTrace_append hprefix tailTrace_2187318
  have hstable : (prefixWord ++ tailWord_2187318).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2187318).length < 2 ^ (prefixWord ++ tailWord_2187318).sum := by decide
  have hdescent : baseEnd_2187318 < baseStart_2187318 := by decide
  rcases family_descends (prefixWord ++ tailWord_2187318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2187320 : List Nat := [2, 1, 2, 1, 6, 2, 2, 6]
def baseStart_2187320 : Nat := 118140960795 + 2187320 * 2 ^ 59
def prefixEnd_2187320 : Nat := 4983230072969 + 3 ^ 40 * 2187320 * 2
def baseEnd_2187320 : Nat := 83196037421665728454867

theorem tailTrace_2187320 : CollatzResearch.WordTrace tailWord_2187320 prefixEnd_2187320 83196037421665728454867 := by
  unfold tailWord_2187320
  simp only [CollatzResearch.WordTrace]
  refine ⟨39889057217860339680059707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53185409623813786240079609 39889057217860339680059707)
  ·
    refine ⟨59833585826790509520089561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39889057217860339680059707 59833585826790509520089561)
    ·
      refine ⟨44875189370092882140067171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59833585826790509520089561 44875189370092882140067171)
      ·
        refine ⟨67312784055139323210100757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44875189370092882140067171 67312784055139323210100757)
        ·
          refine ⟨3155286752584655775473473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 67312784055139323210100757 3155286752584655775473473)
          ·
            refine ⟨2366465064438491831605105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3155286752584655775473473 2366465064438491831605105)
            ·
              refine ⟨1774848798328868873703829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2366465064438491831605105 1774848798328868873703829)
              ·
                refine ⟨83196037421665728454867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1774848798328868873703829 83196037421665728454867)
                ·
                  rfl

theorem cell22_2187320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 2, 6].length) (baseStart_2187320 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2187320 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2187320 prefixEnd_2187320 := by exact prefixLift 2187320
  have htrace : WordTrace (prefixWord ++ tailWord_2187320) baseStart_2187320 baseEnd_2187320 := by
    simpa [prefixWord, tailWord_2187320, baseEnd_2187320] using wordTrace_append hprefix tailTrace_2187320
  have hstable : (prefixWord ++ tailWord_2187320).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2187320).length < 2 ^ (prefixWord ++ tailWord_2187320).sum := by decide
  have hdescent : baseEnd_2187320 < baseStart_2187320 := by decide
  rcases family_descends (prefixWord ++ tailWord_2187320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2187348 : List Nat := [2, 4, 1, 1, 1, 1, 1, 6, 5]
def baseStart_2187348 : Nat := 118140960795 + 2187348 * 2 ^ 59
def prefixEnd_2187348 : Nat := 4983230072969 + 3 ^ 40 * 2187348 * 2
def baseEnd_2187348 : Nat := 249591307255736272131239

theorem tailTrace_2187348 : CollatzResearch.WordTrace tailWord_2187348 prefixEnd_2187348 249591307255736272131239 := by
  unfold tailWord_2187348
  simp only [CollatzResearch.WordTrace]
  refine ⟨39889567839809620071069349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53186090453079493428092465 39889567839809620071069349)
  ·
    refine ⟨7479293969964303763325503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39889567839809620071069349 7479293969964303763325503)
    ·
      refine ⟨11218940954946455644988255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7479293969964303763325503 11218940954946455644988255)
      ·
        refine ⟨16828411432419683467482383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11218940954946455644988255 16828411432419683467482383)
        ·
          refine ⟨25242617148629525201223575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16828411432419683467482383 25242617148629525201223575)
          ·
            refine ⟨37863925722944287801835363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25242617148629525201223575 37863925722944287801835363)
            ·
              refine ⟨56795888584416431702753045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37863925722944287801835363 56795888584416431702753045)
              ·
                refine ⟨2662307277394520236066549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 56795888584416431702753045 2662307277394520236066549)
                ·
                  refine ⟨249591307255736272131239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2662307277394520236066549 249591307255736272131239)
                  ·
                    rfl

theorem cell22_2187348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 6, 5].length) (baseStart_2187348 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2187348 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2187348 prefixEnd_2187348 := by exact prefixLift 2187348
  have htrace : WordTrace (prefixWord ++ tailWord_2187348) baseStart_2187348 baseEnd_2187348 := by
    simpa [prefixWord, tailWord_2187348, baseEnd_2187348] using wordTrace_append hprefix tailTrace_2187348
  have hstable : (prefixWord ++ tailWord_2187348).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2187348).length < 2 ^ (prefixWord ++ tailWord_2187348).sum := by decide
  have hdescent : baseEnd_2187348 < baseStart_2187348 := by decide
  rcases family_descends (prefixWord ++ tailWord_2187348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2187358 : List Nat := [4, 4, 1, 1, 2, 2, 2, 1, 2, 3]
def baseStart_2187358 : Nat := 118140960795 + 2187358 * 2 ^ 59
def prefixEnd_2187358 : Nat := 4983230072969 + 3 ^ 40 * 2187358 * 2
def baseEnd_2187358 : Nat := 748777344971572123643687

theorem tailTrace_2187358 : CollatzResearch.WordTrace tailWord_2187358 prefixEnd_2187358 748777344971572123643687 := by
  unfold tailWord_2187358
  simp only [CollatzResearch.WordTrace]
  refine ⟨9972437551197876481250341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53186333606388674566668485 9972437551197876481250341)
  ·
    refine ⟨1869832040849601840234439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9972437551197876481250341 1869832040849601840234439)
    ·
      refine ⟨2804748061274402760351659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1869832040849601840234439 2804748061274402760351659)
      ·
        refine ⟨4207122091911604140527489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2804748061274402760351659 4207122091911604140527489)
        ·
          refine ⟨3155341568933703105395617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4207122091911604140527489 3155341568933703105395617)
          ·
            refine ⟨2366506176700277329046713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3155341568933703105395617 2366506176700277329046713)
            ·
              refine ⟨1774879632525207996785035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2366506176700277329046713 1774879632525207996785035)
              ·
                refine ⟨2662319448787811995177553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1774879632525207996785035 2662319448787811995177553)
                ·
                  refine ⟨1996739586590858996383165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2662319448787811995177553 1996739586590858996383165)
                  ·
                    refine ⟨748777344971572123643687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1996739586590858996383165 748777344971572123643687)
                    ·
                      rfl

theorem cell22_2187358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 2, 1, 2, 3].length) (baseStart_2187358 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2187358 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2187358 prefixEnd_2187358 := by exact prefixLift 2187358
  have htrace : WordTrace (prefixWord ++ tailWord_2187358) baseStart_2187358 baseEnd_2187358 := by
    simpa [prefixWord, tailWord_2187358, baseEnd_2187358] using wordTrace_append hprefix tailTrace_2187358
  have hstable : (prefixWord ++ tailWord_2187358).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2187358).length < 2 ^ (prefixWord ++ tailWord_2187358).sum := by decide
  have hdescent : baseEnd_2187358 < baseStart_2187358 := by decide
  rcases family_descends (prefixWord ++ tailWord_2187358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2187361 : List Nat := [1, 2, 3, 1, 1, 2, 1, 1, 2, 8]
def baseStart_2187361 : Nat := 118140960795 + 2187361 * 2 ^ 59
def prefixEnd_2187361 : Nat := 4983230072969 + 3 ^ 40 * 2187361 * 2
def baseEnd_2187361 : Nat := 748778371932881115818677

theorem tailTrace_2187361 : CollatzResearch.WordTrace tailWord_2187361 prefixEnd_2187361 748778371932881115818677 := by
  unfold tailWord_2187361
  simp only [CollatzResearch.WordTrace]
  refine ⟨79779609828572143362361937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53186406552381428908241291 79779609828572143362361937)
  ·
    refine ⟨59834707371429107521771453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79779609828572143362361937 59834707371429107521771453)
    ·
      refine ⟨22438015264285915320664295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59834707371429107521771453 22438015264285915320664295)
      ·
        refine ⟨33657022896428872980996443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22438015264285915320664295 33657022896428872980996443)
        ·
          refine ⟨50485534344643309471494665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33657022896428872980996443 50485534344643309471494665)
          ·
            refine ⟨37864150758482482103620999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50485534344643309471494665 37864150758482482103620999)
            ·
              refine ⟨56796226137723723155431499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37864150758482482103620999 56796226137723723155431499)
              ·
                refine ⟨85194339206585584733147249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56796226137723723155431499 85194339206585584733147249)
                ·
                  refine ⟨63895754404939188549860437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 85194339206585584733147249 63895754404939188549860437)
                  ·
                    refine ⟨748778371932881115818677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 63895754404939188549860437 748778371932881115818677)
                    ·
                      rfl

theorem cell22_2187361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 1, 2, 8].length) (baseStart_2187361 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2187361 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2187361 prefixEnd_2187361 := by exact prefixLift 2187361
  have htrace : WordTrace (prefixWord ++ tailWord_2187361) baseStart_2187361 baseEnd_2187361 := by
    simpa [prefixWord, tailWord_2187361, baseEnd_2187361] using wordTrace_append hprefix tailTrace_2187361
  have hstable : (prefixWord ++ tailWord_2187361).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2187361).length < 2 ^ (prefixWord ++ tailWord_2187361).sum := by decide
  have hdescent : baseEnd_2187361 < baseStart_2187361 := by decide
  rcases family_descends (prefixWord ++ tailWord_2187361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2187365 : List Nat := [1, 3, 1, 3, 2, 2, 4, 1, 5]
def baseStart_2187365 : Nat := 118140960795 + 2187365 * 2 ^ 59
def prefixEnd_2187365 : Nat := 4983230072969 + 3 ^ 40 * 2187365 * 2
def baseEnd_2187365 : Nat := 249593247071542146239555

theorem tailTrace_2187365 : CollatzResearch.WordTrace tailWord_2187365 prefixEnd_2187365 249593247071542146239555 := by
  unfold tailWord_2187365
  simp only [CollatzResearch.WordTrace]
  refine ⟨79779755720557652045507549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53186503813705101363671699 79779755720557652045507549)
  ·
    refine ⟨29917408395209119517065331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79779755720557652045507549 29917408395209119517065331)
    ·
      refine ⟨44876112592813679275597997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29917408395209119517065331 44876112592813679275597997)
      ·
        refine ⟨16828542222305129728349249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44876112592813679275597997 16828542222305129728349249)
        ·
          refine ⟨12621406666728847296261937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16828542222305129728349249 12621406666728847296261937)
          ·
            refine ⟨9466055000046635472196453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12621406666728847296261937 9466055000046635472196453)
            ·
              refine ⟨1774885312508744151036835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9466055000046635472196453 1774885312508744151036835)
              ·
                refine ⟨2662327968763116226555253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1774885312508744151036835 2662327968763116226555253)
                ·
                  refine ⟨249593247071542146239555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2662327968763116226555253 249593247071542146239555)
                  ·
                    rfl

theorem cell22_2187365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 4, 1, 5].length) (baseStart_2187365 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2187365 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2187365 prefixEnd_2187365 := by exact prefixLift 2187365
  have htrace : WordTrace (prefixWord ++ tailWord_2187365) baseStart_2187365 baseEnd_2187365 := by
    simpa [prefixWord, tailWord_2187365, baseEnd_2187365] using wordTrace_append hprefix tailTrace_2187365
  have hstable : (prefixWord ++ tailWord_2187365).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2187365).length < 2 ^ (prefixWord ++ tailWord_2187365).sum := by decide
  have hdescent : baseEnd_2187365 < baseStart_2187365 := by decide
  rcases family_descends (prefixWord ++ tailWord_2187365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2187425 : List Nat := [1, 2, 3, 3, 1, 3, 2, 1, 1, 5]
def baseStart_2187425 : Nat := 118140960795 + 2187425 * 2 ^ 59
def prefixEnd_2187425 : Nat := 4983230072969 + 3 ^ 40 * 2187425 * 2
def baseEnd_2187425 : Nat := 748800280440806282218481

theorem tailTrace_2187425 : CollatzResearch.WordTrace tailWord_2187425 prefixEnd_2187425 748800280440806282218481 := by
  unfold tailWord_2187425
  simp only [CollatzResearch.WordTrace]
  refine ⟨79781944100340282292691729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53187962733560188195127819 79781944100340282292691729)
  ·
    refine ⟨59836458075255211719518797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79781944100340282292691729 59836458075255211719518797)
    ·
      refine ⟨22438671778220704394819549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59836458075255211719518797 22438671778220704394819549)
      ·
        refine ⟨8414501916832764148057331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22438671778220704394819549 8414501916832764148057331)
        ·
          refine ⟨12621752875249146222085997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8414501916832764148057331 12621752875249146222085997)
          ·
            refine ⟨4733157328218429833282249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12621752875249146222085997 4733157328218429833282249)
            ·
              refine ⟨3549867996163822374961687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4733157328218429833282249 3549867996163822374961687)
              ·
                refine ⟨5324801994245733562442531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3549867996163822374961687 5324801994245733562442531)
                ·
                  refine ⟨7987202991368600343663797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5324801994245733562442531 7987202991368600343663797)
                  ·
                    refine ⟨748800280440806282218481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7987202991368600343663797 748800280440806282218481)
                    ·
                      rfl

theorem cell22_2187425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 2, 1, 1, 5].length) (baseStart_2187425 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2187425 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2187425 prefixEnd_2187425 := by exact prefixLift 2187425
  have htrace : WordTrace (prefixWord ++ tailWord_2187425) baseStart_2187425 baseEnd_2187425 := by
    simpa [prefixWord, tailWord_2187425, baseEnd_2187425] using wordTrace_append hprefix tailTrace_2187425
  have hstable : (prefixWord ++ tailWord_2187425).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2187425).length < 2 ^ (prefixWord ++ tailWord_2187425).sum := by decide
  have hdescent : baseEnd_2187425 < baseStart_2187425 := by decide
  rcases family_descends (prefixWord ++ tailWord_2187425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2187690 : List Nat := [3, 1, 6, 1, 1, 2, 1, 1, 3, 3]
def baseStart_2187690 : Nat := 118140960795 + 2187690 * 2 ^ 59
def prefixEnd_2187690 : Nat := 4983230072969 + 3 ^ 40 * 2187690 * 2
def baseEnd_2187690 : Nat := 748890995356433924342669

theorem tailTrace_2187690 : CollatzResearch.WordTrace tailWord_2187690 prefixEnd_2187690 748890995356433924342669 := by
  unfold tailWord_2187690
  simp only [CollatzResearch.WordTrace]
  refine ⟨19947902361095058137772131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53194406296253488367392349 19947902361095058137772131)
  ·
    refine ⟨29921853541642587206658197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19947902361095058137772131 29921853541642587206658197)
    ·
      refine ⟨1402586884764496275312103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 29921853541642587206658197 1402586884764496275312103)
      ·
        refine ⟨2103880327146744412968155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1402586884764496275312103 2103880327146744412968155)
        ·
          refine ⟨3155820490720116619452233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2103880327146744412968155 3155820490720116619452233)
          ·
            refine ⟨2366865368040087464589175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3155820490720116619452233 2366865368040087464589175)
            ·
              refine ⟨3550298052060131196883763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2366865368040087464589175 3550298052060131196883763)
              ·
                refine ⟨5325447078090196795325645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3550298052060131196883763 5325447078090196795325645)
                ·
                  refine ⟨1997042654283823798247117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5325447078090196795325645 1997042654283823798247117)
                  ·
                    refine ⟨748890995356433924342669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1997042654283823798247117 748890995356433924342669)
                    ·
                      rfl

theorem cell22_2187690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_2187690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2187690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2187690 prefixEnd_2187690 := by exact prefixLift 2187690
  have htrace : WordTrace (prefixWord ++ tailWord_2187690) baseStart_2187690 baseEnd_2187690 := by
    simpa [prefixWord, tailWord_2187690, baseEnd_2187690] using wordTrace_append hprefix tailTrace_2187690
  have hstable : (prefixWord ++ tailWord_2187690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2187690).length < 2 ^ (prefixWord ++ tailWord_2187690).sum := by decide
  have hdescent : baseEnd_2187690 < baseStart_2187690 := by decide
  rcases family_descends (prefixWord ++ tailWord_2187690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2187697 : List Nat := [1, 2, 2, 4, 1, 2, 3, 1, 6]
def baseStart_2187697 : Nat := 118140960795 + 2187697 * 2 ^ 59
def prefixEnd_2187697 : Nat := 4983230072969 + 3 ^ 40 * 2187697 * 2
def baseEnd_2187697 : Nat := 249631130533162746472549

theorem tailTrace_2187697 : CollatzResearch.WordTrace tailWord_2187697 prefixEnd_2187697 249631130533162746472549 := by
  unfold tailWord_2187697
  simp only [CollatzResearch.WordTrace]
  refine ⟨79791864755354872746593345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53194576503569915164395563 79791864755354872746593345)
  ·
    refine ⟨59843898566516154559945009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79791864755354872746593345 59843898566516154559945009)
    ·
      refine ⟨44882923924887115919958757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59843898566516154559945009 44882923924887115919958757)
      ·
        refine ⟨8415548235916334234992267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44882923924887115919958757 8415548235916334234992267)
        ·
          refine ⟨12623322353874501352488401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8415548235916334234992267 12623322353874501352488401)
          ·
            refine ⟨9467491765405876014366301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12623322353874501352488401 9467491765405876014366301)
            ·
              refine ⟨3550309412027203505387363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9467491765405876014366301 3550309412027203505387363)
              ·
                refine ⟨5325464118040805258081045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3550309412027203505387363 5325464118040805258081045)
                ·
                  refine ⟨249631130533162746472549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5325464118040805258081045 249631130533162746472549)
                  ·
                    rfl

theorem cell22_2187697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 3, 1, 6].length) (baseStart_2187697 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2187697 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2187697 prefixEnd_2187697 := by exact prefixLift 2187697
  have htrace : WordTrace (prefixWord ++ tailWord_2187697) baseStart_2187697 baseEnd_2187697 := by
    simpa [prefixWord, tailWord_2187697, baseEnd_2187697] using wordTrace_append hprefix tailTrace_2187697
  have hstable : (prefixWord ++ tailWord_2187697).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2187697).length < 2 ^ (prefixWord ++ tailWord_2187697).sum := by decide
  have hdescent : baseEnd_2187697 < baseStart_2187697 := by decide
  rcases family_descends (prefixWord ++ tailWord_2187697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2187755 : List Nat := [1, 1, 1, 1, 2, 3, 3, 1, 1, 8]
def baseStart_2187755 : Nat := 118140960795 + 2187755 * 2 ^ 59
def prefixEnd_2187755 : Nat := 4983230072969 + 3 ^ 40 * 2187755 * 2
def baseEnd_2187755 : Nat := 748913246184795421467469

theorem tailTrace_2187755 : CollatzResearch.WordTrace tailWord_2187755 prefixEnd_2187755 748913246184795421467469 := by
  unfold tailWord_2187755
  simp only [CollatzResearch.WordTrace]
  refine ⟨79793980189144748652204719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53195986792763165768136479 79793980189144748652204719)
  ·
    refine ⟨119690970283717122978307079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79793980189144748652204719 119690970283717122978307079)
    ·
      refine ⟨179536455425575684467460619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119690970283717122978307079 179536455425575684467460619)
      ·
        refine ⟨269304683138363526701190929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 179536455425575684467460619 269304683138363526701190929)
        ·
          refine ⟨201978512353772645025893197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 269304683138363526701190929 201978512353772645025893197)
          ·
            refine ⟨75741942132664741884709949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 201978512353772645025893197 75741942132664741884709949)
            ·
              refine ⟨28403228299749278206766231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 75741942132664741884709949 28403228299749278206766231)
              ·
                refine ⟨42604842449623917310149347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28403228299749278206766231 42604842449623917310149347)
                ·
                  refine ⟨63907263674435875965224021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42604842449623917310149347 63907263674435875965224021)
                  ·
                    refine ⟨748913246184795421467469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 63907263674435875965224021 748913246184795421467469)
                    ·
                      rfl

theorem cell22_2187755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 1, 1, 8].length) (baseStart_2187755 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2187755 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2187755 prefixEnd_2187755 := by exact prefixLift 2187755
  have htrace : WordTrace (prefixWord ++ tailWord_2187755) baseStart_2187755 baseEnd_2187755 := by
    simpa [prefixWord, tailWord_2187755, baseEnd_2187755] using wordTrace_append hprefix tailTrace_2187755
  have hstable : (prefixWord ++ tailWord_2187755).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2187755).length < 2 ^ (prefixWord ++ tailWord_2187755).sum := by decide
  have hdescent : baseEnd_2187755 < baseStart_2187755 := by decide
  rcases family_descends (prefixWord ++ tailWord_2187755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2187778 : List Nat := [3, 4, 1, 2, 2, 2, 1, 1, 2, 4]
def baseStart_2187778 : Nat := 118140960795 + 2187778 * 2 ^ 59
def prefixEnd_2187778 : Nat := 4983230072969 + 3 ^ 40 * 2187778 * 2
def baseEnd_2187778 : Nat := 748921119554831028142399

theorem tailTrace_2187778 : CollatzResearch.WordTrace tailWord_2187778 prefixEnd_2187778 748921119554831028142399 := by
  unfold tailWord_2187778
  simp only [CollatzResearch.WordTrace]
  refine ⟨19948704767015355895072997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53196546045374282386861325 19948704767015355895072997)
  ·
    refine ⟨3740382143815379230326187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19948704767015355895072997 3740382143815379230326187)
    ·
      refine ⟨5610573215723068845489281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3740382143815379230326187 5610573215723068845489281)
      ·
        refine ⟨4207929911792301634116961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5610573215723068845489281 4207929911792301634116961)
        ·
          refine ⟨3155947433844226225587721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4207929911792301634116961 3155947433844226225587721)
          ·
            refine ⟨2366960575383169669190791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3155947433844226225587721 2366960575383169669190791)
            ·
              refine ⟨3550440863074754503786187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2366960575383169669190791 3550440863074754503786187)
              ·
                refine ⟨5325661294612131755679281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3550440863074754503786187 5325661294612131755679281)
                ·
                  refine ⟨3994245970959098816759461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5325661294612131755679281 3994245970959098816759461)
                  ·
                    refine ⟨748921119554831028142399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3994245970959098816759461 748921119554831028142399)
                    ·
                      rfl

theorem cell22_2187778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 1, 1, 2, 4].length) (baseStart_2187778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2187778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2187778 prefixEnd_2187778 := by exact prefixLift 2187778
  have htrace : WordTrace (prefixWord ++ tailWord_2187778) baseStart_2187778 baseEnd_2187778 := by
    simpa [prefixWord, tailWord_2187778, baseEnd_2187778] using wordTrace_append hprefix tailTrace_2187778
  have hstable : (prefixWord ++ tailWord_2187778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2187778).length < 2 ^ (prefixWord ++ tailWord_2187778).sum := by decide
  have hdescent : baseEnd_2187778 < baseStart_2187778 := by decide
  rcases family_descends (prefixWord ++ tailWord_2187778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2187802 : List Nat := [3, 1, 1, 3, 1, 1, 3, 2, 2, 5]
def baseStart_2187802 : Nat := 118140960795 + 2187802 * 2 ^ 59
def prefixEnd_2187802 : Nat := 4983230072969 + 3 ^ 40 * 2187802 * 2
def baseEnd_2187802 : Nat := 748929335245302965542325

theorem tailTrace_2187802 : CollatzResearch.WordTrace tailWord_2187802 prefixEnd_2187802 748929335245302965542325 := by
  unfold tailWord_2187802
  simp only [CollatzResearch.WordTrace]
  refine ⟨19948923604993618919791415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53197129613316317119443773 19948923604993618919791415)
  ·
    refine ⟨29923385407490428379687123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19948923604993618919791415 29923385407490428379687123)
    ·
      refine ⟨44885078111235642569530685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29923385407490428379687123 44885078111235642569530685)
      ·
        refine ⟨16831904291713365963574007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44885078111235642569530685 16831904291713365963574007)
        ·
          refine ⟨25247856437570048945361011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16831904291713365963574007 25247856437570048945361011)
          ·
            refine ⟨37871784656355073418041517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25247856437570048945361011 37871784656355073418041517)
            ·
              refine ⟨14201919246133152531765569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37871784656355073418041517 14201919246133152531765569)
              ·
                refine ⟨10651439434599864398824177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14201919246133152531765569 10651439434599864398824177)
                ·
                  refine ⟨7988579575949898299118133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10651439434599864398824177 7988579575949898299118133)
                  ·
                    refine ⟨748929335245302965542325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7988579575949898299118133 748929335245302965542325)
                    ·
                      rfl

theorem cell22_2187802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 2, 2, 5].length) (baseStart_2187802 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2187802 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2187802 prefixEnd_2187802 := by exact prefixLift 2187802
  have htrace : WordTrace (prefixWord ++ tailWord_2187802) baseStart_2187802 baseEnd_2187802 := by
    simpa [prefixWord, tailWord_2187802, baseEnd_2187802] using wordTrace_append hprefix tailTrace_2187802
  have hstable : (prefixWord ++ tailWord_2187802).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2187802).length < 2 ^ (prefixWord ++ tailWord_2187802).sum := by decide
  have hdescent : baseEnd_2187802 < baseStart_2187802 := by decide
  rcases family_descends (prefixWord ++ tailWord_2187802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2187804 : List Nat := [2, 2, 3, 1, 2, 2, 3, 2, 5]
def baseStart_2187804 : Nat := 118140960795 + 2187804 * 2 ^ 59
def prefixEnd_2187804 : Nat := 4983230072969 + 3 ^ 40 * 2187804 * 2
def baseEnd_2187804 : Nat := 249643339962058542330773

theorem tailTrace_2187804 : CollatzResearch.WordTrace tailWord_2187804 prefixEnd_2187804 249643339962058542330773 := by
  unfold tailWord_2187804
  simp only [CollatzResearch.WordTrace]
  refine ⟨39897883682983615010369233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53197178243978153347158977 39897883682983615010369233)
  ·
    refine ⟨29923412762237711257776925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39897883682983615010369233 29923412762237711257776925)
    ·
      refine ⟨11221279785839141721666347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29923412762237711257776925 11221279785839141721666347)
      ·
        refine ⟨16831919678758712582499521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11221279785839141721666347 16831919678758712582499521)
        ·
          refine ⟨12623939759069034436874641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16831919678758712582499521 12623939759069034436874641)
          ·
            refine ⟨9467954819301775827655981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12623939759069034436874641 9467954819301775827655981)
            ·
              refine ⟨3550483057238165935370993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9467954819301775827655981 3550483057238165935370993)
              ·
                refine ⟨2662862292928624451528245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3550483057238165935370993 2662862292928624451528245)
                ·
                  refine ⟨249643339962058542330773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2662862292928624451528245 249643339962058542330773)
                  ·
                    rfl

theorem cell22_2187804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 3, 2, 5].length) (baseStart_2187804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2187804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2187804 prefixEnd_2187804 := by exact prefixLift 2187804
  have htrace : WordTrace (prefixWord ++ tailWord_2187804) baseStart_2187804 baseEnd_2187804 := by
    simpa [prefixWord, tailWord_2187804, baseEnd_2187804] using wordTrace_append hprefix tailTrace_2187804
  have hstable : (prefixWord ++ tailWord_2187804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2187804).length < 2 ^ (prefixWord ++ tailWord_2187804).sum := by decide
  have hdescent : baseEnd_2187804 < baseStart_2187804 := by decide
  rcases family_descends (prefixWord ++ tailWord_2187804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2187832 : List Nat := [2, 1, 2, 1, 4, 1, 1, 4, 6]
def baseStart_2187832 : Nat := 118140960795 + 2187832 * 2 ^ 59
def prefixEnd_2187832 : Nat := 4983230072969 + 3 ^ 40 * 2187832 * 2
def baseEnd_2187832 : Nat := 249646534952797629097411

theorem tailTrace_2187832 : CollatzResearch.WordTrace tailWord_2187832 prefixEnd_2187832 249646534952797629097411 := by
  unfold tailWord_2187832
  simp only [CollatzResearch.WordTrace]
  refine ⟨39898394304932895401378875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53197859073243860535171833 39898394304932895401378875)
  ·
    refine ⟨59847591457399343102068313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39898394304932895401378875 59847591457399343102068313)
    ·
      refine ⟨44885693593049507326551235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59847591457399343102068313 44885693593049507326551235)
      ·
        refine ⟨67328540389574260989826853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44885693593049507326551235 67328540389574260989826853)
        ·
          refine ⟨12624101323045173935592535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 67328540389574260989826853 12624101323045173935592535)
          ·
            refine ⟨18936151984567760903388803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12624101323045173935592535 18936151984567760903388803)
            ·
              refine ⟨28404227976851641355083205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18936151984567760903388803 28404227976851641355083205)
              ·
                refine ⟨5325792745659682754078101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28404227976851641355083205 5325792745659682754078101)
                ·
                  refine ⟨249646534952797629097411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5325792745659682754078101 249646534952797629097411)
                  ·
                    rfl

theorem cell22_2187832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 4, 6].length) (baseStart_2187832 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2187832 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2187832 prefixEnd_2187832 := by exact prefixLift 2187832
  have htrace : WordTrace (prefixWord ++ tailWord_2187832) baseStart_2187832 baseEnd_2187832 := by
    simpa [prefixWord, tailWord_2187832, baseEnd_2187832] using wordTrace_append hprefix tailTrace_2187832
  have hstable : (prefixWord ++ tailWord_2187832).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2187832).length < 2 ^ (prefixWord ++ tailWord_2187832).sum := by decide
  have hdescent : baseEnd_2187832 < baseStart_2187832 := by decide
  rcases family_descends (prefixWord ++ tailWord_2187832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2187834 : List Nat := [3, 1, 1, 1, 3, 3, 1, 4, 1, 4]
def baseStart_2187834 : Nat := 118140960795 + 2187834 * 2 ^ 59
def prefixEnd_2187834 : Nat := 4983230072969 + 3 ^ 40 * 2187834 * 2
def baseEnd_2187834 : Nat := 748940289499265548742227

theorem tailTrace_2187834 : CollatzResearch.WordTrace tailWord_2187834 prefixEnd_2187834 748940289499265548742227 := by
  unfold tailWord_2187834
  simp only [CollatzResearch.WordTrace]
  refine ⟨19949215388964636286082639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53197907703905696762887037 19949215388964636286082639)
  ·
    refine ⟨29923823083446954429123959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19949215388964636286082639 29923823083446954429123959)
    ·
      refine ⟨44885734625170431643685939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29923823083446954429123959 44885734625170431643685939)
      ·
        refine ⟨67328601937755647465528909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44885734625170431643685939 67328601937755647465528909)
        ·
          refine ⟨25248225726658367799573341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67328601937755647465528909 25248225726658367799573341)
          ·
            refine ⟨9468084647496887924840003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25248225726658367799573341 9468084647496887924840003)
            ·
              refine ⟨14202126971245331887260005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9468084647496887924840003 14202126971245331887260005)
              ·
                refine ⟨2662898807108499728861251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14202126971245331887260005 2662898807108499728861251)
                ·
                  refine ⟨3994348210662749593291877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2662898807108499728861251 3994348210662749593291877)
                  ·
                    refine ⟨748940289499265548742227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3994348210662749593291877 748940289499265548742227)
                    ·
                      rfl

theorem cell22_2187834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 4, 1, 4].length) (baseStart_2187834 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2187834 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2187834 prefixEnd_2187834 := by exact prefixLift 2187834
  have htrace : WordTrace (prefixWord ++ tailWord_2187834) baseStart_2187834 baseEnd_2187834 := by
    simpa [prefixWord, tailWord_2187834, baseEnd_2187834] using wordTrace_append hprefix tailTrace_2187834
  have hstable : (prefixWord ++ tailWord_2187834).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2187834).length < 2 ^ (prefixWord ++ tailWord_2187834).sum := by decide
  have hdescent : baseEnd_2187834 < baseStart_2187834 := by decide
  rcases family_descends (prefixWord ++ tailWord_2187834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2187864 : List Nat := [2, 1, 2, 2, 1, 2, 4, 1, 4, 3]
def baseStart_2187864 : Nat := 118140960795 + 2187864 * 2 ^ 59
def prefixEnd_2187864 : Nat := 4983230072969 + 3 ^ 40 * 2187864 * 2
def baseEnd_2187864 : Nat := 748950559112355470492135

theorem tailTrace_2187864 : CollatzResearch.WordTrace tailWord_2187864 prefixEnd_2187864 748950559112355470492135 := by
  unfold tailWord_2187864
  simp only [CollatzResearch.WordTrace]
  refine ⟨39898977872874930133961323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53198637163833240178615097 39898977872874930133961323)
  ·
    refine ⟨59848466809312395200941985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39898977872874930133961323 59848466809312395200941985)
    ·
      refine ⟨44886350106984296400706489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59848466809312395200941985 44886350106984296400706489)
      ·
        refine ⟨33664762580238222300529867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44886350106984296400706489 33664762580238222300529867)
        ·
          refine ⟨50497143870357333450794801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33664762580238222300529867 50497143870357333450794801)
          ·
            refine ⟨37872857902768000088096101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50497143870357333450794801 37872857902768000088096101)
            ·
              refine ⟨7101160856769000016518019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37872857902768000088096101 7101160856769000016518019)
              ·
                refine ⟨10651741285153500024777029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7101160856769000016518019 10651741285153500024777029)
                ·
                  refine ⟨1997201490966281254645693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10651741285153500024777029 1997201490966281254645693)
                  ·
                    refine ⟨748950559112355470492135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1997201490966281254645693 748950559112355470492135)
                    ·
                      rfl

theorem cell22_2187864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 1, 4, 3].length) (baseStart_2187864 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2187864 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2187864 prefixEnd_2187864 := by exact prefixLift 2187864
  have htrace : WordTrace (prefixWord ++ tailWord_2187864) baseStart_2187864 baseEnd_2187864 := by
    simpa [prefixWord, tailWord_2187864, baseEnd_2187864] using wordTrace_append hprefix tailTrace_2187864
  have hstable : (prefixWord ++ tailWord_2187864).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2187864).length < 2 ^ (prefixWord ++ tailWord_2187864).sum := by decide
  have hdescent : baseEnd_2187864 < baseStart_2187864 := by decide
  rcases family_descends (prefixWord ++ tailWord_2187864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2188003 : List Nat := [1, 1, 1, 7, 1, 2, 2, 2, 1, 4]
def baseStart_2188003 : Nat := 118140960795 + 2188003 * 2 ^ 59
def prefixEnd_2188003 : Nat := 4983230072969 + 3 ^ 40 * 2188003 * 2
def baseEnd_2188003 : Nat := 748998141653005441266709

theorem tailTrace_2188003 : CollatzResearch.WordTrace tailWord_2188003 prefixEnd_2188003 748998141653005441266709 := by
  unfold tailWord_2188003
  simp only [CollatzResearch.WordTrace]
  refine ⟨79803025492246287007232663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53202016994830858004821775 79803025492246287007232663)
  ·
    refine ⟨119704538238369430510848995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79803025492246287007232663 119704538238369430510848995)
    ·
      refine ⟨179556807357554145766273493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119704538238369430510848995 179556807357554145766273493)
      ·
        refine ⟨4208362672442675291397035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 179556807357554145766273493 4208362672442675291397035)
        ·
          refine ⟨6312544008664012937095553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4208362672442675291397035 6312544008664012937095553)
          ·
            refine ⟨4734408006498009702821665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6312544008664012937095553 4734408006498009702821665)
            ·
              refine ⟨3550806004873507277116249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4734408006498009702821665 3550806004873507277116249)
              ·
                refine ⟨2663104503655130457837187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3550806004873507277116249 2663104503655130457837187)
                ·
                  refine ⟨3994656755482695686755781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2663104503655130457837187 3994656755482695686755781)
                  ·
                    refine ⟨748998141653005441266709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3994656755482695686755781 748998141653005441266709)
                    ·
                      rfl

theorem cell22_2188003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 2, 2, 1, 4].length) (baseStart_2188003 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2188003 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2188003 prefixEnd_2188003 := by exact prefixLift 2188003
  have htrace : WordTrace (prefixWord ++ tailWord_2188003) baseStart_2188003 baseEnd_2188003 := by
    simpa [prefixWord, tailWord_2188003, baseEnd_2188003] using wordTrace_append hprefix tailTrace_2188003
  have hstable : (prefixWord ++ tailWord_2188003).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2188003).length < 2 ^ (prefixWord ++ tailWord_2188003).sum := by decide
  have hdescent : baseEnd_2188003 < baseStart_2188003 := by decide
  rcases family_descends (prefixWord ++ tailWord_2188003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2188018 : List Nat := [3, 2, 1, 3, 1, 2, 3, 3, 4]
def baseStart_2188018 : Nat := 118140960795 + 2188018 * 2 ^ 59
def prefixEnd_2188018 : Nat := 4983230072969 + 3 ^ 40 * 2188018 * 2
def baseEnd_2188018 : Nat := 249667758819850134047221

theorem tailTrace_2188018 : CollatzResearch.WordTrace tailWord_2188018 prefixEnd_2188018 249667758819850134047221 := by
  unfold tailWord_2188018
  simp only [CollatzResearch.WordTrace]
  refine ⟨19950893146797986142257177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53202381724794629712685805 19950893146797986142257177)
  ·
    refine ⟨14963169860098489606692883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19950893146797986142257177 14963169860098489606692883)
    ·
      refine ⟨22444754790147734410039325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14963169860098489606692883 22444754790147734410039325)
      ·
        refine ⟨8416783046305400403764747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22444754790147734410039325 8416783046305400403764747)
        ·
          refine ⟨12625174569458100605647121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8416783046305400403764747 12625174569458100605647121)
          ·
            refine ⟨9468880927093575454235341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12625174569458100605647121 9468880927093575454235341)
            ·
              refine ⟨3550830347660090795338253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9468880927093575454235341 3550830347660090795338253)
              ·
                refine ⟨1331561380372534048251845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3550830347660090795338253 1331561380372534048251845)
                ·
                  refine ⟨249667758819850134047221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1331561380372534048251845 249667758819850134047221)
                  ·
                    rfl

theorem cell22_2188018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 3, 3, 4].length) (baseStart_2188018 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2188018 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2188018 prefixEnd_2188018 := by exact prefixLift 2188018
  have htrace : WordTrace (prefixWord ++ tailWord_2188018) baseStart_2188018 baseEnd_2188018 := by
    simpa [prefixWord, tailWord_2188018, baseEnd_2188018] using wordTrace_append hprefix tailTrace_2188018
  have hstable : (prefixWord ++ tailWord_2188018).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2188018).length < 2 ^ (prefixWord ++ tailWord_2188018).sum := by decide
  have hdescent : baseEnd_2188018 < baseStart_2188018 := by decide
  rcases family_descends (prefixWord ++ tailWord_2188018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2188095 : List Nat := [1, 1, 2, 2, 5, 2, 1, 4, 1, 3]
def baseStart_2188095 : Nat := 118140960795 + 2188095 * 2 ^ 59
def prefixEnd_2188095 : Nat := 4983230072969 + 3 ^ 40 * 2188095 * 2
def baseEnd_2188095 : Nat := 749029635133147867966427

theorem tailTrace_2188095 : CollatzResearch.WordTrace tailWord_2188095 prefixEnd_2188095 749029635133147867966427 := by
  unfold tailWord_2188095
  simp only [CollatzResearch.WordTrace]
  refine ⟨79806381007912986719581739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53204254005275324479721159 79806381007912986719581739)
  ·
    refine ⟨119709571511869480079372609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79806381007912986719581739 119709571511869480079372609)
    ·
      refine ⟨89782178633902110059529457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119709571511869480079372609 89782178633902110059529457)
      ·
        refine ⟨67336633975426582544647093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89782178633902110059529457 67336633975426582544647093)
        ·
          refine ⟨6312809435196242113560665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 67336633975426582544647093 6312809435196242113560665)
          ·
            refine ⟨4734607076397181585170499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6312809435196242113560665 4734607076397181585170499)
            ·
              refine ⟨7101910614595772377755749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4734607076397181585170499 7101910614595772377755749)
              ·
                refine ⟨1331608240236707320829203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7101910614595772377755749 1331608240236707320829203)
                ·
                  refine ⟨1997412360355060981243805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1331608240236707320829203 1997412360355060981243805)
                  ·
                    refine ⟨749029635133147867966427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1997412360355060981243805 749029635133147867966427)
                    ·
                      rfl

theorem cell22_2188095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 4, 1, 3].length) (baseStart_2188095 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2188095 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2188095 prefixEnd_2188095 := by exact prefixLift 2188095
  have htrace : WordTrace (prefixWord ++ tailWord_2188095) baseStart_2188095 baseEnd_2188095 := by
    simpa [prefixWord, tailWord_2188095, baseEnd_2188095] using wordTrace_append hprefix tailTrace_2188095
  have hstable : (prefixWord ++ tailWord_2188095).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2188095).length < 2 ^ (prefixWord ++ tailWord_2188095).sum := by decide
  have hdescent : baseEnd_2188095 < baseStart_2188095 := by decide
  rcases family_descends (prefixWord ++ tailWord_2188095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2188121 : List Nat := [1, 2, 1, 2, 2, 4, 2, 1, 3, 4]
def baseStart_2188121 : Nat := 118140960795 + 2188121 * 2 ^ 59
def prefixEnd_2188121 : Nat := 4983230072969 + 3 ^ 40 * 2188121 * 2
def baseEnd_2188121 : Nat := 749038535464492466816347

theorem tailTrace_2188121 : CollatzResearch.WordTrace tailWord_2188121 prefixEnd_2188121 749038535464492466816347 := by
  unfold tailWord_2188121
  simp only [CollatzResearch.WordTrace]
  refine ⟨79807329305818793160028217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53204886203879195440018811 79807329305818793160028217)
  ·
    refine ⟨59855496979364094870021163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79807329305818793160028217 59855496979364094870021163)
    ·
      refine ⟨89783245469046142305031745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59855496979364094870021163 89783245469046142305031745)
      ·
        refine ⟨67337434101784606728773809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89783245469046142305031745 67337434101784606728773809)
        ·
          refine ⟨50503075576338455046580357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67337434101784606728773809 50503075576338455046580357)
          ·
            refine ⟨9469326670563460321233817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50503075576338455046580357 9469326670563460321233817)
            ·
              refine ⟨7101995002922595240925363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9469326670563460321233817 7101995002922595240925363)
              ·
                refine ⟨10652992504383892861388045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7101995002922595240925363 10652992504383892861388045)
                ·
                  refine ⟨3994872189143959823020517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10652992504383892861388045 3994872189143959823020517)
                  ·
                    refine ⟨749038535464492466816347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3994872189143959823020517 749038535464492466816347)
                    ·
                      rfl

theorem cell22_2188121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 1, 3, 4].length) (baseStart_2188121 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2188121 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2188121 prefixEnd_2188121 := by exact prefixLift 2188121
  have htrace : WordTrace (prefixWord ++ tailWord_2188121) baseStart_2188121 baseEnd_2188121 := by
    simpa [prefixWord, tailWord_2188121, baseEnd_2188121] using wordTrace_append hprefix tailTrace_2188121
  have hstable : (prefixWord ++ tailWord_2188121).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2188121).length < 2 ^ (prefixWord ++ tailWord_2188121).sum := by decide
  have hdescent : baseEnd_2188121 < baseStart_2188121 := by decide
  rcases family_descends (prefixWord ++ tailWord_2188121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2188142 : List Nat := [4, 1, 2, 3, 3, 1, 1, 2, 5]
def baseStart_2188142 : Nat := 118140960795 + 2188142 * 2 ^ 59
def prefixEnd_2188142 : Nat := 4983230072969 + 3 ^ 40 * 2188142 * 2
def baseEnd_2188142 : Nat := 249681908064551804013761

theorem tailTrace_2188142 : CollatzResearch.WordTrace tailWord_2188142 prefixEnd_2188142 249681908064551804013761 := by
  unfold tailWord_2188142
  simp only [CollatzResearch.WordTrace]
  refine ⟨9976011904842839218317835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53205396825828475831028453 9976011904842839218317835)
  ·
    refine ⟨14964017857264258827476753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9976011904842839218317835 14964017857264258827476753)
    ·
      refine ⟨11223013392948194120607565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14964017857264258827476753 11223013392948194120607565)
      ·
        refine ⟨4208630022355572795227837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11223013392948194120607565 4208630022355572795227837)
        ·
          refine ⟨1578236258383339798210439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4208630022355572795227837 1578236258383339798210439)
          ·
            refine ⟨2367354387575009697315659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1578236258383339798210439 2367354387575009697315659)
            ·
              refine ⟨3551031581362514545973489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2367354387575009697315659 3551031581362514545973489)
              ·
                refine ⟨2663273686021885909480117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3551031581362514545973489 2663273686021885909480117)
                ·
                  refine ⟨249681908064551804013761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2663273686021885909480117 249681908064551804013761)
                  ·
                    rfl

theorem cell22_2188142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 1, 2, 5].length) (baseStart_2188142 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2188142 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2188142 prefixEnd_2188142 := by exact prefixLift 2188142
  have htrace : WordTrace (prefixWord ++ tailWord_2188142) baseStart_2188142 baseEnd_2188142 := by
    simpa [prefixWord, tailWord_2188142, baseEnd_2188142] using wordTrace_append hprefix tailTrace_2188142
  have hstable : (prefixWord ++ tailWord_2188142).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2188142).length < 2 ^ (prefixWord ++ tailWord_2188142).sum := by decide
  have hdescent : baseEnd_2188142 < baseStart_2188142 := by decide
  rcases family_descends (prefixWord ++ tailWord_2188142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2188153 : List Nat := [1, 2, 1, 3, 2, 3, 2, 4, 4]
def baseStart_2188153 : Nat := 118140960795 + 2188153 * 2 ^ 59
def prefixEnd_2188153 : Nat := 4983230072969 + 3 ^ 40 * 2188153 * 2
def baseEnd_2188153 : Nat := 249683163239485016672083

theorem tailTrace_2188153 : CollatzResearch.WordTrace tailWord_2188153 prefixEnd_2188153 249683163239485016672083 := by
  unfold tailWord_2188153
  simp only [CollatzResearch.WordTrace]
  refine ⟨79808496441702862625193113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53205664294468575083462075 79808496441702862625193113)
  ·
    refine ⟨59856372331277146968894835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79808496441702862625193113 59856372331277146968894835)
    ·
      refine ⟨89784558496915720453342253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59856372331277146968894835 89784558496915720453342253)
      ·
        refine ⟨33669209436343395170003345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89784558496915720453342253 33669209436343395170003345)
        ·
          refine ⟨25251907077257546377502509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33669209436343395170003345 25251907077257546377502509)
          ·
            refine ⟨9469465153971579891563441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25251907077257546377502509 9469465153971579891563441)
            ·
              refine ⟨7102098865478684918672581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9469465153971579891563441 7102098865478684918672581)
              ·
                refine ⟨1331643537277253422251109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7102098865478684918672581 1331643537277253422251109)
                ·
                  refine ⟨249683163239485016672083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1331643537277253422251109 249683163239485016672083)
                  ·
                    rfl

theorem cell22_2188153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 4, 4].length) (baseStart_2188153 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2188153 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2188153 prefixEnd_2188153 := by exact prefixLift 2188153
  have htrace : WordTrace (prefixWord ++ tailWord_2188153) baseStart_2188153 baseEnd_2188153 := by
    simpa [prefixWord, tailWord_2188153, baseEnd_2188153] using wordTrace_append hprefix tailTrace_2188153
  have hstable : (prefixWord ++ tailWord_2188153).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2188153).length < 2 ^ (prefixWord ++ tailWord_2188153).sum := by decide
  have hdescent : baseEnd_2188153 < baseStart_2188153 := by decide
  rcases family_descends (prefixWord ++ tailWord_2188153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2188168 : List Nat := [2, 1, 3, 3, 2, 1, 3, 1, 1, 5]
def baseStart_2188168 : Nat := 118140960795 + 2188168 * 2 ^ 59
def prefixEnd_2188168 : Nat := 4983230072969 + 3 ^ 40 * 2188168 * 2
def baseEnd_2188168 : Nat := 749054624525000010891203

theorem tailTrace_2188168 : CollatzResearch.WordTrace tailWord_2188168 prefixEnd_2188168 749054624525000010891203 := by
  unfold tailWord_2188168
  simp only [CollatzResearch.WordTrace]
  refine ⟨39904521768324260093494579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53206029024432346791326105 39904521768324260093494579)
  ·
    refine ⟨59856782652486390140241869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39904521768324260093494579 59856782652486390140241869)
    ·
      refine ⟨22446293494682396302590701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59856782652486390140241869 22446293494682396302590701)
      ·
        refine ⟨8417360060505898613471513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22446293494682396302590701 8417360060505898613471513)
        ·
          refine ⟨6313020045379423960103635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8417360060505898613471513 6313020045379423960103635)
          ·
            refine ⟨9469530068069135940155453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6313020045379423960103635 9469530068069135940155453)
            ·
              refine ⟨3551073775525925977558295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9469530068069135940155453 3551073775525925977558295)
              ·
                refine ⟨5326610663288888966337443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3551073775525925977558295 5326610663288888966337443)
                ·
                  refine ⟨7989915994933333449506165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5326610663288888966337443 7989915994933333449506165)
                  ·
                    refine ⟨749054624525000010891203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7989915994933333449506165 749054624525000010891203)
                    ·
                      rfl

theorem cell22_2188168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 3, 1, 1, 5].length) (baseStart_2188168 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2188168 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2188168 prefixEnd_2188168 := by exact prefixLift 2188168
  have htrace : WordTrace (prefixWord ++ tailWord_2188168) baseStart_2188168 baseEnd_2188168 := by
    simpa [prefixWord, tailWord_2188168, baseEnd_2188168] using wordTrace_append hprefix tailTrace_2188168
  have hstable : (prefixWord ++ tailWord_2188168).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2188168).length < 2 ^ (prefixWord ++ tailWord_2188168).sum := by decide
  have hdescent : baseEnd_2188168 < baseStart_2188168 := by decide
  rcases family_descends (prefixWord ++ tailWord_2188168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2188181 : List Nat := [1, 3, 2, 1, 1, 5, 1, 8]
def baseStart_2188181 : Nat := 118140960795 + 2188181 * 2 ^ 59
def prefixEnd_2188181 : Nat := 4983230072969 + 3 ^ 40 * 2188181 * 2
def baseEnd_2188181 : Nat := 83228786076741367812907

theorem tailTrace_2188181 : CollatzResearch.WordTrace tailWord_2188181 prefixEnd_2188181 83228786076741367812907 := by
  unfold tailWord_2188181
  simp only [CollatzResearch.WordTrace]
  refine ⟨79809517685601423407212397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53206345123734282271474931 79809517685601423407212397)
  ·
    refine ⟨29928569132100533777704649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79809517685601423407212397 29928569132100533777704649)
    ·
      refine ⟨22446426849075400333278487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29928569132100533777704649 22446426849075400333278487)
      ·
        refine ⟨33669640273613100499917731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22446426849075400333278487 33669640273613100499917731)
        ·
          refine ⟨50504460410419650749876597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33669640273613100499917731 50504460410419650749876597)
          ·
            refine ⟨4734793163476842257800931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 50504460410419650749876597 4734793163476842257800931)
            ·
              refine ⟨7102189745215263386701397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4734793163476842257800931 7102189745215263386701397)
              ·
                refine ⟨83228786076741367812907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7102189745215263386701397 83228786076741367812907)
                ·
                  rfl

theorem cell22_2188181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 8].length) (baseStart_2188181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2188181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2188181 prefixEnd_2188181 := by exact prefixLift 2188181
  have htrace : WordTrace (prefixWord ++ tailWord_2188181) baseStart_2188181 baseEnd_2188181 := by
    simpa [prefixWord, tailWord_2188181, baseEnd_2188181] using wordTrace_append hprefix tailTrace_2188181
  have hstable : (prefixWord ++ tailWord_2188181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2188181).length < 2 ^ (prefixWord ++ tailWord_2188181).sum := by decide
  have hdescent : baseEnd_2188181 < baseStart_2188181 := by decide
  rcases family_descends (prefixWord ++ tailWord_2188181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2188273 : List Nat := [1, 2, 2, 2, 4, 1, 1, 2, 3, 4]
def baseStart_2188273 : Nat := 118140960795 + 2188273 * 2 ^ 59
def prefixEnd_2188273 : Nat := 4983230072969 + 3 ^ 40 * 2188273 * 2
def baseEnd_2188273 : Nat := 749090568170814737015881

theorem tailTrace_2188273 : CollatzResearch.WordTrace tailWord_2188273 prefixEnd_2188273 749090568170814737015881 := by
  unfold tailWord_2188273
  simp only [CollatzResearch.WordTrace]
  refine ⟨79812873201268123119561473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53208582134178748746374315 79812873201268123119561473)
  ·
    refine ⟨59859654900951092339671105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79812873201268123119561473 59859654900951092339671105)
    ·
      refine ⟨44894741175713319254753329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59859654900951092339671105 44894741175713319254753329)
      ·
        refine ⟨33671055881784989441064997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44894741175713319254753329 33671055881784989441064997)
        ·
          refine ⟨6313322977834685520199687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33671055881784989441064997 6313322977834685520199687)
          ·
            refine ⟨9469984466752028280299531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6313322977834685520199687 9469984466752028280299531)
            ·
              refine ⟨14204976700128042420449297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9469984466752028280299531 14204976700128042420449297)
              ·
                refine ⟨10653732525096031815336973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14204976700128042420449297 10653732525096031815336973)
                ·
                  refine ⟨3995149696911011930751365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10653732525096031815336973 3995149696911011930751365)
                  ·
                    refine ⟨749090568170814737015881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3995149696911011930751365 749090568170814737015881)
                    ·
                      rfl

theorem cell22_2188273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 2, 3, 4].length) (baseStart_2188273 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2188273 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2188273 prefixEnd_2188273 := by exact prefixLift 2188273
  have htrace : WordTrace (prefixWord ++ tailWord_2188273) baseStart_2188273 baseEnd_2188273 := by
    simpa [prefixWord, tailWord_2188273, baseEnd_2188273] using wordTrace_append hprefix tailTrace_2188273
  have hstable : (prefixWord ++ tailWord_2188273).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2188273).length < 2 ^ (prefixWord ++ tailWord_2188273).sum := by decide
  have hdescent : baseEnd_2188273 < baseStart_2188273 := by decide
  rcases family_descends (prefixWord ++ tailWord_2188273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2188337 : List Nat := [1, 2, 2, 3, 1, 2, 5, 1, 2, 3]
def baseStart_2188337 : Nat := 118140960795 + 2188337 * 2 ^ 59
def prefixEnd_2188337 : Nat := 4983230072969 + 3 ^ 40 * 2188337 * 2
def baseEnd_2188337 : Nat := 749112476678739903415685

theorem tailTrace_2188337 : CollatzResearch.WordTrace tailWord_2188337 prefixEnd_2188337 749112476678739903415685 := by
  unfold tailWord_2188337
  simp only [CollatzResearch.WordTrace]
  refine ⟨79815207473036262049891265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53210138315357508033260843 79815207473036262049891265)
  ·
    refine ⟨59861405604777196537418449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79815207473036262049891265 59861405604777196537418449)
    ·
      refine ⟨44896054203582897403063837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59861405604777196537418449 44896054203582897403063837)
      ·
        refine ⟨16836020326343586526148939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44896054203582897403063837 16836020326343586526148939)
        ·
          refine ⟨25254030489515379789223409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16836020326343586526148939 25254030489515379789223409)
          ·
            refine ⟨18940522867136534841917557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25254030489515379789223409 18940522867136534841917557)
            ·
              refine ⟨1775674018794050141429771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18940522867136534841917557 1775674018794050141429771)
              ·
                refine ⟨2663511028191075212144657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1775674018794050141429771 2663511028191075212144657)
                ·
                  refine ⟨1997633271143306409108493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2663511028191075212144657 1997633271143306409108493)
                  ·
                    refine ⟨749112476678739903415685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1997633271143306409108493 749112476678739903415685)
                    ·
                      rfl

theorem cell22_2188337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 5, 1, 2, 3].length) (baseStart_2188337 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2188337 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2188337 prefixEnd_2188337 := by exact prefixLift 2188337
  have htrace : WordTrace (prefixWord ++ tailWord_2188337) baseStart_2188337 baseEnd_2188337 := by
    simpa [prefixWord, tailWord_2188337, baseEnd_2188337] using wordTrace_append hprefix tailTrace_2188337
  have hstable : (prefixWord ++ tailWord_2188337).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2188337).length < 2 ^ (prefixWord ++ tailWord_2188337).sum := by decide
  have hdescent : baseEnd_2188337 < baseStart_2188337 := by decide
  rcases family_descends (prefixWord ++ tailWord_2188337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2188350 : List Nat := [4, 2, 1, 3, 1, 2, 1, 8]
def baseStart_2188350 : Nat := 118140960795 + 2188350 * 2 ^ 59
def prefixEnd_2188350 : Nat := 4983230072969 + 3 ^ 40 * 2188350 * 2
def baseEnd_2188350 : Nat := 83235214093823578093405

theorem tailTrace_2188350 : CollatzResearch.WordTrace tailWord_2188350 prefixEnd_2188350 83235214093823578093405 := by
  unfold tailWord_2188350
  simp only [CollatzResearch.WordTrace]
  refine ⟨9976960202748645658764313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53210454414659443513409669 9976960202748645658764313)
  ·
    refine ⟨7482720152061484244073235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9976960202748645658764313 7482720152061484244073235)
    ·
      refine ⟨11224080228092226366109853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7482720152061484244073235 11224080228092226366109853)
      ·
        refine ⟨4209030085534584887291195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11224080228092226366109853 4209030085534584887291195)
        ·
          refine ⟨6313545128301877330936793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4209030085534584887291195 6313545128301877330936793)
          ·
            refine ⟨4735158846226407998202595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6313545128301877330936793 4735158846226407998202595)
            ·
              refine ⟨7102738269339611997303893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4735158846226407998202595 7102738269339611997303893)
              ·
                refine ⟨83235214093823578093405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7102738269339611997303893 83235214093823578093405)
                ·
                  rfl

theorem cell22_2188350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 8].length) (baseStart_2188350 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2188350 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2188350 prefixEnd_2188350 := by exact prefixLift 2188350
  have htrace : WordTrace (prefixWord ++ tailWord_2188350) baseStart_2188350 baseEnd_2188350 := by
    simpa [prefixWord, tailWord_2188350, baseEnd_2188350] using wordTrace_append hprefix tailTrace_2188350
  have hstable : (prefixWord ++ tailWord_2188350).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2188350).length < 2 ^ (prefixWord ++ tailWord_2188350).sum := by decide
  have hdescent : baseEnd_2188350 < baseStart_2188350 := by decide
  rcases family_descends (prefixWord ++ tailWord_2188350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2188519 : List Nat := [1, 1, 5, 3, 2, 2, 2, 6]
def baseStart_2188519 : Nat := 118140960795 + 2188519 * 2 ^ 59
def prefixEnd_2188519 : Nat := 4983230072969 + 3 ^ 40 * 2188519 * 2
def baseEnd_2188519 : Nat := 83241642110905788373903

theorem tailTrace_2188519 : CollatzResearch.WordTrace tailWord_2188519 prefixEnd_2188519 83241642110905788373903 := by
  unfold tailWord_2188519
  simp only [CollatzResearch.WordTrace]
  refine ⟨79821845558376907133016611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53214563705584604755344407 79821845558376907133016611)
  ·
    refine ⟨119732768337565360699524917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79821845558376907133016611 119732768337565360699524917)
    ·
      refine ⟨11224947031646752565580461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 119732768337565360699524917 11224947031646752565580461)
      ·
        refine ⟨4209355136867532212092673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11224947031646752565580461 4209355136867532212092673)
        ·
          refine ⟨3157016352650649159069505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4209355136867532212092673 3157016352650649159069505)
          ·
            refine ⟨2367762264487986869302129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3157016352650649159069505 2367762264487986869302129)
            ·
              refine ⟨1775821698365990151976597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2367762264487986869302129 1775821698365990151976597)
              ·
                refine ⟨83241642110905788373903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1775821698365990151976597 83241642110905788373903)
                ·
                  rfl

theorem cell22_2188519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 2, 6].length) (baseStart_2188519 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2188519 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2188519 prefixEnd_2188519 := by exact prefixLift 2188519
  have htrace : WordTrace (prefixWord ++ tailWord_2188519) baseStart_2188519 baseEnd_2188519 := by
    simpa [prefixWord, tailWord_2188519, baseEnd_2188519] using wordTrace_append hprefix tailTrace_2188519
  have hstable : (prefixWord ++ tailWord_2188519).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2188519).length < 2 ^ (prefixWord ++ tailWord_2188519).sum := by decide
  have hdescent : baseEnd_2188519 < baseStart_2188519 := by decide
  rcases family_descends (prefixWord ++ tailWord_2188519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2188592 : List Nat := [2, 1, 1, 1, 2, 2, 4, 5, 4]
def baseStart_2188592 : Nat := 118140960795 + 2188592 * 2 ^ 59
def prefixEnd_2188592 : Nat := 4983230072969 + 3 ^ 40 * 2188592 * 2
def baseEnd_2188592 : Nat := 249733256130001412763301

theorem tailTrace_2188592 : CollatzResearch.WordTrace tailWord_2188592 prefixEnd_2188592 249733256130001412763301 := by
  unfold tailWord_2188592
  simp only [CollatzResearch.WordTrace]
  refine ⟨39912254043556220300212015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53216338724741627066949353 39912254043556220300212015)
  ·
    refine ⟨59868381065334330450318023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39912254043556220300212015 59868381065334330450318023)
    ·
      refine ⟨89802571598001495675477035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59868381065334330450318023 89802571598001495675477035)
      ·
        refine ⟨134703857397002243513215553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89802571598001495675477035 134703857397002243513215553)
        ·
          refine ⟨101027893047751682634911665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 134703857397002243513215553 101027893047751682634911665)
          ·
            refine ⟨75770919785813761976183749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 101027893047751682634911665 75770919785813761976183749)
            ·
              refine ⟨14207047459840080370534453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 75770919785813761976183749 14207047459840080370534453)
              ·
                refine ⟨1331910699360007534737605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14207047459840080370534453 1331910699360007534737605)
                ·
                  refine ⟨249733256130001412763301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1331910699360007534737605 249733256130001412763301)
                  ·
                    rfl

theorem cell22_2188592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 5, 4].length) (baseStart_2188592 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2188592 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2188592 prefixEnd_2188592 := by exact prefixLift 2188592
  have htrace : WordTrace (prefixWord ++ tailWord_2188592) baseStart_2188592 baseEnd_2188592 := by
    simpa [prefixWord, tailWord_2188592, baseEnd_2188592] using wordTrace_append hprefix tailTrace_2188592
  have hstable : (prefixWord ++ tailWord_2188592).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2188592).length < 2 ^ (prefixWord ++ tailWord_2188592).sum := by decide
  have hdescent : baseEnd_2188592 < baseStart_2188592 := by decide
  rcases family_descends (prefixWord ++ tailWord_2188592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2188654 : List Nat := [4, 1, 2, 4, 1, 1, 9]
def baseStart_2188654 : Nat := 118140960795 + 2188654 * 2 ^ 59
def prefixEnd_2188654 : Nat := 4983230072969 + 3 ^ 40 * 2188654 * 2
def baseEnd_2188654 : Nat := 27748925639150249749619

theorem tailTrace_2188654 : CollatzResearch.WordTrace tailWord_2188654 prefixEnd_2188654 27748925639150249749619 := by
  unfold tailWord_2188654
  simp only [CollatzResearch.WordTrace]
  refine ⟨9978346176610978148647627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53217846275258550126120677 9978346176610978148647627)
  ·
    refine ⟨14967519264916467222971441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9978346176610978148647627 14967519264916467222971441)
    ·
      refine ⟨11225639448687350417228581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14967519264916467222971441 11225639448687350417228581)
      ·
        refine ⟨2104807396628878203230359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11225639448687350417228581 2104807396628878203230359)
        ·
          refine ⟨3157211094943317304845539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2104807396628878203230359 3157211094943317304845539)
          ·
            refine ⟨4735816642414975957268309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3157211094943317304845539 4735816642414975957268309)
            ·
              refine ⟨27748925639150249749619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4735816642414975957268309 27748925639150249749619)
              ·
                rfl

theorem cell22_2188654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 9].length) (baseStart_2188654 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2188654 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2188654 prefixEnd_2188654 := by exact prefixLift 2188654
  have htrace : WordTrace (prefixWord ++ tailWord_2188654) baseStart_2188654 baseEnd_2188654 := by
    simpa [prefixWord, tailWord_2188654, baseEnd_2188654] using wordTrace_append hprefix tailTrace_2188654
  have hstable : (prefixWord ++ tailWord_2188654).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2188654).length < 2 ^ (prefixWord ++ tailWord_2188654).sum := by decide
  have hdescent : baseEnd_2188654 < baseStart_2188654 := by decide
  rcases family_descends (prefixWord ++ tailWord_2188654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2188669 : List Nat := [1, 4, 1, 1, 2, 2, 4, 1, 3, 3]
def baseStart_2188669 : Nat := 118140960795 + 2188669 * 2 ^ 59
def prefixEnd_2188669 : Nat := 4983230072969 + 3 ^ 40 * 2188669 * 2
def baseEnd_2188669 : Nat := 749226127063601704114667

theorem tailTrace_2188669 : CollatzResearch.WordTrace tailWord_2188669 prefixEnd_2188669 749226127063601704114667 := by
  unfold tailWord_2188669
  simp only [CollatzResearch.WordTrace]
  refine ⟨79827316507833482750977061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53218211005222321833984707 79827316507833482750977061)
  ·
    refine ⟨14967621845218778015808199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 79827316507833482750977061 14967621845218778015808199)
    ·
      refine ⟨22451432767828167023712299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14967621845218778015808199 22451432767828167023712299)
      ·
        refine ⟨33677149151742250535568449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22451432767828167023712299 33677149151742250535568449)
        ·
          refine ⟨25257861863806687901676337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33677149151742250535568449 25257861863806687901676337)
          ·
            refine ⟨18943396397855015926257253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25257861863806687901676337 18943396397855015926257253)
            ·
              refine ⟨3551886824597815486173235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18943396397855015926257253 3551886824597815486173235)
              ·
                refine ⟨5327830236896723229259853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3551886824597815486173235 5327830236896723229259853)
                ·
                  refine ⟨1997936338836271210972445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5327830236896723229259853 1997936338836271210972445)
                  ·
                    refine ⟨749226127063601704114667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1997936338836271210972445 749226127063601704114667)
                    ·
                      rfl

theorem cell22_2188669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 4, 1, 3, 3].length) (baseStart_2188669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2188669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2188669 prefixEnd_2188669 := by exact prefixLift 2188669
  have htrace : WordTrace (prefixWord ++ tailWord_2188669) baseStart_2188669 baseEnd_2188669 := by
    simpa [prefixWord, tailWord_2188669, baseEnd_2188669] using wordTrace_append hprefix tailTrace_2188669
  have hstable : (prefixWord ++ tailWord_2188669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2188669).length < 2 ^ (prefixWord ++ tailWord_2188669).sum := by decide
  have hdescent : baseEnd_2188669 < baseStart_2188669 := by decide
  rcases family_descends (prefixWord ++ tailWord_2188669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2188703 : List Nat := [1, 1, 2, 5, 1, 4, 1, 3, 1, 3]
def baseStart_2188703 : Nat := 118140960795 + 2188703 * 2 ^ 59
def prefixEnd_2188703 : Nat := 4983230072969 + 3 ^ 40 * 2188703 * 2
def baseEnd_2188703 : Nat := 749237765958436948764563

theorem tailTrace_2188703 : CollatzResearch.WordTrace tailWord_2188703 prefixEnd_2188703 749237765958436948764563 := by
  unfold tailWord_2188703
  simp only [CollatzResearch.WordTrace]
  refine ⟨79828556589710306557714763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53219037726473537705143175 79828556589710306557714763)
  ·
    refine ⟨119742834884565459836572145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79828556589710306557714763 119742834884565459836572145)
    ·
      refine ⟨89807126163424094877429109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119742834884565459836572145 89807126163424094877429109)
      ·
        refine ⟨8419418077821008894758979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 89807126163424094877429109 8419418077821008894758979)
        ·
          refine ⟨12629127116731513342138469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8419418077821008894758979 12629127116731513342138469)
          ·
            refine ⟨2367961334387158751650963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12629127116731513342138469 2367961334387158751650963)
            ·
              refine ⟨3551942001580738127476445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2367961334387158751650963 3551942001580738127476445)
              ·
                refine ⟨1331978250592776797803667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3551942001580738127476445 1331978250592776797803667)
                ·
                  refine ⟨1997967375889165196705501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1331978250592776797803667 1997967375889165196705501)
                  ·
                    refine ⟨749237765958436948764563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1997967375889165196705501 749237765958436948764563)
                    ·
                      rfl

theorem cell22_2188703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 1, 3, 1, 3].length) (baseStart_2188703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2188703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2188703 prefixEnd_2188703 := by exact prefixLift 2188703
  have htrace : WordTrace (prefixWord ++ tailWord_2188703) baseStart_2188703 baseEnd_2188703 := by
    simpa [prefixWord, tailWord_2188703, baseEnd_2188703] using wordTrace_append hprefix tailTrace_2188703
  have hstable : (prefixWord ++ tailWord_2188703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2188703).length < 2 ^ (prefixWord ++ tailWord_2188703).sum := by decide
  have hdescent : baseEnd_2188703 < baseStart_2188703 := by decide
  rcases family_descends (prefixWord ++ tailWord_2188703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2188746 : List Nat := [3, 1, 2, 1, 2, 5, 1, 2, 1, 4]
def baseStart_2188746 : Nat := 118140960795 + 2188746 * 2 ^ 59
def prefixEnd_2188746 : Nat := 4983230072969 + 3 ^ 40 * 2188746 * 2
def baseEnd_2188746 : Nat := 749252485737199169939431

theorem tailTrace_2188746 : CollatzResearch.WordTrace tailWord_2188746 prefixEnd_2188746 749252485737199169939431 := by
  unfold tailWord_2188746
  simp only [CollatzResearch.WordTrace]
  refine ⟨19957531232138631225382523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53220083285703016601020061 19957531232138631225382523)
  ·
    refine ⟨29936296848207946838073785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19957531232138631225382523 29936296848207946838073785)
    ·
      refine ⟨22452222636155960128555339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29936296848207946838073785 22452222636155960128555339)
      ·
        refine ⟨33678333954233940192833009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22452222636155960128555339 33678333954233940192833009)
        ·
          refine ⟨25258750465675455144624757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33678333954233940192833009 25258750465675455144624757)
          ·
            refine ⟨2368007856157073919808571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 25258750465675455144624757 2368007856157073919808571)
            ·
              refine ⟨3552011784235610879712857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2368007856157073919808571 3552011784235610879712857)
              ·
                refine ⟨2664008838176708159784643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3552011784235610879712857 2664008838176708159784643)
                ·
                  refine ⟨3996013257265062239676965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2664008838176708159784643 3996013257265062239676965)
                  ·
                    refine ⟨749252485737199169939431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3996013257265062239676965 749252485737199169939431)
                    ·
                      rfl

theorem cell22_2188746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 1, 2, 1, 4].length) (baseStart_2188746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2188746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2188746 prefixEnd_2188746 := by exact prefixLift 2188746
  have htrace : WordTrace (prefixWord ++ tailWord_2188746) baseStart_2188746 baseEnd_2188746 := by
    simpa [prefixWord, tailWord_2188746, baseEnd_2188746] using wordTrace_append hprefix tailTrace_2188746
  have hstable : (prefixWord ++ tailWord_2188746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2188746).length < 2 ^ (prefixWord ++ tailWord_2188746).sum := by decide
  have hdescent : baseEnd_2188746 < baseStart_2188746 := by decide
  rcases family_descends (prefixWord ++ tailWord_2188746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2188776 : List Nat := [2, 1, 4, 1, 1, 2, 4, 2, 2, 3]
def baseStart_2188776 : Nat := 118140960795 + 2188776 * 2 ^ 59
def prefixEnd_2188776 : Nat := 4983230072969 + 3 ^ 40 * 2188776 * 2
def baseEnd_2188776 : Nat := 749262755350289091689339

theorem tailTrace_2188776 : CollatzResearch.WordTrace tailWord_2188776 prefixEnd_2188776 749262755350289091689339 := by
  unfold tailWord_2188776
  simp only [CollatzResearch.WordTrace]
  refine ⟨39915609559222920012561091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53220812745630560016748121 39915609559222920012561091)
  ·
    refine ⟨59873414338834380018841637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39915609559222920012561091 59873414338834380018841637)
    ·
      refine ⟨11226265188531446253532807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 59873414338834380018841637 11226265188531446253532807)
      ·
        refine ⟨16839397782797169380299211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11226265188531446253532807 16839397782797169380299211)
        ·
          refine ⟨25259096674195754070448817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16839397782797169380299211 25259096674195754070448817)
          ·
            refine ⟨18944322505646815552836613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25259096674195754070448817 18944322505646815552836613)
            ·
              refine ⟨3552060469808777916156865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18944322505646815552836613 3552060469808777916156865)
              ·
                refine ⟨2664045352356583437117649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3552060469808777916156865 2664045352356583437117649)
                ·
                  refine ⟨1998034014267437577838237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2664045352356583437117649 1998034014267437577838237)
                  ·
                    refine ⟨749262755350289091689339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1998034014267437577838237 749262755350289091689339)
                    ·
                      rfl

theorem cell22_2188776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 4, 2, 2, 3].length) (baseStart_2188776 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2188776 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2188776 prefixEnd_2188776 := by exact prefixLift 2188776
  have htrace : WordTrace (prefixWord ++ tailWord_2188776) baseStart_2188776 baseEnd_2188776 := by
    simpa [prefixWord, tailWord_2188776, baseEnd_2188776] using wordTrace_append hprefix tailTrace_2188776
  have hstable : (prefixWord ++ tailWord_2188776).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2188776).length < 2 ^ (prefixWord ++ tailWord_2188776).sum := by decide
  have hdescent : baseEnd_2188776 < baseStart_2188776 := by decide
  rcases family_descends (prefixWord ++ tailWord_2188776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2188817 : List Nat := [1, 2, 2, 1, 1, 2, 4, 2, 7]
def baseStart_2188817 : Nat := 118140960795 + 2188817 * 2 ^ 59
def prefixEnd_2188817 : Nat := 4983230072969 + 3 ^ 40 * 2188817 * 2
def baseEnd_2188817 : Nat := 249758930162726217138071

theorem tailTrace_2188817 : CollatzResearch.WordTrace tailWord_2188817 prefixEnd_2188817 249758930162726217138071 := by
  unfold tailWord_2188817
  simp only [CollatzResearch.WordTrace]
  refine ⟨79832714511297304027364705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53221809674198202684909803 79832714511297304027364705)
  ·
    refine ⟨59874535883472978020523529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79832714511297304027364705 59874535883472978020523529)
    ·
      refine ⟨44905901912604733515392647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59874535883472978020523529 44905901912604733515392647)
      ·
        refine ⟨67358852868907100273088971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44905901912604733515392647 67358852868907100273088971)
        ·
          refine ⟨101038279303360650409633457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67358852868907100273088971 101038279303360650409633457)
          ·
            refine ⟨75778709477520487807225093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 101038279303360650409633457 75778709477520487807225093)
            ·
              refine ⟨14208508027035091463854705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 75778709477520487807225093 14208508027035091463854705)
              ·
                refine ⟨10656381020276318597891029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14208508027035091463854705 10656381020276318597891029)
                ·
                  refine ⟨249758930162726217138071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10656381020276318597891029 249758930162726217138071)
                  ·
                    rfl

theorem cell22_2188817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 2, 7].length) (baseStart_2188817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2188817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2188817 prefixEnd_2188817 := by exact prefixLift 2188817
  have htrace : WordTrace (prefixWord ++ tailWord_2188817) baseStart_2188817 baseEnd_2188817 := by
    simpa [prefixWord, tailWord_2188817, baseEnd_2188817] using wordTrace_append hprefix tailTrace_2188817
  have hstable : (prefixWord ++ tailWord_2188817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2188817).length < 2 ^ (prefixWord ++ tailWord_2188817).sum := by decide
  have hdescent : baseEnd_2188817 < baseStart_2188817 := by decide
  rcases family_descends (prefixWord ++ tailWord_2188817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2188851 : List Nat := [1, 1, 1, 2, 4, 4, 3, 1, 5]
def baseStart_2188851 : Nat := 118140960795 + 2188851 * 2 ^ 59
def prefixEnd_2188851 : Nat := 4983230072969 + 3 ^ 40 * 2188851 * 2
def baseEnd_2188851 : Nat := 249762809794337965354703

theorem tailTrace_2188851 : CollatzResearch.WordTrace tailWord_2188851 prefixEnd_2188851 249762809794337965354703 := by
  unfold tailWord_2188851
  simp only [CollatzResearch.WordTrace]
  refine ⟨79833954593174127834102407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53222636395449418556068271 79833954593174127834102407)
  ·
    refine ⟨119750931889761191751153611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79833954593174127834102407 119750931889761191751153611)
    ·
      refine ⟨179626397834641787626730417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119750931889761191751153611 179626397834641787626730417)
      ·
        refine ⟨134719798375981340720047813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 179626397834641787626730417 134719798375981340720047813)
        ·
          refine ⟨25259962195496501385008965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 134719798375981340720047813 25259962195496501385008965)
          ·
            refine ⟨4736242911655594009689181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25259962195496501385008965 4736242911655594009689181)
            ·
              refine ⟨1776091091870847753633443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4736242911655594009689181 1776091091870847753633443)
              ·
                refine ⟨2664136637806271630450165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1776091091870847753633443 2664136637806271630450165)
                ·
                  refine ⟨249762809794337965354703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2664136637806271630450165 249762809794337965354703)
                  ·
                    rfl

theorem cell22_2188851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 3, 1, 5].length) (baseStart_2188851 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2188851 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2188851 prefixEnd_2188851 := by exact prefixLift 2188851
  have htrace : WordTrace (prefixWord ++ tailWord_2188851) baseStart_2188851 baseEnd_2188851 := by
    simpa [prefixWord, tailWord_2188851, baseEnd_2188851] using wordTrace_append hprefix tailTrace_2188851
  have hstable : (prefixWord ++ tailWord_2188851).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2188851).length < 2 ^ (prefixWord ++ tailWord_2188851).sum := by decide
  have hdescent : baseEnd_2188851 < baseStart_2188851 := by decide
  rcases family_descends (prefixWord ++ tailWord_2188851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2188958 : List Nat := [4, 3, 1, 1, 1, 4, 1, 7]
def baseStart_2188958 : Nat := 118140960795 + 2188958 * 2 ^ 59
def prefixEnd_2188958 : Nat := 4983230072969 + 3 ^ 40 * 2188958 * 2
def baseEnd_2188958 : Nat := 83258339741077920404309

theorem tailTrace_2188958 : CollatzResearch.WordTrace tailWord_2188958 prefixEnd_2188958 83258339741077920404309 := by
  unfold tailWord_2188958
  simp only [CollatzResearch.WordTrace]
  refine ⟨9979732150473310638530941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53225238135857656738831685 9979732150473310638530941)
  ·
    refine ⟨3742399556427491489449103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9979732150473310638530941 3742399556427491489449103)
    ·
      refine ⟨5613599334641237234173655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3742399556427491489449103 5613599334641237234173655)
      ·
        refine ⟨8420399001961855851260483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5613599334641237234173655 8420399001961855851260483)
        ·
          refine ⟨12630598502942783776890725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8420399001961855851260483 12630598502942783776890725)
          ·
            refine ⟨2368237219301771958167011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12630598502942783776890725 2368237219301771958167011)
            ·
              refine ⟨3552355828952657937250517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2368237219301771958167011 3552355828952657937250517)
              ·
                refine ⟨83258339741077920404309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3552355828952657937250517 83258339741077920404309)
                ·
                  rfl

theorem cell22_2188958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 1, 7].length) (baseStart_2188958 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2188958 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2188958 prefixEnd_2188958 := by exact prefixLift 2188958
  have htrace : WordTrace (prefixWord ++ tailWord_2188958) baseStart_2188958 baseEnd_2188958 := by
    simpa [prefixWord, tailWord_2188958, baseEnd_2188958] using wordTrace_append hprefix tailTrace_2188958
  have hstable : (prefixWord ++ tailWord_2188958).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2188958).length < 2 ^ (prefixWord ++ tailWord_2188958).sum := by decide
  have hdescent : baseEnd_2188958 < baseStart_2188958 := by decide
  rcases family_descends (prefixWord ++ tailWord_2188958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2188973 : List Nat := [1, 5, 2, 1, 1, 1, 3, 2, 3, 3]
def baseStart_2188973 : Nat := 118140960795 + 2188973 * 2 ^ 59
def prefixEnd_2188973 : Nat := 4983230072969 + 3 ^ 40 * 2188973 * 2
def baseEnd_2188973 : Nat := 749330192476246244513735

theorem tailTrace_2188973 : CollatzResearch.WordTrace tailWord_2188973 prefixEnd_2188973 749330192476246244513735 := by
  unfold tailWord_2188973
  simp only [CollatzResearch.WordTrace]
  refine ⟨79838404298732142670043573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53225602865821428446695715 79838404298732142670043573)
  ·
    refine ⟨7484850403006138375316585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 79838404298732142670043573 7484850403006138375316585)
    ·
      refine ⟨5613637802254603781487439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7484850403006138375316585 5613637802254603781487439)
      ·
        refine ⟨8420456703381905672231159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5613637802254603781487439 8420456703381905672231159)
        ·
          refine ⟨12630685055072858508346739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8420456703381905672231159 12630685055072858508346739)
          ·
            refine ⟨18946027582609287762520109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12630685055072858508346739 18946027582609287762520109)
            ·
              refine ⟨7104760343478482910945041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18946027582609287762520109 7104760343478482910945041)
              ·
                refine ⟨5328570257608862183208781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7104760343478482910945041 5328570257608862183208781)
                ·
                  refine ⟨1998213846603323318703293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5328570257608862183208781 1998213846603323318703293)
                  ·
                    refine ⟨749330192476246244513735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1998213846603323318703293 749330192476246244513735)
                    ·
                      rfl

theorem cell22_2188973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 2, 3, 3].length) (baseStart_2188973 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2188973 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2188973 prefixEnd_2188973 := by exact prefixLift 2188973
  have htrace : WordTrace (prefixWord ++ tailWord_2188973) baseStart_2188973 baseEnd_2188973 := by
    simpa [prefixWord, tailWord_2188973, baseEnd_2188973] using wordTrace_append hprefix tailTrace_2188973
  have hstable : (prefixWord ++ tailWord_2188973).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2188973).length < 2 ^ (prefixWord ++ tailWord_2188973).sum := by decide
  have hdescent : baseEnd_2188973 < baseStart_2188973 := by decide
  rcases family_descends (prefixWord ++ tailWord_2188973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2188990 : List Nat := [4, 2, 1, 1, 2, 2, 1, 5, 1, 3]
def baseStart_2188990 : Nat := 118140960795 + 2188990 * 2 ^ 59
def prefixEnd_2188990 : Nat := 4983230072969 + 3 ^ 40 * 2188990 * 2
def baseEnd_2188990 : Nat := 749336011923663866838683

theorem tailTrace_2188990 : CollatzResearch.WordTrace tailWord_2188990 prefixEnd_2188990 749336011923663866838683 := by
  unfold tailWord_2188990
  simp only [CollatzResearch.WordTrace]
  refine ⟨9979878042458819321676553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53226016226447036382274949 9979878042458819321676553)
  ·
    refine ⟨7484908531844114491257415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9979878042458819321676553 7484908531844114491257415)
    ·
      refine ⟨11227362797766171736886123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7484908531844114491257415 11227362797766171736886123)
      ·
        refine ⟨16841044196649257605329185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11227362797766171736886123 16841044196649257605329185)
        ·
          refine ⟨12630783147486943203996889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16841044196649257605329185 12630783147486943203996889)
          ·
            refine ⟨9473087360615207402997667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12630783147486943203996889 9473087360615207402997667)
            ·
              refine ⟨14209631040922811104496501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9473087360615207402997667 14209631040922811104496501)
              ·
                refine ⟨1332152910086513541046547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14209631040922811104496501 1332152910086513541046547)
                ·
                  refine ⟨1998229365129770311569821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1332152910086513541046547 1998229365129770311569821)
                  ·
                    refine ⟨749336011923663866838683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1998229365129770311569821 749336011923663866838683)
                    ·
                      rfl

theorem cell22_2188990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 5, 1, 3].length) (baseStart_2188990 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2188990 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2188990 prefixEnd_2188990 := by exact prefixLift 2188990
  have htrace : WordTrace (prefixWord ++ tailWord_2188990) baseStart_2188990 baseEnd_2188990 := by
    simpa [prefixWord, tailWord_2188990, baseEnd_2188990] using wordTrace_append hprefix tailTrace_2188990
  have hstable : (prefixWord ++ tailWord_2188990).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2188990).length < 2 ^ (prefixWord ++ tailWord_2188990).sum := by decide
  have hdescent : baseEnd_2188990 < baseStart_2188990 := by decide
  rcases family_descends (prefixWord ++ tailWord_2188990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2189059 : List Nat := [1, 1, 1, 3, 2, 2, 12]
def baseStart_2189059 : Nat := 118140960795 + 2189059 * 2 ^ 59
def prefixEnd_2189059 : Nat := 4983230072969 + 3 ^ 40 * 2189059 * 2
def baseEnd_2189059 : Nat := 27754060445695210624573

theorem tailTrace_2189059 : CollatzResearch.WordTrace tailWord_2189059 prefixEnd_2189059 27754060445695210624573 := by
  unfold tailWord_2189059
  simp only [CollatzResearch.WordTrace]
  refine ⟨79841540976420579357674231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53227693984280386238449487 79841540976420579357674231)
  ·
    refine ⟨119762311464630869036511347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79841540976420579357674231 119762311464630869036511347)
    ·
      refine ⟨179643467196946303554767021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119762311464630869036511347 179643467196946303554767021)
      ·
        refine ⟨67366300198854863833037633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 179643467196946303554767021 67366300198854863833037633)
        ·
          refine ⟨50524725149141147874778225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67366300198854863833037633 50524725149141147874778225)
          ·
            refine ⟨37893543861855860906083669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50524725149141147874778225 37893543861855860906083669)
            ·
              refine ⟨27754060445695210624573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 37893543861855860906083669 27754060445695210624573)
              ·
                rfl

theorem cell22_2189059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 12].length) (baseStart_2189059 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2189059 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2189059 prefixEnd_2189059 := by exact prefixLift 2189059
  have htrace : WordTrace (prefixWord ++ tailWord_2189059) baseStart_2189059 baseEnd_2189059 := by
    simpa [prefixWord, tailWord_2189059, baseEnd_2189059] using wordTrace_append hprefix tailTrace_2189059
  have hstable : (prefixWord ++ tailWord_2189059).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2189059).length < 2 ^ (prefixWord ++ tailWord_2189059).sum := by decide
  have hdescent : baseEnd_2189059 < baseStart_2189059 := by decide
  rcases family_descends (prefixWord ++ tailWord_2189059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2189080 : List Nat := [2, 1, 2, 3, 1, 1, 6, 1, 2, 3]
def baseStart_2189080 : Nat := 118140960795 + 2189080 * 2 ^ 59
def prefixEnd_2189080 : Nat := 4983230072969 + 3 ^ 40 * 2189080 * 2
def baseEnd_2189080 : Nat := 749366820762933632088407

theorem tailTrace_2189080 : CollatzResearch.WordTrace tailWord_2189080 prefixEnd_2189080 749366820762933632088407 := by
  unfold tailWord_2189080
  simp only [CollatzResearch.WordTrace]
  refine ⟨39921153454672249972094347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53228204606229666629459129 39921153454672249972094347)
  ·
    refine ⟨59881730182008374958141521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39921153454672249972094347 59881730182008374958141521)
    ·
      refine ⟨44911297636506281218606141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59881730182008374958141521 44911297636506281218606141)
      ·
        refine ⟨16841736613689855456977303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44911297636506281218606141 16841736613689855456977303)
        ·
          refine ⟨25262604920534783185465955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16841736613689855456977303 25262604920534783185465955)
          ·
            refine ⟨37893907380802174778198933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25262604920534783185465955 37893907380802174778198933)
            ·
              refine ⟨1776276908475101942728075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 37893907380802174778198933 1776276908475101942728075)
              ·
                refine ⟨2664415362712652914092113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1776276908475101942728075 2664415362712652914092113)
                ·
                  refine ⟨1998311522034489685569085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2664415362712652914092113 1998311522034489685569085)
                  ·
                    refine ⟨749366820762933632088407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1998311522034489685569085 749366820762933632088407)
                    ·
                      rfl

theorem cell22_2189080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 6, 1, 2, 3].length) (baseStart_2189080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2189080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2189080 prefixEnd_2189080 := by exact prefixLift 2189080
  have htrace : WordTrace (prefixWord ++ tailWord_2189080) baseStart_2189080 baseEnd_2189080 := by
    simpa [prefixWord, tailWord_2189080, baseEnd_2189080] using wordTrace_append hprefix tailTrace_2189080
  have hstable : (prefixWord ++ tailWord_2189080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2189080).length < 2 ^ (prefixWord ++ tailWord_2189080).sum := by decide
  have hdescent : baseEnd_2189080 < baseStart_2189080 := by decide
  rcases family_descends (prefixWord ++ tailWord_2189080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2189125 : List Nat := [1, 3, 1, 1, 1, 2, 5, 4, 1, 3]
def baseStart_2189125 : Nat := 118140960795 + 2189125 * 2 ^ 59
def prefixEnd_2189125 : Nat := 4983230072969 + 3 ^ 40 * 2189125 * 2
def baseEnd_2189125 : Nat := 749382225182568514713269

theorem tailTrace_2189125 : CollatzResearch.WordTrace tailWord_2189125 prefixEnd_2189125 749382225182568514713269 := by
  unfold tailWord_2189125
  simp only [CollatzResearch.WordTrace]
  refine ⟨79843948194181472629576829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53229298796120981753051219 79843948194181472629576829)
  ·
    refine ⟨29941480572818052236091311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79843948194181472629576829 29941480572818052236091311)
    ·
      refine ⟨44912220859227078354136967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29941480572818052236091311 44912220859227078354136967)
      ·
        refine ⟨67368331288840617531205451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44912220859227078354136967 67368331288840617531205451)
        ·
          refine ⟨101052496933260926296808177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67368331288840617531205451 101052496933260926296808177)
          ·
            refine ⟨75789372699945694722606133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 101052496933260926296808177 75789372699945694722606133)
            ·
              refine ⟨7105253690619908880244325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 75789372699945694722606133 7105253690619908880244325)
              ·
                refine ⟨1332235066991232915045811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7105253690619908880244325 1332235066991232915045811)
                ·
                  refine ⟨1998352600486849372568717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1332235066991232915045811 1998352600486849372568717)
                  ·
                    refine ⟨749382225182568514713269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1998352600486849372568717 749382225182568514713269)
                    ·
                      rfl

theorem cell22_2189125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 4, 1, 3].length) (baseStart_2189125 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2189125 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2189125 prefixEnd_2189125 := by exact prefixLift 2189125
  have htrace : WordTrace (prefixWord ++ tailWord_2189125) baseStart_2189125 baseEnd_2189125 := by
    simpa [prefixWord, tailWord_2189125, baseEnd_2189125] using wordTrace_append hprefix tailTrace_2189125
  have hstable : (prefixWord ++ tailWord_2189125).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2189125).length < 2 ^ (prefixWord ++ tailWord_2189125).sum := by decide
  have hdescent : baseEnd_2189125 < baseStart_2189125 := by decide
  rcases family_descends (prefixWord ++ tailWord_2189125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2189138 : List Nat := [3, 2, 2, 1, 1, 3, 2, 3, 5]
def baseStart_2189138 : Nat := 118140960795 + 2189138 * 2 ^ 59
def prefixEnd_2189138 : Nat := 4983230072969 + 3 ^ 40 * 2189138 * 2
def baseEnd_2189138 : Nat := 249795558449413604712743

theorem tailTrace_2189138 : CollatzResearch.WordTrace tailWord_2189138 prefixEnd_2189138 249795558449413604712743 := by
  unfold tailWord_2189138
  simp only [CollatzResearch.WordTrace]
  refine ⟨19961105585783593962450017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53229614895422917233200045 19961105585783593962450017)
  ·
    refine ⟨14970829189337695471837513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19961105585783593962450017 14970829189337695471837513)
    ·
      refine ⟨11228121892003271603878135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14970829189337695471837513 11228121892003271603878135)
      ·
        refine ⟨16842182838004907405817203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11228121892003271603878135 16842182838004907405817203)
        ·
          refine ⟨25263274257007361108725805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16842182838004907405817203 25263274257007361108725805)
          ·
            refine ⟨9473727846377760415772177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25263274257007361108725805 9473727846377760415772177)
            ·
              refine ⟨7105295884783320311829133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9473727846377760415772177 7105295884783320311829133)
              ·
                refine ⟨2664485956793745116935925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7105295884783320311829133 2664485956793745116935925)
                ·
                  refine ⟨249795558449413604712743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2664485956793745116935925 249795558449413604712743)
                  ·
                    rfl

theorem cell22_2189138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 3, 5].length) (baseStart_2189138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2189138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2189138 prefixEnd_2189138 := by exact prefixLift 2189138
  have htrace : WordTrace (prefixWord ++ tailWord_2189138) baseStart_2189138 baseEnd_2189138 := by
    simpa [prefixWord, tailWord_2189138, baseEnd_2189138] using wordTrace_append hprefix tailTrace_2189138
  have hstable : (prefixWord ++ tailWord_2189138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2189138).length < 2 ^ (prefixWord ++ tailWord_2189138).sum := by decide
  have hdescent : baseEnd_2189138 < baseStart_2189138 := by decide
  rcases family_descends (prefixWord ++ tailWord_2189138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2189202 : List Nat := [3, 2, 3, 2, 1, 2, 2, 2, 1, 4]
def baseStart_2189202 : Nat := 118140960795 + 2189202 * 2 ^ 59
def prefixEnd_2189202 : Nat := 4983230072969 + 3 ^ 40 * 2189202 * 2
def baseEnd_2189202 : Nat := 749408583856165980538033

theorem tailTrace_2189202 : CollatzResearch.WordTrace tailWord_2189202 prefixEnd_2189202 749408583856165980538033 := by
  unfold tailWord_2189202
  simp only [CollatzResearch.WordTrace]
  refine ⟨19961689153725628695032465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53231171076601676520086573 19961689153725628695032465)
  ·
    refine ⟨14971266865294221521274349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19961689153725628695032465 14971266865294221521274349)
    ·
      refine ⟨5614225074485333070477881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14971266865294221521274349 5614225074485333070477881)
      ·
        refine ⟨4210668805863999802858411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5614225074485333070477881 4210668805863999802858411)
        ·
          refine ⟨6316003208795999704287617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4210668805863999802858411 6316003208795999704287617)
          ·
            refine ⟨4737002406596999778215713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6316003208795999704287617 4737002406596999778215713)
            ·
              refine ⟨3552751804947749833661785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4737002406596999778215713 3552751804947749833661785)
              ·
                refine ⟨2664563853710812375246339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3552751804947749833661785 2664563853710812375246339)
                ·
                  refine ⟨3996845780566218562869509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2664563853710812375246339 3996845780566218562869509)
                  ·
                    refine ⟨749408583856165980538033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3996845780566218562869509 749408583856165980538033)
                    ·
                      rfl

theorem cell22_2189202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 2, 2, 1, 4].length) (baseStart_2189202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2189202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2189202 prefixEnd_2189202 := by exact prefixLift 2189202
  have htrace : WordTrace (prefixWord ++ tailWord_2189202) baseStart_2189202 baseEnd_2189202 := by
    simpa [prefixWord, tailWord_2189202, baseEnd_2189202] using wordTrace_append hprefix tailTrace_2189202
  have hstable : (prefixWord ++ tailWord_2189202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2189202).length < 2 ^ (prefixWord ++ tailWord_2189202).sum := by decide
  have hdescent : baseEnd_2189202 < baseStart_2189202 := by decide
  rcases family_descends (prefixWord ++ tailWord_2189202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2189213 : List Nat := [1, 4, 2, 1, 2, 2, 2, 1, 1, 6]
def baseStart_2189213 : Nat := 118140960795 + 2189213 * 2 ^ 59
def prefixEnd_2189213 : Nat := 4983230072969 + 3 ^ 40 * 2189213 * 2
def baseEnd_2189213 : Nat := 749412349380965618512999

theorem tailTrace_2189213 : CollatzResearch.WordTrace tailWord_2189213 prefixEnd_2189213 749412349380965618512999 := by
  unfold tailWord_2189213
  simp only [CollatzResearch.WordTrace]
  refine ⟨79847157817862663658780293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53231438545241775772520195 79847157817862663658780293)
  ·
    refine ⟨14971342090849249436021305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 79847157817862663658780293 14971342090849249436021305)
    ·
      refine ⟨11228506568136937077015979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14971342090849249436021305 11228506568136937077015979)
      ·
        refine ⟨16842759852205405615523969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11228506568136937077015979 16842759852205405615523969)
        ·
          refine ⟨12632069889154054211642977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16842759852205405615523969 12632069889154054211642977)
          ·
            refine ⟨9474052416865540658732233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12632069889154054211642977 9474052416865540658732233)
            ·
              refine ⟨7105539312649155494049175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9474052416865540658732233 7105539312649155494049175)
              ·
                refine ⟨10658308968973733241073763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7105539312649155494049175 10658308968973733241073763)
                ·
                  refine ⟨15987463453460599861610645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10658308968973733241073763 15987463453460599861610645)
                  ·
                    refine ⟨749412349380965618512999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15987463453460599861610645 749412349380965618512999)
                    ·
                      rfl

theorem cell22_2189213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 1, 1, 6].length) (baseStart_2189213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2189213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2189213 prefixEnd_2189213 := by exact prefixLift 2189213
  have htrace : WordTrace (prefixWord ++ tailWord_2189213) baseStart_2189213 baseEnd_2189213 := by
    simpa [prefixWord, tailWord_2189213, baseEnd_2189213] using wordTrace_append hprefix tailTrace_2189213
  have hstable : (prefixWord ++ tailWord_2189213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2189213).length < 2 ^ (prefixWord ++ tailWord_2189213).sum := by decide
  have hdescent : baseEnd_2189213 < baseStart_2189213 := by decide
  rcases family_descends (prefixWord ++ tailWord_2189213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2189288 : List Nat := [2, 1, 4, 1, 1, 1, 1, 4, 2, 5]
def baseStart_2189288 : Nat := 118140960795 + 2189288 * 2 ^ 59
def prefixEnd_2189288 : Nat := 4983230072969 + 3 ^ 40 * 2189288 * 2
def baseEnd_2189288 : Nat := 749438023413690422887769

theorem tailTrace_2189288 : CollatzResearch.WordTrace tailWord_2189288 prefixEnd_2189288 749438023413690422887769 := by
  unfold tailWord_2189288
  simp only [CollatzResearch.WordTrace]
  refine ⟨39924946646295475733880259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53233262195060634311840345 39924946646295475733880259)
  ·
    refine ⟨59887419969443213600820389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39924946646295475733880259 59887419969443213600820389)
    ·
      refine ⟨11228891244270602550153823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 59887419969443213600820389 11228891244270602550153823)
      ·
        refine ⟨16843336866405903825230735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11228891244270602550153823 16843336866405903825230735)
        ·
          refine ⟨25265005299608855737846103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16843336866405903825230735 25265005299608855737846103)
          ·
            refine ⟨37897507949413283606769155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25265005299608855737846103 37897507949413283606769155)
            ·
              refine ⟨56846261924119925410153733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37897507949413283606769155 56846261924119925410153733)
              ·
                refine ⟨10658674110772486014403825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 56846261924119925410153733 10658674110772486014403825)
                ·
                  refine ⟨7994005583079364510802869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10658674110772486014403825 7994005583079364510802869)
                  ·
                    refine ⟨749438023413690422887769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7994005583079364510802869 749438023413690422887769)
                    ·
                      rfl

theorem cell22_2189288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 4, 2, 5].length) (baseStart_2189288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2189288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2189288 prefixEnd_2189288 := by exact prefixLift 2189288
  have htrace : WordTrace (prefixWord ++ tailWord_2189288) baseStart_2189288 baseEnd_2189288 := by
    simpa [prefixWord, tailWord_2189288, baseEnd_2189288] using wordTrace_append hprefix tailTrace_2189288
  have hstable : (prefixWord ++ tailWord_2189288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2189288).length < 2 ^ (prefixWord ++ tailWord_2189288).sum := by decide
  have hdescent : baseEnd_2189288 < baseStart_2189288 := by decide
  rcases family_descends (prefixWord ++ tailWord_2189288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2189290 : List Nat := [3, 1, 3, 1, 2, 1, 4, 2, 5]
def baseStart_2189290 : Nat := 118140960795 + 2189290 * 2 ^ 59
def prefixEnd_2189290 : Nat := 4983230072969 + 3 ^ 40 * 2189290 * 2
def baseEnd_2189290 : Nat := 249812902684854361445921

theorem tailTrace_2189290 : CollatzResearch.WordTrace tailWord_2189290 prefixEnd_2189290 249812902684854361445921 := by
  unfold tailWord_2189290
  simp only [CollatzResearch.WordTrace]
  refine ⟨19962491559645926452333331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53233310825722470539555549 19962491559645926452333331)
  ·
    refine ⟨29943737339468889678499997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19962491559645926452333331 29943737339468889678499997)
    ·
      refine ⟨11228901502300833629437499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29943737339468889678499997 11228901502300833629437499)
      ·
        refine ⟨16843352253451250444156249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11228901502300833629437499 16843352253451250444156249)
        ·
          refine ⟨12632514190088437833117187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16843352253451250444156249 12632514190088437833117187)
          ·
            refine ⟨18948771285132656749675781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12632514190088437833117187 18948771285132656749675781)
            ·
              refine ⟨3552894615962373140564209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18948771285132656749675781 3552894615962373140564209)
              ·
                refine ⟨2664670961971779855423157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3552894615962373140564209 2664670961971779855423157)
                ·
                  refine ⟨249812902684854361445921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2664670961971779855423157 249812902684854361445921)
                  ·
                    rfl

theorem cell22_2189290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 4, 2, 5].length) (baseStart_2189290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2189290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2189290 prefixEnd_2189290 := by exact prefixLift 2189290
  have htrace : WordTrace (prefixWord ++ tailWord_2189290) baseStart_2189290 baseEnd_2189290 := by
    simpa [prefixWord, tailWord_2189290, baseEnd_2189290] using wordTrace_append hprefix tailTrace_2189290
  have hstable : (prefixWord ++ tailWord_2189290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2189290).length < 2 ^ (prefixWord ++ tailWord_2189290).sum := by decide
  have hdescent : baseEnd_2189290 < baseStart_2189290 := by decide
  rcases family_descends (prefixWord ++ tailWord_2189290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2189294 : List Nat := [4, 1, 2, 1, 3, 2, 1, 4, 1, 3]
def baseStart_2189294 : Nat := 118140960795 + 2189294 * 2 ^ 59
def prefixEnd_2189294 : Nat := 4983230072969 + 3 ^ 40 * 2189294 * 2
def baseEnd_2189294 : Nat := 749440077336308407237751

theorem tailTrace_2189294 : CollatzResearch.WordTrace tailWord_2189294 prefixEnd_2189294 749440077336308407237751 := by
  unfold tailWord_2189294
  simp only [CollatzResearch.WordTrace]
  refine ⟨9981264016321151811559867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53233408087046142994985957 9981264016321151811559867)
  ·
    refine ⟨14971896024481727717339801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9981264016321151811559867 14971896024481727717339801)
    ·
      refine ⟨11228922018361295788004851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14971896024481727717339801 11228922018361295788004851)
      ·
        refine ⟨16843383027541943682007277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11228922018361295788004851 16843383027541943682007277)
        ·
          refine ⟨6316268635328228880752729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16843383027541943682007277 6316268635328228880752729)
          ·
            refine ⟨4737201476496171660564547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6316268635328228880752729 4737201476496171660564547)
            ·
              refine ⟨7105802214744257490846821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4737201476496171660564547 7105802214744257490846821)
              ·
                refine ⟨1332337915264548279533779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7105802214744257490846821 1332337915264548279533779)
                ·
                  refine ⟨1998506872896822419300669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1332337915264548279533779 1998506872896822419300669)
                  ·
                    refine ⟨749440077336308407237751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1998506872896822419300669 749440077336308407237751)
                    ·
                      rfl

theorem cell22_2189294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 4, 1, 3].length) (baseStart_2189294 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2189294 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2189294 prefixEnd_2189294 := by exact prefixLift 2189294
  have htrace : WordTrace (prefixWord ++ tailWord_2189294) baseStart_2189294 baseEnd_2189294 := by
    simpa [prefixWord, tailWord_2189294, baseEnd_2189294] using wordTrace_append hprefix tailTrace_2189294
  have hstable : (prefixWord ++ tailWord_2189294).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2189294).length < 2 ^ (prefixWord ++ tailWord_2189294).sum := by decide
  have hdescent : baseEnd_2189294 < baseStart_2189294 := by decide
  rcases family_descends (prefixWord ++ tailWord_2189294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2189320 : List Nat := [2, 1, 3, 2, 1, 2, 2, 4, 1, 4]
def baseStart_2189320 : Nat := 118140960795 + 2189320 * 2 ^ 59
def prefixEnd_2189320 : Nat := 4983230072969 + 3 ^ 40 * 2189320 * 2
def baseEnd_2189320 : Nat := 749448977667653006087671

theorem tailTrace_2189320 : CollatzResearch.WordTrace tailWord_2189320 prefixEnd_2189320 749448977667653006087671 := by
  unfold tailWord_2189320
  simp only [CollatzResearch.WordTrace]
  refine ⟨39925530214237510466462707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53234040285650013955283609 39925530214237510466462707)
  ·
    refine ⟨59888295321356265699694061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39925530214237510466462707 59888295321356265699694061)
    ·
      refine ⟨22458110745508599637385273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59888295321356265699694061 22458110745508599637385273)
      ·
        refine ⟨16843583059131449728038955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22458110745508599637385273 16843583059131449728038955)
        ·
          refine ⟨25265374588697174592058433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16843583059131449728038955 25265374588697174592058433)
          ·
            refine ⟨18949030941522880944043825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25265374588697174592058433 18949030941522880944043825)
            ·
              refine ⟨14211773206142160708032869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18949030941522880944043825 14211773206142160708032869)
              ·
                refine ⟨2664707476151655132756163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14211773206142160708032869 2664707476151655132756163)
                ·
                  refine ⟨3997061214227482699134245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2664707476151655132756163 3997061214227482699134245)
                  ·
                    refine ⟨749448977667653006087671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3997061214227482699134245 749448977667653006087671)
                    ·
                      rfl

theorem cell22_2189320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 4, 1, 4].length) (baseStart_2189320 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2189320 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2189320 prefixEnd_2189320 := by exact prefixLift 2189320
  have htrace : WordTrace (prefixWord ++ tailWord_2189320) baseStart_2189320 baseEnd_2189320 := by
    simpa [prefixWord, tailWord_2189320, baseEnd_2189320] using wordTrace_append hprefix tailTrace_2189320
  have hstable : (prefixWord ++ tailWord_2189320).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2189320).length < 2 ^ (prefixWord ++ tailWord_2189320).sum := by decide
  have hdescent : baseEnd_2189320 < baseStart_2189320 := by decide
  rcases family_descends (prefixWord ++ tailWord_2189320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2189382 : List Nat := [6, 1, 1, 1, 1, 1, 1, 3, 1, 6]
def baseStart_2189382 : Nat := 118140960795 + 2189382 * 2 ^ 59
def prefixEnd_2189382 : Nat := 4983230072969 + 3 ^ 40 * 2189382 * 2
def baseEnd_2189382 : Nat := 749470201534705511037481

theorem tailTrace_2189382 : CollatzResearch.WordTrace tailWord_2189382 prefixEnd_2189382 749470201534705511037481 := by
  unfold tailWord_2189382
  simp only [CollatzResearch.WordTrace]
  refine ⟨2495416304820325172552575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 53235547836166937014454933 2495416304820325172552575)
  ·
    refine ⟨3743124457230487758828863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2495416304820325172552575 3743124457230487758828863)
    ·
      refine ⟨5614686685845731638243295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3743124457230487758828863 5614686685845731638243295)
      ·
        refine ⟨8422030028768597457364943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5614686685845731638243295 8422030028768597457364943)
        ·
          refine ⟨12633045043152896186047415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8422030028768597457364943 12633045043152896186047415)
          ·
            refine ⟨18949567564729344279071123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12633045043152896186047415 18949567564729344279071123)
            ·
              refine ⟨28424351347094016418606685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18949567564729344279071123 28424351347094016418606685)
              ·
                refine ⟨10659131755160256156977507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28424351347094016418606685 10659131755160256156977507)
                ·
                  refine ⟨15988697632740384235466261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10659131755160256156977507 15988697632740384235466261)
                  ·
                    refine ⟨749470201534705511037481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15988697632740384235466261 749470201534705511037481)
                    ·
                      rfl

theorem cell22_2189382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 3, 1, 6].length) (baseStart_2189382 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2189382 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2189382 prefixEnd_2189382 := by exact prefixLift 2189382
  have htrace : WordTrace (prefixWord ++ tailWord_2189382) baseStart_2189382 baseEnd_2189382 := by
    simpa [prefixWord, tailWord_2189382, baseEnd_2189382] using wordTrace_append hprefix tailTrace_2189382
  have hstable : (prefixWord ++ tailWord_2189382).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2189382).length < 2 ^ (prefixWord ++ tailWord_2189382).sum := by decide
  have hdescent : baseEnd_2189382 < baseStart_2189382 := by decide
  rcases family_descends (prefixWord ++ tailWord_2189382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2189393 : List Nat := [1, 2, 2, 1, 3, 1, 1, 2, 1, 8]
def baseStart_2189393 : Nat := 118140960795 + 2189393 * 2 ^ 59
def prefixEnd_2189393 : Nat := 4983230072969 + 3 ^ 40 * 2189393 * 2
def baseEnd_2189393 : Nat := 749473967059505149012447

theorem tailTrace_2189393 : CollatzResearch.WordTrace tailWord_2189393 prefixEnd_2189393 749473967059505149012447 := by
  unfold tailWord_2189393
  simp only [CollatzResearch.WordTrace]
  refine ⟨79853722957210554400332833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53235815304807036266888555 79853722957210554400332833)
  ·
    refine ⟨59890292217907915800249625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79853722957210554400332833 59890292217907915800249625)
    ·
      refine ⟨44917719163430936850187219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59890292217907915800249625 44917719163430936850187219)
      ·
        refine ⟨67376578745146405275280829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44917719163430936850187219 67376578745146405275280829)
        ·
          refine ⟨25266217029429901978230311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67376578745146405275280829 25266217029429901978230311)
          ·
            refine ⟨37899325544144852967345467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25266217029429901978230311 37899325544144852967345467)
            ·
              refine ⟨56848988316217279451018201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37899325544144852967345467 56848988316217279451018201)
              ·
                refine ⟨42636741237162959588263651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56848988316217279451018201 42636741237162959588263651)
                ·
                  refine ⟨63955111855744439382395477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42636741237162959588263651 63955111855744439382395477)
                  ·
                    refine ⟨749473967059505149012447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 63955111855744439382395477 749473967059505149012447)
                    ·
                      rfl

theorem cell22_2189393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 2, 1, 8].length) (baseStart_2189393 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2189393 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2189393 prefixEnd_2189393 := by exact prefixLift 2189393
  have htrace : WordTrace (prefixWord ++ tailWord_2189393) baseStart_2189393 baseEnd_2189393 := by
    simpa [prefixWord, tailWord_2189393, baseEnd_2189393] using wordTrace_append hprefix tailTrace_2189393
  have hstable : (prefixWord ++ tailWord_2189393).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2189393).length < 2 ^ (prefixWord ++ tailWord_2189393).sum := by decide
  have hdescent : baseEnd_2189393 < baseStart_2189393 := by decide
  rcases family_descends (prefixWord ++ tailWord_2189393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2189412 : List Nat := [2, 3, 1, 1, 2, 1, 5, 1, 3, 3]
def baseStart_2189412 : Nat := 118140960795 + 2189412 * 2 ^ 59
def prefixEnd_2189412 : Nat := 4983230072969 + 3 ^ 40 * 2189412 * 2
def baseEnd_2189412 : Nat := 749480471147795432787389

theorem tailTrace_2189412 : CollatzResearch.WordTrace tailWord_2189412 prefixEnd_2189412 749480471147795432787389 := by
  unfold tailWord_2189412
  simp only [CollatzResearch.WordTrace]
  refine ⟨39927207972070860322637245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53236277296094480430182993 39927207972070860322637245)
  ·
    refine ⟨14972702989526572620988967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39927207972070860322637245 14972702989526572620988967)
    ·
      refine ⟨22459054484289858931483451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14972702989526572620988967 22459054484289858931483451)
      ·
        refine ⟨33688581726434788397225177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22459054484289858931483451 33688581726434788397225177)
        ·
          refine ⟨25266436294826091297918883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33688581726434788397225177 25266436294826091297918883)
          ·
            refine ⟨37899654442239136946878325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25266436294826091297918883 37899654442239136946878325)
            ·
              refine ⟨3553092603959919088769843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 37899654442239136946878325 3553092603959919088769843)
              ·
                refine ⟨5329638905939878633154765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3553092603959919088769843 5329638905939878633154765)
                ·
                  refine ⟨1998614589727454487433037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5329638905939878633154765 1998614589727454487433037)
                  ·
                    refine ⟨749480471147795432787389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1998614589727454487433037 749480471147795432787389)
                    ·
                      rfl

theorem cell22_2189412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 5, 1, 3, 3].length) (baseStart_2189412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2189412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2189412 prefixEnd_2189412 := by exact prefixLift 2189412
  have htrace : WordTrace (prefixWord ++ tailWord_2189412) baseStart_2189412 baseEnd_2189412 := by
    simpa [prefixWord, tailWord_2189412, baseEnd_2189412] using wordTrace_append hprefix tailTrace_2189412
  have hstable : (prefixWord ++ tailWord_2189412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2189412).length < 2 ^ (prefixWord ++ tailWord_2189412).sum := by decide
  have hdescent : baseEnd_2189412 < baseStart_2189412 := by decide
  rcases family_descends (prefixWord ++ tailWord_2189412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2189418 : List Nat := [3, 1, 3, 2, 4, 1, 2, 1, 2, 3]
def baseStart_2189418 : Nat := 118140960795 + 2189418 * 2 ^ 59
def prefixEnd_2189418 : Nat := 4983230072969 + 3 ^ 40 * 2189418 * 2
def baseEnd_2189418 : Nat := 749482525070413417137371

theorem tailTrace_2189418 : CollatzResearch.WordTrace tailWord_2189418 prefixEnd_2189418 749482525070413417137371 := by
  unfold tailWord_2189418
  simp only [CollatzResearch.WordTrace]
  refine ⟨19963658695529995917498227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53236423188079989113328605 19963658695529995917498227)
  ·
    refine ⟨29945488043294993876247341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19963658695529995917498227 29945488043294993876247341)
    ·
      refine ⟨11229558016235622703592753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29945488043294993876247341 11229558016235622703592753)
      ·
        refine ⟨8422168512176717027694565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11229558016235622703592753 8422168512176717027694565)
        ·
          refine ⟨1579156596033134442692731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8422168512176717027694565 1579156596033134442692731)
          ·
            refine ⟨2368734894049701664039097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1579156596033134442692731 2368734894049701664039097)
            ·
              refine ⟨1776551170537276248029323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2368734894049701664039097 1776551170537276248029323)
              ·
                refine ⟨2664826755805914372043985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1776551170537276248029323 2664826755805914372043985)
                ·
                  refine ⟨1998620066854435779032989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2664826755805914372043985 1998620066854435779032989)
                  ·
                    refine ⟨749482525070413417137371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1998620066854435779032989 749482525070413417137371)
                    ·
                      rfl

theorem cell22_2189418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 2, 1, 2, 3].length) (baseStart_2189418 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2189418 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2189418 prefixEnd_2189418 := by exact prefixLift 2189418
  have htrace : WordTrace (prefixWord ++ tailWord_2189418) baseStart_2189418 baseEnd_2189418 := by
    simpa [prefixWord, tailWord_2189418, baseEnd_2189418] using wordTrace_append hprefix tailTrace_2189418
  have hstable : (prefixWord ++ tailWord_2189418).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2189418).length < 2 ^ (prefixWord ++ tailWord_2189418).sum := by decide
  have hdescent : baseEnd_2189418 < baseStart_2189418 := by decide
  rcases family_descends (prefixWord ++ tailWord_2189418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2189425 : List Nat := [1, 2, 2, 2, 1, 1, 5, 3, 5]
def baseStart_2189425 : Nat := 118140960795 + 2189425 * 2 ^ 59
def prefixEnd_2189425 : Nat := 4983230072969 + 3 ^ 40 * 2189425 * 2
def baseEnd_2189425 : Nat := 249828307104489244070783

theorem tailTrace_2189425 : CollatzResearch.WordTrace tailWord_2189425 prefixEnd_2189425 249828307104489244070783 := by
  unfold tailWord_2189425
  simp only [CollatzResearch.WordTrace]
  refine ⟨79854890093094623865497729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53236593395396415910331819 79854890093094623865497729)
  ·
    refine ⟨59891167569820967899123297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79854890093094623865497729 59891167569820967899123297)
    ·
      refine ⟨44918375677365725924342473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59891167569820967899123297 44918375677365725924342473)
      ·
        refine ⟨33688781758024294443256855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44918375677365725924342473 33688781758024294443256855)
        ·
          refine ⟨50533172637036441664885283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33688781758024294443256855 50533172637036441664885283)
          ·
            refine ⟨75799758955554662497327925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50533172637036441664885283 75799758955554662497327925)
            ·
              refine ⟨7106227402083249609124493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 75799758955554662497327925 7106227402083249609124493)
              ·
                refine ⟨2664835275781218603421685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7106227402083249609124493 2664835275781218603421685)
                ·
                  refine ⟨249828307104489244070783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2664835275781218603421685 249828307104489244070783)
                  ·
                    rfl

theorem cell22_2189425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 3, 5].length) (baseStart_2189425 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2189425 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2189425 prefixEnd_2189425 := by exact prefixLift 2189425
  have htrace : WordTrace (prefixWord ++ tailWord_2189425) baseStart_2189425 baseEnd_2189425 := by
    simpa [prefixWord, tailWord_2189425, baseEnd_2189425] using wordTrace_append hprefix tailTrace_2189425
  have hstable : (prefixWord ++ tailWord_2189425).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2189425).length < 2 ^ (prefixWord ++ tailWord_2189425).sum := by decide
  have hdescent : baseEnd_2189425 < baseStart_2189425 := by decide
  rcases family_descends (prefixWord ++ tailWord_2189425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2189463 : List Nat := [1, 1, 3, 3, 4, 2, 2, 2, 1, 3]
def baseStart_2189463 : Nat := 118140960795 + 2189463 * 2 ^ 59
def prefixEnd_2189463 : Nat := 4983230072969 + 3 ^ 40 * 2189463 * 2
def baseEnd_2189463 : Nat := 749497929490048299762233

theorem tailTrace_2189463 : CollatzResearch.WordTrace tailWord_2189463 prefixEnd_2189463 749497929490048299762233 := by
  unfold tailWord_2189463
  simp only [CollatzResearch.WordTrace]
  refine ⟨79856276066956956355381043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53237517377971304236920695 79856276066956956355381043)
  ·
    refine ⟨119784414100435434533071565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79856276066956956355381043 119784414100435434533071565)
    ·
      refine ⟨44919155287663287949901837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 119784414100435434533071565 44919155287663287949901837)
      ·
        refine ⟨16844683232873732981213189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44919155287663287949901837 16844683232873732981213189)
        ·
          refine ⟨3158378106163824933977473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16844683232873732981213189 3158378106163824933977473)
          ·
            refine ⟨2368783579622868700483105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3158378106163824933977473 2368783579622868700483105)
            ·
              refine ⟨1776587684717151525362329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2368783579622868700483105 1776587684717151525362329)
              ·
                refine ⟨1332440763537863644021747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1776587684717151525362329 1332440763537863644021747)
                ·
                  refine ⟨1998661145306795466032621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1332440763537863644021747 1998661145306795466032621)
                  ·
                    refine ⟨749497929490048299762233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1998661145306795466032621 749497929490048299762233)
                    ·
                      rfl

theorem cell22_2189463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 2, 2, 1, 3].length) (baseStart_2189463 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2189463 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2189463 prefixEnd_2189463 := by exact prefixLift 2189463
  have htrace : WordTrace (prefixWord ++ tailWord_2189463) baseStart_2189463 baseEnd_2189463 := by
    simpa [prefixWord, tailWord_2189463, baseEnd_2189463] using wordTrace_append hprefix tailTrace_2189463
  have hstable : (prefixWord ++ tailWord_2189463).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2189463).length < 2 ^ (prefixWord ++ tailWord_2189463).sum := by decide
  have hdescent : baseEnd_2189463 < baseStart_2189463 := by decide
  rcases family_descends (prefixWord ++ tailWord_2189463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2189504 : List Nat := [2, 1, 1, 2, 5, 2, 2, 3, 4]
def baseStart_2189504 : Nat := 118140960795 + 2189504 * 2 ^ 59
def prefixEnd_2189504 : Nat := 4983230072969 + 3 ^ 40 * 2189504 * 2
def baseEnd_2189504 : Nat := 249837321542645953162369

theorem tailTrace_2189504 : CollatzResearch.WordTrace tailWord_2189504 prefixEnd_2189504 249837321542645953162369 := by
  unfold tailWord_2189504
  simp only [CollatzResearch.WordTrace]
  refine ⟨39928885729904210178811783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53238514306538946905082377 39928885729904210178811783)
  ·
    refine ⟨59893328594856315268217675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39928885729904210178811783 59893328594856315268217675)
    ·
      refine ⟨89839992892284472902326513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59893328594856315268217675 89839992892284472902326513)
      ·
        refine ⟨67379994669213354676744885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89839992892284472902326513 67379994669213354676744885)
        ·
          refine ⟨6316874500238752000944833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 67379994669213354676744885 6316874500238752000944833)
          ·
            refine ⟨4737655875179064000708625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6316874500238752000944833 4737655875179064000708625)
            ·
              refine ⟨3553241906384298000531469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4737655875179064000708625 3553241906384298000531469)
              ·
                refine ⟨1332465714894111750199301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3553241906384298000531469 1332465714894111750199301)
                ·
                  refine ⟨249837321542645953162369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1332465714894111750199301 249837321542645953162369)
                  ·
                    rfl

theorem cell22_2189504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 2, 3, 4].length) (baseStart_2189504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2189504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2189504 prefixEnd_2189504 := by exact prefixLift 2189504
  have htrace : WordTrace (prefixWord ++ tailWord_2189504) baseStart_2189504 baseEnd_2189504 := by
    simpa [prefixWord, tailWord_2189504, baseEnd_2189504] using wordTrace_append hprefix tailTrace_2189504
  have hstable : (prefixWord ++ tailWord_2189504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2189504).length < 2 ^ (prefixWord ++ tailWord_2189504).sum := by decide
  have hdescent : baseEnd_2189504 < baseStart_2189504 := by decide
  rcases family_descends (prefixWord ++ tailWord_2189504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2189547 : List Nat := [1, 1, 1, 1, 2, 5, 1, 4, 3, 3]
def baseStart_2189547 : Nat := 118140960795 + 2189547 * 2 ^ 59
def prefixEnd_2189547 : Nat := 4983230072969 + 3 ^ 40 * 2189547 * 2
def baseEnd_2189547 : Nat := 749526684406700080661975

theorem tailTrace_2189547 : CollatzResearch.WordTrace tailWord_2189547 prefixEnd_2189547 749526684406700080661975 := by
  unfold tailWord_2189547
  simp only [CollatzResearch.WordTrace]
  refine ⟨79859339798652638701438895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53239559865768425800959263 79859339798652638701438895)
  ·
    refine ⟨119789009697978958052158343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79859339798652638701438895 119789009697978958052158343)
    ·
      refine ⟨179683514546968437078237515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119789009697978958052158343 179683514546968437078237515)
      ·
        refine ⟨269525271820452655617356273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 179683514546968437078237515 269525271820452655617356273)
        ·
          refine ⟨202143953865339491713017205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 269525271820452655617356273 202143953865339491713017205)
          ·
            refine ⟨18950995674875577348095363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 202143953865339491713017205 18950995674875577348095363)
            ·
              refine ⟨28426493512313366022143045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18950995674875577348095363 28426493512313366022143045)
              ·
                refine ⟨5329967533558756129151821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28426493512313366022143045 5329967533558756129151821)
                ·
                  refine ⟨1998737825084533548431933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5329967533558756129151821 1998737825084533548431933)
                  ·
                    refine ⟨749526684406700080661975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1998737825084533548431933 749526684406700080661975)
                    ·
                      rfl

theorem cell22_2189547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 4, 3, 3].length) (baseStart_2189547 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2189547 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2189547 prefixEnd_2189547 := by exact prefixLift 2189547
  have htrace : WordTrace (prefixWord ++ tailWord_2189547) baseStart_2189547 baseEnd_2189547 := by
    simpa [prefixWord, tailWord_2189547, baseEnd_2189547] using wordTrace_append hprefix tailTrace_2189547
  have hstable : (prefixWord ++ tailWord_2189547).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2189547).length < 2 ^ (prefixWord ++ tailWord_2189547).sum := by decide
  have hdescent : baseEnd_2189547 < baseStart_2189547 := by decide
  rcases family_descends (prefixWord ++ tailWord_2189547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2189594 : List Nat := [3, 1, 1, 3, 4, 1, 1, 3, 5]
def baseStart_2189594 : Nat := 118140960795 + 2189594 * 2 ^ 59
def prefixEnd_2189594 : Nat := 4983230072969 + 3 ^ 40 * 2189594 * 2
def baseEnd_2189594 : Nat := 249847591155735874912277

theorem tailTrace_2189594 : CollatzResearch.WordTrace tailWord_2189594 prefixEnd_2189594 249847591155735874912277 := by
  unfold tailWord_2189594
  simp only [CollatzResearch.WordTrace]
  refine ⟨19965263507370591432099959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53240702686321577152266557 19965263507370591432099959)
  ·
    refine ⟨29947895261055887148149939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19965263507370591432099959 29947895261055887148149939)
    ·
      refine ⟨44921842891583830722224909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29947895261055887148149939 44921842891583830722224909)
      ·
        refine ⟨16845691084343936520834341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44921842891583830722224909 16845691084343936520834341)
        ·
          refine ⟨3158567078314488097656439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16845691084343936520834341 3158567078314488097656439)
          ·
            refine ⟨4737850617471732146484659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3158567078314488097656439 4737850617471732146484659)
            ·
              refine ⟨7106775926207598219726989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4737850617471732146484659 7106775926207598219726989)
              ·
                refine ⟨2665040972327849332397621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7106775926207598219726989 2665040972327849332397621)
                ·
                  refine ⟨249847591155735874912277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2665040972327849332397621 249847591155735874912277)
                  ·
                    rfl

theorem cell22_2189594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 3, 5].length) (baseStart_2189594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2189594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2189594 prefixEnd_2189594 := by exact prefixLift 2189594
  have htrace : WordTrace (prefixWord ++ tailWord_2189594) baseStart_2189594 baseEnd_2189594 := by
    simpa [prefixWord, tailWord_2189594, baseEnd_2189594] using wordTrace_append hprefix tailTrace_2189594
  have hstable : (prefixWord ++ tailWord_2189594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2189594).length < 2 ^ (prefixWord ++ tailWord_2189594).sum := by decide
  have hdescent : baseEnd_2189594 < baseStart_2189594 := by decide
  rcases family_descends (prefixWord ++ tailWord_2189594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2189639 : List Nat := [1, 1, 4, 1, 2, 2, 3, 4, 4]
def baseStart_2189639 : Nat := 118140960795 + 2189639 * 2 ^ 59
def prefixEnd_2189639 : Nat := 4983230072969 + 3 ^ 40 * 2189639 * 2
def baseEnd_2189639 : Nat := 249852725962280835787231

theorem tailTrace_2189639 : CollatzResearch.WordTrace tailWord_2189639 prefixEnd_2189639 249852725962280835787231 := by
  unfold tailWord_2189639
  simp only [CollatzResearch.WordTrace]
  refine ⟨79862695314319338413787971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53241796876212892275858647 79862695314319338413787971)
  ·
    refine ⟨119794042971479007620681957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79862695314319338413787971 119794042971479007620681957)
    ·
      refine ⟨22461383057152313928877867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 119794042971479007620681957 22461383057152313928877867)
      ·
        refine ⟨33692074585728470893316801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22461383057152313928877867 33692074585728470893316801)
        ·
          refine ⟨25269055939296353169987601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33692074585728470893316801 25269055939296353169987601)
          ·
            refine ⟨18951791954472264877490701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25269055939296353169987601 18951791954472264877490701)
            ·
              refine ⟨7106921982927099329059013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18951791954472264877490701 7106921982927099329059013)
              ·
                refine ⟨1332547871798831124198565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7106921982927099329059013 1332547871798831124198565)
                ·
                  refine ⟨249852725962280835787231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1332547871798831124198565 249852725962280835787231)
                  ·
                    rfl

theorem cell22_2189639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 4, 4].length) (baseStart_2189639 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2189639 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2189639 prefixEnd_2189639 := by exact prefixLift 2189639
  have htrace : WordTrace (prefixWord ++ tailWord_2189639) baseStart_2189639 baseEnd_2189639 := by
    simpa [prefixWord, tailWord_2189639, baseEnd_2189639] using wordTrace_append hprefix tailTrace_2189639
  have hstable : (prefixWord ++ tailWord_2189639).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2189639).length < 2 ^ (prefixWord ++ tailWord_2189639).sum := by decide
  have hdescent : baseEnd_2189639 < baseStart_2189639 := by decide
  rcases family_descends (prefixWord ++ tailWord_2189639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2189669 : List Nat := [1, 3, 1, 3, 1, 3, 3, 1, 2, 4]
def baseStart_2189669 : Nat := 118140960795 + 2189669 * 2 ^ 59
def prefixEnd_2189669 : Nat := 4983230072969 + 3 ^ 40 * 2189669 * 2
def baseEnd_2189669 : Nat := 749568447499932429111601

theorem tailTrace_2189669 : CollatzResearch.WordTrace tailWord_2189669 prefixEnd_2189669 749568447499932429111601 := by
  unfold tailWord_2189669
  simp only [CollatzResearch.WordTrace]
  refine ⟨79863789504210653537380061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53242526336140435691586707 79863789504210653537380061)
  ·
    refine ⟨29948921064078995076517523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79863789504210653537380061 29948921064078995076517523)
    ·
      refine ⟨44923381596118492614776285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29948921064078995076517523 44923381596118492614776285)
      ·
        refine ⟨16846268098544434730541107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44923381596118492614776285 16846268098544434730541107)
        ·
          refine ⟨25269402147816652095811661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16846268098544434730541107 25269402147816652095811661)
          ·
            refine ⟨9476025805431244535929373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25269402147816652095811661 9476025805431244535929373)
            ·
              refine ⟨3553509677036716700973515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9476025805431244535929373 3553509677036716700973515)
              ·
                refine ⟨5330264515555075051460273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3553509677036716700973515 5330264515555075051460273)
                ·
                  refine ⟨3997698386666306288595205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5330264515555075051460273 3997698386666306288595205)
                  ·
                    refine ⟨749568447499932429111601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3997698386666306288595205 749568447499932429111601)
                    ·
                      rfl

theorem cell22_2189669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 3, 1, 2, 4].length) (baseStart_2189669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2189669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2189669 prefixEnd_2189669 := by exact prefixLift 2189669
  have htrace : WordTrace (prefixWord ++ tailWord_2189669) baseStart_2189669 baseEnd_2189669 := by
    simpa [prefixWord, tailWord_2189669, baseEnd_2189669] using wordTrace_append hprefix tailTrace_2189669
  have hstable : (prefixWord ++ tailWord_2189669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2189669).length < 2 ^ (prefixWord ++ tailWord_2189669).sum := by decide
  have hdescent : baseEnd_2189669 < baseStart_2189669 := by decide
  rcases family_descends (prefixWord ++ tailWord_2189669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2189804 : List Nat := [2, 2, 1, 1, 2, 1, 3, 4, 2, 4]
def baseStart_2189804 : Nat := 118140960795 + 2189804 * 2 ^ 59
def prefixEnd_2189804 : Nat := 4983230072969 + 3 ^ 40 * 2189804 * 2
def baseEnd_2189804 : Nat := 749614660758837076986187

theorem tailTrace_2189804 : CollatzResearch.WordTrace tailWord_2189804 prefixEnd_2189804 749614660758837076986187 := by
  unfold tailWord_2189804
  simp only [CollatzResearch.WordTrace]
  refine ⟨39934356679360785796772233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53245808905814381062362977 39934356679360785796772233)
  ·
    refine ⟨29950767509520589347579175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39934356679360785796772233 29950767509520589347579175)
    ·
      refine ⟨44926151264280884021368763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29950767509520589347579175 44926151264280884021368763)
      ·
        refine ⟨67389226896421326032053145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44926151264280884021368763 67389226896421326032053145)
        ·
          refine ⟨50541920172315994524039859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67389226896421326032053145 50541920172315994524039859)
          ·
            refine ⟨75812880258473991786059789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50541920172315994524039859 75812880258473991786059789)
            ·
              refine ⟨28429830096927746919772421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 75812880258473991786059789 28429830096927746919772421)
              ·
                refine ⟨5330593143173952547457329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28429830096927746919772421 5330593143173952547457329)
                ·
                  refine ⟨3997944857380464410592997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5330593143173952547457329 3997944857380464410592997)
                  ·
                    refine ⟨749614660758837076986187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3997944857380464410592997 749614660758837076986187)
                    ·
                      rfl

theorem cell22_2189804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 4].length) (baseStart_2189804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2189804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2189804 prefixEnd_2189804 := by exact prefixLift 2189804
  have htrace : WordTrace (prefixWord ++ tailWord_2189804) baseStart_2189804 baseEnd_2189804 := by
    simpa [prefixWord, tailWord_2189804, baseEnd_2189804] using wordTrace_append hprefix tailTrace_2189804
  have hstable : (prefixWord ++ tailWord_2189804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2189804).length < 2 ^ (prefixWord ++ tailWord_2189804).sum := by decide
  have hdescent : baseEnd_2189804 < baseStart_2189804 := by decide
  rcases family_descends (prefixWord ++ tailWord_2189804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2189836 : List Nat := [2, 2, 1, 2, 4, 2, 3, 6]
def baseStart_2189836 : Nat := 118140960795 + 2189836 * 2 ^ 59
def prefixEnd_2189836 : Nat := 4983230072969 + 3 ^ 40 * 2189836 * 2
def baseEnd_2189836 : Nat := 83291735001422184465121

theorem tailTrace_2189836 : CollatzResearch.WordTrace tailWord_2189836 prefixEnd_2189836 83291735001422184465121 := by
  unfold tailWord_2189836
  simp only [CollatzResearch.WordTrace]
  refine ⟨39934940247302820529354681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53246586996403760705806241 39934940247302820529354681)
  ·
    refine ⟨29951205185477115397016011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39934940247302820529354681 29951205185477115397016011)
    ·
      refine ⟨44926807778215673095524017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29951205185477115397016011 44926807778215673095524017)
      ·
        refine ⟨33695105833661754821643013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44926807778215673095524017 33695105833661754821643013)
        ·
          refine ⟨6317832343811579029058065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33695105833661754821643013 6317832343811579029058065)
          ·
            refine ⟨4738374257858684271793549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6317832343811579029058065 4738374257858684271793549)
            ·
              refine ⟨1776890346697006601922581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4738374257858684271793549 1776890346697006601922581)
              ·
                refine ⟨83291735001422184465121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1776890346697006601922581 83291735001422184465121)
                ·
                  rfl

theorem cell22_2189836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 3, 6].length) (baseStart_2189836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2189836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2189836 prefixEnd_2189836 := by exact prefixLift 2189836
  have htrace : WordTrace (prefixWord ++ tailWord_2189836) baseStart_2189836 baseEnd_2189836 := by
    simpa [prefixWord, tailWord_2189836, baseEnd_2189836] using wordTrace_append hprefix tailTrace_2189836
  have hstable : (prefixWord ++ tailWord_2189836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2189836).length < 2 ^ (prefixWord ++ tailWord_2189836).sum := by decide
  have hdescent : baseEnd_2189836 < baseStart_2189836 := by decide
  rcases family_descends (prefixWord ++ tailWord_2189836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2189838 : List Nat := [4, 1, 1, 2, 3, 3, 1, 1, 2, 4]
def baseStart_2189838 : Nat := 118140960795 + 2189838 * 2 ^ 59
def prefixEnd_2189838 : Nat := 4983230072969 + 3 ^ 40 * 2189838 * 2
def baseEnd_2189838 : Nat := 749626299653672321636083

theorem tailTrace_2189838 : CollatzResearch.WordTrace tailWord_2189838 prefixEnd_2189838 749626299653672321636083 := by
  unfold tailWord_2189838
  simp only [CollatzResearch.WordTrace]
  refine ⟨9983744180074799425035271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53246635627065596933521445 9983744180074799425035271)
  ·
    refine ⟨14975616270112199137552907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9983744180074799425035271 14975616270112199137552907)
    ·
      refine ⟨22463424405168298706329361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14975616270112199137552907 22463424405168298706329361)
      ·
        refine ⟨16847568303876224029747021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22463424405168298706329361 16847568303876224029747021)
        ·
          refine ⟨6317838113953584011155133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16847568303876224029747021 6317838113953584011155133)
          ·
            refine ⟨2369189292732594004183175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6317838113953584011155133 2369189292732594004183175)
            ·
              refine ⟨3553783939098891006274763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2369189292732594004183175 3553783939098891006274763)
              ·
                refine ⟨5330675908648336509412145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3553783939098891006274763 5330675908648336509412145)
                ·
                  refine ⟨3998006931486252382059109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5330675908648336509412145 3998006931486252382059109)
                  ·
                    refine ⟨749626299653672321636083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3998006931486252382059109 749626299653672321636083)
                    ·
                      rfl

theorem cell22_2189838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 1, 1, 2, 4].length) (baseStart_2189838 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2189838 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2189838 prefixEnd_2189838 := by exact prefixLift 2189838
  have htrace : WordTrace (prefixWord ++ tailWord_2189838) baseStart_2189838 baseEnd_2189838 := by
    simpa [prefixWord, tailWord_2189838, baseEnd_2189838] using wordTrace_append hprefix tailTrace_2189838
  have hstable : (prefixWord ++ tailWord_2189838).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2189838).length < 2 ^ (prefixWord ++ tailWord_2189838).sum := by decide
  have hdescent : baseEnd_2189838 < baseStart_2189838 := by decide
  rcases family_descends (prefixWord ++ tailWord_2189838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2189879 : List Nat := [1, 1, 3, 1, 2, 3, 1, 3, 2, 5]
def baseStart_2189879 : Nat := 118140960795 + 2189879 * 2 ^ 59
def prefixEnd_2189879 : Nat := 4983230072969 + 3 ^ 40 * 2189879 * 2
def baseEnd_2189879 : Nat := 749640334791561881360957

theorem tailTrace_2189879 : CollatzResearch.WordTrace tailWord_2189879 prefixEnd_2189879 749640334791561881360957 := by
  unfold tailWord_2189879
  simp only [CollatzResearch.WordTrace]
  refine ⟨79871448833449859402524691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53247632555633239601683127 79871448833449859402524691)
  ·
    refine ⟨119807173250174789103787037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79871448833449859402524691 119807173250174789103787037)
    ·
      refine ⟨44927689968815545913920139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 119807173250174789103787037 44927689968815545913920139)
      ·
        refine ⟨67391534953223318870880209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44927689968815545913920139 67391534953223318870880209)
        ·
          refine ⟨50543651214917489153160157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67391534953223318870880209 50543651214917489153160157)
          ·
            refine ⟨18953869205594058432435059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50543651214917489153160157 18953869205594058432435059)
            ·
              refine ⟨28430803808391087648652589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18953869205594058432435059 28430803808391087648652589)
              ·
                refine ⟨10661551428146657868244721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28430803808391087648652589 10661551428146657868244721)
                ·
                  refine ⟨7996163571109993401183541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10661551428146657868244721 7996163571109993401183541)
                  ·
                    refine ⟨749640334791561881360957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7996163571109993401183541 749640334791561881360957)
                    ·
                      rfl

theorem cell22_2189879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 3, 2, 5].length) (baseStart_2189879 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2189879 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2189879 prefixEnd_2189879 := by exact prefixLift 2189879
  have htrace : WordTrace (prefixWord ++ tailWord_2189879) baseStart_2189879 baseEnd_2189879 := by
    simpa [prefixWord, tailWord_2189879, baseEnd_2189879] using wordTrace_append hprefix tailTrace_2189879
  have hstable : (prefixWord ++ tailWord_2189879).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2189879).length < 2 ^ (prefixWord ++ tailWord_2189879).sum := by decide
  have hdescent : baseEnd_2189879 < baseStart_2189879 := by decide
  rcases family_descends (prefixWord ++ tailWord_2189879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2189909 : List Nat := [1, 3, 2, 2, 1, 1, 2, 2, 8]
def baseStart_2189909 : Nat := 118140960795 + 2189909 * 2 ^ 59
def prefixEnd_2189909 : Nat := 4983230072969 + 3 ^ 40 * 2189909 * 2
def baseEnd_2189909 : Nat := 249883534801550601036955

theorem tailTrace_2189909 : CollatzResearch.WordTrace tailWord_2189909 prefixEnd_2189909 249883534801550601036955 := by
  unfold tailWord_2189909
  simp only [CollatzResearch.WordTrace]
  refine ⟨79872543023341174526116781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53248362015560783017411187 79872543023341174526116781)
  ·
    refine ⟨29952203633752940447293793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79872543023341174526116781 29952203633752940447293793)
    ·
      refine ⟨22464152725314705335470345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29952203633752940447293793 22464152725314705335470345)
      ·
        refine ⟨16848114543986029001602759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22464152725314705335470345 16848114543986029001602759)
        ·
          refine ⟨25272171815979043502404139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16848114543986029001602759 25272171815979043502404139)
          ·
            refine ⟨37908257723968565253606209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25272171815979043502404139 37908257723968565253606209)
            ·
              refine ⟨28431193292976423940204657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37908257723968565253606209 28431193292976423940204657)
              ·
                refine ⟨21323394969732317955153493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28431193292976423940204657 21323394969732317955153493)
                ·
                  refine ⟨249883534801550601036955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21323394969732317955153493 249883534801550601036955)
                  ·
                    rfl

theorem cell22_2189909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 2, 8].length) (baseStart_2189909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2189909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2189909 prefixEnd_2189909 := by exact prefixLift 2189909
  have htrace : WordTrace (prefixWord ++ tailWord_2189909) baseStart_2189909 baseEnd_2189909 := by
    simpa [prefixWord, tailWord_2189909, baseEnd_2189909] using wordTrace_append hprefix tailTrace_2189909
  have hstable : (prefixWord ++ tailWord_2189909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2189909).length < 2 ^ (prefixWord ++ tailWord_2189909).sum := by decide
  have hdescent : baseEnd_2189909 < baseStart_2189909 := by decide
  rcases family_descends (prefixWord ++ tailWord_2189909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2189911 : List Nat := [1, 1, 3, 2, 2, 2, 1, 5, 1, 4]
def baseStart_2189911 : Nat := 118140960795 + 2189911 * 2 ^ 59
def prefixEnd_2189911 : Nat := 4983230072969 + 3 ^ 40 * 2189911 * 2
def baseEnd_2189911 : Nat := 749651289045524464560859

theorem tailTrace_2189911 : CollatzResearch.WordTrace tailWord_2189911 prefixEnd_2189911 749651289045524464560859 := by
  unfold tailWord_2189911
  simp only [CollatzResearch.WordTrace]
  refine ⟨79872615969333928867689587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53248410646222619245126391 79872615969333928867689587)
  ·
    refine ⟨119808923954000893301534381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79872615969333928867689587 119808923954000893301534381)
    ·
      refine ⟨44928346482750334988075393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 119808923954000893301534381 44928346482750334988075393)
      ·
        refine ⟨33696259862062751241056545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44928346482750334988075393 33696259862062751241056545)
        ·
          refine ⟨25272194896547063430792409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33696259862062751241056545 25272194896547063430792409)
          ·
            refine ⟨18954146172410297573094307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25272194896547063430792409 18954146172410297573094307)
            ·
              refine ⟨28431219258615446359641461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18954146172410297573094307 28431219258615446359641461)
              ·
                refine ⟨2665426805495198096216387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28431219258615446359641461 2665426805495198096216387)
                ·
                  refine ⟨3998140208242797144324581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2665426805495198096216387 3998140208242797144324581)
                  ·
                    refine ⟨749651289045524464560859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3998140208242797144324581 749651289045524464560859)
                    ·
                      rfl

theorem cell22_2189911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 5, 1, 4].length) (baseStart_2189911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2189911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2189911 prefixEnd_2189911 := by exact prefixLift 2189911
  have htrace : WordTrace (prefixWord ++ tailWord_2189911) baseStart_2189911 baseEnd_2189911 := by
    simpa [prefixWord, tailWord_2189911, baseEnd_2189911] using wordTrace_append hprefix tailTrace_2189911
  have hstable : (prefixWord ++ tailWord_2189911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2189911).length < 2 ^ (prefixWord ++ tailWord_2189911).sum := by decide
  have hdescent : baseEnd_2189911 < baseStart_2189911 := by decide
  rcases family_descends (prefixWord ++ tailWord_2189911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2189939 : List Nat := [1, 1, 1, 2, 2, 1, 1, 6, 1, 6]
def baseStart_2189939 : Nat := 118140960795 + 2189939 * 2 ^ 59
def prefixEnd_2189939 : Nat := 4983230072969 + 3 ^ 40 * 2189939 * 2
def baseEnd_2189939 : Nat := 749660874017741724860773

theorem tailTrace_2189939 : CollatzResearch.WordTrace tailWord_2189939 prefixEnd_2189939 749660874017741724860773 := by
  unfold tailWord_2189939
  simp only [CollatzResearch.WordTrace]
  refine ⟨79873637213232489649708871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53249091475488326433139247 79873637213232489649708871)
  ·
    refine ⟨119810455819848734474563307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79873637213232489649708871 119810455819848734474563307)
    ·
      refine ⟨179715683729773101711844961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119810455819848734474563307 179715683729773101711844961)
      ·
        refine ⟨134786762797329826283883721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 179715683729773101711844961 134786762797329826283883721)
        ·
          refine ⟨101090072097997369712912791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 134786762797329826283883721 101090072097997369712912791)
          ·
            refine ⟨151635108146996054569369187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101090072097997369712912791 151635108146996054569369187)
            ·
              refine ⟨227452662220494081854053781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 151635108146996054569369187 227452662220494081854053781)
              ·
                refine ⟨10661843541585660086908771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 227452662220494081854053781 10661843541585660086908771)
                ·
                  refine ⟨15992765312378490130363157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10661843541585660086908771 15992765312378490130363157)
                  ·
                    refine ⟨749660874017741724860773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15992765312378490130363157 749660874017741724860773)
                    ·
                      rfl

theorem cell22_2189939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 6, 1, 6].length) (baseStart_2189939 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2189939 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2189939 prefixEnd_2189939 := by exact prefixLift 2189939
  have htrace : WordTrace (prefixWord ++ tailWord_2189939) baseStart_2189939 baseEnd_2189939 := by
    simpa [prefixWord, tailWord_2189939, baseEnd_2189939] using wordTrace_append hprefix tailTrace_2189939
  have hstable : (prefixWord ++ tailWord_2189939).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2189939).length < 2 ^ (prefixWord ++ tailWord_2189939).sum := by decide
  have hdescent : baseEnd_2189939 < baseStart_2189939 := by decide
  rcases family_descends (prefixWord ++ tailWord_2189939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2189969 : List Nat := [1, 2, 2, 1, 1, 1, 1, 2, 4, 7]
def baseStart_2189969 : Nat := 118140960795 + 2189969 * 2 ^ 59
def prefixEnd_2189969 : Nat := 4983230072969 + 3 ^ 40 * 2189969 * 2
def baseEnd_2189969 : Nat := 749671143630831646610681

theorem tailTrace_2189969 : CollatzResearch.WordTrace tailWord_2189969 prefixEnd_2189969 749671143630831646610681 := by
  unfold tailWord_2189969
  simp only [CollatzResearch.WordTrace]
  refine ⟨79874731403123804773300961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53249820935415869848867307 79874731403123804773300961)
  ·
    refine ⟨59906048552342853579975721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79874731403123804773300961 59906048552342853579975721)
    ·
      refine ⟨44929536414257140184981791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59906048552342853579975721 44929536414257140184981791)
      ·
        refine ⟨67394304621385710277472687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44929536414257140184981791 67394304621385710277472687)
        ·
          refine ⟨101091456932078565416209031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67394304621385710277472687 101091456932078565416209031)
          ·
            refine ⟨151637185398117848124313547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101091456932078565416209031 151637185398117848124313547)
            ·
              refine ⟨227455778097176772186470321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 151637185398117848124313547 227455778097176772186470321)
              ·
                refine ⟨170591833572882579139852741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 227455778097176772186470321 170591833572882579139852741)
                ·
                  refine ⟨31985968794915483588722389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 170591833572882579139852741 31985968794915483588722389)
                  ·
                    refine ⟨749671143630831646610681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31985968794915483588722389 749671143630831646610681)
                    ·
                      rfl

theorem cell22_2189969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 7].length) (baseStart_2189969 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2189969 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2189969 prefixEnd_2189969 := by exact prefixLift 2189969
  have htrace : WordTrace (prefixWord ++ tailWord_2189969) baseStart_2189969 baseEnd_2189969 := by
    simpa [prefixWord, tailWord_2189969, baseEnd_2189969] using wordTrace_append hprefix tailTrace_2189969
  have hstable : (prefixWord ++ tailWord_2189969).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2189969).length < 2 ^ (prefixWord ++ tailWord_2189969).sum := by decide
  have hdescent : baseEnd_2189969 < baseStart_2189969 := by decide
  rcases family_descends (prefixWord ++ tailWord_2189969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2190003 : List Nat := [1, 1, 1, 2, 3, 5, 1, 2, 3, 3]
def baseStart_2190003 : Nat := 118140960795 + 2190003 * 2 ^ 59
def prefixEnd_2190003 : Nat := 4983230072969 + 3 ^ 40 * 2190003 * 2
def baseEnd_2190003 : Nat := 749682782525666891260577

theorem tailTrace_2190003 : CollatzResearch.WordTrace tailWord_2190003 prefixEnd_2190003 749682782525666891260577 := by
  unfold tailWord_2190003
  simp only [CollatzResearch.WordTrace]
  refine ⟨79875971485000628580038663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53250647656667085720025775 79875971485000628580038663)
  ·
    refine ⟨119813957227500942870057995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79875971485000628580038663 119813957227500942870057995)
    ·
      refine ⟨179720935841251414305086993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119813957227500942870057995 179720935841251414305086993)
      ·
        refine ⟨134790701880938560728815245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 179720935841251414305086993 134790701880938560728815245)
        ·
          refine ⟨50546513205351960273305717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 134790701880938560728815245 50546513205351960273305717)
          ·
            refine ⟨4738735613001746275622411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 50546513205351960273305717 4738735613001746275622411)
            ·
              refine ⟨7108103419502619413433617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4738735613001746275622411 7108103419502619413433617)
              ·
                refine ⟨5331077564626964560075213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7108103419502619413433617 5331077564626964560075213)
                ·
                  refine ⟨1999154086735111710028205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5331077564626964560075213 1999154086735111710028205)
                  ·
                    refine ⟨749682782525666891260577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1999154086735111710028205 749682782525666891260577)
                    ·
                      rfl

theorem cell22_2190003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 2, 3, 3].length) (baseStart_2190003 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2190003 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2190003 prefixEnd_2190003 := by exact prefixLift 2190003
  have htrace : WordTrace (prefixWord ++ tailWord_2190003) baseStart_2190003 baseEnd_2190003 := by
    simpa [prefixWord, tailWord_2190003, baseEnd_2190003] using wordTrace_append hprefix tailTrace_2190003
  have hstable : (prefixWord ++ tailWord_2190003).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2190003).length < 2 ^ (prefixWord ++ tailWord_2190003).sum := by decide
  have hdescent : baseEnd_2190003 < baseStart_2190003 := by decide
  rcases family_descends (prefixWord ++ tailWord_2190003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2190037 : List Nat := [1, 3, 2, 5, 1, 1, 2, 1, 3, 3]
def baseStart_2190037 : Nat := 118140960795 + 2190037 * 2 ^ 59
def prefixEnd_2190037 : Nat := 4983230072969 + 3 ^ 40 * 2190037 * 2
def baseEnd_2190037 : Nat := 749694421420502135910473

theorem tailTrace_2190037 : CollatzResearch.WordTrace tailWord_2190037 prefixEnd_2190037 749694421420502135910473 := by
  unfold tailWord_2190037
  simp only [CollatzResearch.WordTrace]
  refine ⟨79877211566877452386776365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53251474377918301591184243 79877211566877452386776365)
  ·
    refine ⟨29953954337579044645041137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79877211566877452386776365 29953954337579044645041137)
    ·
      refine ⟨22465465753184283483780853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29953954337579044645041137 22465465753184283483780853)
      ·
        refine ⟨2106137414361026576604455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 22465465753184283483780853 2106137414361026576604455)
        ·
          refine ⟨3159206121541539864906683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2106137414361026576604455 3159206121541539864906683)
          ·
            refine ⟨4738809182312309797360025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3159206121541539864906683 4738809182312309797360025)
            ·
              refine ⟨3554106886734232348020019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4738809182312309797360025 3554106886734232348020019)
              ·
                refine ⟨5331160330101348522030029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3554106886734232348020019 5331160330101348522030029)
                ·
                  refine ⟨1999185123788005695761261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5331160330101348522030029 1999185123788005695761261)
                  ·
                    refine ⟨749694421420502135910473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1999185123788005695761261 749694421420502135910473)
                    ·
                      rfl

theorem cell22_2190037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 2, 1, 3, 3].length) (baseStart_2190037 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2190037 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2190037 prefixEnd_2190037 := by exact prefixLift 2190037
  have htrace : WordTrace (prefixWord ++ tailWord_2190037) baseStart_2190037 baseEnd_2190037 := by
    simpa [prefixWord, tailWord_2190037, baseEnd_2190037] using wordTrace_append hprefix tailTrace_2190037
  have hstable : (prefixWord ++ tailWord_2190037).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2190037).length < 2 ^ (prefixWord ++ tailWord_2190037).sum := by decide
  have hdescent : baseEnd_2190037 < baseStart_2190037 := by decide
  rcases family_descends (prefixWord ++ tailWord_2190037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2190063 : List Nat := [1, 1, 2, 1, 5, 2, 1, 4, 1, 4]
def baseStart_2190063 : Nat := 118140960795 + 2190063 * 2 ^ 59
def prefixEnd_2190063 : Nat := 4983230072969 + 3 ^ 40 * 2190063 * 2
def baseEnd_2190063 : Nat := 749703321751846734760393

theorem tailTrace_2190063 : CollatzResearch.WordTrace tailWord_2190063 prefixEnd_2190063 749703321751846734760393 := by
  unfold tailWord_2190063
  simp only [CollatzResearch.WordTrace]
  refine ⟨79878159864783258827222843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53252106576522172551481895 79878159864783258827222843)
  ·
    refine ⟨119817239797174888240834265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79878159864783258827222843 119817239797174888240834265)
    ·
      refine ⟨89862929847881166180625699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119817239797174888240834265 89862929847881166180625699)
      ·
        refine ⟨134794394771821749270938549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89862929847881166180625699 134794394771821749270938549)
        ·
          refine ⟨12636974509858288994150489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 134794394771821749270938549 12636974509858288994150489)
          ·
            refine ⟨9477730882393716745612867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12636974509858288994150489 9477730882393716745612867)
            ·
              refine ⟨14216596323590575118419301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9477730882393716745612867 14216596323590575118419301)
              ·
                refine ⟨2665611810673232834703619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14216596323590575118419301 2665611810673232834703619)
                ·
                  refine ⟨3998417716009849252055429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2665611810673232834703619 3998417716009849252055429)
                  ·
                    refine ⟨749703321751846734760393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3998417716009849252055429 749703321751846734760393)
                    ·
                      rfl

theorem cell22_2190063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 4, 1, 4].length) (baseStart_2190063 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2190063 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2190063 prefixEnd_2190063 := by exact prefixLift 2190063
  have htrace : WordTrace (prefixWord ++ tailWord_2190063) baseStart_2190063 baseEnd_2190063 := by
    simpa [prefixWord, tailWord_2190063, baseEnd_2190063] using wordTrace_append hprefix tailTrace_2190063
  have hstable : (prefixWord ++ tailWord_2190063).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2190063).length < 2 ^ (prefixWord ++ tailWord_2190063).sum := by decide
  have hdescent : baseEnd_2190063 < baseStart_2190063 := by decide
  rcases family_descends (prefixWord ++ tailWord_2190063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2190095 : List Nat := [1, 1, 2, 1, 1, 1, 9, 2, 4]
def baseStart_2190095 : Nat := 118140960795 + 2190095 * 2 ^ 59
def prefixEnd_2190095 : Nat := 4983230072969 + 3 ^ 40 * 2190095 * 2
def baseEnd_2190095 : Nat := 249904758668603105986765

theorem tailTrace_2190095 : CollatzResearch.WordTrace tailWord_2190095 prefixEnd_2190095 249904758668603105986765 := by
  unfold tailWord_2190095
  simp only [CollatzResearch.WordTrace]
  refine ⟨79879327000667328292387739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53252884667111552194925159 79879327000667328292387739)
  ·
    refine ⟨119818990501000992438581609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79879327000667328292387739 119818990501000992438581609)
    ·
      refine ⟨89864242875750744328936207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119818990501000992438581609 89864242875750744328936207)
      ·
        refine ⟨134796364313626116493404311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89864242875750744328936207 134796364313626116493404311)
        ·
          refine ⟨202194546470439174740106467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134796364313626116493404311 202194546470439174740106467)
          ·
            refine ⟨303291819705658762110159701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 202194546470439174740106467 303291819705658762110159701)
            ·
              refine ⟨1777100506087844309239217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 303291819705658762110159701 1777100506087844309239217)
              ·
                refine ⟨1332825379565883231929413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1777100506087844309239217 1332825379565883231929413)
                ·
                  refine ⟨249904758668603105986765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1332825379565883231929413 249904758668603105986765)
                  ·
                    rfl

theorem cell22_2190095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 9, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 9, 2, 4].length) (baseStart_2190095 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2190095 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2190095 prefixEnd_2190095 := by exact prefixLift 2190095
  have htrace : WordTrace (prefixWord ++ tailWord_2190095) baseStart_2190095 baseEnd_2190095 := by
    simpa [prefixWord, tailWord_2190095, baseEnd_2190095] using wordTrace_append hprefix tailTrace_2190095
  have hstable : (prefixWord ++ tailWord_2190095).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2190095).length < 2 ^ (prefixWord ++ tailWord_2190095).sum := by decide
  have hdescent : baseEnd_2190095 < baseStart_2190095 := by decide
  rcases family_descends (prefixWord ++ tailWord_2190095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2190157 : List Nat := [1, 6, 1, 2, 2, 2, 1, 7]
def baseStart_2190157 : Nat := 118140960795 + 2190157 * 2 ^ 59
def prefixEnd_2190157 : Nat := 4983230072969 + 3 ^ 40 * 2190157 * 2
def baseEnd_2190157 : Nat := 83303944430317980323345

theorem tailTrace_2190157 : CollatzResearch.WordTrace tailWord_2190157 prefixEnd_2190157 83303944430317980323345 := by
  unfold tailWord_2190157
  simp only [CollatzResearch.WordTrace]
  refine ⟨79881588326442712881144725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53254392217628475254096483 79881588326442712881144725)
  ·
    refine ⟨3744449452802002166303659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 79881588326442712881144725 3744449452802002166303659)
    ·
      refine ⟨5616674179203003249455489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3744449452802002166303659 5616674179203003249455489)
      ·
        refine ⟨4212505634402252437091617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5616674179203003249455489 4212505634402252437091617)
        ·
          refine ⟨3159379225801689327818713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4212505634402252437091617 3159379225801689327818713)
          ·
            refine ⟨2369534419351266995864035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3159379225801689327818713 2369534419351266995864035)
            ·
              refine ⟨3554301629026900493796053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2369534419351266995864035 3554301629026900493796053)
              ·
                refine ⟨83303944430317980323345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3554301629026900493796053 83303944430317980323345)
                ·
                  rfl

theorem cell22_2190157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 1, 7].length) (baseStart_2190157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2190157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2190157 prefixEnd_2190157 := by exact prefixLift 2190157
  have htrace : WordTrace (prefixWord ++ tailWord_2190157) baseStart_2190157 baseEnd_2190157 := by
    simpa [prefixWord, tailWord_2190157, baseEnd_2190157] using wordTrace_append hprefix tailTrace_2190157
  have hstable : (prefixWord ++ tailWord_2190157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2190157).length < 2 ^ (prefixWord ++ tailWord_2190157).sum := by decide
  have hdescent : baseEnd_2190157 < baseStart_2190157 := by decide
  rcases family_descends (prefixWord ++ tailWord_2190157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2190172 : List Nat := [2, 2, 4, 2, 1, 2, 1, 2, 3, 3]
def baseStart_2190172 : Nat := 118140960795 + 2190172 * 2 ^ 59
def prefixEnd_2190172 : Nat := 4983230072969 + 3 ^ 40 * 2190172 * 2
def baseEnd_2190172 : Nat := 749740634679406783785059

theorem tailTrace_2190172 : CollatzResearch.WordTrace tailWord_2190172 prefixEnd_2190172 749740634679406783785059 := by
  unfold tailWord_2190172
  simp only [CollatzResearch.WordTrace]
  refine ⟨39941067710694185221470385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53254756947592246961960513 39941067710694185221470385)
  ·
    refine ⟨29955800783020638916102789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39941067710694185221470385 29955800783020638916102789)
    ·
      refine ⟨5616712646816369796769273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29955800783020638916102789 5616712646816369796769273)
      ·
        refine ⟨4212534485112277347576955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5616712646816369796769273 4212534485112277347576955)
        ·
          refine ⟨6318801727668416021365433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4212534485112277347576955 6318801727668416021365433)
          ·
            refine ⟨4739101295751312016024075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6318801727668416021365433 4739101295751312016024075)
            ·
              refine ⟨7108651943626968024036113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4739101295751312016024075 7108651943626968024036113)
              ·
                refine ⟨5331488957720226018027085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7108651943626968024036113 5331488957720226018027085)
                ·
                  refine ⟨1999308359145084756760157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5331488957720226018027085 1999308359145084756760157)
                  ·
                    refine ⟨749740634679406783785059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1999308359145084756760157 749740634679406783785059)
                    ·
                      rfl

theorem cell22_2190172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 2, 3, 3].length) (baseStart_2190172 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2190172 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2190172 prefixEnd_2190172 := by exact prefixLift 2190172
  have htrace : WordTrace (prefixWord ++ tailWord_2190172) baseStart_2190172 baseEnd_2190172 := by
    simpa [prefixWord, tailWord_2190172, baseEnd_2190172] using wordTrace_append hprefix tailTrace_2190172
  have hstable : (prefixWord ++ tailWord_2190172).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2190172).length < 2 ^ (prefixWord ++ tailWord_2190172).sum := by decide
  have hdescent : baseEnd_2190172 < baseStart_2190172 := by decide
  rcases family_descends (prefixWord ++ tailWord_2190172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2190213 : List Nat := [1, 3, 1, 1, 3, 3, 1, 3, 6]
def baseStart_2190213 : Nat := 118140960795 + 2190213 * 2 ^ 59
def prefixEnd_2190213 : Nat := 4983230072969 + 3 ^ 40 * 2190213 * 2
def baseEnd_2190213 : Nat := 249918223272432114503311

theorem tailTrace_2190213 : CollatzResearch.WordTrace tailWord_2190213 prefixEnd_2190213 249918223272432114503311 := by
  unfold tailWord_2190213
  simp only [CollatzResearch.WordTrace]
  refine ⟨79883630814239834445183293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53255753876159889630122195 79883630814239834445183293)
  ·
    refine ⟨29956361555339937916943735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79883630814239834445183293 29956361555339937916943735)
    ·
      refine ⟨44934542333009906875415603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29956361555339937916943735 44934542333009906875415603)
      ·
        refine ⟨67401813499514860313123405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44934542333009906875415603 67401813499514860313123405)
        ·
          refine ⟨25275680062318072617421277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67401813499514860313123405 25275680062318072617421277)
          ·
            refine ⟨9478380023369277231532979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25275680062318072617421277 9478380023369277231532979)
            ·
              refine ⟨14217570035053915847299469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9478380023369277231532979 14217570035053915847299469)
              ·
                refine ⟨5331588763145218442737301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14217570035053915847299469 5331588763145218442737301)
                ·
                  refine ⟨249918223272432114503311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5331588763145218442737301 249918223272432114503311)
                  ·
                    rfl

theorem cell22_2190213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 3, 6].length) (baseStart_2190213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2190213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2190213 prefixEnd_2190213 := by exact prefixLift 2190213
  have htrace : WordTrace (prefixWord ++ tailWord_2190213) baseStart_2190213 baseEnd_2190213 := by
    simpa [prefixWord, tailWord_2190213, baseEnd_2190213] using wordTrace_append hprefix tailTrace_2190213
  have hstable : (prefixWord ++ tailWord_2190213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2190213).length < 2 ^ (prefixWord ++ tailWord_2190213).sum := by decide
  have hdescent : baseEnd_2190213 < baseStart_2190213 := by decide
  rcases family_descends (prefixWord ++ tailWord_2190213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2190243 : List Nat := [1, 1, 1, 4, 1, 2, 4, 1, 1, 6]
def baseStart_2190243 : Nat := 118140960795 + 2190243 * 2 ^ 59
def prefixEnd_2190243 : Nat := 4983230072969 + 3 ^ 40 * 2190243 * 2
def baseEnd_2190243 : Nat := 749764939430386265259841

theorem tailTrace_2190243 : CollatzResearch.WordTrace tailWord_2190243 prefixEnd_2190243 749764939430386265259841 := by
  unfold tailWord_2190243
  simp only [CollatzResearch.WordTrace]
  refine ⟨79884725004131149568775383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53256483336087433045850255 79884725004131149568775383)
  ·
    refine ⟨119827087506196724353163075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79884725004131149568775383 119827087506196724353163075)
    ·
      refine ⟨179740631259295086529744613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119827087506196724353163075 179740631259295086529744613)
      ·
        refine ⟨33701368361117828724327115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 179740631259295086529744613 33701368361117828724327115)
        ·
          refine ⟨50552052541676743086490673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33701368361117828724327115 50552052541676743086490673)
          ·
            refine ⟨37914039406257557314868005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50552052541676743086490673 37914039406257557314868005)
            ·
              refine ⟨7108882388673291996537751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37914039406257557314868005 7108882388673291996537751)
              ·
                refine ⟨10663323583009937994806627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7108882388673291996537751 10663323583009937994806627)
                ·
                  refine ⟨15994985374514906992209941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10663323583009937994806627 15994985374514906992209941)
                  ·
                    refine ⟨749764939430386265259841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15994985374514906992209941 749764939430386265259841)
                    ·
                      rfl

theorem cell22_2190243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 1, 1, 6].length) (baseStart_2190243 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2190243 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2190243 prefixEnd_2190243 := by exact prefixLift 2190243
  have htrace : WordTrace (prefixWord ++ tailWord_2190243) baseStart_2190243 baseEnd_2190243 := by
    simpa [prefixWord, tailWord_2190243, baseEnd_2190243] using wordTrace_append hprefix tailTrace_2190243
  have hstable : (prefixWord ++ tailWord_2190243).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2190243).length < 2 ^ (prefixWord ++ tailWord_2190243).sum := by decide
  have hdescent : baseEnd_2190243 < baseStart_2190243 := by decide
  rcases family_descends (prefixWord ++ tailWord_2190243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2190294 : List Nat := [5, 2, 1, 1, 2, 2, 2, 1, 2, 4]
def baseStart_2190294 : Nat := 118140960795 + 2190294 * 2 ^ 59
def prefixEnd_2190294 : Nat := 4983230072969 + 3 ^ 40 * 2190294 * 2
def baseEnd_2190294 : Nat := 749782397772639132234685

theorem tailTrace_2190294 : CollatzResearch.WordTrace tailWord_2190294 prefixEnd_2190294 749782397772639132234685 := by
  unfold tailWord_2190294
  simp only [CollatzResearch.WordTrace]
  refine ⟨4992911570434149079930121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 53257723417964256852587957 4992911570434149079930121)
  ·
    refine ⟨3744683677825611809947591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4992911570434149079930121 3744683677825611809947591)
    ·
      refine ⟨5617025516738417714921387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3744683677825611809947591 5617025516738417714921387)
      ·
        refine ⟨8425538275107626572382081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5617025516738417714921387 8425538275107626572382081)
        ·
          refine ⟨6319153706330719929286561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8425538275107626572382081 6319153706330719929286561)
          ·
            refine ⟨4739365279748039946964921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6319153706330719929286561 4739365279748039946964921)
            ·
              refine ⟨3554523959811029960223691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4739365279748039946964921 3554523959811029960223691)
              ·
                refine ⟨5331785939716544940335537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3554523959811029960223691 5331785939716544940335537)
                ·
                  refine ⟨3998839454787408705251653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5331785939716544940335537 3998839454787408705251653)
                  ·
                    refine ⟨749782397772639132234685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3998839454787408705251653 749782397772639132234685)
                    ·
                      rfl

theorem cell22_2190294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 2, 1, 2, 4].length) (baseStart_2190294 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2190294 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2190294 prefixEnd_2190294 := by exact prefixLift 2190294
  have htrace : WordTrace (prefixWord ++ tailWord_2190294) baseStart_2190294 baseEnd_2190294 := by
    simpa [prefixWord, tailWord_2190294, baseEnd_2190294] using wordTrace_append hprefix tailTrace_2190294
  have hstable : (prefixWord ++ tailWord_2190294).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2190294).length < 2 ^ (prefixWord ++ tailWord_2190294).sum := by decide
  have hdescent : baseEnd_2190294 < baseStart_2190294 := by decide
  rcases family_descends (prefixWord ++ tailWord_2190294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2190363 : List Nat := [1, 1, 1, 1, 1, 1, 3, 2, 2, 9]
def baseStart_2190363 : Nat := 118140960795 + 2190363 * 2 ^ 59
def prefixEnd_2190363 : Nat := 4983230072969 + 3 ^ 40 * 2190363 * 2
def baseEnd_2190363 : Nat := 749806017882745952259473

theorem tailTrace_2190363 : CollatzResearch.WordTrace tailWord_2190363 prefixEnd_2190363 749806017882745952259473 := by
  unfold tailWord_2190363
  simp only [CollatzResearch.WordTrace]
  refine ⟨79889101763696410063143743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53259401175797606708762495 79889101763696410063143743)
  ·
    refine ⟨119833652645544615094715615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79889101763696410063143743 119833652645544615094715615)
    ·
      refine ⟨179750478968316922642073423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119833652645544615094715615 179750478968316922642073423)
      ·
        refine ⟨269625718452475383963110135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 179750478968316922642073423 269625718452475383963110135)
        ·
          refine ⟨404438577678713075944665203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 269625718452475383963110135 404438577678713075944665203)
          ·
            refine ⟨606657866518069613916997805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 404438577678713075944665203 606657866518069613916997805)
            ·
              refine ⟨227496699944276105218874177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 606657866518069613916997805 227496699944276105218874177)
              ·
                refine ⟨170622524958207078914155633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 227496699944276105218874177 170622524958207078914155633)
                ·
                  refine ⟨127966893718655309185616725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 170622524958207078914155633 127966893718655309185616725)
                  ·
                    refine ⟨749806017882745952259473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 127966893718655309185616725 749806017882745952259473)
                    ·
                      rfl

theorem cell22_2190363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 2, 9].length) (baseStart_2190363 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2190363 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2190363 prefixEnd_2190363 := by exact prefixLift 2190363
  have htrace : WordTrace (prefixWord ++ tailWord_2190363) baseStart_2190363 baseEnd_2190363 := by
    simpa [prefixWord, tailWord_2190363, baseEnd_2190363] using wordTrace_append hprefix tailTrace_2190363
  have hstable : (prefixWord ++ tailWord_2190363).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2190363).length < 2 ^ (prefixWord ++ tailWord_2190363).sum := by decide
  have hdescent : baseEnd_2190363 < baseStart_2190363 := by decide
  rcases family_descends (prefixWord ++ tailWord_2190363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2190367 : List Nat := [1, 1, 2, 4, 1, 4, 1, 3, 1, 4]
def baseStart_2190367 : Nat := 118140960795 + 2190367 * 2 ^ 59
def prefixEnd_2190367 : Nat := 4983230072969 + 3 ^ 40 * 2190367 * 2
def baseEnd_2190367 : Nat := 749807387164491275159461

theorem tailTrace_2190367 : CollatzResearch.WordTrace tailWord_2190367 prefixEnd_2190367 749807387164491275159461 := by
  unfold tailWord_2190367
  simp only [CollatzResearch.WordTrace]
  refine ⟨79889247655681918746289355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53259498437121279164192903 79889247655681918746289355)
  ·
    refine ⟨119833871483522878119434033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79889247655681918746289355 119833871483522878119434033)
    ·
      refine ⟨89875403612642158589575525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119833871483522878119434033 89875403612642158589575525)
      ·
        refine ⟨16851638177370404735545411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 89875403612642158589575525 16851638177370404735545411)
        ·
          refine ⟨25277457266055607103318117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16851638177370404735545411 25277457266055607103318117)
          ·
            refine ⟨4739523237385426331872147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25277457266055607103318117 4739523237385426331872147)
            ·
              refine ⟨7109284856078139497808221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4739523237385426331872147 7109284856078139497808221)
              ·
                refine ⟨2665981821029302311678083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7109284856078139497808221 2665981821029302311678083)
                ·
                  refine ⟨3998972731543953467517125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2665981821029302311678083 3998972731543953467517125)
                  ·
                    refine ⟨749807387164491275159461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3998972731543953467517125 749807387164491275159461)
                    ·
                      rfl

theorem cell22_2190367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 3, 1, 4].length) (baseStart_2190367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2190367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2190367 prefixEnd_2190367 := by exact prefixLift 2190367
  have htrace : WordTrace (prefixWord ++ tailWord_2190367) baseStart_2190367 baseEnd_2190367 := by
    simpa [prefixWord, tailWord_2190367, baseEnd_2190367] using wordTrace_append hprefix tailTrace_2190367
  have hstable : (prefixWord ++ tailWord_2190367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2190367).length < 2 ^ (prefixWord ++ tailWord_2190367).sum := by decide
  have hdescent : baseEnd_2190367 < baseStart_2190367 := by decide
  rcases family_descends (prefixWord ++ tailWord_2190367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2190382 : List Nat := [4, 1, 3, 1, 1, 1, 4, 1, 6]
def baseStart_2190382 : Nat := 118140960795 + 2190382 * 2 ^ 59
def prefixEnd_2190382 : Nat := 4983230072969 + 3 ^ 40 * 2190382 * 2
def baseEnd_2190382 : Nat := 249937507323678745344805

theorem tailTrace_2190382 : CollatzResearch.WordTrace tailWord_2190382 prefixEnd_2190382 249937507323678745344805 := by
  unfold tailWord_2190382
  simp only [CollatzResearch.WordTrace]
  refine ⟨9986224343828447038510675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53259863167085050872056933 9986224343828447038510675)
  ·
    refine ⟨14979336515742670557766013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9986224343828447038510675 14979336515742670557766013)
    ·
      refine ⟨5617251193403501459162255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14979336515742670557766013 5617251193403501459162255)
      ·
        refine ⟨8425876790105252188743383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5617251193403501459162255 8425876790105252188743383)
        ·
          refine ⟨12638815185157878283115075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8425876790105252188743383 12638815185157878283115075)
          ·
            refine ⟨18958222777736817424672613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12638815185157878283115075 18958222777736817424672613)
            ·
              refine ⟨3554666770825653267126115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18958222777736817424672613 3554666770825653267126115)
              ·
                refine ⟨5332000156238479900689173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3554666770825653267126115 5332000156238479900689173)
                ·
                  refine ⟨249937507323678745344805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5332000156238479900689173 249937507323678745344805)
                  ·
                    rfl

theorem cell22_2190382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 4, 1, 6].length) (baseStart_2190382 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2190382 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2190382 prefixEnd_2190382 := by exact prefixLift 2190382
  have htrace : WordTrace (prefixWord ++ tailWord_2190382) baseStart_2190382 baseEnd_2190382 := by
    simpa [prefixWord, tailWord_2190382, baseEnd_2190382] using wordTrace_append hprefix tailTrace_2190382
  have hstable : (prefixWord ++ tailWord_2190382).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2190382).length < 2 ^ (prefixWord ++ tailWord_2190382).sum := by decide
  have hdescent : baseEnd_2190382 < baseStart_2190382 := by decide
  rcases family_descends (prefixWord ++ tailWord_2190382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2190397 : List Nat := [1, 4, 1, 3, 1, 2, 3, 1, 1, 5]
def baseStart_2190397 : Nat := 118140960795 + 2190397 * 2 ^ 59
def prefixEnd_2190397 : Nat := 4983230072969 + 3 ^ 40 * 2190397 * 2
def baseEnd_2190397 : Nat := 749817656777581196909369

theorem tailTrace_2190397 : CollatzResearch.WordTrace tailWord_2190397 prefixEnd_2190397 749817656777581196909369 := by
  unfold tailWord_2190397
  simp only [CollatzResearch.WordTrace]
  refine ⟨79890341845573233869881445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53260227897048822579920963 79890341845573233869881445)
  ·
    refine ⟨14979439096044981350602771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 79890341845573233869881445 14979439096044981350602771)
    ·
      refine ⟨22469158644067472025904157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14979439096044981350602771 22469158644067472025904157)
      ·
        refine ⟨8425934491525302009714059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22469158644067472025904157 8425934491525302009714059)
        ·
          refine ⟨12638901737287953014571089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8425934491525302009714059 12638901737287953014571089)
          ·
            refine ⟨9479176302965964760928317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12638901737287953014571089 9479176302965964760928317)
            ·
              refine ⟨3554691113612236785348119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9479176302965964760928317 3554691113612236785348119)
              ·
                refine ⟨5332036670418355178022179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3554691113612236785348119 5332036670418355178022179)
                ·
                  refine ⟨7998055005627532767033269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5332036670418355178022179 7998055005627532767033269)
                  ·
                    refine ⟨749817656777581196909369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7998055005627532767033269 749817656777581196909369)
                    ·
                      rfl

theorem cell22_2190397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 3, 1, 1, 5].length) (baseStart_2190397 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2190397 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2190397 prefixEnd_2190397 := by exact prefixLift 2190397
  have htrace : WordTrace (prefixWord ++ tailWord_2190397) baseStart_2190397 baseEnd_2190397 := by
    simpa [prefixWord, tailWord_2190397, baseEnd_2190397] using wordTrace_append hprefix tailTrace_2190397
  have hstable : (prefixWord ++ tailWord_2190397).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2190397).length < 2 ^ (prefixWord ++ tailWord_2190397).sum := by decide
  have hdescent : baseEnd_2190397 < baseStart_2190397 := by decide
  rcases family_descends (prefixWord ++ tailWord_2190397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2190579 : List Nat := [1, 1, 1, 2, 2, 7, 2, 6]
def baseStart_2190579 : Nat := 118140960795 + 2190579 * 2 ^ 59
def prefixEnd_2190579 : Nat := 4983230072969 + 3 ^ 40 * 2190579 * 2
def baseEnd_2190579 : Nat := 83319995455221487650979

theorem tailTrace_2190579 : CollatzResearch.WordTrace tailWord_2190579 prefixEnd_2190579 83319995455221487650979 := by
  unfold tailWord_2190579
  simp only [CollatzResearch.WordTrace]
  refine ⟨79896979930913878953006791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53264653287275919302004527 79896979930913878953006791)
  ·
    refine ⟨119845469896370818429510187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79896979930913878953006791 119845469896370818429510187)
    ·
      refine ⟨179768204844556227644265281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119845469896370818429510187 179768204844556227644265281)
      ·
        refine ⟨134826153633417170733198961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 179768204844556227644265281 134826153633417170733198961)
        ·
          refine ⟨101119615225062878049899221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 134826153633417170733198961 101119615225062878049899221)
          ·
            refine ⟨2369990981837411204294513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 101119615225062878049899221 2369990981837411204294513)
            ·
              refine ⟨1777493236378058403220885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2369990981837411204294513 1777493236378058403220885)
              ·
                refine ⟨83319995455221487650979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1777493236378058403220885 83319995455221487650979)
                ·
                  rfl

theorem cell22_2190579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 2, 6].length) (baseStart_2190579 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2190579 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2190579 prefixEnd_2190579 := by exact prefixLift 2190579
  have htrace : WordTrace (prefixWord ++ tailWord_2190579) baseStart_2190579 baseEnd_2190579 := by
    simpa [prefixWord, tailWord_2190579, baseEnd_2190579] using wordTrace_append hprefix tailTrace_2190579
  have hstable : (prefixWord ++ tailWord_2190579).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2190579).length < 2 ^ (prefixWord ++ tailWord_2190579).sum := by decide
  have hdescent : baseEnd_2190579 < baseStart_2190579 := by decide
  rcases family_descends (prefixWord ++ tailWord_2190579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2190712 : List Nat := [2, 1, 2, 1, 1, 1, 1, 1, 3, 9]
def baseStart_2190712 : Nat := 118140960795 + 2190712 * 2 ^ 59
def prefixEnd_2190712 : Nat := 4983230072969 + 3 ^ 40 * 2190712 * 2
def baseEnd_2190712 : Nat := 749925487715025375283403

theorem tailTrace_2190712 : CollatzResearch.WordTrace tailWord_2190712 prefixEnd_2190712 749925487715025375283403 := by
  unfold tailWord_2190712
  simp only [CollatzResearch.WordTrace]
  refine ⟨39950915419716021333799195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53267887226288028445065593 39950915419716021333799195)
  ·
    refine ⟨59926373129574032000698793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39950915419716021333799195 59926373129574032000698793)
    ·
      refine ⟨44944779847180524000524095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59926373129574032000698793 44944779847180524000524095)
      ·
        refine ⟨67417169770770786000786143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44944779847180524000524095 67417169770770786000786143)
        ·
          refine ⟨101125754656156179001179215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67417169770770786000786143 101125754656156179001179215)
          ·
            refine ⟨151688631984234268501768823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101125754656156179001179215 151688631984234268501768823)
            ·
              refine ⟨227532947976351402752653235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 151688631984234268501768823 227532947976351402752653235)
              ·
                refine ⟨341299421964527104128979853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 227532947976351402752653235 341299421964527104128979853)
                ·
                  refine ⟨127987283236697664048367445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 341299421964527104128979853 127987283236697664048367445)
                  ·
                    refine ⟨749925487715025375283403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 127987283236697664048367445 749925487715025375283403)
                    ·
                      rfl

theorem cell22_2190712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 3, 9].length) (baseStart_2190712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2190712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2190712 prefixEnd_2190712 := by exact prefixLift 2190712
  have htrace : WordTrace (prefixWord ++ tailWord_2190712) baseStart_2190712 baseEnd_2190712 := by
    simpa [prefixWord, tailWord_2190712, baseEnd_2190712] using wordTrace_append hprefix tailTrace_2190712
  have hstable : (prefixWord ++ tailWord_2190712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2190712).length < 2 ^ (prefixWord ++ tailWord_2190712).sum := by decide
  have hdescent : baseEnd_2190712 < baseStart_2190712 := by decide
  rcases family_descends (prefixWord ++ tailWord_2190712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2190746 : List Nat := [3, 1, 1, 4, 1, 1, 1, 4, 3, 3]
def baseStart_2190746 : Nat := 118140960795 + 2190746 * 2 ^ 59
def prefixEnd_2190746 : Nat := 4983230072969 + 3 ^ 40 * 2190746 * 2
def baseEnd_2190746 : Nat := 749937126609860619933299

theorem tailTrace_2190746 : CollatzResearch.WordTrace tailWord_2190746 prefixEnd_2190746 749937126609860619933299 := by
  unfold tailWord_2190746
  simp only [CollatzResearch.WordTrace]
  refine ⟨19975767730327216618584023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53268713947539244316224061 19975767730327216618584023)
  ·
    refine ⟨29963651595490824927876035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19975767730327216618584023 29963651595490824927876035)
    ·
      refine ⟨44945477393236237391814053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29963651595490824927876035 44945477393236237391814053)
      ·
        refine ⟨8427277011231794510965135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44945477393236237391814053 8427277011231794510965135)
        ·
          refine ⟨12640915516847691766447703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8427277011231794510965135 12640915516847691766447703)
          ·
            refine ⟨18961373275271537649671555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12640915516847691766447703 18961373275271537649671555)
            ·
              refine ⟨28442059912907306474507333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18961373275271537649671555 28442059912907306474507333)
              ·
                refine ⟨5332886233670119963970125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28442059912907306474507333 5332886233670119963970125)
                ·
                  refine ⟨1999832337626294986488797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5332886233670119963970125 1999832337626294986488797)
                  ·
                    refine ⟨749937126609860619933299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1999832337626294986488797 749937126609860619933299)
                    ·
                      rfl

theorem cell22_2190746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 4, 3, 3].length) (baseStart_2190746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2190746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2190746 prefixEnd_2190746 := by exact prefixLift 2190746
  have htrace : WordTrace (prefixWord ++ tailWord_2190746) baseStart_2190746 baseEnd_2190746 := by
    simpa [prefixWord, tailWord_2190746, baseEnd_2190746] using wordTrace_append hprefix tailTrace_2190746
  have hstable : (prefixWord ++ tailWord_2190746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2190746).length < 2 ^ (prefixWord ++ tailWord_2190746).sum := by decide
  have hdescent : baseEnd_2190746 < baseStart_2190746 := by decide
  rcases family_descends (prefixWord ++ tailWord_2190746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2190759 : List Nat := [1, 1, 6, 1, 1, 1, 1, 1, 9]
def baseStart_2190759 : Nat := 118140960795 + 2190759 * 2 ^ 59
def prefixEnd_2190759 : Nat := 4983230072969 + 3 ^ 40 * 2190759 * 2
def baseEnd_2190759 : Nat := 249980525591844306452753

theorem tailTrace_2190759 : CollatzResearch.WordTrace tailWord_2190759 prefixEnd_2190759 249980525591844306452753 := by
  unfold tailWord_2190759
  simp only [CollatzResearch.WordTrace]
  refine ⟨79903545070261769694559331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53269030046841179796372887 79903545070261769694559331)
  ·
    refine ⟨119855317605392654541838997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79903545070261769694559331 119855317605392654541838997)
    ·
      refine ⟨5618218012752780681648703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 119855317605392654541838997 5618218012752780681648703)
      ·
        refine ⟨8427327019129171022473055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5618218012752780681648703 8427327019129171022473055)
        ·
          refine ⟨12640990528693756533709583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8427327019129171022473055 12640990528693756533709583)
          ·
            refine ⟨18961485793040634800564375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12640990528693756533709583 18961485793040634800564375)
            ·
              refine ⟨28442228689560952200846563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18961485793040634800564375 28442228689560952200846563)
              ·
                refine ⟨42663343034341428301269845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28442228689560952200846563 42663343034341428301269845)
                ·
                  refine ⟨249980525591844306452753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 42663343034341428301269845 249980525591844306452753)
                  ·
                    rfl

theorem cell22_2190759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 1, 9].length) (baseStart_2190759 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2190759 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2190759 prefixEnd_2190759 := by exact prefixLift 2190759
  have htrace : WordTrace (prefixWord ++ tailWord_2190759) baseStart_2190759 baseEnd_2190759 := by
    simpa [prefixWord, tailWord_2190759, baseEnd_2190759] using wordTrace_append hprefix tailTrace_2190759
  have hstable : (prefixWord ++ tailWord_2190759).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2190759).length < 2 ^ (prefixWord ++ tailWord_2190759).sum := by decide
  have hdescent : baseEnd_2190759 < baseStart_2190759 := by decide
  rcases family_descends (prefixWord ++ tailWord_2190759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2190780 : List Nat := [2, 2, 2, 4, 2, 2, 1, 1, 3, 3]
def baseStart_2190780 : Nat := 118140960795 + 2190780 * 2 ^ 59
def prefixEnd_2190780 : Nat := 4983230072969 + 3 ^ 40 * 2190780 * 2
def baseEnd_2190780 : Nat := 749948765504695864583195

theorem tailTrace_2190780 : CollatzResearch.WordTrace tailWord_2190780 prefixEnd_2190780 749948765504695864583195 := by
  unfold tailWord_2190780
  simp only [CollatzResearch.WordTrace]
  refine ⟨39952155501592845140536897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53269540668790460187382529 39952155501592845140536897)
  ·
    refine ⟨29964116626194633855402673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39952155501592845140536897 29964116626194633855402673)
    ·
      refine ⟨22473087469645975391552005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29964116626194633855402673 22473087469645975391552005)
      ·
        refine ⟨4213703900558620385916001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22473087469645975391552005 4213703900558620385916001)
        ·
          refine ⟨3160277925418965289437001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4213703900558620385916001 3160277925418965289437001)
          ·
            refine ⟨2370208444064223967077751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3160277925418965289437001 2370208444064223967077751)
            ·
              refine ⟨3555312666096335950616627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2370208444064223967077751 3555312666096335950616627)
              ·
                refine ⟨5332968999144503925924941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3555312666096335950616627 5332968999144503925924941)
                ·
                  refine ⟨1999863374679188972221853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5332968999144503925924941 1999863374679188972221853)
                  ·
                    refine ⟨749948765504695864583195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1999863374679188972221853 749948765504695864583195)
                    ·
                      rfl

theorem cell22_2190780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 1, 1, 3, 3].length) (baseStart_2190780 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2190780 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2190780 prefixEnd_2190780 := by exact prefixLift 2190780
  have htrace : WordTrace (prefixWord ++ tailWord_2190780) baseStart_2190780 baseEnd_2190780 := by
    simpa [prefixWord, tailWord_2190780, baseEnd_2190780] using wordTrace_append hprefix tailTrace_2190780
  have hstable : (prefixWord ++ tailWord_2190780).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2190780).length < 2 ^ (prefixWord ++ tailWord_2190780).sum := by decide
  have hdescent : baseEnd_2190780 < baseStart_2190780 := by decide
  rcases family_descends (prefixWord ++ tailWord_2190780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2190971 : List Nat := [1, 1, 1, 1, 1, 4, 4, 3, 1, 5]
def baseStart_2190971 : Nat := 118140960795 + 2190971 * 2 ^ 59
def prefixEnd_2190971 : Nat := 4983230072969 + 3 ^ 40 * 2190971 * 2
def baseEnd_2190971 : Nat := 750014148708035033057609

theorem tailTrace_2190971 : CollatzResearch.WordTrace tailWord_2190971 prefixEnd_2190971 750014148708035033057609 := by
  unfold tailWord_2190971
  simp only [CollatzResearch.WordTrace]
  refine ⟨79911277345493729901276767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53274184896995819934184511 79911277345493729901276767)
  ·
    refine ⟨119866916018240594851915151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79911277345493729901276767 119866916018240594851915151)
    ·
      refine ⟨179800374027360892277872727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119866916018240594851915151 179800374027360892277872727)
      ·
        refine ⟨269700561041041338416809091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 179800374027360892277872727 269700561041041338416809091)
        ·
          refine ⟨404550841561562007625213637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 269700561041041338416809091 404550841561562007625213637)
          ·
            refine ⟨75853282792792876429727557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 404550841561562007625213637 75853282792792876429727557)
            ·
              refine ⟨14222490523648664330573917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 75853282792792876429727557 14222490523648664330573917)
              ·
                refine ⟨5333433946368249123965219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14222490523648664330573917 5333433946368249123965219)
                ·
                  refine ⟨8000150919552373685947829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5333433946368249123965219 8000150919552373685947829)
                  ·
                    refine ⟨750014148708035033057609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8000150919552373685947829 750014148708035033057609)
                    ·
                      rfl

theorem cell22_2190971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 3, 1, 5].length) (baseStart_2190971 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2190971 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2190971 prefixEnd_2190971 := by exact prefixLift 2190971
  have htrace : WordTrace (prefixWord ++ tailWord_2190971) baseStart_2190971 baseEnd_2190971 := by
    simpa [prefixWord, tailWord_2190971, baseEnd_2190971] using wordTrace_append hprefix tailTrace_2190971
  have hstable : (prefixWord ++ tailWord_2190971).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2190971).length < 2 ^ (prefixWord ++ tailWord_2190971).sum := by decide
  have hdescent : baseEnd_2190971 < baseStart_2190971 := by decide
  rcases family_descends (prefixWord ++ tailWord_2190971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2191007 : List Nat := [1, 1, 2, 7, 1, 1, 1, 4, 4]
def baseStart_2191007 : Nat := 118140960795 + 2191007 * 2 ^ 59
def prefixEnd_2191007 : Nat := 4983230072969 + 3 ^ 40 * 2191007 * 2
def baseEnd_2191007 : Nat := 250008824081247646385833

theorem tailTrace_2191007 : CollatzResearch.WordTrace tailWord_2191007 prefixEnd_2191007 250008824081247646385833 := by
  unfold tailWord_2191007
  simp only [CollatzResearch.WordTrace]
  refine ⟨79912590373363308049587275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53275060248908872033058183 79912590373363308049587275)
  ·
    refine ⟨119868885560044962074380913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79912590373363308049587275 119868885560044962074380913)
    ·
      refine ⟨89901664170033721555785685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119868885560044962074380913 89901664170033721555785685)
      ·
        refine ⟨2107070253985165348963727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 89901664170033721555785685 2107070253985165348963727)
        ·
          refine ⟨3160605380977748023445591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2107070253985165348963727 3160605380977748023445591)
          ·
            refine ⟨4740908071466622035168387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3160605380977748023445591 4740908071466622035168387)
            ·
              refine ⟨7111362107199933052752581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4740908071466622035168387 7111362107199933052752581)
              ·
                refine ⟨1333380395099987447391109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7111362107199933052752581 1333380395099987447391109)
                ·
                  refine ⟨250008824081247646385833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1333380395099987447391109 250008824081247646385833)
                  ·
                    rfl

theorem cell22_2191007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 4, 4].length) (baseStart_2191007 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2191007 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2191007 prefixEnd_2191007 := by exact prefixLift 2191007
  have htrace : WordTrace (prefixWord ++ tailWord_2191007) baseStart_2191007 baseEnd_2191007 := by
    simpa [prefixWord, tailWord_2191007, baseEnd_2191007] using wordTrace_append hprefix tailTrace_2191007
  have hstable : (prefixWord ++ tailWord_2191007).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2191007).length < 2 ^ (prefixWord ++ tailWord_2191007).sum := by decide
  have hdescent : baseEnd_2191007 < baseStart_2191007 := by decide
  rcases family_descends (prefixWord ++ tailWord_2191007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2191022 : List Nat := [4, 1, 4, 1, 2, 1, 2, 1, 1, 5]
def baseStart_2191022 : Nat := 118140960795 + 2191022 * 2 ^ 59
def prefixEnd_2191022 : Nat := 4983230072969 + 3 ^ 40 * 2191022 * 2
def baseEnd_2191022 : Nat := 750031607050287900032453

theorem tailTrace_2191022 : CollatzResearch.WordTrace tailWord_2191022 prefixEnd_2191022 750031607050287900032453 := by
  unfold tailWord_2191022
  simp only [CollatzResearch.WordTrace]
  refine ⟨9989142183538620701422915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53275424978872643740922213 9989142183538620701422915)
  ·
    refine ⟨14983713275307931052134373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9989142183538620701422915 14983713275307931052134373)
    ·
      refine ⟨2809446239120237072275195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14983713275307931052134373 2809446239120237072275195)
      ·
        refine ⟨4214169358680355608412793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2809446239120237072275195 4214169358680355608412793)
        ·
          refine ⟨3160627019010266706309595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4214169358680355608412793 3160627019010266706309595)
          ·
            refine ⟨4740940528515400059464393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3160627019010266706309595 4740940528515400059464393)
            ·
              refine ⟨3555705396386550044598295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4740940528515400059464393 3555705396386550044598295)
              ·
                refine ⟨5333558094579825066897443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3555705396386550044598295 5333558094579825066897443)
                ·
                  refine ⟨8000337141869737600346165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5333558094579825066897443 8000337141869737600346165)
                  ·
                    refine ⟨750031607050287900032453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8000337141869737600346165 750031607050287900032453)
                    ·
                      rfl

theorem cell22_2191022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_2191022 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2191022 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2191022 prefixEnd_2191022 := by exact prefixLift 2191022
  have htrace : WordTrace (prefixWord ++ tailWord_2191022) baseStart_2191022 baseEnd_2191022 := by
    simpa [prefixWord, tailWord_2191022, baseEnd_2191022] using wordTrace_append hprefix tailTrace_2191022
  have hstable : (prefixWord ++ tailWord_2191022).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2191022).length < 2 ^ (prefixWord ++ tailWord_2191022).sum := by decide
  have hdescent : baseEnd_2191022 < baseStart_2191022 := by decide
  rcases family_descends (prefixWord ++ tailWord_2191022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2191033 : List Nat := [1, 2, 1, 4, 1, 1, 3, 1, 5, 3]
def baseStart_2191033 : Nat := 118140960795 + 2191033 * 2 ^ 59
def prefixEnd_2191033 : Nat := 4983230072969 + 3 ^ 40 * 2191033 * 2
def baseEnd_2191033 : Nat := 750035372575087538007419

theorem tailTrace_2191033 : CollatzResearch.WordTrace tailWord_2191033 prefixEnd_2191033 750035372575087538007419 := by
  unfold tailWord_2191033
  simp only [CollatzResearch.WordTrace]
  refine ⟨79913538671269114490033753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53275692447512742993355835 79913538671269114490033753)
  ·
    refine ⟨59935154003451835867525315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79913538671269114490033753 59935154003451835867525315)
    ·
      refine ⟨89902731005177753801287973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59935154003451835867525315 89902731005177753801287973)
      ·
        refine ⟨16856762063470828837741495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 89902731005177753801287973 16856762063470828837741495)
        ·
          refine ⟨25285143095206243256612243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16856762063470828837741495 25285143095206243256612243)
          ·
            refine ⟨37927714642809364884918365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25285143095206243256612243 37927714642809364884918365)
            ·
              refine ⟨14222892991053511831844387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37927714642809364884918365 14222892991053511831844387)
              ·
                refine ⟨21334339486580267747766581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14222892991053511831844387 21334339486580267747766581)
                ·
                  refine ⟨2000094326866900101353117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21334339486580267747766581 2000094326866900101353117)
                  ·
                    refine ⟨750035372575087538007419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2000094326866900101353117 750035372575087538007419)
                    ·
                      rfl

theorem cell22_2191033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 1, 5, 3].length) (baseStart_2191033 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2191033 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2191033 prefixEnd_2191033 := by exact prefixLift 2191033
  have htrace : WordTrace (prefixWord ++ tailWord_2191033) baseStart_2191033 baseEnd_2191033 := by
    simpa [prefixWord, tailWord_2191033, baseEnd_2191033] using wordTrace_append hprefix tailTrace_2191033
  have hstable : (prefixWord ++ tailWord_2191033).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2191033).length < 2 ^ (prefixWord ++ tailWord_2191033).sum := by decide
  have hdescent : baseEnd_2191033 < baseStart_2191033 := by decide
  rcases family_descends (prefixWord ++ tailWord_2191033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2191125 : List Nat := [1, 3, 2, 1, 2, 5, 1, 1, 6]
def baseStart_2191125 : Nat := 118140960795 + 2191125 * 2 ^ 59
def prefixEnd_2191125 : Nat := 4983230072969 + 3 ^ 40 * 2191125 * 2
def baseEnd_2191125 : Nat := 250022288685076654902379

theorem tailTrace_2191125 : CollatzResearch.WordTrace tailWord_2191125 prefixEnd_2191125 250022288685076654902379 := by
  unfold tailWord_2191125
  simp only [CollatzResearch.WordTrace]
  refine ⟨79916894186935814202382829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53277929457957209468255219 79916894186935814202382829)
  ·
    refine ⟨29968835320100930325893561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79916894186935814202382829 29968835320100930325893561)
    ·
      refine ⟨22476626490075697744420171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29968835320100930325893561 22476626490075697744420171)
      ·
        refine ⟨33714939735113546616630257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22476626490075697744420171 33714939735113546616630257)
        ·
          refine ⟨25286204801335159962472693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33714939735113546616630257 25286204801335159962472693)
          ·
            refine ⟨2370581700125171246481815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 25286204801335159962472693 2370581700125171246481815)
            ·
              refine ⟨3555872550187756869722723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2370581700125171246481815 3555872550187756869722723)
              ·
                refine ⟨5333808825281635304584085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3555872550187756869722723 5333808825281635304584085)
                ·
                  refine ⟨250022288685076654902379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5333808825281635304584085 250022288685076654902379)
                  ·
                    rfl

theorem cell22_2191125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 1, 1, 6].length) (baseStart_2191125 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2191125 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2191125 prefixEnd_2191125 := by exact prefixLift 2191125
  have htrace : WordTrace (prefixWord ++ tailWord_2191125) baseStart_2191125 baseEnd_2191125 := by
    simpa [prefixWord, tailWord_2191125, baseEnd_2191125] using wordTrace_append hprefix tailTrace_2191125
  have hstable : (prefixWord ++ tailWord_2191125).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2191125).length < 2 ^ (prefixWord ++ tailWord_2191125).sum := by decide
  have hdescent : baseEnd_2191125 < baseStart_2191125 := by decide
  rcases family_descends (prefixWord ++ tailWord_2191125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2191153 : List Nat := [1, 2, 2, 3, 2, 2, 2, 8]
def baseStart_2191153 : Nat := 118140960795 + 2191153 * 2 ^ 59
def prefixEnd_2191153 : Nat := 4983230072969 + 3 ^ 40 * 2191153 * 2
def baseEnd_2191153 : Nat := 83341827891938580556339

theorem tailTrace_2191153 : CollatzResearch.WordTrace tailWord_2191153 prefixEnd_2191153 83341827891938580556339 := by
  unfold tailWord_2191153
  simp only [CollatzResearch.WordTrace]
  refine ⟨79917915430834374984402113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53278610287222916656268075 79917915430834374984402113)
  ·
    refine ⟨59938436573125781238301585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79917915430834374984402113 59938436573125781238301585)
    ·
      refine ⟨44953827429844335928726189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59938436573125781238301585 44953827429844335928726189)
      ·
        refine ⟨16857685286191625973272321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44953827429844335928726189 16857685286191625973272321)
        ·
          refine ⟨12643263964643719479954241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16857685286191625973272321 12643263964643719479954241)
          ·
            refine ⟨9482447973482789609965681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12643263964643719479954241 9482447973482789609965681)
            ·
              refine ⟨7111835980112092207474261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9482447973482789609965681 7111835980112092207474261)
              ·
                refine ⟨83341827891938580556339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7111835980112092207474261 83341827891938580556339)
                ·
                  rfl

theorem cell22_2191153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 8].length) (baseStart_2191153 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2191153 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2191153 prefixEnd_2191153 := by exact prefixLift 2191153
  have htrace : WordTrace (prefixWord ++ tailWord_2191153) baseStart_2191153 baseEnd_2191153 := by
    simpa [prefixWord, tailWord_2191153, baseEnd_2191153] using wordTrace_append hprefix tailTrace_2191153
  have hstable : (prefixWord ++ tailWord_2191153).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2191153).length < 2 ^ (prefixWord ++ tailWord_2191153).sum := by decide
  have hdescent : baseEnd_2191153 < baseStart_2191153 := by decide
  rcases family_descends (prefixWord ++ tailWord_2191153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2191202 : List Nat := [3, 3, 2, 1, 2, 1, 1, 1, 5, 3]
def baseStart_2191202 : Nat := 118140960795 + 2191202 * 2 ^ 59
def prefixEnd_2191202 : Nat := 4983230072969 + 3 ^ 40 * 2191202 * 2
def baseEnd_2191202 : Nat := 750093224728827430531901

theorem tailTrace_2191202 : CollatzResearch.WordTrace tailWord_2191202 prefixEnd_2191202 750093224728827430531901 := by
  unfold tailWord_2191202
  simp only [CollatzResearch.WordTrace]
  refine ⟨19979925651914214088233965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53279801738437904235290573 19979925651914214088233965)
  ·
    refine ⟨7492472119467830283087737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19979925651914214088233965 7492472119467830283087737)
    ·
      refine ⟨5619354089600872712315803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7492472119467830283087737 5619354089600872712315803)
      ·
        refine ⟨8429031134401309068473705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5619354089600872712315803 8429031134401309068473705)
        ·
          refine ⟨6321773350800981801355279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8429031134401309068473705 6321773350800981801355279)
          ·
            refine ⟨9482660026201472702032919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6321773350800981801355279 9482660026201472702032919)
            ·
              refine ⟨14223990039302209053049379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9482660026201472702032919 14223990039302209053049379)
              ·
                refine ⟨21335985058953313579574069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14223990039302209053049379 21335985058953313579574069)
                ·
                  refine ⟨2000248599276873148085069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21335985058953313579574069 2000248599276873148085069)
                  ·
                    refine ⟨750093224728827430531901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2000248599276873148085069 750093224728827430531901)
                    ·
                      rfl

theorem cell22_2191202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 1, 5, 3].length) (baseStart_2191202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2191202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2191202 prefixEnd_2191202 := by exact prefixLift 2191202
  have htrace : WordTrace (prefixWord ++ tailWord_2191202) baseStart_2191202 baseEnd_2191202 := by
    simpa [prefixWord, tailWord_2191202, baseEnd_2191202] using wordTrace_append hprefix tailTrace_2191202
  have hstable : (prefixWord ++ tailWord_2191202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2191202).length < 2 ^ (prefixWord ++ tailWord_2191202).sum := by decide
  have hdescent : baseEnd_2191202 < baseStart_2191202 := by decide
  rcases family_descends (prefixWord ++ tailWord_2191202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2191365 : List Nat := [1, 3, 1, 1, 2, 4, 1, 1, 1, 7]
def baseStart_2191365 : Nat := 118140960795 + 2191365 * 2 ^ 59
def prefixEnd_2191365 : Nat := 4983230072969 + 3 ^ 40 * 2191365 * 2
def baseEnd_2191365 : Nat := 750149022959949338706401

theorem tailTrace_2191365 : CollatzResearch.WordTrace tailWord_2191365 prefixEnd_2191365 750149022959949338706401 := by
  unfold tailWord_2191365
  simp only [CollatzResearch.WordTrace]
  refine ⟨79925647706066335191119549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53283765137377556794079699 79925647706066335191119549)
  ·
    refine ⟨29972117889774875696669831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79925647706066335191119549 29972117889774875696669831)
    ·
      refine ⟨44958176834662313545004747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29972117889774875696669831 44958176834662313545004747)
      ·
        refine ⟨67437265251993470317507121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44958176834662313545004747 67437265251993470317507121)
        ·
          refine ⟨50577948938995102738130341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67437265251993470317507121 50577948938995102738130341)
          ·
            refine ⟨9483365426061581763399439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50577948938995102738130341 9483365426061581763399439)
            ·
              refine ⟨14225048139092372645099159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9483365426061581763399439 14225048139092372645099159)
              ·
                refine ⟨21337572208638558967648739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14225048139092372645099159 21337572208638558967648739)
                ·
                  refine ⟨32006358312957838451473109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21337572208638558967648739 32006358312957838451473109)
                  ·
                    refine ⟨750149022959949338706401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32006358312957838451473109 750149022959949338706401)
                    ·
                      rfl

theorem cell22_2191365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 1, 1, 7].length) (baseStart_2191365 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2191365 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2191365 prefixEnd_2191365 := by exact prefixLift 2191365
  have htrace : WordTrace (prefixWord ++ tailWord_2191365) baseStart_2191365 baseEnd_2191365 := by
    simpa [prefixWord, tailWord_2191365, baseEnd_2191365] using wordTrace_append hprefix tailTrace_2191365
  have hstable : (prefixWord ++ tailWord_2191365).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2191365).length < 2 ^ (prefixWord ++ tailWord_2191365).sum := by decide
  have hdescent : baseEnd_2191365 < baseStart_2191365 := by decide
  rcases family_descends (prefixWord ++ tailWord_2191365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2191367 : List Nat := [1, 1, 4, 3, 1, 2, 2, 3, 5]
def baseStart_2191367 : Nat := 118140960795 + 2191367 * 2 ^ 59
def prefixEnd_2191367 : Nat := 4983230072969 + 3 ^ 40 * 2191367 * 2
def baseEnd_2191367 : Nat := 250049902533607333385465

theorem tailTrace_2191367 : CollatzResearch.WordTrace tailWord_2191367 prefixEnd_2191367 250049902533607333385465 := by
  unfold tailWord_2191367
  simp only [CollatzResearch.WordTrace]
  refine ⟨79925720652059089532692355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53283813768039393021794903 79925720652059089532692355)
  ·
    refine ⟨119888580978088634299038533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79925720652059089532692355 119888580978088634299038533)
    ·
      refine ⟨22479108933391618931069725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 119888580978088634299038533 22479108933391618931069725)
      ·
        refine ⟨8429665850021857099151147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22479108933391618931069725 8429665850021857099151147)
        ·
          refine ⟨12644498775032785648726721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8429665850021857099151147 12644498775032785648726721)
          ·
            refine ⟨9483374081274589236545041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12644498775032785648726721 9483374081274589236545041)
            ·
              refine ⟨7112530560955941927408781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9483374081274589236545041 7112530560955941927408781)
              ·
                refine ⟨2667198960358478222778293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7112530560955941927408781 2667198960358478222778293)
                ·
                  refine ⟨250049902533607333385465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2667198960358478222778293 250049902533607333385465)
                  ·
                    rfl

theorem cell22_2191367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 3, 5].length) (baseStart_2191367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2191367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2191367 prefixEnd_2191367 := by exact prefixLift 2191367
  have htrace : WordTrace (prefixWord ++ tailWord_2191367) baseStart_2191367 baseEnd_2191367 := by
    simpa [prefixWord, tailWord_2191367, baseEnd_2191367] using wordTrace_append hprefix tailTrace_2191367
  have hstable : (prefixWord ++ tailWord_2191367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2191367).length < 2 ^ (prefixWord ++ tailWord_2191367).sum := by decide
  have hdescent : baseEnd_2191367 < baseStart_2191367 := by decide
  rcases family_descends (prefixWord ++ tailWord_2191367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2191373 : List Nat := [1, 7, 1, 2, 1, 1, 3, 6]
def baseStart_2191373 : Nat := 118140960795 + 2191373 * 2 ^ 59
def prefixEnd_2191373 : Nat := 4983230072969 + 3 ^ 40 * 2191373 * 2
def baseEnd_2191373 : Nat := 83350195724826664945153

theorem tailTrace_2191373 : CollatzResearch.WordTrace tailWord_2191373 prefixEnd_2191373 83350195724826664945153 := by
  unfold tailWord_2191373
  simp only [CollatzResearch.WordTrace]
  refine ⟨79925939490037352557410773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53283959660024901704940515 79925939490037352557410773)
  ·
    refine ⟨1873264206797750450564315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 79925939490037352557410773 1873264206797750450564315)
    ·
      refine ⟨2809896310196625675846473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1873264206797750450564315 2809896310196625675846473)
      ·
        refine ⟨2107422232647469256884855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2809896310196625675846473 2107422232647469256884855)
        ·
          refine ⟨3161133348971203885327283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2107422232647469256884855 3161133348971203885327283)
          ·
            refine ⟨4741700023456805827990925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3161133348971203885327283 4741700023456805827990925)
            ·
              refine ⟨1778137508796302185496597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4741700023456805827990925 1778137508796302185496597)
              ·
                refine ⟨83350195724826664945153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1778137508796302185496597 83350195724826664945153)
                ·
                  rfl

theorem cell22_2191373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 3, 6].length) (baseStart_2191373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2191373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2191373 prefixEnd_2191373 := by exact prefixLift 2191373
  have htrace : WordTrace (prefixWord ++ tailWord_2191373) baseStart_2191373 baseEnd_2191373 := by
    simpa [prefixWord, tailWord_2191373, baseEnd_2191373] using wordTrace_append hprefix tailTrace_2191373
  have hstable : (prefixWord ++ tailWord_2191373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2191373).length < 2 ^ (prefixWord ++ tailWord_2191373).sum := by decide
  have hdescent : baseEnd_2191373 < baseStart_2191373 := by decide
  rcases family_descends (prefixWord ++ tailWord_2191373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2191395 : List Nat := [1, 1, 1, 4, 3, 1, 1, 2, 8]
def baseStart_2191395 : Nat := 118140960795 + 2191395 * 2 ^ 59
def prefixEnd_2191395 : Nat := 4983230072969 + 3 ^ 40 * 2191395 * 2
def baseEnd_2191395 : Nat := 250053097524346420152103

theorem tailTrace_2191395 : CollatzResearch.WordTrace tailWord_2191395 prefixEnd_2191395 250053097524346420152103 := by
  unfold tailWord_2191395
  simp only [CollatzResearch.WordTrace]
  refine ⟨79926741895957650314711639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53284494597305100209807759 79926741895957650314711639)
  ·
    refine ⟨119890112843936475472067459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79926741895957650314711639 119890112843936475472067459)
    ·
      refine ⟨179835169265904713208101189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119890112843936475472067459 179835169265904713208101189)
      ·
        refine ⟨33719094237357133726518973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 179835169265904713208101189 33719094237357133726518973)
        ·
          refine ⟨12644660339008925147444615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33719094237357133726518973 12644660339008925147444615)
          ·
            refine ⟨18966990508513387721166923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12644660339008925147444615 18966990508513387721166923)
            ·
              refine ⟨28450485762770081581750385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18966990508513387721166923 28450485762770081581750385)
              ·
                refine ⟨21337864322077561186312789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28450485762770081581750385 21337864322077561186312789)
                ·
                  refine ⟨250053097524346420152103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21337864322077561186312789 250053097524346420152103)
                  ·
                    rfl

theorem cell22_2191395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 2, 8].length) (baseStart_2191395 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2191395 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2191395 prefixEnd_2191395 := by exact prefixLift 2191395
  have htrace : WordTrace (prefixWord ++ tailWord_2191395) baseStart_2191395 baseEnd_2191395 := by
    simpa [prefixWord, tailWord_2191395, baseEnd_2191395] using wordTrace_append hprefix tailTrace_2191395
  have hstable : (prefixWord ++ tailWord_2191395).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2191395).length < 2 ^ (prefixWord ++ tailWord_2191395).sum := by decide
  have hdescent : baseEnd_2191395 < baseStart_2191395 := by decide
  rcases family_descends (prefixWord ++ tailWord_2191395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2191478 : List Nat := [5, 1, 1, 2, 1, 2, 4, 1, 2, 3]
def baseStart_2191478 : Nat := 118140960795 + 2191478 * 2 ^ 59
def prefixEnd_2191478 : Nat := 4983230072969 + 3 ^ 40 * 2191478 * 2
def baseEnd_2191478 : Nat := 750187705169254710631055

theorem tailTrace_2191478 : CollatzResearch.WordTrace tailWord_2191478 prefixEnd_2191478 750187705169254710631055 := by
  unfold tailWord_2191478
  simp only [CollatzResearch.WordTrace]
  refine ⟨4995610572166059718123943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 53286512769771303659988725 4995610572166059718123943)
  ·
    refine ⟨7493415858249089577185915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4995610572166059718123943 7493415858249089577185915)
    ·
      refine ⟨11240123787373634365778873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7493415858249089577185915 11240123787373634365778873)
      ·
        refine ⟨8430092840530225774334155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11240123787373634365778873 8430092840530225774334155)
        ·
          refine ⟨12645139260795338661501233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8430092840530225774334155 12645139260795338661501233)
          ·
            refine ⟨9483854445596503996125925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12645139260795338661501233 9483854445596503996125925)
            ·
              refine ⟨1778222708549344499273611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9483854445596503996125925 1778222708549344499273611)
              ·
                refine ⟨2667334062824016748910417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1778222708549344499273611 2667334062824016748910417)
                ·
                  refine ⟨2000500547118012561682813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2667334062824016748910417 2000500547118012561682813)
                  ·
                    refine ⟨750187705169254710631055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2000500547118012561682813 750187705169254710631055)
                    ·
                      rfl

theorem cell22_2191478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 4, 1, 2, 3].length) (baseStart_2191478 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2191478 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2191478 prefixEnd_2191478 := by exact prefixLift 2191478
  have htrace : WordTrace (prefixWord ++ tailWord_2191478) baseStart_2191478 baseEnd_2191478 := by
    simpa [prefixWord, tailWord_2191478, baseEnd_2191478] using wordTrace_append hprefix tailTrace_2191478
  have hstable : (prefixWord ++ tailWord_2191478).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2191478).length < 2 ^ (prefixWord ++ tailWord_2191478).sum := by decide
  have hdescent : baseEnd_2191478 < baseStart_2191478 := by decide
  rcases family_descends (prefixWord ++ tailWord_2191478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2191519 : List Nat := [1, 1, 2, 6, 1, 1, 1, 4, 5]
def baseStart_2191519 : Nat := 118140960795 + 2191519 * 2 ^ 59
def prefixEnd_2191519 : Nat := 4983230072969 + 3 ^ 40 * 2191519 * 2
def baseEnd_2191519 : Nat := 250067246769048090118643

theorem tailTrace_2191519 : CollatzResearch.WordTrace tailWord_2191519 prefixEnd_2191519 250067246769048090118643 := by
  unfold tailWord_2191519
  simp only [CollatzResearch.WordTrace]
  refine ⟨79931264547508419492225611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53287509698338946328150407 79931264547508419492225611)
  ·
    refine ⟨119896896821262629238338417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79931264547508419492225611 119896896821262629238338417)
    ·
      refine ⟨89922672615946971928753813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119896896821262629238338417 89922672615946971928753813)
      ·
        refine ⟨4215125278872514309160335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 89922672615946971928753813 4215125278872514309160335)
        ·
          refine ⟨6322687918308771463740503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4215125278872514309160335 6322687918308771463740503)
          ·
            refine ⟨9484031877463157195610755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6322687918308771463740503 9484031877463157195610755)
            ·
              refine ⟨14226047816194735793416133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9484031877463157195610755 14226047816194735793416133)
              ·
                refine ⟨2667383965536512961265525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14226047816194735793416133 2667383965536512961265525)
                ·
                  refine ⟨250067246769048090118643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2667383965536512961265525 250067246769048090118643)
                  ·
                    rfl

theorem cell22_2191519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 4, 5].length) (baseStart_2191519 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2191519 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2191519 prefixEnd_2191519 := by exact prefixLift 2191519
  have htrace : WordTrace (prefixWord ++ tailWord_2191519) baseStart_2191519 baseEnd_2191519 := by
    simpa [prefixWord, tailWord_2191519, baseEnd_2191519] using wordTrace_append hprefix tailTrace_2191519
  have hstable : (prefixWord ++ tailWord_2191519).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2191519).length < 2 ^ (prefixWord ++ tailWord_2191519).sum := by decide
  have hdescent : baseEnd_2191519 < baseStart_2191519 := by decide
  rcases family_descends (prefixWord ++ tailWord_2191519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2191547 : List Nat := [1, 1, 1, 1, 1, 2, 7, 2, 6]
def baseStart_2191547 : Nat := 118140960795 + 2191547 * 2 ^ 59
def prefixEnd_2191547 : Nat := 4983230072969 + 3 ^ 40 * 2191547 * 2
def baseEnd_2191547 : Nat := 250070441759787176885281

theorem tailTrace_2191547 : CollatzResearch.WordTrace tailWord_2191547 prefixEnd_2191547 250070441759787176885281 := by
  unfold tailWord_2191547
  simp only [CollatzResearch.WordTrace]
  refine ⟨79932285791406980274244895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53288190527604653516163263 79932285791406980274244895)
  ·
    refine ⟨119898428687110470411367343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79932285791406980274244895 119898428687110470411367343)
    ·
      refine ⟨179847643030665705617051015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119898428687110470411367343 179847643030665705617051015)
      ·
        refine ⟨269771464545998558425576523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 179847643030665705617051015 269771464545998558425576523)
        ·
          refine ⟨404657196818997837638364785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 269771464545998558425576523 404657196818997837638364785)
          ·
            refine ⟨303492897614248378228773589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 404657196818997837638364785 303492897614248378228773589)
            ·
              refine ⟨7113114787833946364736881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 303492897614248378228773589 7113114787833946364736881)
              ·
                refine ⟨5334836090875459773552661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7113114787833946364736881 5334836090875459773552661)
                ·
                  refine ⟨250070441759787176885281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5334836090875459773552661 250070441759787176885281)
                  ·
                    rfl

theorem cell22_2191547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 2, 6].length) (baseStart_2191547 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2191547 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2191547 prefixEnd_2191547 := by exact prefixLift 2191547
  have htrace : WordTrace (prefixWord ++ tailWord_2191547) baseStart_2191547 baseEnd_2191547 := by
    simpa [prefixWord, tailWord_2191547, baseEnd_2191547] using wordTrace_append hprefix tailTrace_2191547
  have hstable : (prefixWord ++ tailWord_2191547).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2191547).length < 2 ^ (prefixWord ++ tailWord_2191547).sum := by decide
  have hdescent : baseEnd_2191547 < baseStart_2191547 := by decide
  rcases family_descends (prefixWord ++ tailWord_2191547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2191549 : List Nat := [1, 4, 1, 2, 1, 1, 1, 6, 1, 4]
def baseStart_2191549 : Nat := 118140960795 + 2191549 * 2 ^ 59
def prefixEnd_2191549 : Nat := 4983230072969 + 3 ^ 40 * 2191549 * 2
def baseEnd_2191549 : Nat := 750212009920234192105837

theorem tailTrace_2191549 : CollatzResearch.WordTrace tailWord_2191549 prefixEnd_2191549 750212009920234192105837 := by
  unfold tailWord_2191549
  simp only [CollatzResearch.WordTrace]
  refine ⟨79932358737399734615817701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53288239158266489743878467 79932358737399734615817701)
  ·
    refine ⟨14987317263262450240465819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 79932358737399734615817701 14987317263262450240465819)
    ·
      refine ⟨22480975894893675360698729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14987317263262450240465819 22480975894893675360698729)
      ·
        refine ⟨16860731921170256520524047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22480975894893675360698729 16860731921170256520524047)
        ·
          refine ⟨25291097881755384780786071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16860731921170256520524047 25291097881755384780786071)
          ·
            refine ⟨37936646822633077171179107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25291097881755384780786071 37936646822633077171179107)
            ·
              refine ⟨56904970233949615756768661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37936646822633077171179107 56904970233949615756768661)
              ·
                refine ⟨2667420479716388238598531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 56904970233949615756768661 2667420479716388238598531)
                ·
                  refine ⟨4001130719574582357897797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2667420479716388238598531 4001130719574582357897797)
                  ·
                    refine ⟨750212009920234192105837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4001130719574582357897797 750212009920234192105837)
                    ·
                      rfl

theorem cell22_2191549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 6, 1, 4].length) (baseStart_2191549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2191549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2191549 prefixEnd_2191549 := by exact prefixLift 2191549
  have htrace : WordTrace (prefixWord ++ tailWord_2191549) baseStart_2191549 baseEnd_2191549 := by
    simpa [prefixWord, tailWord_2191549, baseEnd_2191549] using wordTrace_append hprefix tailTrace_2191549
  have hstable : (prefixWord ++ tailWord_2191549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2191549).length < 2 ^ (prefixWord ++ tailWord_2191549).sum := by decide
  have hdescent : baseEnd_2191549 < baseStart_2191549 := by decide
  rcases family_descends (prefixWord ++ tailWord_2191549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2191566 : List Nat := [4, 1, 1, 1, 4, 2, 1, 3, 1, 4]
def baseStart_2191566 : Nat := 118140960795 + 2191566 * 2 ^ 59
def prefixEnd_2191566 : Nat := 4983230072969 + 3 ^ 40 * 2191566 * 2
def baseEnd_2191566 : Nat := 750217829367651814430785

theorem tailTrace_2191566 : CollatzResearch.WordTrace tailWord_2191566 prefixEnd_2191566 750217829367651814430785 := by
  unfold tailWord_2191566
  simp only [CollatzResearch.WordTrace]
  refine ⟨9991622347292268314898319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53288652518892097679457701 9991622347292268314898319)
  ·
    refine ⟨14987433520938402472347479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9991622347292268314898319 14987433520938402472347479)
    ·
      refine ⟨22481150281407603708521219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14987433520938402472347479 22481150281407603708521219)
      ·
        refine ⟨33721725422111405562781829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22481150281407603708521219 33721725422111405562781829)
        ·
          refine ⟨6322823516645888543021593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33721725422111405562781829 6322823516645888543021593)
          ·
            refine ⟨4742117637484416407266195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6322823516645888543021593 4742117637484416407266195)
            ·
              refine ⟨7113176456226624610899293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4742117637484416407266195 7113176456226624610899293)
              ·
                refine ⟨2667441171084984229087235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7113176456226624610899293 2667441171084984229087235)
                ·
                  refine ⟨4001161756627476343630853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2667441171084984229087235 4001161756627476343630853)
                  ·
                    refine ⟨750217829367651814430785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4001161756627476343630853 750217829367651814430785)
                    ·
                      rfl

theorem cell22_2191566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 3, 1, 4].length) (baseStart_2191566 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2191566 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2191566 prefixEnd_2191566 := by exact prefixLift 2191566
  have htrace : WordTrace (prefixWord ++ tailWord_2191566) baseStart_2191566 baseEnd_2191566 := by
    simpa [prefixWord, tailWord_2191566, baseEnd_2191566] using wordTrace_append hprefix tailTrace_2191566
  have hstable : (prefixWord ++ tailWord_2191566).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2191566).length < 2 ^ (prefixWord ++ tailWord_2191566).sum := by decide
  have hdescent : baseEnd_2191566 < baseStart_2191566 := by decide
  rcases family_descends (prefixWord ++ tailWord_2191566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2191581 : List Nat := [1, 4, 3, 2, 1, 2, 2, 1, 6]
def baseStart_2191581 : Nat := 118140960795 + 2191581 * 2 ^ 59
def prefixEnd_2191581 : Nat := 4983230072969 + 3 ^ 40 * 2191581 * 2
def baseEnd_2191581 : Nat := 250074321391398925101913

theorem tailTrace_2191581 : CollatzResearch.WordTrace tailWord_2191581 prefixEnd_2191581 250074321391398925101913 := by
  unfold tailWord_2191581
  simp only [CollatzResearch.WordTrace]
  refine ⟨79933525873283804080982597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53289017248855869387321731 79933525873283804080982597)
  ·
    refine ⟨14987536101240713265184237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 79933525873283804080982597 14987536101240713265184237)
    ·
      refine ⟨5620326037965267474444089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14987536101240713265184237 5620326037965267474444089)
      ·
        refine ⟨4215244528473950605833067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5620326037965267474444089 4215244528473950605833067)
        ·
          refine ⟨6322866792710925908749601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4215244528473950605833067 6322866792710925908749601)
          ·
            refine ⟨4742150094533194431562201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6322866792710925908749601 4742150094533194431562201)
            ·
              refine ⟨3556612570899895823671651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4742150094533194431562201 3556612570899895823671651)
              ·
                refine ⟨5334918856349843735507477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3556612570899895823671651 5334918856349843735507477)
                ·
                  refine ⟨250074321391398925101913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5334918856349843735507477 250074321391398925101913)
                  ·
                    rfl

theorem cell22_2191581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 2, 1, 6].length) (baseStart_2191581 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2191581 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2191581 prefixEnd_2191581 := by exact prefixLift 2191581
  have htrace : WordTrace (prefixWord ++ tailWord_2191581) baseStart_2191581 baseEnd_2191581 := by
    simpa [prefixWord, tailWord_2191581, baseEnd_2191581] using wordTrace_append hprefix tailTrace_2191581
  have hstable : (prefixWord ++ tailWord_2191581).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2191581).length < 2 ^ (prefixWord ++ tailWord_2191581).sum := by decide
  have hdescent : baseEnd_2191581 < baseStart_2191581 := by decide
  rcases family_descends (prefixWord ++ tailWord_2191581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2191733 : List Nat := [1, 3, 4, 1, 2, 1, 1, 5, 4]
def baseStart_2191733 : Nat := 118140960795 + 2191733 * 2 ^ 59
def prefixEnd_2191733 : Nat := 4983230072969 + 3 ^ 40 * 2191733 * 2
def baseEnd_2191733 : Nat := 250091665626839681835091

theorem tailTrace_2191733 : CollatzResearch.WordTrace tailWord_2191733 prefixEnd_2191733 250091665626839681835091 := by
  unfold tailWord_2191733
  simp only [CollatzResearch.WordTrace]
  refine ⟨79939069768733134040515853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53292713179155422693677235 79939069768733134040515853)
  ·
    refine ⟨29977151163274925265193445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79939069768733134040515853 29977151163274925265193445)
    ·
      refine ⟨5620715843114048487223771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29977151163274925265193445 5620715843114048487223771)
      ·
        refine ⟨8431073764671072730835657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5620715843114048487223771 8431073764671072730835657)
        ·
          refine ⟨6323305323503304548126743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8431073764671072730835657 6323305323503304548126743)
          ·
            refine ⟨9484957985254956822190115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6323305323503304548126743 9484957985254956822190115)
            ·
              refine ⟨14227436977882435233285173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9484957985254956822190115 14227436977882435233285173)
              ·
                refine ⟨1333822216676478303120485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14227436977882435233285173 1333822216676478303120485)
                ·
                  refine ⟨250091665626839681835091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1333822216676478303120485 250091665626839681835091)
                  ·
                    rfl

theorem cell22_2191733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 5, 4].length) (baseStart_2191733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2191733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2191733 prefixEnd_2191733 := by exact prefixLift 2191733
  have htrace : WordTrace (prefixWord ++ tailWord_2191733) baseStart_2191733 baseEnd_2191733 := by
    simpa [prefixWord, tailWord_2191733, baseEnd_2191733] using wordTrace_append hprefix tailTrace_2191733
  have hstable : (prefixWord ++ tailWord_2191733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2191733).length < 2 ^ (prefixWord ++ tailWord_2191733).sum := by decide
  have hdescent : baseEnd_2191733 < baseStart_2191733 := by decide
  rcases family_descends (prefixWord ++ tailWord_2191733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2191806 : List Nat := [4, 2, 1, 1, 1, 1, 4, 1, 7]
def baseStart_2191806 : Nat := 118140960795 + 2191806 * 2 ^ 59
def prefixEnd_2191806 : Nat := 4983230072969 + 3 ^ 40 * 2191806 * 2
def baseEnd_2191806 : Nat := 250099995424123729476683

theorem tailTrace_2191806 : CollatzResearch.WordTrace tailWord_2191806 prefixEnd_2191806 250099995424123729476683 := by
  unfold tailWord_2191806
  simp only [CollatzResearch.WordTrace]
  refine ⟨9992716537183583438490409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53294488198312445005282181 9992716537183583438490409)
  ·
    refine ⟨7494537402887687578867807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9992716537183583438490409 7494537402887687578867807)
    ·
      refine ⟨11241806104331531368301711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7494537402887687578867807 11241806104331531368301711)
      ·
        refine ⟨16862709156497297052452567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11241806104331531368301711 16862709156497297052452567)
        ·
          refine ⟨25294063734745945578678851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16862709156497297052452567 25294063734745945578678851)
          ·
            refine ⟨37941095602118918368018277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25294063734745945578678851 37941095602118918368018277)
            ·
              refine ⟨7113955425397297194003427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37941095602118918368018277 7113955425397297194003427)
              ·
                refine ⟨10670933138095945791005141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7113955425397297194003427 10670933138095945791005141)
                ·
                  refine ⟨250099995424123729476683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10670933138095945791005141 250099995424123729476683)
                  ·
                    rfl

theorem cell22_2191806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 1, 7].length) (baseStart_2191806 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2191806 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2191806 prefixEnd_2191806 := by exact prefixLift 2191806
  have htrace : WordTrace (prefixWord ++ tailWord_2191806) baseStart_2191806 baseEnd_2191806 := by
    simpa [prefixWord, tailWord_2191806, baseEnd_2191806] using wordTrace_append hprefix tailTrace_2191806
  have hstable : (prefixWord ++ tailWord_2191806).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2191806).length < 2 ^ (prefixWord ++ tailWord_2191806).sum := by decide
  have hdescent : baseEnd_2191806 < baseStart_2191806 := by decide
  rcases family_descends (prefixWord ++ tailWord_2191806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2191819 : List Nat := [1, 1, 1, 1, 3, 3, 1, 1, 2, 8]
def baseStart_2191819 : Nat := 118140960795 + 2191819 * 2 ^ 59
def prefixEnd_2191819 : Nat := 4983230072969 + 3 ^ 40 * 2191819 * 2
def baseEnd_2191819 : Nat := 750304436438043487855009

theorem tailTrace_2191819 : CollatzResearch.WordTrace tailWord_2191819 prefixEnd_2191819 750304436438043487855009 := by
  unfold tailWord_2191819
  simp only [CollatzResearch.WordTrace]
  refine ⟨79942206446421570728146511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53294804297614380485431007 79942206446421570728146511)
  ·
    refine ⟨119913309669632356092219767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79942206446421570728146511 119913309669632356092219767)
    ·
      refine ⟨179869964504448534138329651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119913309669632356092219767 179869964504448534138329651)
      ·
        refine ⟨269804946756672801207494477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 179869964504448534138329651 269804946756672801207494477)
        ·
          refine ⟨101176855033752300452810429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 269804946756672801207494477 101176855033752300452810429)
          ·
            refine ⟨37941320637657112669803911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 101176855033752300452810429 37941320637657112669803911)
            ·
              refine ⟨56911980956485669004705867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37941320637657112669803911 56911980956485669004705867)
              ·
                refine ⟨85367971434728503507058801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56911980956485669004705867 85367971434728503507058801)
                ·
                  refine ⟨64025978576046377630294101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 85367971434728503507058801 64025978576046377630294101)
                  ·
                    refine ⟨750304436438043487855009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 64025978576046377630294101 750304436438043487855009)
                    ·
                      rfl

theorem cell22_2191819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 1, 2, 8].length) (baseStart_2191819 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2191819 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2191819 prefixEnd_2191819 := by exact prefixLift 2191819
  have htrace : WordTrace (prefixWord ++ tailWord_2191819) baseStart_2191819 baseEnd_2191819 := by
    simpa [prefixWord, tailWord_2191819, baseEnd_2191819] using wordTrace_append hprefix tailTrace_2191819
  have hstable : (prefixWord ++ tailWord_2191819).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2191819).length < 2 ^ (prefixWord ++ tailWord_2191819).sum := by decide
  have hdescent : baseEnd_2191819 < baseStart_2191819 := by decide
  rcases family_descends (prefixWord ++ tailWord_2191819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2191861 : List Nat := [1, 3, 5, 1, 2, 2, 2, 2, 1, 3]
def baseStart_2191861 : Nat := 118140960795 + 2191861 * 2 ^ 59
def prefixEnd_2191861 : Nat := 4983230072969 + 3 ^ 40 * 2191861 * 2
def baseEnd_2191861 : Nat := 750318813896369378304881

theorem tailTrace_2191861 : CollatzResearch.WordTrace tailWord_2191861 prefixEnd_2191861 750318813896369378304881 := by
  unfold tailWord_2191861
  simp only [CollatzResearch.WordTrace]
  refine ⟨79943738312269411901175437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53295825541512941267450291 79943738312269411901175437)
  ·
    refine ⟨29978901867101029462940789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79943738312269411901175437 29978901867101029462940789)
    ·
      refine ⟨2810522050040721512150699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 29978901867101029462940789 2810522050040721512150699)
      ·
        refine ⟨4215783075061082268226049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2810522050040721512150699 4215783075061082268226049)
        ·
          refine ⟨3161837306295811701169537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4215783075061082268226049 3161837306295811701169537)
          ·
            refine ⟨2371377979721858775877153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3161837306295811701169537 2371377979721858775877153)
            ·
              refine ⟨1778533484791394081907865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2371377979721858775877153 1778533484791394081907865)
              ·
                refine ⟨1333900113593545561430899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1778533484791394081907865 1333900113593545561430899)
                ·
                  refine ⟨2000850170390318342146349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1333900113593545561430899 2000850170390318342146349)
                  ·
                    refine ⟨750318813896369378304881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2000850170390318342146349 750318813896369378304881)
                    ·
                      rfl

theorem cell22_2191861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 2, 2, 1, 3].length) (baseStart_2191861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2191861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2191861 prefixEnd_2191861 := by exact prefixLift 2191861
  have htrace : WordTrace (prefixWord ++ tailWord_2191861) baseStart_2191861 baseEnd_2191861 := by
    simpa [prefixWord, tailWord_2191861, baseEnd_2191861] using wordTrace_append hprefix tailTrace_2191861
  have hstable : (prefixWord ++ tailWord_2191861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2191861).length < 2 ^ (prefixWord ++ tailWord_2191861).sum := by decide
  have hdescent : baseEnd_2191861 < baseStart_2191861 := by decide
  rcases family_descends (prefixWord ++ tailWord_2191861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2191883 : List Nat := [1, 1, 1, 1, 7, 2, 2, 1, 1, 5]
def baseStart_2191883 : Nat := 118140960795 + 2191883 * 2 ^ 59
def prefixEnd_2191883 : Nat := 4983230072969 + 3 ^ 40 * 2191883 * 2
def baseEnd_2191883 : Nat := 750326344945968654254813

theorem tailTrace_2191883 : CollatzResearch.WordTrace tailWord_2191883 prefixEnd_2191883 750326344945968654254813 := by
  unfold tailWord_2191883
  simp only [CollatzResearch.WordTrace]
  refine ⟨79944540718189709658476303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53296360478793139772317535 79944540718189709658476303)
  ·
    refine ⟨119916811077284564487714455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79944540718189709658476303 119916811077284564487714455)
    ·
      refine ⟨179875216615926846731571683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119916811077284564487714455 179875216615926846731571683)
      ·
        refine ⟨269812824923890270097357525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 179875216615926846731571683 269812824923890270097357525)
        ·
          refine ⟨6323738084153678205406817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 269812824923890270097357525 6323738084153678205406817)
          ·
            refine ⟨4742803563115258654055113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6323738084153678205406817 4742803563115258654055113)
            ·
              refine ⟨3557102672336443990541335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4742803563115258654055113 3557102672336443990541335)
              ·
                refine ⟨5335654008504665985812003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3557102672336443990541335 5335654008504665985812003)
                ·
                  refine ⟨8003481012756998978718005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5335654008504665985812003 8003481012756998978718005)
                  ·
                    refine ⟨750326344945968654254813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8003481012756998978718005 750326344945968654254813)
                    ·
                      rfl

theorem cell22_2191883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 2, 1, 1, 5].length) (baseStart_2191883 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2191883 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2191883 prefixEnd_2191883 := by exact prefixLift 2191883
  have htrace : WordTrace (prefixWord ++ tailWord_2191883) baseStart_2191883 baseEnd_2191883 := by
    simpa [prefixWord, tailWord_2191883, baseEnd_2191883] using wordTrace_append hprefix tailTrace_2191883
  have hstable : (prefixWord ++ tailWord_2191883).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2191883).length < 2 ^ (prefixWord ++ tailWord_2191883).sum := by decide
  have hdescent : baseEnd_2191883 < baseStart_2191883 := by decide
  rcases family_descends (prefixWord ++ tailWord_2191883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2191885 : List Nat := [1, 7, 1, 1, 1, 1, 1, 1, 8]
def baseStart_2191885 : Nat := 118140960795 + 2191885 * 2 ^ 59
def prefixEnd_2191885 : Nat := 4983230072969 + 3 ^ 40 * 2191885 * 2
def baseEnd_2191885 : Nat := 250109009862280438568269

theorem tailTrace_2191885 : CollatzResearch.WordTrace tailWord_2191885 prefixEnd_2191885 250109009862280438568269 := by
  unfold tailWord_2191885
  simp only [CollatzResearch.WordTrace]
  refine ⟨79944613664182464000049109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53296409109454976000032739 79944613664182464000049109)
  ·
    refine ⟨1873701882754276500001151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 79944613664182464000049109 1873701882754276500001151)
    ·
      refine ⟨2810552824131414750001727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1873701882754276500001151 2810552824131414750001727)
      ·
        refine ⟨4215829236197122125002591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2810552824131414750001727 4215829236197122125002591)
        ·
          refine ⟨6323743854295683187503887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4215829236197122125002591 6323743854295683187503887)
          ·
            refine ⟨9485615781443524781255831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6323743854295683187503887 9485615781443524781255831)
            ·
              refine ⟨14228423672165287171883747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9485615781443524781255831 14228423672165287171883747)
              ·
                refine ⟨21342635508247930757825621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14228423672165287171883747 21342635508247930757825621)
                ·
                  refine ⟨250109009862280438568269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21342635508247930757825621 250109009862280438568269)
                  ·
                    rfl

theorem cell22_2191885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 1, 8].length) (baseStart_2191885 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2191885 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2191885 prefixEnd_2191885 := by exact prefixLift 2191885
  have htrace : WordTrace (prefixWord ++ tailWord_2191885) baseStart_2191885 baseEnd_2191885 := by
    simpa [prefixWord, tailWord_2191885, baseEnd_2191885] using wordTrace_append hprefix tailTrace_2191885
  have hstable : (prefixWord ++ tailWord_2191885).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2191885).length < 2 ^ (prefixWord ++ tailWord_2191885).sum := by decide
  have hdescent : baseEnd_2191885 < baseStart_2191885 := by decide
  rcases family_descends (prefixWord ++ tailWord_2191885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2191898 : List Nat := [3, 1, 1, 3, 1, 1, 5, 1, 2, 4]
def baseStart_2191898 : Nat := 118140960795 + 2191898 * 2 ^ 59
def prefixEnd_2191898 : Nat := 4983230072969 + 3 ^ 40 * 2191898 * 2
def baseEnd_2191898 : Nat := 750331479752513615129767

theorem tailTrace_2191898 : CollatzResearch.WordTrace tailWord_2191898 prefixEnd_2191898 750331479752513615129767 := by
  unfold tailWord_2191898
  simp only [CollatzResearch.WordTrace]
  refine ⟨19986271953283841805068087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53296725208756911480181565 19986271953283841805068087)
  ·
    refine ⟨29979407929925762707602131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19986271953283841805068087 29979407929925762707602131)
    ·
      refine ⟨44969111894888644061403197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29979407929925762707602131 44969111894888644061403197)
      ·
        refine ⟨16863416960583241523026199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44969111894888644061403197 16863416960583241523026199)
        ·
          refine ⟨25295125440874862284539299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16863416960583241523026199 25295125440874862284539299)
          ·
            refine ⟨37942688161312293426808949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25295125440874862284539299 37942688161312293426808949)
            ·
              refine ⟨3557127015123027508763339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 37942688161312293426808949 3557127015123027508763339)
              ·
                refine ⟨5335690522684541263145009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3557127015123027508763339 5335690522684541263145009)
                ·
                  refine ⟨4001767892013405947358757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5335690522684541263145009 4001767892013405947358757)
                  ·
                    refine ⟨750331479752513615129767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4001767892013405947358757 750331479752513615129767)
                    ·
                      rfl

theorem cell22_2191898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 5, 1, 2, 4].length) (baseStart_2191898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2191898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2191898 prefixEnd_2191898 := by exact prefixLift 2191898
  have htrace : WordTrace (prefixWord ++ tailWord_2191898) baseStart_2191898 baseEnd_2191898 := by
    simpa [prefixWord, tailWord_2191898, baseEnd_2191898] using wordTrace_append hprefix tailTrace_2191898
  have hstable : (prefixWord ++ tailWord_2191898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2191898).length < 2 ^ (prefixWord ++ tailWord_2191898).sum := by decide
  have hdescent : baseEnd_2191898 < baseStart_2191898 := by decide
  rcases family_descends (prefixWord ++ tailWord_2191898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2191904 : List Nat := [2, 1, 1, 6, 3, 1, 2, 1, 1, 4]
def baseStart_2191904 : Nat := 118140960795 + 2191904 * 2 ^ 59
def prefixEnd_2191904 : Nat := 4983230072969 + 3 ^ 40 * 2191904 * 2
def baseEnd_2191904 : Nat := 750333533675131599479749

theorem tailTrace_2191904 : CollatzResearch.WordTrace tailWord_2191904 prefixEnd_2191904 750333533675131599479749 := by
  unfold tailWord_2191904
  simp only [CollatzResearch.WordTrace]
  refine ⟨39972653325556815122495383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53296871100742420163327177 39972653325556815122495383)
  ·
    refine ⟨59958979988335222683743075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39972653325556815122495383 59958979988335222683743075)
    ·
      refine ⟨89938469982502834025614613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59958979988335222683743075 89938469982502834025614613)
      ·
        refine ⟨4215865780429820344950685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 89938469982502834025614613 4215865780429820344950685)
        ·
          refine ⟨1580949667661182629356507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4215865780429820344950685 1580949667661182629356507)
          ·
            refine ⟨2371424501491773944034761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1580949667661182629356507 2371424501491773944034761)
            ·
              refine ⟨1778568376118830458026071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2371424501491773944034761 1778568376118830458026071)
              ·
                refine ⟨2667852564178245687039107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1778568376118830458026071 2667852564178245687039107)
                ·
                  refine ⟨4001778846267368530558661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2667852564178245687039107 4001778846267368530558661)
                  ·
                    refine ⟨750333533675131599479749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4001778846267368530558661 750333533675131599479749)
                    ·
                      rfl

theorem cell22_2191904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 2, 1, 1, 4].length) (baseStart_2191904 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2191904 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2191904 prefixEnd_2191904 := by exact prefixLift 2191904
  have htrace : WordTrace (prefixWord ++ tailWord_2191904) baseStart_2191904 baseEnd_2191904 := by
    simpa [prefixWord, tailWord_2191904, baseEnd_2191904] using wordTrace_append hprefix tailTrace_2191904
  have hstable : (prefixWord ++ tailWord_2191904).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2191904).length < 2 ^ (prefixWord ++ tailWord_2191904).sum := by decide
  have hdescent : baseEnd_2191904 < baseStart_2191904 := by decide
  rcases family_descends (prefixWord ++ tailWord_2191904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2191934 : List Nat := [4, 2, 1, 4, 2, 1, 1, 1, 1, 5]
def baseStart_2191934 : Nat := 118140960795 + 2191934 * 2 ^ 59
def prefixEnd_2191934 : Nat := 4983230072969 + 3 ^ 40 * 2191934 * 2
def baseEnd_2191934 : Nat := 750343803288221521229657

theorem tailTrace_2191934 : CollatzResearch.WordTrace tailWord_2191934 prefixEnd_2191934 750343803288221521229657 := by
  unfold tailWord_2191934
  simp only [CollatzResearch.WordTrace]
  refine ⟨9993300105125618171072857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53297600560669963579055237 9993300105125618171072857)
  ·
    refine ⟨7494975078844213628304643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9993300105125618171072857 7494975078844213628304643)
    ·
      refine ⟨11242462618266320442456965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7494975078844213628304643 11242462618266320442456965)
      ·
        refine ⟨2107961740924935082960681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11242462618266320442456965 2107961740924935082960681)
        ·
          refine ⟨1580971305693701312220511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2107961740924935082960681 1580971305693701312220511)
          ·
            refine ⟨2371456958540551968330767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1580971305693701312220511 2371456958540551968330767)
            ·
              refine ⟨3557185437810827952496151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2371456958540551968330767 3557185437810827952496151)
              ·
                refine ⟨5335778156716241928744227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3557185437810827952496151 5335778156716241928744227)
                ·
                  refine ⟨8003667235074362893116341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5335778156716241928744227 8003667235074362893116341)
                  ·
                    refine ⟨750343803288221521229657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8003667235074362893116341 750343803288221521229657)
                    ·
                      rfl

theorem cell22_2191934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 1, 1, 1, 5].length) (baseStart_2191934 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2191934 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2191934 prefixEnd_2191934 := by exact prefixLift 2191934
  have htrace : WordTrace (prefixWord ++ tailWord_2191934) baseStart_2191934 baseEnd_2191934 := by
    simpa [prefixWord, tailWord_2191934, baseEnd_2191934] using wordTrace_append hprefix tailTrace_2191934
  have hstable : (prefixWord ++ tailWord_2191934).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2191934).length < 2 ^ (prefixWord ++ tailWord_2191934).sum := by decide
  have hdescent : baseEnd_2191934 < baseStart_2191934 := by decide
  rcases family_descends (prefixWord ++ tailWord_2191934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2192005 : List Nat := [1, 3, 1, 1, 4, 2, 3, 2, 1, 4]
def baseStart_2192005 : Nat := 118140960795 + 2192005 * 2 ^ 59
def prefixEnd_2192005 : Nat := 4983230072969 + 3 ^ 40 * 2192005 * 2
def baseEnd_2192005 : Nat := 750368108039201002704439

theorem tailTrace_2192005 : CollatzResearch.WordTrace tailWord_2192005 prefixEnd_2192005 750368108039201002704439 := by
  unfold tailWord_2192005
  simp only [CollatzResearch.WordTrace]
  refine ⟨79948990423747724494417469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53299326949165149662944979 79948990423747724494417469)
  ·
    refine ⟨29980871408905396685406551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79948990423747724494417469 29980871408905396685406551)
    ·
      refine ⟨44971307113358095028109827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29980871408905396685406551 44971307113358095028109827)
      ·
        refine ⟨67456960670037142542164741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44971307113358095028109827 67456960670037142542164741)
        ·
          refine ⟨12648180125631964226655889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 67456960670037142542164741 12648180125631964226655889)
          ·
            refine ⟨9486135094223973169991917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12648180125631964226655889 9486135094223973169991917)
            ·
              refine ⟨3557300660333989938746969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9486135094223973169991917 3557300660333989938746969)
              ·
                refine ⟨2667975495250492454060227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3557300660333989938746969 2667975495250492454060227)
                ·
                  refine ⟨4001963242875738681090341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2667975495250492454060227 4001963242875738681090341)
                  ·
                    refine ⟨750368108039201002704439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4001963242875738681090341 750368108039201002704439)
                    ·
                      rfl

theorem cell22_2192005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 3, 2, 1, 4].length) (baseStart_2192005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2192005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2192005 prefixEnd_2192005 := by exact prefixLift 2192005
  have htrace : WordTrace (prefixWord ++ tailWord_2192005) baseStart_2192005 baseEnd_2192005 := by
    simpa [prefixWord, tailWord_2192005, baseEnd_2192005] using wordTrace_append hprefix tailTrace_2192005
  have hstable : (prefixWord ++ tailWord_2192005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2192005).length < 2 ^ (prefixWord ++ tailWord_2192005).sum := by decide
  have hdescent : baseEnd_2192005 < baseStart_2192005 := by decide
  rcases family_descends (prefixWord ++ tailWord_2192005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2192031 : List Nat := [1, 1, 2, 18]
def baseStart_2192031 : Nat := 118140960795 + 2192031 * 2 ^ 59
def prefixEnd_2192031 : Nat := 4983230072969 + 3 ^ 40 * 2192031 * 2
def baseEnd_2192031 : Nat := 1029323742620775859471

theorem tailTrace_2192031 : CollatzResearch.WordTrace tailWord_2192031 prefixEnd_2192031 1029323742620775859471 := by
  unfold tailWord_2192031
  simp only [CollatzResearch.WordTrace]
  refine ⟨79949938721653530934863947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53299959147769020623242631 79949938721653530934863947)
  ·
    refine ⟨119924908082480296402295921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79949938721653530934863947 119924908082480296402295921)
    ·
      refine ⟨89943681061860222301721941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119924908082480296402295921 89943681061860222301721941)
      ·
        refine ⟨1029323742620775859471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 18 89943681061860222301721941 1029323742620775859471)
        ·
          rfl

theorem cell22_2192031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 18].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 18].length) (baseStart_2192031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2192031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2192031 prefixEnd_2192031 := by exact prefixLift 2192031
  have htrace : WordTrace (prefixWord ++ tailWord_2192031) baseStart_2192031 baseEnd_2192031 := by
    simpa [prefixWord, tailWord_2192031, baseEnd_2192031] using wordTrace_append hprefix tailTrace_2192031
  have hstable : (prefixWord ++ tailWord_2192031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2192031).length < 2 ^ (prefixWord ++ tailWord_2192031).sum := by decide
  have hdescent : baseEnd_2192031 < baseStart_2192031 := by decide
  rcases family_descends (prefixWord ++ tailWord_2192031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2192097 : List Nat := [1, 2, 3, 1, 4, 2, 2, 1, 3, 3]
def baseStart_2192097 : Nat := 118140960795 + 2192097 * 2 ^ 59
def prefixEnd_2192097 : Nat := 4983230072969 + 3 ^ 40 * 2192097 * 2
def baseEnd_2192097 : Nat := 750399601519343429404157

theorem tailTrace_2192097 : CollatzResearch.WordTrace tailWord_2192097 prefixEnd_2192097 750399601519343429404157 := by
  unfold tailWord_2192097
  simp only [CollatzResearch.WordTrace]
  refine ⟨79952345939414424206766545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53301563959609616137844363 79952345939414424206766545)
  ·
    refine ⟨59964259454560818155074909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79952345939414424206766545 59964259454560818155074909)
    ·
      refine ⟨22486597295460306808153091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59964259454560818155074909 22486597295460306808153091)
      ·
        refine ⟨33729895943190460212229637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22486597295460306808153091 33729895943190460212229637)
        ·
          refine ⟨6324355489348211289793057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33729895943190460212229637 6324355489348211289793057)
          ·
            refine ⟨4743266617011158467344793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6324355489348211289793057 4743266617011158467344793)
            ·
              refine ⟨3557449962758368850508595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4743266617011158467344793 3557449962758368850508595)
              ·
                refine ⟨5336174944137553275762893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3557449962758368850508595 5336174944137553275762893)
                ·
                  refine ⟨2001065604051582478411085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5336174944137553275762893 2001065604051582478411085)
                  ·
                    refine ⟨750399601519343429404157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2001065604051582478411085 750399601519343429404157)
                    ·
                      rfl

theorem cell22_2192097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 2, 1, 3, 3].length) (baseStart_2192097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2192097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2192097 prefixEnd_2192097 := by exact prefixLift 2192097
  have htrace : WordTrace (prefixWord ++ tailWord_2192097) baseStart_2192097 baseEnd_2192097 := by
    simpa [prefixWord, tailWord_2192097, baseEnd_2192097] using wordTrace_append hprefix tailTrace_2192097
  have hstable : (prefixWord ++ tailWord_2192097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2192097).length < 2 ^ (prefixWord ++ tailWord_2192097).sum := by decide
  have hdescent : baseEnd_2192097 < baseStart_2192097 := by decide
  rcases family_descends (prefixWord ++ tailWord_2192097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2192116 : List Nat := [2, 6, 1, 1, 2, 2, 2, 6]
def baseStart_2192116 : Nat := 118140960795 + 2192116 * 2 ^ 59
def prefixEnd_2192116 : Nat := 4983230072969 + 3 ^ 40 * 2192116 * 2
def baseEnd_2192116 : Nat := 83378456178625968131011

theorem tailTrace_2192116 : CollatzResearch.WordTrace tailWord_2192116 prefixEnd_2192116 83378456178625968131011 := by
  unfold tailWord_2192116
  simp only [CollatzResearch.WordTrace]
  refine ⟨39976519463172795225854101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53302025950897060301138801 39976519463172795225854101)
  ·
    refine ⟨1873899349836224776211911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 39976519463172795225854101 1873899349836224776211911)
    ·
      refine ⟨2810849024754337164317867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1873899349836224776211911 2810849024754337164317867)
      ·
        refine ⟨4216273537131505746476801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2810849024754337164317867 4216273537131505746476801)
        ·
          refine ⟨3162205152848629309857601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4216273537131505746476801 3162205152848629309857601)
          ·
            refine ⟨2371653864636471982393201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3162205152848629309857601 2371653864636471982393201)
            ·
              refine ⟨1778740398477353986794901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2371653864636471982393201 1778740398477353986794901)
              ·
                refine ⟨83378456178625968131011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1778740398477353986794901 83378456178625968131011)
                ·
                  rfl

theorem cell22_2192116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 2, 6].length) (baseStart_2192116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2192116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2192116 prefixEnd_2192116 := by exact prefixLift 2192116
  have htrace : WordTrace (prefixWord ++ tailWord_2192116) baseStart_2192116 baseEnd_2192116 := by
    simpa [prefixWord, tailWord_2192116, baseEnd_2192116] using wordTrace_append hprefix tailTrace_2192116
  have hstable : (prefixWord ++ tailWord_2192116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2192116).length < 2 ^ (prefixWord ++ tailWord_2192116).sum := by decide
  have hdescent : baseEnd_2192116 < baseStart_2192116 := by decide
  rcases family_descends (prefixWord ++ tailWord_2192116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2192123 : List Nat := [1, 1, 1, 1, 1, 3, 1, 2, 7, 4]
def baseStart_2192123 : Nat := 118140960795 + 2192123 * 2 ^ 59
def prefixEnd_2192123 : Nat := 4983230072969 + 3 ^ 40 * 2192123 * 2
def baseEnd_2192123 : Nat := 750408501850688028254077

theorem tailTrace_2192123 : CollatzResearch.WordTrace tailWord_2192123 prefixEnd_2192123 750408501850688028254077 := by
  unfold tailWord_2192123
  simp only [CollatzResearch.WordTrace]
  refine ⟨79953294237320230647213023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53302196158213487098142015 79953294237320230647213023)
  ·
    refine ⟨119929941355980345970819535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79953294237320230647213023 119929941355980345970819535)
    ·
      refine ⟨179894912033970518956229303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119929941355980345970819535 179894912033970518956229303)
      ·
        refine ⟨269842368050955778434343955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 179894912033970518956229303 269842368050955778434343955)
        ·
          refine ⟨404763552076433667651515933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 269842368050955778434343955 404763552076433667651515933)
          ·
            refine ⟨151786332028662625369318475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 404763552076433667651515933 151786332028662625369318475)
            ·
              refine ⟨227679498042993938053977713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 151786332028662625369318475 227679498042993938053977713)
              ·
                refine ⟨170759623532245453540483285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 227679498042993938053977713 170759623532245453540483285)
                ·
                  refine ⟨4002178676537002817355077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 170759623532245453540483285 4002178676537002817355077)
                  ·
                    refine ⟨750408501850688028254077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4002178676537002817355077 750408501850688028254077)
                    ·
                      rfl

theorem cell22_2192123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 7, 4].length) (baseStart_2192123 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2192123 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2192123 prefixEnd_2192123 := by exact prefixLift 2192123
  have htrace : WordTrace (prefixWord ++ tailWord_2192123) baseStart_2192123 baseEnd_2192123 := by
    simpa [prefixWord, tailWord_2192123, baseEnd_2192123] using wordTrace_append hprefix tailTrace_2192123
  have hstable : (prefixWord ++ tailWord_2192123).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2192123).length < 2 ^ (prefixWord ++ tailWord_2192123).sum := by decide
  have hdescent : baseEnd_2192123 < baseStart_2192123 := by decide
  rcases family_descends (prefixWord ++ tailWord_2192123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2192153 : List Nat := [1, 2, 1, 2, 1, 1, 1, 3, 5, 5]
def baseStart_2192153 : Nat := 118140960795 + 2192153 * 2 ^ 59
def prefixEnd_2192153 : Nat := 4983230072969 + 3 ^ 40 * 2192153 * 2
def baseEnd_2192153 : Nat := 750418771463777950003985

theorem tailTrace_2192153 : CollatzResearch.WordTrace tailWord_2192153 prefixEnd_2192153 750418771463777950003985 := by
  unfold tailWord_2192153
  simp only [CollatzResearch.WordTrace]
  refine ⟨79954388427211545770805113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53302925618141030513870075 79954388427211545770805113)
  ·
    refine ⟨59965791320408659328103835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79954388427211545770805113 59965791320408659328103835)
    ·
      refine ⟨89948686980612988992155753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59965791320408659328103835 89948686980612988992155753)
      ·
        refine ⟨67461515235459741744116815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89948686980612988992155753 67461515235459741744116815)
        ·
          refine ⟨101192272853189612616175223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67461515235459741744116815 101192272853189612616175223)
          ·
            refine ⟨151788409279784418924262835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101192272853189612616175223 151788409279784418924262835)
            ·
              refine ⟨227682613919676628386394253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 151788409279784418924262835 227682613919676628386394253)
              ·
                refine ⟨85380980219878735644897845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 227682613919676628386394253 85380980219878735644897845)
                ·
                  refine ⟨8004466895613631466709173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 85380980219878735644897845 8004466895613631466709173)
                  ·
                    refine ⟨750418771463777950003985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8004466895613631466709173 750418771463777950003985)
                    ·
                      rfl

theorem cell22_2192153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 3, 5, 5].length) (baseStart_2192153 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2192153 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2192153 prefixEnd_2192153 := by exact prefixLift 2192153
  have htrace : WordTrace (prefixWord ++ tailWord_2192153) baseStart_2192153 baseEnd_2192153 := by
    simpa [prefixWord, tailWord_2192153, baseEnd_2192153] using wordTrace_append hprefix tailTrace_2192153
  have hstable : (prefixWord ++ tailWord_2192153).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2192153).length < 2 ^ (prefixWord ++ tailWord_2192153).sum := by decide
  have hdescent : baseEnd_2192153 < baseStart_2192153 := by decide
  rcases family_descends (prefixWord ++ tailWord_2192153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2192174 : List Nat := [4, 1, 3, 2, 1, 1, 3, 2, 1, 4]
def baseStart_2192174 : Nat := 118140960795 + 2192174 * 2 ^ 59
def prefixEnd_2192174 : Nat := 4983230072969 + 3 ^ 40 * 2192174 * 2
def baseEnd_2192174 : Nat := 750425960192940895228921

theorem tailTrace_2192174 : CollatzResearch.WordTrace tailWord_2192174 prefixEnd_2192174 750425960192940895228921 := by
  unfold tailWord_2192174
  simp only [CollatzResearch.WordTrace]
  refine ⟨9994394295016933294664947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53303436240090310904879717 9994394295016933294664947)
  ·
    refine ⟨14991591442525399941997421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9994394295016933294664947 14991591442525399941997421)
    ·
      refine ⟨5621846790947024978249033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14991591442525399941997421 5621846790947024978249033)
      ·
        refine ⟨4216385093210268733686775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5621846790947024978249033 4216385093210268733686775)
        ·
          refine ⟨6324577639815403100530163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4216385093210268733686775 6324577639815403100530163)
          ·
            refine ⟨9486866459723104650795245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6324577639815403100530163 9486866459723104650795245)
            ·
              refine ⟨3557574922396164244048217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9486866459723104650795245 3557574922396164244048217)
              ·
                refine ⟨2668181191797123183036163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3557574922396164244048217 2668181191797123183036163)
                ·
                  refine ⟨4002271787695684774554245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2668181191797123183036163 4002271787695684774554245)
                  ·
                    refine ⟨750425960192940895228921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4002271787695684774554245 750425960192940895228921)
                    ·
                      rfl

theorem cell22_2192174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 3, 2, 1, 4].length) (baseStart_2192174 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2192174 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2192174 prefixEnd_2192174 := by exact prefixLift 2192174
  have htrace : WordTrace (prefixWord ++ tailWord_2192174) baseStart_2192174 baseEnd_2192174 := by
    simpa [prefixWord, tailWord_2192174, baseEnd_2192174] using wordTrace_append hprefix tailTrace_2192174
  have hstable : (prefixWord ++ tailWord_2192174).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2192174).length < 2 ^ (prefixWord ++ tailWord_2192174).sum := by decide
  have hdescent : baseEnd_2192174 < baseStart_2192174 := by decide
  rcases family_descends (prefixWord ++ tailWord_2192174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2192183 : List Nat := [1, 1, 3, 1, 2, 1, 3, 10]
def baseStart_2192183 : Nat := 118140960795 + 2192183 * 2 ^ 59
def prefixEnd_2192183 : Nat := 4983230072969 + 3 ^ 40 * 2192183 * 2
def baseEnd_2192183 : Nat := 83381004564096430194877

theorem tailTrace_2192183 : CollatzResearch.WordTrace tailWord_2192183 prefixEnd_2192183 83381004564096430194877 := by
  unfold tailWord_2192183
  simp only [CollatzResearch.WordTrace]
  refine ⟨79955482617102860894397203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53303655078068573929598135 79955482617102860894397203)
  ·
    refine ⟨119933223925654291341595805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79955482617102860894397203 119933223925654291341595805)
    ·
      refine ⟨44974958972120359253098427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 119933223925654291341595805 44974958972120359253098427)
      ·
        refine ⟨67462438458180538879647641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44974958972120359253098427 67462438458180538879647641)
        ·
          refine ⟨50596828843635404159735731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67462438458180538879647641 50596828843635404159735731)
          ·
            refine ⟨75895243265453106239603597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50596828843635404159735731 75895243265453106239603597)
            ·
              refine ⟨28460716224544914839851349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 75895243265453106239603597 28460716224544914839851349)
              ·
                refine ⟨83381004564096430194877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 28460716224544914839851349 83381004564096430194877)
                ·
                  rfl

theorem cell22_2192183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 10].length) (baseStart_2192183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2192183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2192183 prefixEnd_2192183 := by exact prefixLift 2192183
  have htrace : WordTrace (prefixWord ++ tailWord_2192183) baseStart_2192183 baseEnd_2192183 := by
    simpa [prefixWord, tailWord_2192183, baseEnd_2192183] using wordTrace_append hprefix tailTrace_2192183
  have hstable : (prefixWord ++ tailWord_2192183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2192183).length < 2 ^ (prefixWord ++ tailWord_2192183).sum := by decide
  have hdescent : baseEnd_2192183 < baseStart_2192183 := by decide
  rcases family_descends (prefixWord ++ tailWord_2192183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2192204 : List Nat := [2, 2, 1, 3, 3, 2, 2, 2, 2, 3]
def baseStart_2192204 : Nat := 118140960795 + 2192204 * 2 ^ 59
def prefixEnd_2192204 : Nat := 4983230072969 + 3 ^ 40 * 2192204 * 2
def baseEnd_2192204 : Nat := 750436229806030816978829

theorem tailTrace_2192204 : CollatzResearch.WordTrace tailWord_2192204 prefixEnd_2192204 750436229806030816978829 := by
  unfold tailWord_2192204
  simp only [CollatzResearch.WordTrace]
  refine ⟨39978124275013390740455833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53304165700017854320607777 39978124275013390740455833)
  ·
    refine ⟨29983593206260043055341875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39978124275013390740455833 29983593206260043055341875)
    ·
      refine ⟨44975389809390064583012813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29983593206260043055341875 44975389809390064583012813)
      ·
        refine ⟨16865771178521274218629805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44975389809390064583012813 16865771178521274218629805)
        ·
          refine ⟨6324664191945477831986177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16865771178521274218629805 6324664191945477831986177)
          ·
            refine ⟨4743498143959108373989633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6324664191945477831986177 4743498143959108373989633)
            ·
              refine ⟨3557623607969331280492225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4743498143959108373989633 3557623607969331280492225)
              ·
                refine ⟨2668217705976998460369169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3557623607969331280492225 2668217705976998460369169)
                ·
                  refine ⟨2001163279482748845276877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2668217705976998460369169 2001163279482748845276877)
                  ·
                    refine ⟨750436229806030816978829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2001163279482748845276877 750436229806030816978829)
                    ·
                      rfl

theorem cell22_2192204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 2, 2, 2, 3].length) (baseStart_2192204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2192204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2192204 prefixEnd_2192204 := by exact prefixLift 2192204
  have htrace : WordTrace (prefixWord ++ tailWord_2192204) baseStart_2192204 baseEnd_2192204 := by
    simpa [prefixWord, tailWord_2192204, baseEnd_2192204] using wordTrace_append hprefix tailTrace_2192204
  have hstable : (prefixWord ++ tailWord_2192204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2192204).length < 2 ^ (prefixWord ++ tailWord_2192204).sum := by decide
  have hdescent : baseEnd_2192204 < baseStart_2192204 := by decide
  rcases family_descends (prefixWord ++ tailWord_2192204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2192232 : List Nat := [2, 1, 4, 2, 1, 2, 1, 1, 5, 3]
def baseStart_2192232 : Nat := 118140960795 + 2192232 * 2 ^ 59
def prefixEnd_2192232 : Nat := 4983230072969 + 3 ^ 40 * 2192232 * 2
def baseEnd_2192232 : Nat := 750445814778248077278743

theorem tailTrace_2192232 : CollatzResearch.WordTrace tailWord_2192232 prefixEnd_2192232 750445814778248077278743 := by
  unfold tailWord_2192232
  simp only [CollatzResearch.WordTrace]
  refine ⟨39978634896962671131465475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53304846529283561508620633 39978634896962671131465475)
  ·
    refine ⟨59967952345444006697198213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39978634896962671131465475 59967952345444006697198213)
    ·
      refine ⟨11243991064770751255724665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 59967952345444006697198213 11243991064770751255724665)
      ·
        refine ⟨8432993298578063441793499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11243991064770751255724665 8432993298578063441793499)
        ·
          refine ⟨12649489947867095162690249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8432993298578063441793499 12649489947867095162690249)
          ·
            refine ⟨9487117460900321372017687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12649489947867095162690249 9487117460900321372017687)
            ·
              refine ⟨14230676191350482058026531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9487117460900321372017687 14230676191350482058026531)
              ·
                refine ⟨21346014287025723087039797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14230676191350482058026531 21346014287025723087039797)
                ·
                  refine ⟨2001188839408661539409981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21346014287025723087039797 2001188839408661539409981)
                  ·
                    refine ⟨750445814778248077278743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2001188839408661539409981 750445814778248077278743)
                    ·
                      rfl

theorem cell22_2192232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 1, 5, 3].length) (baseStart_2192232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2192232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2192232 prefixEnd_2192232 := by exact prefixLift 2192232
  have htrace : WordTrace (prefixWord ++ tailWord_2192232) baseStart_2192232 baseEnd_2192232 := by
    simpa [prefixWord, tailWord_2192232, baseEnd_2192232] using wordTrace_append hprefix tailTrace_2192232
  have hstable : (prefixWord ++ tailWord_2192232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2192232).length < 2 ^ (prefixWord ++ tailWord_2192232).sum := by decide
  have hdescent : baseEnd_2192232 < baseStart_2192232 := by decide
  rcases family_descends (prefixWord ++ tailWord_2192232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2192249 : List Nat := [1, 2, 1, 3, 2, 3, 1, 5, 1, 3]
def baseStart_2192249 : Nat := 118140960795 + 2192249 * 2 ^ 59
def prefixEnd_2192249 : Nat := 4983230072969 + 3 ^ 40 * 2192249 * 2
def baseEnd_2192249 : Nat := 750451634225665699603691

theorem tailTrace_2192249 : CollatzResearch.WordTrace tailWord_2192249 prefixEnd_2192249 750451634225665699603691 := by
  unfold tailWord_2192249
  simp only [CollatzResearch.WordTrace]
  refine ⟨79957889834863754166299801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53305259889909169444199867 79957889834863754166299801)
  ·
    refine ⟨59968417376147815624724851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79957889834863754166299801 59968417376147815624724851)
    ·
      refine ⟨89952626064221723437087277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59968417376147815624724851 89952626064221723437087277)
      ·
        refine ⟨33732234774083146288907729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89952626064221723437087277 33732234774083146288907729)
        ·
          refine ⟨25299176080562359716680797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33732234774083146288907729 25299176080562359716680797)
          ·
            refine ⟨9487191030210884893755299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25299176080562359716680797 9487191030210884893755299)
            ·
              refine ⟨14230786545316327340632949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9487191030210884893755299 14230786545316327340632949)
              ·
                refine ⟨1334136238623405688184339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14230786545316327340632949 1334136238623405688184339)
                ·
                  refine ⟨2001204357935108532276509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1334136238623405688184339 2001204357935108532276509)
                  ·
                    refine ⟨750451634225665699603691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2001204357935108532276509 750451634225665699603691)
                    ·
                      rfl

theorem cell22_2192249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 5, 1, 3].length) (baseStart_2192249 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2192249 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2192249 prefixEnd_2192249 := by exact prefixLift 2192249
  have htrace : WordTrace (prefixWord ++ tailWord_2192249) baseStart_2192249 baseEnd_2192249 := by
    simpa [prefixWord, tailWord_2192249, baseEnd_2192249] using wordTrace_append hprefix tailTrace_2192249
  have hstable : (prefixWord ++ tailWord_2192249).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2192249).length < 2 ^ (prefixWord ++ tailWord_2192249).sum := by decide
  have hdescent : baseEnd_2192249 < baseStart_2192249 := by decide
  rcases family_descends (prefixWord ++ tailWord_2192249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2192266 : List Nat := [3, 1, 2, 4, 1, 1, 2, 4, 1, 3]
def baseStart_2192266 : Nat := 118140960795 + 2192266 * 2 ^ 59
def prefixEnd_2192266 : Nat := 4983230072969 + 3 ^ 40 * 2192266 * 2
def baseEnd_2192266 : Nat := 750457453673083321928639

theorem tailTrace_2192266 : CollatzResearch.WordTrace tailWord_2192266 prefixEnd_2192266 750457453673083321928639 := by
  unfold tailWord_2192266
  simp only [CollatzResearch.WordTrace]
  refine ⟨19989627468950541517417163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53305673250534777379779101 19989627468950541517417163)
  ·
    refine ⟨29984441203425812276125745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19989627468950541517417163 29984441203425812276125745)
    ·
      refine ⟨22488330902569359207094309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29984441203425812276125745 22488330902569359207094309)
      ·
        refine ⟨4216562044231754851330183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22488330902569359207094309 4216562044231754851330183)
        ·
          refine ⟨6324843066347632276995275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4216562044231754851330183 6324843066347632276995275)
          ·
            refine ⟨9487264599521448415492913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6324843066347632276995275 9487264599521448415492913)
            ·
              refine ⟨7115448449641086311619685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9487264599521448415492913 7115448449641086311619685)
              ·
                refine ⟨1334146584307703683428691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7115448449641086311619685 1334146584307703683428691)
                ·
                  refine ⟨2001219876461555525143037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1334146584307703683428691 2001219876461555525143037)
                  ·
                    refine ⟨750457453673083321928639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2001219876461555525143037 750457453673083321928639)
                    ·
                      rfl

theorem cell22_2192266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 4, 1, 3].length) (baseStart_2192266 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2192266 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2192266 prefixEnd_2192266 := by exact prefixLift 2192266
  have htrace : WordTrace (prefixWord ++ tailWord_2192266) baseStart_2192266 baseEnd_2192266 := by
    simpa [prefixWord, tailWord_2192266, baseEnd_2192266] using wordTrace_append hprefix tailTrace_2192266
  have hstable : (prefixWord ++ tailWord_2192266).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2192266).length < 2 ^ (prefixWord ++ tailWord_2192266).sum := by decide
  have hdescent : baseEnd_2192266 < baseStart_2192266 := by decide
  rcases family_descends (prefixWord ++ tailWord_2192266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2192275 : List Nat := [1, 1, 1, 2, 1, 2, 1, 6, 3, 4]
def baseStart_2192275 : Nat := 118140960795 + 2192275 * 2 ^ 59
def prefixEnd_2192275 : Nat := 4983230072969 + 3 ^ 40 * 2192275 * 2
def baseEnd_2192275 : Nat := 750460534557010298453611

theorem tailTrace_2192275 : CollatzResearch.WordTrace tailWord_2192275 prefixEnd_2192275 750460534557010298453611 := by
  unfold tailWord_2192275
  simp only [CollatzResearch.WordTrace]
  refine ⟨79958838132769560606746279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53305892088513040404497519 79958838132769560606746279)
  ·
    refine ⟨119938257199154340910119419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79958838132769560606746279 119938257199154340910119419)
    ·
      refine ⟨179907385798731511365179129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119938257199154340910119419 179907385798731511365179129)
      ·
        refine ⟨134930539349048633523884347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 179907385798731511365179129 134930539349048633523884347)
        ·
          refine ⟨202395809023572950285826521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134930539349048633523884347 202395809023572950285826521)
          ·
            refine ⟨151796856767679712714369891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 202395809023572950285826521 151796856767679712714369891)
            ·
              refine ⟨227695285151519569071554837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 151796856767679712714369891 227695285151519569071554837)
              ·
                refine ⟨10673216491477479800229133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 227695285151519569071554837 10673216491477479800229133)
                ·
                  refine ⟨4002456184304054925085925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10673216491477479800229133 4002456184304054925085925)
                  ·
                    refine ⟨750460534557010298453611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4002456184304054925085925 750460534557010298453611)
                    ·
                      rfl

theorem cell22_2192275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 6, 3, 4].length) (baseStart_2192275 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2192275 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2192275 prefixEnd_2192275 := by exact prefixLift 2192275
  have htrace : WordTrace (prefixWord ++ tailWord_2192275) baseStart_2192275 baseEnd_2192275 := by
    simpa [prefixWord, tailWord_2192275, baseEnd_2192275] using wordTrace_append hprefix tailTrace_2192275
  have hstable : (prefixWord ++ tailWord_2192275).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2192275).length < 2 ^ (prefixWord ++ tailWord_2192275).sum := by decide
  have hdescent : baseEnd_2192275 < baseStart_2192275 := by decide
  rcases family_descends (prefixWord ++ tailWord_2192275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2192307 : List Nat := [1, 1, 1, 2, 3, 1, 2, 7, 4]
def baseStart_2192307 : Nat := 118140960795 + 2192307 * 2 ^ 59
def prefixEnd_2192307 : Nat := 4983230072969 + 3 ^ 40 * 2192307 * 2
def baseEnd_2192307 : Nat := 250157162936990960551171

theorem tailTrace_2192307 : CollatzResearch.WordTrace tailWord_2192307 prefixEnd_2192307 250157162936990960551171 := by
  unfold tailWord_2192307
  simp only [CollatzResearch.WordTrace]
  refine ⟨79960005268653630071911175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53306670179102420047940783 79960005268653630071911175)
  ·
    refine ⟨119940007902980445107866763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79960005268653630071911175 119940007902980445107866763)
    ·
      refine ⟨179910011854470667661800145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119940007902980445107866763 179910011854470667661800145)
      ·
        refine ⟨134932508890853000746350109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 179910011854470667661800145 134932508890853000746350109)
        ·
          refine ⟨50599690834069875279881291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 134932508890853000746350109 50599690834069875279881291)
          ·
            refine ⟨75899536251104812919821937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50599690834069875279881291 75899536251104812919821937)
            ·
              refine ⟨56924652188328609689866453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75899536251104812919821937 56924652188328609689866453)
              ·
                refine ⟨1334171535663951789606245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 56924652188328609689866453 1334171535663951789606245)
                ·
                  refine ⟨250157162936990960551171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1334171535663951789606245 250157162936990960551171)
                  ·
                    rfl

theorem cell22_2192307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 7, 4].length) (baseStart_2192307 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2192307 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2192307 prefixEnd_2192307 := by exact prefixLift 2192307
  have htrace : WordTrace (prefixWord ++ tailWord_2192307) baseStart_2192307 baseEnd_2192307 := by
    simpa [prefixWord, tailWord_2192307, baseEnd_2192307] using wordTrace_append hprefix tailTrace_2192307
  have hstable : (prefixWord ++ tailWord_2192307).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2192307).length < 2 ^ (prefixWord ++ tailWord_2192307).sum := by decide
  have hdescent : baseEnd_2192307 < baseStart_2192307 := by decide
  rcases family_descends (prefixWord ++ tailWord_2192307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2192335 : List Nat := [1, 1, 2, 1, 1, 6, 1, 9]
def baseStart_2192335 : Nat := 118140960795 + 2192335 * 2 ^ 59
def prefixEnd_2192335 : Nat := 4983230072969 + 3 ^ 40 * 2192335 * 2
def baseEnd_2192335 : Nat := 83386785975910015772603

theorem tailTrace_2192335 : CollatzResearch.WordTrace tailWord_2192335 prefixEnd_2192335 83386785975910015772603 := by
  unfold tailWord_2192335
  simp only [CollatzResearch.WordTrace]
  refine ⟨79961026512552190853930459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53307351008368127235953639 79961026512552190853930459)
  ·
    refine ⟨119941539768828286280895689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79961026512552190853930459 119941539768828286280895689)
    ·
      refine ⟨89956154826621214710671767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119941539768828286280895689 89956154826621214710671767)
      ·
        refine ⟨134934232239931822066007651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89956154826621214710671767 134934232239931822066007651)
        ·
          refine ⟨202401348359897733099011477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134934232239931822066007651 202401348359897733099011477)
          ·
            refine ⟨9487563204370206239016163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 202401348359897733099011477 9487563204370206239016163)
            ·
              refine ⟨14231344806555309358524245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9487563204370206239016163 14231344806555309358524245)
              ·
                refine ⟨83386785975910015772603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 14231344806555309358524245 83386785975910015772603)
                ·
                  rfl

theorem cell22_2192335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 9].length) (baseStart_2192335 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2192335 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2192335 prefixEnd_2192335 := by exact prefixLift 2192335
  have htrace : WordTrace (prefixWord ++ tailWord_2192335) baseStart_2192335 baseEnd_2192335 := by
    simpa [prefixWord, tailWord_2192335, baseEnd_2192335] using wordTrace_append hprefix tailTrace_2192335
  have hstable : (prefixWord ++ tailWord_2192335).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2192335).length < 2 ^ (prefixWord ++ tailWord_2192335).sum := by decide
  have hdescent : baseEnd_2192335 < baseStart_2192335 := by decide
  rcases family_descends (prefixWord ++ tailWord_2192335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2192418 : List Nat := [3, 3, 1, 1, 1, 4, 2, 3, 1, 3]
def baseStart_2192418 : Nat := 118140960795 + 2192418 * 2 ^ 59
def prefixEnd_2192418 : Nat := 4983230072969 + 3 ^ 40 * 2192418 * 2
def baseEnd_2192418 : Nat := 750509486379405592128173

theorem tailTrace_2192418 : CollatzResearch.WordTrace tailWord_2192418 prefixEnd_2192418 750509486379405592128173 := by
  unfold tailWord_2192418
  simp only [CollatzResearch.WordTrace]
  refine ⟨19991013442812874007300477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53309369180834330686134605 19991013442812874007300477)
  ·
    refine ⟨7496630041054827752737679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19991013442812874007300477 7496630041054827752737679)
    ·
      refine ⟨11244945061582241629106519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7496630041054827752737679 11244945061582241629106519)
      ·
        refine ⟨16867417592373362443659779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11244945061582241629106519 16867417592373362443659779)
        ·
          refine ⟨25301126388560043665489669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16867417592373362443659779 25301126388560043665489669)
          ·
            refine ⟨4743961197855008187279313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25301126388560043665489669 4743961197855008187279313)
            ·
              refine ⟨3557970898391256140459485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4743961197855008187279313 3557970898391256140459485)
              ·
                refine ⟨1334239086896721052672307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3557970898391256140459485 1334239086896721052672307)
                ·
                  refine ⟨2001358630345081579008461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1334239086896721052672307 2001358630345081579008461)
                  ·
                    refine ⟨750509486379405592128173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2001358630345081579008461 750509486379405592128173)
                    ·
                      rfl

theorem cell22_2192418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 2, 3, 1, 3].length) (baseStart_2192418 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2192418 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2192418 prefixEnd_2192418 := by exact prefixLift 2192418
  have htrace : WordTrace (prefixWord ++ tailWord_2192418) baseStart_2192418 baseEnd_2192418 := by
    simpa [prefixWord, tailWord_2192418, baseEnd_2192418] using wordTrace_append hprefix tailTrace_2192418
  have hstable : (prefixWord ++ tailWord_2192418).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2192418).length < 2 ^ (prefixWord ++ tailWord_2192418).sum := by decide
  have hdescent : baseEnd_2192418 < baseStart_2192418 := by decide
  rcases family_descends (prefixWord ++ tailWord_2192418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2192442 : List Nat := [3, 1, 1, 1, 3, 1, 3, 3, 6]
def baseStart_2192442 : Nat := 118140960795 + 2192442 * 2 ^ 59
def prefixEnd_2192442 : Nat := 4983230072969 + 3 ^ 40 * 2192442 * 2
def baseEnd_2192442 : Nat := 250172567356625843176033

theorem tailTrace_2192442 : CollatzResearch.WordTrace tailWord_2192442 prefixEnd_2192442 250172567356625843176033 := by
  unfold tailWord_2192442
  simp only [CollatzResearch.WordTrace]
  refine ⟨19991232280791137032018895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53309952748776365418717053 19991232280791137032018895)
  ·
    refine ⟨29986848421186705548028343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19991232280791137032018895 29986848421186705548028343)
    ·
      refine ⟨44980272631780058322042515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29986848421186705548028343 44980272631780058322042515)
      ·
        refine ⟨67470408947670087483063773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44980272631780058322042515 67470408947670087483063773)
        ·
          refine ⟨25301403355376282806148915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67470408947670087483063773 25301403355376282806148915)
          ·
            refine ⟨37952105033064424209223373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25301403355376282806148915 37952105033064424209223373)
            ·
              refine ⟨14232039387399159078458765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37952105033064424209223373 14232039387399159078458765)
              ·
                refine ⟨5337014770274684654422037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14232039387399159078458765 5337014770274684654422037)
                ·
                  refine ⟨250172567356625843176033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5337014770274684654422037 250172567356625843176033)
                  ·
                    rfl

theorem cell22_2192442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 3, 6].length) (baseStart_2192442 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2192442 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2192442 prefixEnd_2192442 := by exact prefixLift 2192442
  have htrace : WordTrace (prefixWord ++ tailWord_2192442) baseStart_2192442 baseEnd_2192442 := by
    simpa [prefixWord, tailWord_2192442, baseEnd_2192442] using wordTrace_append hprefix tailTrace_2192442
  have hstable : (prefixWord ++ tailWord_2192442).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2192442).length < 2 ^ (prefixWord ++ tailWord_2192442).sum := by decide
  have hdescent : baseEnd_2192442 < baseStart_2192442 := by decide
  rcases family_descends (prefixWord ++ tailWord_2192442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2192457 : List Nat := [1, 2, 1, 1, 2, 2, 2, 5, 1, 5]
def baseStart_2192457 : Nat := 118140960795 + 2192457 * 2 ^ 59
def prefixEnd_2192457 : Nat := 4983230072969 + 3 ^ 40 * 2192457 * 2
def baseEnd_2192457 : Nat := 750522836876422490403053

theorem tailTrace_2192457 : CollatzResearch.WordTrace tailWord_2192457 prefixEnd_2192457 750522836876422490403053 := by
  unfold tailWord_2192457
  simp only [CollatzResearch.WordTrace]
  refine ⟨79965476218110205689871625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53310317478740137126581083 79965476218110205689871625)
  ·
    refine ⟨59974107163582654267403719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79965476218110205689871625 59974107163582654267403719)
    ·
      refine ⟨89961160745373981401105579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59974107163582654267403719 89961160745373981401105579)
      ·
        refine ⟨134941741118060972101658369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89961160745373981401105579 134941741118060972101658369)
        ·
          refine ⟨101206305838545729076243777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 134941741118060972101658369 101206305838545729076243777)
          ·
            refine ⟨75904729378909296807182833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 101206305838545729076243777 75904729378909296807182833)
            ·
              refine ⟨56928547034181972605387125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75904729378909296807182833 56928547034181972605387125)
              ·
                refine ⟨5337051284454559931755043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 56928547034181972605387125 5337051284454559931755043)
                ·
                  refine ⟨8005576926681839897632565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5337051284454559931755043 8005576926681839897632565)
                  ·
                    refine ⟨750522836876422490403053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8005576926681839897632565 750522836876422490403053)
                    ·
                      rfl

theorem cell22_2192457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 5, 1, 5].length) (baseStart_2192457 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2192457 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2192457 prefixEnd_2192457 := by exact prefixLift 2192457
  have htrace : WordTrace (prefixWord ++ tailWord_2192457) baseStart_2192457 baseEnd_2192457 := by
    simpa [prefixWord, tailWord_2192457, baseEnd_2192457] using wordTrace_append hprefix tailTrace_2192457
  have hstable : (prefixWord ++ tailWord_2192457).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2192457).length < 2 ^ (prefixWord ++ tailWord_2192457).sum := by decide
  have hdescent : baseEnd_2192457 < baseStart_2192457 := by decide
  rcases family_descends (prefixWord ++ tailWord_2192457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2192461 : List Nat := [1, 6, 1, 1, 1, 2, 1, 4, 1, 4]
def baseStart_2192461 : Nat := 118140960795 + 2192461 * 2 ^ 59
def prefixEnd_2192461 : Nat := 4983230072969 + 3 ^ 40 * 2192461 * 2
def baseEnd_2192461 : Nat := 750524206158167813303041

theorem tailTrace_2192461 : CollatzResearch.WordTrace tailWord_2192461 prefixEnd_2192461 750524206158167813303041 := by
  unfold tailWord_2192461
  simp only [CollatzResearch.WordTrace]
  refine ⟨79965622110095714373017237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53310414740063809582011491 79965622110095714373017237)
  ·
    refine ⟨3748388536410736611235183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 79965622110095714373017237 3748388536410736611235183)
    ·
      refine ⟨5622582804616104916852775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3748388536410736611235183 5622582804616104916852775)
      ·
        refine ⟨8433874206924157375279163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5622582804616104916852775 8433874206924157375279163)
        ·
          refine ⟨12650811310386236062918745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8433874206924157375279163 12650811310386236062918745)
          ·
            refine ⟨9488108482789677047189059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12650811310386236062918745 9488108482789677047189059)
            ·
              refine ⟨14232162724184515570783589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9488108482789677047189059 14232162724184515570783589)
              ·
                refine ⟨2668530510784596669521923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14232162724184515570783589 2668530510784596669521923)
                ·
                  refine ⟨4002795766176895004282885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2668530510784596669521923 4002795766176895004282885)
                  ·
                    refine ⟨750524206158167813303041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4002795766176895004282885 750524206158167813303041)
                    ·
                      rfl

theorem cell22_2192461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 4, 1, 4].length) (baseStart_2192461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2192461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2192461 prefixEnd_2192461 := by exact prefixLift 2192461
  have htrace : WordTrace (prefixWord ++ tailWord_2192461) baseStart_2192461 baseEnd_2192461 := by
    simpa [prefixWord, tailWord_2192461, baseEnd_2192461] using wordTrace_append hprefix tailTrace_2192461
  have hstable : (prefixWord ++ tailWord_2192461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2192461).length < 2 ^ (prefixWord ++ tailWord_2192461).sum := by decide
  have hdescent : baseEnd_2192461 < baseStart_2192461 := by decide
  rcases family_descends (prefixWord ++ tailWord_2192461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2192472 : List Nat := [2, 1, 2, 2, 1, 3, 1, 3, 1, 6]
def baseStart_2192472 : Nat := 118140960795 + 2192472 * 2 ^ 59
def prefixEnd_2192472 : Nat := 4983230072969 + 3 ^ 40 * 2192472 * 2
def baseEnd_2192472 : Nat := 750527971682967451278007

theorem tailTrace_2192472 : CollatzResearch.WordTrace tailWord_2192472 prefixEnd_2192472 750527971682967451278007 := by
  unfold tailWord_2192472
  simp only [CollatzResearch.WordTrace]
  refine ⟨39983011656527931625833835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53310682208703908834445113 39983011656527931625833835)
  ·
    refine ⟨59974517484791897438750753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39983011656527931625833835 59974517484791897438750753)
    ·
      refine ⟨44980888113593923079063065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59974517484791897438750753 44980888113593923079063065)
      ·
        refine ⟨33735666085195442309297299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44980888113593923079063065 33735666085195442309297299)
        ·
          refine ⟨50603499127793163463945949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33735666085195442309297299 50603499127793163463945949)
          ·
            refine ⟨18976312172922436298979731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50603499127793163463945949 18976312172922436298979731)
            ·
              refine ⟨28464468259383654448469597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18976312172922436298979731 28464468259383654448469597)
              ·
                refine ⟨10674175597268870418176099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28464468259383654448469597 10674175597268870418176099)
                ·
                  refine ⟨16011263395903305627264149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10674175597268870418176099 16011263395903305627264149)
                  ·
                    refine ⟨750527971682967451278007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16011263395903305627264149 750527971682967451278007)
                    ·
                      rfl

theorem cell22_2192472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 3, 1, 6].length) (baseStart_2192472 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2192472 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2192472 prefixEnd_2192472 := by exact prefixLift 2192472
  have htrace : WordTrace (prefixWord ++ tailWord_2192472) baseStart_2192472 baseEnd_2192472 := by
    simpa [prefixWord, tailWord_2192472, baseEnd_2192472] using wordTrace_append hprefix tailTrace_2192472
  have hstable : (prefixWord ++ tailWord_2192472).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2192472).length < 2 ^ (prefixWord ++ tailWord_2192472).sum := by decide
  have hdescent : baseEnd_2192472 < baseStart_2192472 := by decide
  rcases family_descends (prefixWord ++ tailWord_2192472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2192487 : List Nat := [1, 1, 5, 1, 1, 3, 10]
def baseStart_2192487 : Nat := 118140960795 + 2192487 * 2 ^ 59
def prefixEnd_2192487 : Nat := 4983230072969 + 3 ^ 40 * 2192487 * 2
def baseEnd_2192487 : Nat := 27797522462574533783443

theorem tailTrace_2192487 : CollatzResearch.WordTrace tailWord_2192487 prefixEnd_2192487 27797522462574533783443 := by
  unfold tailWord_2192487
  simp only [CollatzResearch.WordTrace]
  refine ⟨79966570408001520813463715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53311046938667680542309143 79966570408001520813463715)
  ·
    refine ⟨119949855612002281220195573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79966570408001520813463715 119949855612002281220195573)
    ·
      refine ⟨11245298963625213864393335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 119949855612002281220195573 11245298963625213864393335)
      ·
        refine ⟨16867948445437820796590003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11245298963625213864393335 16867948445437820796590003)
        ·
          refine ⟨25301922668156731194885005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16867948445437820796590003 25301922668156731194885005)
          ·
            refine ⟨9488221000558774198081877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25301922668156731194885005 9488221000558774198081877)
            ·
              refine ⟨27797522462574533783443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 9488221000558774198081877 27797522462574533783443)
              ·
                rfl

theorem cell22_2192487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 10].length) (baseStart_2192487 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2192487 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2192487 prefixEnd_2192487 := by exact prefixLift 2192487
  have htrace : WordTrace (prefixWord ++ tailWord_2192487) baseStart_2192487 baseEnd_2192487 := by
    simpa [prefixWord, tailWord_2192487, baseEnd_2192487] using wordTrace_append hprefix tailTrace_2192487
  have hstable : (prefixWord ++ tailWord_2192487).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2192487).length < 2 ^ (prefixWord ++ tailWord_2192487).sum := by decide
  have hdescent : baseEnd_2192487 < baseStart_2192487 := by decide
  rcases family_descends (prefixWord ++ tailWord_2192487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2192489 : List Nat := [1, 2, 1, 1, 1, 7, 1, 2, 2, 4]
def baseStart_2192489 : Nat := 118140960795 + 2192489 * 2 ^ 59
def prefixEnd_2192489 : Nat := 4983230072969 + 3 ^ 40 * 2192489 * 2
def baseEnd_2192489 : Nat := 750533791130385073602955

theorem tailTrace_2192489 : CollatzResearch.WordTrace tailWord_2192489 prefixEnd_2192489 750533791130385073602955 := by
  unfold tailWord_2192489
  simp only [CollatzResearch.WordTrace]
  refine ⟨79966643353994275155036521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53311095569329516770024347 79966643353994275155036521)
  ·
    refine ⟨59974982515495706366277391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79966643353994275155036521 59974982515495706366277391)
    ·
      refine ⟨89962473773243559549416087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59974982515495706366277391 89962473773243559549416087)
      ·
        refine ⟨134943710659865339324124131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89962473773243559549416087 134943710659865339324124131)
        ·
          refine ⟨202415565989798008986186197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134943710659865339324124131 202415565989798008986186197)
          ·
            refine ⟨4744114827885890835613739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 202415565989798008986186197 4744114827885890835613739)
            ·
              refine ⟨7116172241828836253420609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4744114827885890835613739 7116172241828836253420609)
              ·
                refine ⟨5337129181371627190065457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7116172241828836253420609 5337129181371627190065457)
                ·
                  refine ⟨4002846886028720392549093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5337129181371627190065457 4002846886028720392549093)
                  ·
                    refine ⟨750533791130385073602955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4002846886028720392549093 750533791130385073602955)
                    ·
                      rfl

theorem cell22_2192489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 2, 2, 4].length) (baseStart_2192489 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2192489 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2192489 prefixEnd_2192489 := by exact prefixLift 2192489
  have htrace : WordTrace (prefixWord ++ tailWord_2192489) baseStart_2192489 baseEnd_2192489 := by
    simpa [prefixWord, tailWord_2192489, baseEnd_2192489] using wordTrace_append hprefix tailTrace_2192489
  have hstable : (prefixWord ++ tailWord_2192489).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2192489).length < 2 ^ (prefixWord ++ tailWord_2192489).sum := by decide
  have hdescent : baseEnd_2192489 < baseStart_2192489 := by decide
  rcases family_descends (prefixWord ++ tailWord_2192489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2192493 : List Nat := [1, 5, 1, 1, 2, 3, 3, 2, 4]
def baseStart_2192493 : Nat := 118140960795 + 2192493 * 2 ^ 59
def prefixEnd_2192493 : Nat := 4983230072969 + 3 ^ 40 * 2192493 * 2
def baseEnd_2192493 : Nat := 250178386804043465500981

theorem tailTrace_2192493 : CollatzResearch.WordTrace tailWord_2192493 prefixEnd_2192493 250178386804043465500981 := by
  unfold tailWord_2192493
  simp only [CollatzResearch.WordTrace]
  refine ⟨79966789245979783838182133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53311192830653189225454755 79966789245979783838182133)
  ·
    refine ⟨7496886491810604734829575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 79966789245979783838182133 7496886491810604734829575)
    ·
      refine ⟨11245329737715907102244363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7496886491810604734829575 11245329737715907102244363)
      ·
        refine ⟨16867994606573860653366545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11245329737715907102244363 16867994606573860653366545)
        ·
          refine ⟨12650995954930395490024909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16867994606573860653366545 12650995954930395490024909)
          ·
            refine ⟨4744123483098898308759341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12650995954930395490024909 4744123483098898308759341)
            ·
              refine ⟨1779046306162086865784753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4744123483098898308759341 1779046306162086865784753)
              ·
                refine ⟨1334284729621565149338565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1779046306162086865784753 1334284729621565149338565)
                ·
                  refine ⟨250178386804043465500981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1334284729621565149338565 250178386804043465500981)
                  ·
                    rfl

theorem cell22_2192493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 3, 2, 4].length) (baseStart_2192493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2192493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2192493 prefixEnd_2192493 := by exact prefixLift 2192493
  have htrace : WordTrace (prefixWord ++ tailWord_2192493) baseStart_2192493 baseEnd_2192493 := by
    simpa [prefixWord, tailWord_2192493, baseEnd_2192493] using wordTrace_append hprefix tailTrace_2192493
  have hstable : (prefixWord ++ tailWord_2192493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2192493).length < 2 ^ (prefixWord ++ tailWord_2192493).sum := by decide
  have hdescent : baseEnd_2192493 < baseStart_2192493 := by decide
  rcases family_descends (prefixWord ++ tailWord_2192493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2192519 : List Nat := [1, 1, 4, 2, 1, 1, 1, 3, 5, 3]
def baseStart_2192519 : Nat := 118140960795 + 2192519 * 2 ^ 59
def prefixEnd_2192519 : Nat := 4983230072969 + 3 ^ 40 * 2192519 * 2
def baseEnd_2192519 : Nat := 750544060743474995352863

theorem tailTrace_2192519 : CollatzResearch.WordTrace tailWord_2192519 prefixEnd_2192519 750544060743474995352863 := by
  unfold tailWord_2192519
  simp only [CollatzResearch.WordTrace]
  refine ⟨79967737543885590278628611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53311825029257060185752407 79967737543885590278628611)
  ·
    refine ⟨119951606315828385417942917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79967737543885590278628611 119951606315828385417942917)
    ·
      refine ⟨22490926184217822265864297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 119951606315828385417942917 22490926184217822265864297)
      ·
        refine ⟨16868194638163366699398223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22490926184217822265864297 16868194638163366699398223)
        ·
          refine ⟨25302291957245050049097335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16868194638163366699398223 25302291957245050049097335)
          ·
            refine ⟨37953437935867575073646003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25302291957245050049097335 37953437935867575073646003)
            ·
              refine ⟨56930156903801362610469005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37953437935867575073646003 56930156903801362610469005)
              ·
                refine ⟨21348808838925510978925877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56930156903801362610469005 21348808838925510978925877)
                ·
                  refine ⟨2001450828649266654274301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21348808838925510978925877 2001450828649266654274301)
                  ·
                    refine ⟨750544060743474995352863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2001450828649266654274301 750544060743474995352863)
                    ·
                      rfl

theorem cell22_2192519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 3, 5, 3].length) (baseStart_2192519 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2192519 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2192519 prefixEnd_2192519 := by exact prefixLift 2192519
  have htrace : WordTrace (prefixWord ++ tailWord_2192519) baseStart_2192519 baseEnd_2192519 := by
    simpa [prefixWord, tailWord_2192519, baseEnd_2192519] using wordTrace_append hprefix tailTrace_2192519
  have hstable : (prefixWord ++ tailWord_2192519).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2192519).length < 2 ^ (prefixWord ++ tailWord_2192519).sum := by decide
  have hdescent : baseEnd_2192519 < baseStart_2192519 := by decide
  rcases family_descends (prefixWord ++ tailWord_2192519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2192547 : List Nat := [1, 1, 1, 4, 1, 1, 1, 2, 3, 7]
def baseStart_2192547 : Nat := 118140960795 + 2192547 * 2 ^ 59
def prefixEnd_2192547 : Nat := 4983230072969 + 3 ^ 40 * 2192547 * 2
def baseEnd_2192547 : Nat := 750553645715692255652777

theorem tailTrace_2192547 : CollatzResearch.WordTrace tailWord_2192547 prefixEnd_2192547 750553645715692255652777 := by
  unfold tailWord_2192547
  simp only [CollatzResearch.WordTrace]
  refine ⟨79968758787784151060647895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53312505858522767373765263 79968758787784151060647895)
  ·
    refine ⟨119953138181676226590971843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79968758787784151060647895 119953138181676226590971843)
    ·
      refine ⟨179929707272514339886457765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119953138181676226590971843 179929707272514339886457765)
      ·
        refine ⟨33736820113596438728710831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 179929707272514339886457765 33736820113596438728710831)
        ·
          refine ⟨50605230170394658093066247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33736820113596438728710831 50605230170394658093066247)
          ·
            refine ⟨75907845255591987139599371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50605230170394658093066247 75907845255591987139599371)
            ·
              refine ⟨113861767883387980709399057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75907845255591987139599371 113861767883387980709399057)
              ·
                refine ⟨85396325912540985532049293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 113861767883387980709399057 85396325912540985532049293)
                ·
                  refine ⟨32023622217202869574518485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 85396325912540985532049293 32023622217202869574518485)
                  ·
                    refine ⟨750553645715692255652777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32023622217202869574518485 750553645715692255652777)
                    ·
                      rfl

theorem cell22_2192547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 2, 3, 7].length) (baseStart_2192547 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2192547 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2192547 prefixEnd_2192547 := by exact prefixLift 2192547
  have htrace : WordTrace (prefixWord ++ tailWord_2192547) baseStart_2192547 baseEnd_2192547 := by
    simpa [prefixWord, tailWord_2192547, baseEnd_2192547] using wordTrace_append hprefix tailTrace_2192547
  have hstable : (prefixWord ++ tailWord_2192547).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2192547).length < 2 ^ (prefixWord ++ tailWord_2192547).sum := by decide
  have hdescent : baseEnd_2192547 < baseStart_2192547 := by decide
  rcases family_descends (prefixWord ++ tailWord_2192547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2192549 : List Nat := [1, 3, 1, 2, 1, 4, 1, 4, 5]
def baseStart_2192549 : Nat := 118140960795 + 2192549 * 2 ^ 59
def prefixEnd_2192549 : Nat := 4983230072969 + 3 ^ 40 * 2192549 * 2
def baseEnd_2192549 : Nat := 250184776785521639034257

theorem tailTrace_2192549 : CollatzResearch.WordTrace tailWord_2192549 prefixEnd_2192549 250184776785521639034257 := by
  unfold tailWord_2192549
  simp only [CollatzResearch.WordTrace]
  refine ⟨79968831733776905402220701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53312554489184603601480467 79968831733776905402220701)
  ·
    refine ⟨29988311900166339525832763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79968831733776905402220701 29988311900166339525832763)
    ·
      refine ⟨44982467850249509288749145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29988311900166339525832763 44982467850249509288749145)
      ·
        refine ⟨33736850887687131966561859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44982467850249509288749145 33736850887687131966561859)
        ·
          refine ⟨50605276331530697949842789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33736850887687131966561859 50605276331530697949842789)
          ·
            refine ⟨9488489312162005865595523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50605276331530697949842789 9488489312162005865595523)
            ·
              refine ⟨14232733968243008798393285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9488489312162005865595523 14232733968243008798393285)
              ·
                refine ⟨2668637619045564149698741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14232733968243008798393285 2668637619045564149698741)
                ·
                  refine ⟨250184776785521639034257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2668637619045564149698741 250184776785521639034257)
                  ·
                    rfl

theorem cell22_2192549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 4, 5].length) (baseStart_2192549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2192549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2192549 prefixEnd_2192549 := by exact prefixLift 2192549
  have htrace : WordTrace (prefixWord ++ tailWord_2192549) baseStart_2192549 baseEnd_2192549 := by
    simpa [prefixWord, tailWord_2192549, baseEnd_2192549] using wordTrace_append hprefix tailTrace_2192549
  have hstable : (prefixWord ++ tailWord_2192549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2192549).length < 2 ^ (prefixWord ++ tailWord_2192549).sum := by decide
  have hdescent : baseEnd_2192549 < baseStart_2192549 := by decide
  rcases family_descends (prefixWord ++ tailWord_2192549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2192594 : List Nat := [3, 2, 2, 2, 1, 1, 1, 2, 8]
def baseStart_2192594 : Nat := 118140960795 + 2192594 * 2 ^ 59
def prefixEnd_2192594 : Nat := 4983230072969 + 3 ^ 40 * 2192594 * 2
def baseEnd_2192594 : Nat := 250189911592066599909211

theorem tailTrace_2192594 : CollatzResearch.WordTrace tailWord_2192594 prefixEnd_2192594 250189911592066599909211 := by
  unfold tailWord_2192594
  simp only [CollatzResearch.WordTrace]
  refine ⟨19992618254653469521902209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53313648679075918725072557 19992618254653469521902209)
  ·
    refine ⟨14994463690990102141426657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19992618254653469521902209 14994463690990102141426657)
    ·
      refine ⟨11245847768242576606069993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14994463690990102141426657 11245847768242576606069993)
      ·
        refine ⟨8434385826181932454552495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11245847768242576606069993 8434385826181932454552495)
        ·
          refine ⟨12651578739272898681828743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8434385826181932454552495 12651578739272898681828743)
          ·
            refine ⟨18977368108909348022743115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12651578739272898681828743 18977368108909348022743115)
            ·
              refine ⟨28466052163364022034114673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18977368108909348022743115 28466052163364022034114673)
              ·
                refine ⟨21349539122523016525586005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28466052163364022034114673 21349539122523016525586005)
                ·
                  refine ⟨250189911592066599909211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21349539122523016525586005 250189911592066599909211)
                  ·
                    rfl

theorem cell22_2192594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 2, 8].length) (baseStart_2192594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2192594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2192594 prefixEnd_2192594 := by exact prefixLift 2192594
  have htrace : WordTrace (prefixWord ++ tailWord_2192594) baseStart_2192594 baseEnd_2192594 := by
    simpa [prefixWord, tailWord_2192594, baseEnd_2192594] using wordTrace_append hprefix tailTrace_2192594
  have hstable : (prefixWord ++ tailWord_2192594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2192594).length < 2 ^ (prefixWord ++ tailWord_2192594).sum := by decide
  have hdescent : baseEnd_2192594 < baseStart_2192594 := by decide
  rcases family_descends (prefixWord ++ tailWord_2192594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2192639 : List Nat := [1, 1, 2, 2, 1, 6, 1, 8]
def baseStart_2192639 : Nat := 118140960795 + 2192639 * 2 ^ 59
def prefixEnd_2192639 : Nat := 4983230072969 + 3 ^ 40 * 2192639 * 2
def baseEnd_2192639 : Nat := 83398348799537186928055

theorem tailTrace_2192639 : CollatzResearch.WordTrace tailWord_2192639 prefixEnd_2192639 83398348799537186928055 := by
  unfold tailWord_2192639
  simp only [CollatzResearch.WordTrace]
  refine ⟨79972114303450850772996971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53314742868967233848664647 79972114303450850772996971)
  ·
    refine ⟨119958171455176276159495457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79972114303450850772996971 119958171455176276159495457)
    ·
      refine ⟨89968628591382207119621593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119958171455176276159495457 89968628591382207119621593)
      ·
        refine ⟨67476471443536655339716195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89968628591382207119621593 67476471443536655339716195)
        ·
          refine ⟨101214707165304983009574293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67476471443536655339716195 101214707165304983009574293)
          ·
            refine ⟨4744439398373671078573795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 101214707165304983009574293 4744439398373671078573795)
            ·
              refine ⟨7116659097560506617860693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4744439398373671078573795 7116659097560506617860693)
              ·
                refine ⟨83398348799537186928055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7116659097560506617860693 83398348799537186928055)
                ·
                  rfl

theorem cell22_2192639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 8].length) (baseStart_2192639 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2192639 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2192639 prefixEnd_2192639 := by exact prefixLift 2192639
  have htrace : WordTrace (prefixWord ++ tailWord_2192639) baseStart_2192639 baseEnd_2192639 := by
    simpa [prefixWord, tailWord_2192639, baseEnd_2192639] using wordTrace_append hprefix tailTrace_2192639
  have hstable : (prefixWord ++ tailWord_2192639).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2192639).length < 2 ^ (prefixWord ++ tailWord_2192639).sum := by decide
  have hdescent : baseEnd_2192639 < baseStart_2192639 := by decide
  rcases family_descends (prefixWord ++ tailWord_2192639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2192761 : List Nat := [1, 2, 1, 3, 2, 1, 4, 2, 1, 5]
def baseStart_2192761 : Nat := 118140960795 + 2192761 * 2 ^ 59
def prefixEnd_2192761 : Nat := 4983230072969 + 3 ^ 40 * 2192761 * 2
def baseEnd_2192761 : Nat := 750626902289067030802121

theorem tailTrace_2192761 : CollatzResearch.WordTrace tailWord_2192761 prefixEnd_2192761 750626902289067030802121 := by
  unfold tailWord_2192761
  simp only [CollatzResearch.WordTrace]
  refine ⟨79976564009008865608938137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53317709339339243739292091 79976564009008865608938137)
  ·
    refine ⟨59982423006756649206703603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79976564009008865608938137 59982423006756649206703603)
    ·
      refine ⟨89973634510134973810055405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59982423006756649206703603 89973634510134973810055405)
      ·
        refine ⟨33740112941300615178770777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89973634510134973810055405 33740112941300615178770777)
        ·
          refine ⟨25305084705975461384078083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33740112941300615178770777 25305084705975461384078083)
          ·
            refine ⟨37957627058963192076117125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25305084705975461384078083 37957627058963192076117125)
            ·
              refine ⟨7117055073555598514271961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37957627058963192076117125 7117055073555598514271961)
              ·
                refine ⟨5337791305166698885703971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7117055073555598514271961 5337791305166698885703971)
                ·
                  refine ⟨8006686957750048328555957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5337791305166698885703971 8006686957750048328555957)
                  ·
                    refine ⟨750626902289067030802121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8006686957750048328555957 750626902289067030802121)
                    ·
                      rfl

theorem cell22_2192761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 2, 1, 5].length) (baseStart_2192761 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2192761 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2192761 prefixEnd_2192761 := by exact prefixLift 2192761
  have htrace : WordTrace (prefixWord ++ tailWord_2192761) baseStart_2192761 baseEnd_2192761 := by
    simpa [prefixWord, tailWord_2192761, baseEnd_2192761] using wordTrace_append hprefix tailTrace_2192761
  have hstable : (prefixWord ++ tailWord_2192761).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2192761).length < 2 ^ (prefixWord ++ tailWord_2192761).sum := by decide
  have hdescent : baseEnd_2192761 < baseStart_2192761 := by decide
  rcases family_descends (prefixWord ++ tailWord_2192761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2192763 : List Nat := [1, 1, 1, 1, 1, 6, 4, 3, 4]
def baseStart_2192763 : Nat := 118140960795 + 2192763 * 2 ^ 59
def prefixEnd_2192763 : Nat := 4983230072969 + 3 ^ 40 * 2192763 * 2
def baseEnd_2192763 : Nat := 250209195643313230750705

theorem tailTrace_2192763 : CollatzResearch.WordTrace tailWord_2192763 prefixEnd_2192763 250209195643313230750705 := by
  unfold tailWord_2192763
  simp only [CollatzResearch.WordTrace]
  refine ⟨79976636955001619950510943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53317757970001079967007295 79976636955001619950510943)
  ·
    refine ⟨119964955432502429925766415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79976636955001619950510943 119964955432502429925766415)
    ·
      refine ⟨179947433148753644888649623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119964955432502429925766415 179947433148753644888649623)
      ·
        refine ⟨269921149723130467332974435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 179947433148753644888649623 269921149723130467332974435)
        ·
          refine ⟨404881724584695700999461653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 269921149723130467332974435 404881724584695700999461653)
          ·
            refine ⟨18978830839907610984349765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 404881724584695700999461653 18978830839907610984349765)
            ·
              refine ⟨3558530782482677059565581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18978830839907610984349765 3558530782482677059565581)
              ·
                refine ⟨1334449043431003897337093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3558530782482677059565581 1334449043431003897337093)
                ·
                  refine ⟨250209195643313230750705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1334449043431003897337093 250209195643313230750705)
                  ·
                    rfl

theorem cell22_2192763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 4, 3, 4].length) (baseStart_2192763 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2192763 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2192763 prefixEnd_2192763 := by exact prefixLift 2192763
  have htrace : WordTrace (prefixWord ++ tailWord_2192763) baseStart_2192763 baseEnd_2192763 := by
    simpa [prefixWord, tailWord_2192763, baseEnd_2192763] using wordTrace_append hprefix tailTrace_2192763
  have hstable : (prefixWord ++ tailWord_2192763).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2192763).length < 2 ^ (prefixWord ++ tailWord_2192763).sum := by decide
  have hdescent : baseEnd_2192763 < baseStart_2192763 := by decide
  rcases family_descends (prefixWord ++ tailWord_2192763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2192853 : List Nat := [1, 3, 2, 3, 1, 1, 3, 3, 5]
def baseStart_2192853 : Nat := 118140960795 + 2192853 * 2 ^ 59
def prefixEnd_2192853 : Nat := 4983230072969 + 3 ^ 40 * 2192853 * 2
def baseEnd_2192853 : Nat := 250219465256403152500613

theorem tailTrace_2192853 : CollatzResearch.WordTrace tailWord_2192853 prefixEnd_2192853 250219465256403152500613 := by
  unfold tailWord_2192853
  simp only [CollatzResearch.WordTrace]
  refine ⟨79979919524675565321287213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53319946349783710214191475 79979919524675565321287213)
  ·
    refine ⟨29992469821753336995482705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79979919524675565321287213 29992469821753336995482705)
    ·
      refine ⟨22494352366315002746612029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29992469821753336995482705 22494352366315002746612029)
      ·
        refine ⟨8435382137368126029979511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22494352366315002746612029 8435382137368126029979511)
        ·
          refine ⟨12653073206052189044969267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8435382137368126029979511 12653073206052189044969267)
          ·
            refine ⟨18979609809078283567453901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12653073206052189044969267 18979609809078283567453901)
            ·
              refine ⟨7117353678404356337795213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18979609809078283567453901 7117353678404356337795213)
              ·
                refine ⟨2669007629401633626673205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7117353678404356337795213 2669007629401633626673205)
                ·
                  refine ⟨250219465256403152500613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2669007629401633626673205 250219465256403152500613)
                  ·
                    rfl

theorem cell22_2192853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 3, 5].length) (baseStart_2192853 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2192853 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2192853 prefixEnd_2192853 := by exact prefixLift 2192853
  have htrace : WordTrace (prefixWord ++ tailWord_2192853) baseStart_2192853 baseEnd_2192853 := by
    simpa [prefixWord, tailWord_2192853, baseEnd_2192853] using wordTrace_append hprefix tailTrace_2192853
  have hstable : (prefixWord ++ tailWord_2192853).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2192853).length < 2 ^ (prefixWord ++ tailWord_2192853).sum := by decide
  have hdescent : baseEnd_2192853 < baseStart_2192853 := by decide
  rcases family_descends (prefixWord ++ tailWord_2192853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2192913 : List Nat := [1, 2, 2, 1, 1, 2, 6, 1, 1, 5]
def baseStart_2192913 : Nat := 118140960795 + 2192913 * 2 ^ 59
def prefixEnd_2192913 : Nat := 4983230072969 + 3 ^ 40 * 2192913 * 2
def baseEnd_2192913 : Nat := 750678934995389301001655

theorem tailTrace_2192913 : CollatzResearch.WordTrace tailWord_2192913 prefixEnd_2192913 750678934995389301001655 := by
  unfold tailWord_2192913
  simp only [CollatzResearch.WordTrace]
  refine ⟨79982107904458195568471393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53321405269638797045647595 79982107904458195568471393)
  ·
    refine ⟨59986580928343646676353545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79982107904458195568471393 59986580928343646676353545)
    ·
      refine ⟨44989935696257735007265159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59986580928343646676353545 44989935696257735007265159)
      ·
        refine ⟨67484903544386602510897739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44989935696257735007265159 67484903544386602510897739)
        ·
          refine ⟨101227355316579903766346609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67484903544386602510897739 101227355316579903766346609)
          ·
            refine ⟨75920516487434927824759957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 101227355316579903766346609 75920516487434927824759957)
            ·
              refine ⟨3558774210348512241785623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 75920516487434927824759957 3558774210348512241785623)
              ·
                refine ⟨5338161315522768362678435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3558774210348512241785623 5338161315522768362678435)
                ·
                  refine ⟨8007241973284152544017653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5338161315522768362678435 8007241973284152544017653)
                  ·
                    refine ⟨750678934995389301001655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8007241973284152544017653 750678934995389301001655)
                    ·
                      rfl

theorem cell22_2192913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 5].length) (baseStart_2192913 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2192913 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2192913 prefixEnd_2192913 := by exact prefixLift 2192913
  have htrace : WordTrace (prefixWord ++ tailWord_2192913) baseStart_2192913 baseEnd_2192913 := by
    simpa [prefixWord, tailWord_2192913, baseEnd_2192913] using wordTrace_append hprefix tailTrace_2192913
  have hstable : (prefixWord ++ tailWord_2192913).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2192913).length < 2 ^ (prefixWord ++ tailWord_2192913).sum := by decide
  have hdescent : baseEnd_2192913 < baseStart_2192913 := by decide
  rcases family_descends (prefixWord ++ tailWord_2192913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2192947 : List Nat := [1, 1, 1, 2, 4, 5, 1, 2, 2, 3]
def baseStart_2192947 : Nat := 118140960795 + 2192947 * 2 ^ 59
def prefixEnd_2192947 : Nat := 4983230072969 + 3 ^ 40 * 2192947 * 2
def baseEnd_2192947 : Nat := 750690573890224545651551

theorem tailTrace_2192947 : CollatzResearch.WordTrace tailWord_2192947 prefixEnd_2192947 750690573890224545651551 := by
  unfold tailWord_2192947
  simp only [CollatzResearch.WordTrace]
  refine ⟨79983347986335019375209095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53322231990890012916806063 79983347986335019375209095)
  ·
    refine ⟨119975021979502529062813643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79983347986335019375209095 119975021979502529062813643)
    ·
      refine ⟨179962532969253793594220465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119975021979502529062813643 179962532969253793594220465)
      ·
        refine ⟨134971899726940345195665349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 179962532969253793594220465 134971899726940345195665349)
        ·
          refine ⟨25307231198801314724187253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 134971899726940345195665349 25307231198801314724187253)
          ·
            refine ⟨2372552924887623255392555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 25307231198801314724187253 2372552924887623255392555)
            ·
              refine ⟨3558829387331434883088833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2372552924887623255392555 3558829387331434883088833)
              ·
                refine ⟨2669122040498576162316625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3558829387331434883088833 2669122040498576162316625)
                ·
                  refine ⟨2001841530373932121737469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2669122040498576162316625 2001841530373932121737469)
                  ·
                    refine ⟨750690573890224545651551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2001841530373932121737469 750690573890224545651551)
                    ·
                      rfl

theorem cell22_2192947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 1, 2, 2, 3].length) (baseStart_2192947 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2192947 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2192947 prefixEnd_2192947 := by exact prefixLift 2192947
  have htrace : WordTrace (prefixWord ++ tailWord_2192947) baseStart_2192947 baseEnd_2192947 := by
    simpa [prefixWord, tailWord_2192947, baseEnd_2192947] using wordTrace_append hprefix tailTrace_2192947
  have hstable : (prefixWord ++ tailWord_2192947).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2192947).length < 2 ^ (prefixWord ++ tailWord_2192947).sum := by decide
  have hdescent : baseEnd_2192947 < baseStart_2192947 := by decide
  rcases family_descends (prefixWord ++ tailWord_2192947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2193033 : List Nat := [1, 2, 1, 1, 4, 1, 2, 4, 6]
def baseStart_2193033 : Nat := 118140960795 + 2193033 * 2 ^ 59
def prefixEnd_2193033 : Nat := 4983230072969 + 3 ^ 40 * 2193033 * 2
def baseEnd_2193033 : Nat := 250240004482582996000429

theorem tailTrace_2193033 : CollatzResearch.WordTrace tailWord_2193033 prefixEnd_2193033 250240004482582996000429 := by
  unfold tailWord_2193033
  simp only [CollatzResearch.WordTrace]
  refine ⟨79986484664023456062839753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53324323109348970708559835 79986484664023456062839753)
  ·
    refine ⟨59989863498017592047129815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79986484664023456062839753 59989863498017592047129815)
    ·
      refine ⟨89984795247026388070694723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59989863498017592047129815 89984795247026388070694723)
      ·
        refine ⟨134977192870539582106042085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89984795247026388070694723 134977192870539582106042085)
        ·
          refine ⟨25308223663226171644882891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 134977192870539582106042085 25308223663226171644882891)
          ·
            refine ⟨37962335494839257467324337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25308223663226171644882891 37962335494839257467324337)
            ·
              refine ⟨28471751621129443100493253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37962335494839257467324337 28471751621129443100493253)
              ·
                refine ⟨5338453428961770581342485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28471751621129443100493253 5338453428961770581342485)
                ·
                  refine ⟨250240004482582996000429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5338453428961770581342485 250240004482582996000429)
                  ·
                    rfl

theorem cell22_2193033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 4, 6].length) (baseStart_2193033 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2193033 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2193033 prefixEnd_2193033 := by exact prefixLift 2193033
  have htrace : WordTrace (prefixWord ++ tailWord_2193033) baseStart_2193033 baseEnd_2193033 := by
    simpa [prefixWord, tailWord_2193033, baseEnd_2193033] using wordTrace_append hprefix tailTrace_2193033
  have hstable : (prefixWord ++ tailWord_2193033).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2193033).length < 2 ^ (prefixWord ++ tailWord_2193033).sum := by decide
  have hdescent : baseEnd_2193033 < baseStart_2193033 := by decide
  rcases family_descends (prefixWord ++ tailWord_2193033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2193082 : List Nat := [3, 1, 1, 1, 2, 4, 2, 3, 2, 3]
def baseStart_2193082 : Nat := 118140960795 + 2193082 * 2 ^ 59
def prefixEnd_2193082 : Nat := 4983230072969 + 3 ^ 40 * 2193082 * 2
def baseEnd_2193082 : Nat := 750736787149129193526137

theorem tailTrace_2193082 : CollatzResearch.WordTrace tailWord_2193082 prefixEnd_2193082 750736787149129193526137 := by
  unfold tailWord_2193082
  simp only [CollatzResearch.WordTrace]
  refine ⟨19997067960211484357843375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53325514560563958287582333 19997067960211484357843375)
  ·
    refine ⟨29995601940317226536765063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19997067960211484357843375 29995601940317226536765063)
    ·
      refine ⟨44993402910475839805147595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29995601940317226536765063 44993402910475839805147595)
      ·
        refine ⟨67490104365713759707721393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44993402910475839805147595 67490104365713759707721393)
        ·
          refine ⟨50617578274285319780791045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67490104365713759707721393 50617578274285319780791045)
          ·
            refine ⟨9490795926428497458898321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50617578274285319780791045 9490795926428497458898321)
            ·
              refine ⟨7118096944821373094173741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9490795926428497458898321 7118096944821373094173741)
              ·
                refine ⟨2669286354308014910315153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7118096944821373094173741 2669286354308014910315153)
                ·
                  refine ⟨2001964765731011182736365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2669286354308014910315153 2001964765731011182736365)
                  ·
                    refine ⟨750736787149129193526137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2001964765731011182736365 750736787149129193526137)
                    ·
                      rfl

theorem cell22_2193082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 3, 2, 3].length) (baseStart_2193082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2193082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2193082 prefixEnd_2193082 := by exact prefixLift 2193082
  have htrace : WordTrace (prefixWord ++ tailWord_2193082) baseStart_2193082 baseEnd_2193082 := by
    simpa [prefixWord, tailWord_2193082, baseEnd_2193082] using wordTrace_append hprefix tailTrace_2193082
  have hstable : (prefixWord ++ tailWord_2193082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2193082).length < 2 ^ (prefixWord ++ tailWord_2193082).sum := by decide
  have hdescent : baseEnd_2193082 < baseStart_2193082 := by decide
  rcases family_descends (prefixWord ++ tailWord_2193082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2193093 : List Nat := [1, 3, 1, 1, 1, 1, 2, 3, 2, 7]
def baseStart_2193093 : Nat := 118140960795 + 2193093 * 2 ^ 59
def prefixEnd_2193093 : Nat := 4983230072969 + 3 ^ 40 * 2193093 * 2
def baseEnd_2193093 : Nat := 750740552673928831501103

theorem tailTrace_2193093 : CollatzResearch.WordTrace tailWord_2193093 prefixEnd_2193093 750740552673928831501103 := by
  unfold tailWord_2193093
  simp only [CollatzResearch.WordTrace]
  refine ⟨79988673043806086310023933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53325782029204057540015955 79988673043806086310023933)
  ·
    refine ⟨29995752391427282366258975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79988673043806086310023933 29995752391427282366258975)
    ·
      refine ⟨44993628587140923549388463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29995752391427282366258975 44993628587140923549388463)
      ·
        refine ⟨67490442880711385324082695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44993628587140923549388463 67490442880711385324082695)
        ·
          refine ⟨101235664321067077986124043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67490442880711385324082695 101235664321067077986124043)
          ·
            refine ⟨151853496481600616979186065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101235664321067077986124043 151853496481600616979186065)
            ·
              refine ⟨113890122361200462734389549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 151853496481600616979186065 113890122361200462734389549)
              ·
                refine ⟨42708795885450173525396081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 113890122361200462734389549 42708795885450173525396081)
                ·
                  refine ⟨32031596914087630144047061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42708795885450173525396081 32031596914087630144047061)
                  ·
                    refine ⟨750740552673928831501103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32031596914087630144047061 750740552673928831501103)
                    ·
                      rfl

theorem cell22_2193093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 3, 2, 7].length) (baseStart_2193093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2193093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2193093 prefixEnd_2193093 := by exact prefixLift 2193093
  have htrace : WordTrace (prefixWord ++ tailWord_2193093) baseStart_2193093 baseEnd_2193093 := by
    simpa [prefixWord, tailWord_2193093, baseEnd_2193093] using wordTrace_append hprefix tailTrace_2193093
  have hstable : (prefixWord ++ tailWord_2193093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2193093).length < 2 ^ (prefixWord ++ tailWord_2193093).sum := by decide
  have hdescent : baseEnd_2193093 < baseStart_2193093 := by decide
  rcases family_descends (prefixWord ++ tailWord_2193093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2193095 : List Nat := [1, 1, 4, 1, 1, 1, 7, 6]
def baseStart_2193095 : Nat := 118140960795 + 2193095 * 2 ^ 59
def prefixEnd_2193095 : Nat := 4983230072969 + 3 ^ 40 * 2193095 * 2
def baseEnd_2193095 : Nat := 83415693034977943661233

theorem tailTrace_2193095 : CollatzResearch.WordTrace tailWord_2193095 prefixEnd_2193095 83415693034977943661233 := by
  unfold tailWord_2193095
  simp only [CollatzResearch.WordTrace]
  refine ⟨79988745989798840651596739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53325830659865893767731159 79988745989798840651596739)
  ·
    refine ⟨119983118984698260977395109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79988745989798840651596739 119983118984698260977395109)
    ·
      refine ⟨22496834809630923933261583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 119983118984698260977395109 22496834809630923933261583)
      ·
        refine ⟨33745252214446385899892375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22496834809630923933261583 33745252214446385899892375)
        ·
          refine ⟨50617878321669578849838563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33745252214446385899892375 50617878321669578849838563)
          ·
            refine ⟨75926817482504368274757845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50617878321669578849838563 75926817482504368274757845)
            ·
              refine ⟨1779534784746196131439637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 75926817482504368274757845 1779534784746196131439637)
              ·
                refine ⟨83415693034977943661233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1779534784746196131439637 83415693034977943661233)
                ·
                  rfl

theorem cell22_2193095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 7, 6].length) (baseStart_2193095 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2193095 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2193095 prefixEnd_2193095 := by exact prefixLift 2193095
  have htrace : WordTrace (prefixWord ++ tailWord_2193095) baseStart_2193095 baseEnd_2193095 := by
    simpa [prefixWord, tailWord_2193095, baseEnd_2193095] using wordTrace_append hprefix tailTrace_2193095
  have hstable : (prefixWord ++ tailWord_2193095).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2193095).length < 2 ^ (prefixWord ++ tailWord_2193095).sum := by decide
  have hdescent : baseEnd_2193095 < baseStart_2193095 := by decide
  rcases family_descends (prefixWord ++ tailWord_2193095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2193101 : List Nat := [1, 6, 2, 1, 1, 2, 2, 3, 4]
def baseStart_2193101 : Nat := 118140960795 + 2193101 * 2 ^ 59
def prefixEnd_2193101 : Nat := 4983230072969 + 3 ^ 40 * 2193101 * 2
def baseEnd_2193101 : Nat := 250247763745806492433693

theorem tailTrace_2193101 : CollatzResearch.WordTrace tailWord_2193101 prefixEnd_2193101 250247763745806492433693 := by
  unfold tailWord_2193101
  simp only [CollatzResearch.WordTrace]
  refine ⟨79988964827777103676315157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53325976551851402450876771 79988964827777103676315157)
  ·
    refine ⟨3749482726302051734827273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 79988964827777103676315157 3749482726302051734827273)
    ·
      refine ⟨2812112044726538801120455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3749482726302051734827273 2812112044726538801120455)
      ·
        refine ⟨4218168067089808201680683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2812112044726538801120455 4218168067089808201680683)
        ·
          refine ⟨6327252100634712302521025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4218168067089808201680683 6327252100634712302521025)
          ·
            refine ⟨4745439075476034226890769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6327252100634712302521025 4745439075476034226890769)
            ·
              refine ⟨3559079306607025670168077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4745439075476034226890769 3559079306607025670168077)
              ·
                refine ⟨1334654739977634626313029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3559079306607025670168077 1334654739977634626313029)
                ·
                  refine ⟨250247763745806492433693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1334654739977634626313029 250247763745806492433693)
                  ·
                    rfl

theorem cell22_2193101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 2, 3, 4].length) (baseStart_2193101 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2193101 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2193101 prefixEnd_2193101 := by exact prefixLift 2193101
  have htrace : WordTrace (prefixWord ++ tailWord_2193101) baseStart_2193101 baseEnd_2193101 := by
    simpa [prefixWord, tailWord_2193101, baseEnd_2193101] using wordTrace_append hprefix tailTrace_2193101
  have hstable : (prefixWord ++ tailWord_2193101).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2193101).length < 2 ^ (prefixWord ++ tailWord_2193101).sum := by decide
  have hdescent : baseEnd_2193101 < baseStart_2193101 := by decide
  rcases family_descends (prefixWord ++ tailWord_2193101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2193204 : List Nat := [2, 5, 1, 1, 2, 2, 1, 1, 3, 4]
def baseStart_2193204 : Nat := 118140960795 + 2193204 * 2 ^ 59
def prefixEnd_2193204 : Nat := 4983230072969 + 3 ^ 40 * 2193204 * 2
def baseEnd_2193204 : Nat := 750778550242361541975763

theorem tailTrace_2193204 : CollatzResearch.WordTrace tailWord_2193204 prefixEnd_2193204 750778550242361541975763 := by
  unfold tailWord_2193204
  simp only [CollatzResearch.WordTrace]
  refine ⟨39996360773201976133657333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53328481030935968178209777 39996360773201976133657333)
  ·
    refine ⟨3749658822487685262530375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 39996360773201976133657333 3749658822487685262530375)
    ·
      refine ⟨5624488233731527893795563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3749658822487685262530375 5624488233731527893795563)
      ·
        refine ⟨8436732350597291840693345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5624488233731527893795563 8436732350597291840693345)
        ·
          refine ⟨6327549262947968880520009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8436732350597291840693345 6327549262947968880520009)
          ·
            refine ⟨4745661947210976660390007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6327549262947968880520009 4745661947210976660390007)
            ·
              refine ⟨7118492920816464990585011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4745661947210976660390007 7118492920816464990585011)
              ·
                refine ⟨10677739381224697485877517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7118492920816464990585011 10677739381224697485877517)
                ·
                  refine ⟨4004152267959261557204069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10677739381224697485877517 4004152267959261557204069)
                  ·
                    refine ⟨750778550242361541975763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4004152267959261557204069 750778550242361541975763)
                    ·
                      rfl

theorem cell22_2193204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 1, 3, 4].length) (baseStart_2193204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2193204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2193204 prefixEnd_2193204 := by exact prefixLift 2193204
  have htrace : WordTrace (prefixWord ++ tailWord_2193204) baseStart_2193204 baseEnd_2193204 := by
    simpa [prefixWord, tailWord_2193204, baseEnd_2193204] using wordTrace_append hprefix tailTrace_2193204
  have hstable : (prefixWord ++ tailWord_2193204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2193204).length < 2 ^ (prefixWord ++ tailWord_2193204).sum := by decide
  have hdescent : baseEnd_2193204 < baseStart_2193204 := by decide
  rcases family_descends (prefixWord ++ tailWord_2193204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2193234 : List Nat := [3, 2, 2, 1, 1, 3, 1, 4, 2, 3]
def baseStart_2193234 : Nat := 118140960795 + 2193234 * 2 ^ 59
def prefixEnd_2193234 : Nat := 4983230072969 + 3 ^ 40 * 2193234 * 2
def baseEnd_2193234 : Nat := 750788819855451463725671

theorem tailTrace_2193234 : CollatzResearch.WordTrace tailWord_2193234 prefixEnd_2193234 750788819855451463725671 := by
  unfold tailWord_2193234
  simp only [CollatzResearch.WordTrace]
  refine ⟨19998453934073816847726689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53329210490863511593937837 19998453934073816847726689)
  ·
    refine ⟨14998840450555362635795017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19998453934073816847726689 14998840450555362635795017)
    ·
      refine ⟨11249130337916521976846263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14998840450555362635795017 11249130337916521976846263)
      ·
        refine ⟨16873695506874782965269395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11249130337916521976846263 16873695506874782965269395)
        ·
          refine ⟨25310543260312174447904093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16873695506874782965269395 25310543260312174447904093)
          ·
            refine ⟨9491453722617065417964035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25310543260312174447904093 9491453722617065417964035)
            ·
              refine ⟨14237180583925598126946053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9491453722617065417964035 14237180583925598126946053)
              ·
                refine ⟨2669471359486049648802385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14237180583925598126946053 2669471359486049648802385)
                ·
                  refine ⟨2002103519614537236601789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2669471359486049648802385 2002103519614537236601789)
                  ·
                    refine ⟨750788819855451463725671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2002103519614537236601789 750788819855451463725671)
                    ·
                      rfl

theorem cell22_2193234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 4, 2, 3].length) (baseStart_2193234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2193234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2193234 prefixEnd_2193234 := by exact prefixLift 2193234
  have htrace : WordTrace (prefixWord ++ tailWord_2193234) baseStart_2193234 baseEnd_2193234 := by
    simpa [prefixWord, tailWord_2193234, baseEnd_2193234] using wordTrace_append hprefix tailTrace_2193234
  have hstable : (prefixWord ++ tailWord_2193234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2193234).length < 2 ^ (prefixWord ++ tailWord_2193234).sum := by decide
  have hdescent : baseEnd_2193234 < baseStart_2193234 := by decide
  rcases family_descends (prefixWord ++ tailWord_2193234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2193236 : List Nat := [2, 4, 1, 1, 3, 1, 4, 2, 4]
def baseStart_2193236 : Nat := 118140960795 + 2193236 * 2 ^ 59
def prefixEnd_2193236 : Nat := 4983230072969 + 3 ^ 40 * 2193236 * 2
def baseEnd_2193236 : Nat := 250263168165441375058555

theorem tailTrace_2193236 : CollatzResearch.WordTrace tailWord_2193236 prefixEnd_2193236 250263168165441375058555 := by
  unfold tailWord_2193236
  simp only [CollatzResearch.WordTrace]
  refine ⟨39996944341144010866239781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53329259121525347821653041 39996944341144010866239781)
  ·
    refine ⟨7499427063964502037419959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39996944341144010866239781 7499427063964502037419959)
    ·
      refine ⟨11249140595946753056129939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7499427063964502037419959 11249140595946753056129939)
      ·
        refine ⟨16873710893920129584194909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11249140595946753056129939 16873710893920129584194909)
        ·
          refine ⟨6327641585220048594073091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16873710893920129584194909 6327641585220048594073091)
          ·
            refine ⟨9491462377830072891109637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6327641585220048594073091 9491462377830072891109637)
            ·
              refine ⟨1779649195843138667083057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9491462377830072891109637 1779649195843138667083057)
              ·
                refine ⟨1334736896882354000312293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1779649195843138667083057 1334736896882354000312293)
                ·
                  refine ⟨250263168165441375058555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1334736896882354000312293 250263168165441375058555)
                  ·
                    rfl

theorem cell22_2193236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 4, 2, 4].length) (baseStart_2193236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2193236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2193236 prefixEnd_2193236 := by exact prefixLift 2193236
  have htrace : WordTrace (prefixWord ++ tailWord_2193236) baseStart_2193236 baseEnd_2193236 := by
    simpa [prefixWord, tailWord_2193236, baseEnd_2193236] using wordTrace_append hprefix tailTrace_2193236
  have hstable : (prefixWord ++ tailWord_2193236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2193236).length < 2 ^ (prefixWord ++ tailWord_2193236).sum := by decide
  have hdescent : baseEnd_2193236 < baseStart_2193236 := by decide
  rcases family_descends (prefixWord ++ tailWord_2193236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2193247 : List Nat := [1, 1, 2, 3, 1, 6, 1, 7]
def baseStart_2193247 : Nat := 118140960795 + 2193247 * 2 ^ 59
def prefixEnd_2193247 : Nat := 4983230072969 + 3 ^ 40 * 2193247 * 2
def baseEnd_2193247 : Nat := 83421474446791529238959

theorem tailTrace_2193247 : CollatzResearch.WordTrace tailWord_2193247 prefixEnd_2193247 83421474446791529238959 := by
  unfold tailWord_2193247
  simp only [CollatzResearch.WordTrace]
  refine ⟨79994289885248170611129995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53329526590165447074086663 79994289885248170611129995)
  ·
    refine ⟨119991434827872255916694993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79994289885248170611129995 119991434827872255916694993)
    ·
      refine ⟨89993576120904191937521245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119991434827872255916694993 89993576120904191937521245)
      ·
        refine ⟨33747591045339071976570467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89993576120904191937521245 33747591045339071976570467)
        ·
          refine ⟨50621386568008607964855701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33747591045339071976570467 50621386568008607964855701)
          ·
            refine ⟨2372877495375403498352611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 50621386568008607964855701 2372877495375403498352611)
            ·
              refine ⟨3559316243063105247528917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2372877495375403498352611 3559316243063105247528917)
              ·
                refine ⟨83421474446791529238959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3559316243063105247528917 83421474446791529238959)
                ·
                  rfl

theorem cell22_2193247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 1, 7].length) (baseStart_2193247 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2193247 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2193247 prefixEnd_2193247 := by exact prefixLift 2193247
  have htrace : WordTrace (prefixWord ++ tailWord_2193247) baseStart_2193247 baseEnd_2193247 := by
    simpa [prefixWord, tailWord_2193247, baseEnd_2193247] using wordTrace_append hprefix tailTrace_2193247
  have hstable : (prefixWord ++ tailWord_2193247).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2193247).length < 2 ^ (prefixWord ++ tailWord_2193247).sum := by decide
  have hdescent : baseEnd_2193247 < baseStart_2193247 := by decide
  rcases family_descends (prefixWord ++ tailWord_2193247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2193275 : List Nat := [1, 1, 1, 1, 1, 5, 1, 4, 7]
def baseStart_2193275 : Nat := 118140960795 + 2193275 * 2 ^ 59
def prefixEnd_2193275 : Nat := 4983230072969 + 3 ^ 40 * 2193275 * 2
def baseEnd_2193275 : Nat := 250267618331113674483515

theorem tailTrace_2193275 : CollatzResearch.WordTrace tailWord_2193275 prefixEnd_2193275 250267618331113674483515 := by
  unfold tailWord_2193275
  simp only [CollatzResearch.WordTrace]
  refine ⟨79995311129146731393149279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53330207419431154262099519 79995311129146731393149279)
  ·
    refine ⟨119992966693720097089723919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79995311129146731393149279 119992966693720097089723919)
    ·
      refine ⟨179989450040580145634585879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119992966693720097089723919 179989450040580145634585879)
      ·
        refine ⟨269984175060870218451878819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 179989450040580145634585879 269984175060870218451878819)
        ·
          refine ⟨404976262591305327677818229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 269984175060870218451878819 404976262591305327677818229)
          ·
            refine ⟨37966524617934874469795459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 404976262591305327677818229 37966524617934874469795459)
            ·
              refine ⟨56949786926902311704693189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37966524617934874469795459 56949786926902311704693189)
              ·
                refine ⟨10678085048794183444629973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 56949786926902311704693189 10678085048794183444629973)
                ·
                  refine ⟨250267618331113674483515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10678085048794183444629973 250267618331113674483515)
                  ·
                    rfl

theorem cell22_2193275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 4, 7].length) (baseStart_2193275 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2193275 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2193275 prefixEnd_2193275 := by exact prefixLift 2193275
  have htrace : WordTrace (prefixWord ++ tailWord_2193275) baseStart_2193275 baseEnd_2193275 := by
    simpa [prefixWord, tailWord_2193275, baseEnd_2193275] using wordTrace_append hprefix tailTrace_2193275
  have hstable : (prefixWord ++ tailWord_2193275).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2193275).length < 2 ^ (prefixWord ++ tailWord_2193275).sum := by decide
  have hdescent : baseEnd_2193275 < baseStart_2193275 := by decide
  rcases family_descends (prefixWord ++ tailWord_2193275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2193302 : List Nat := [5, 3, 1, 1, 2, 1, 3, 1, 2, 3]
def baseStart_2193302 : Nat := 118140960795 + 2193302 * 2 ^ 59
def prefixEnd_2193302 : Nat := 4983230072969 + 3 ^ 40 * 2193302 * 2
def baseEnd_2193302 : Nat := 750812097645121953025463

theorem tailTrace_2193302 : CollatzResearch.WordTrace tailWord_2193302 prefixEnd_2193302 750812097645121953025463 := by
  unfold tailWord_2193302
  simp only [CollatzResearch.WordTrace]
  refine ⟨4999768493753057187773885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 53330863933365943336254773 4999768493753057187773885)
  ·
    refine ⟨1874913185157396445415207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4999768493753057187773885 1874913185157396445415207)
    ·
      refine ⟨2812369777736094668122811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1874913185157396445415207 2812369777736094668122811)
      ·
        refine ⟨4218554666604142002184217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2812369777736094668122811 4218554666604142002184217)
        ·
          refine ⟨3163915999953106501638163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4218554666604142002184217 3163915999953106501638163)
          ·
            refine ⟨4745873999929659752457245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3163915999953106501638163 4745873999929659752457245)
            ·
              refine ⟨1779702749973622407171467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4745873999929659752457245 1779702749973622407171467)
              ·
                refine ⟨2669554124960433610757201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1779702749973622407171467 2669554124960433610757201)
                ·
                  refine ⟨2002165593720325208067901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2669554124960433610757201 2002165593720325208067901)
                  ·
                    refine ⟨750812097645121953025463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2002165593720325208067901 750812097645121953025463)
                    ·
                      rfl

theorem cell22_2193302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 3, 1, 2, 3].length) (baseStart_2193302 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2193302 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2193302 prefixEnd_2193302 := by exact prefixLift 2193302
  have htrace : WordTrace (prefixWord ++ tailWord_2193302) baseStart_2193302 baseEnd_2193302 := by
    simpa [prefixWord, tailWord_2193302, baseEnd_2193302] using wordTrace_append hprefix tailTrace_2193302
  have hstable : (prefixWord ++ tailWord_2193302).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2193302).length < 2 ^ (prefixWord ++ tailWord_2193302).sum := by decide
  have hdescent : baseEnd_2193302 < baseStart_2193302 := by decide
  rcases family_descends (prefixWord ++ tailWord_2193302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2193354 : List Nat := [3, 1, 2, 1, 2, 1, 2, 6, 4]
def baseStart_2193354 : Nat := 118140960795 + 2193354 * 2 ^ 59
def prefixEnd_2193354 : Nat := 4983230072969 + 3 ^ 40 * 2193354 * 2
def baseEnd_2193354 : Nat := 250276632769270383575101

theorem tailTrace_2193354 : CollatzResearch.WordTrace tailWord_2193354 prefixEnd_2193354 250276632769270383575101 := by
  unfold tailWord_2193354
  simp only [CollatzResearch.WordTrace]
  refine ⟨19999548123965131971318779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53332128330573685256850077 19999548123965131971318779)
  ·
    refine ⟨29999322185947697956978169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19999548123965131971318779 29999322185947697956978169)
    ·
      refine ⟨22499491639460773467733627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29999322185947697956978169 22499491639460773467733627)
      ·
        refine ⟨33749237459191160201600441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22499491639460773467733627 33749237459191160201600441)
        ·
          refine ⟨25311928094393370151200331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33749237459191160201600441 25311928094393370151200331)
          ·
            refine ⟨37967892141590055226800497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25311928094393370151200331 37967892141590055226800497)
            ·
              refine ⟨28475919106192541420100373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37967892141590055226800497 28475919106192541420100373)
              ·
                refine ⟨1334808708102775379067205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 28475919106192541420100373 1334808708102775379067205)
                ·
                  refine ⟨250276632769270383575101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1334808708102775379067205 250276632769270383575101)
                  ·
                    rfl

theorem cell22_2193354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 6, 4].length) (baseStart_2193354 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2193354 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2193354 prefixEnd_2193354 := by exact prefixLift 2193354
  have htrace : WordTrace (prefixWord ++ tailWord_2193354) baseStart_2193354 baseEnd_2193354 := by
    simpa [prefixWord, tailWord_2193354, baseEnd_2193354] using wordTrace_append hprefix tailTrace_2193354
  have hstable : (prefixWord ++ tailWord_2193354).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2193354).length < 2 ^ (prefixWord ++ tailWord_2193354).sum := by decide
  have hdescent : baseEnd_2193354 < baseStart_2193354 := by decide
  rcases family_descends (prefixWord ++ tailWord_2193354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2193367 : List Nat := [1, 1, 3, 2, 1, 1, 3, 2, 4, 4]
def baseStart_2193367 : Nat := 118140960795 + 2193367 * 2 ^ 59
def prefixEnd_2193367 : Nat := 4983230072969 + 3 ^ 40 * 2193367 * 2
def baseEnd_2193367 : Nat := 750834348473483450150263

theorem tailTrace_2193367 : CollatzResearch.WordTrace tailWord_2193367 prefixEnd_2193367 750834348473483450150263 := by
  unfold tailWord_2193367
  simp only [CollatzResearch.WordTrace]
  refine ⟨79998666644813431105498355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53332444429875620736998903 79998666644813431105498355)
  ·
    refine ⟨119997999967220146658247533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79998666644813431105498355 119997999967220146658247533)
    ·
      refine ⟨44999249987707554996842825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 119997999967220146658247533 44999249987707554996842825)
      ·
        refine ⟨33749437490780666247632119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44999249987707554996842825 33749437490780666247632119)
        ·
          refine ⟨50624156236170999371448179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33749437490780666247632119 50624156236170999371448179)
          ·
            refine ⟨75936234354256499057172269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50624156236170999371448179 75936234354256499057172269)
            ·
              refine ⟨28476087882846187146439601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 75936234354256499057172269 28476087882846187146439601)
              ·
                refine ⟨21357065912134640359829701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28476087882846187146439601 21357065912134640359829701)
                ·
                  refine ⟨4004449858525245067468069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21357065912134640359829701 4004449858525245067468069)
                  ·
                    refine ⟨750834348473483450150263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4004449858525245067468069 750834348473483450150263)
                    ·
                      rfl

theorem cell22_2193367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 2, 4, 4].length) (baseStart_2193367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2193367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2193367 prefixEnd_2193367 := by exact prefixLift 2193367
  have htrace : WordTrace (prefixWord ++ tailWord_2193367) baseStart_2193367 baseEnd_2193367 := by
    simpa [prefixWord, tailWord_2193367, baseEnd_2193367] using wordTrace_append hprefix tailTrace_2193367
  have hstable : (prefixWord ++ tailWord_2193367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2193367).length < 2 ^ (prefixWord ++ tailWord_2193367).sum := by decide
  have hdescent : baseEnd_2193367 < baseStart_2193367 := by decide
  rcases family_descends (prefixWord ++ tailWord_2193367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2193373 : List Nat := [1, 4, 3, 1, 3, 2, 1, 2, 1, 4]
def baseStart_2193373 : Nat := 118140960795 + 2193373 * 2 ^ 59
def prefixEnd_2193373 : Nat := 4983230072969 + 3 ^ 40 * 2193373 * 2
def baseEnd_2193373 : Nat := 750836402396101434500245

theorem tailTrace_2193373 : CollatzResearch.WordTrace tailWord_2193373 prefixEnd_2193373 750836402396101434500245 := by
  unfold tailWord_2193373
  simp only [CollatzResearch.WordTrace]
  refine ⟨79998885482791694130216773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53332590321861129420144515 79998885482791694130216773)
  ·
    refine ⟨14999791028023442649415645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 79998885482791694130216773 14999791028023442649415645)
    ·
      refine ⟨5624921635508790993530867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14999791028023442649415645 5624921635508790993530867)
      ·
        refine ⟨8437382453263186490296301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5624921635508790993530867 8437382453263186490296301)
        ·
          refine ⟨3164018419973694933861113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8437382453263186490296301 3164018419973694933861113)
          ·
            refine ⟨2373013814980271200395835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3164018419973694933861113 2373013814980271200395835)
            ·
              refine ⟨3559520722470406800593753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2373013814980271200395835 3559520722470406800593753)
              ·
                refine ⟨2669640541852805100445315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3559520722470406800593753 2669640541852805100445315)
                ·
                  refine ⟨4004460812779207650667973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2669640541852805100445315 4004460812779207650667973)
                  ·
                    refine ⟨750836402396101434500245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4004460812779207650667973 750836402396101434500245)
                    ·
                      rfl

theorem cell22_2193373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 1, 2, 1, 4].length) (baseStart_2193373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2193373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2193373 prefixEnd_2193373 := by exact prefixLift 2193373
  have htrace : WordTrace (prefixWord ++ tailWord_2193373) baseStart_2193373 baseEnd_2193373 := by
    simpa [prefixWord, tailWord_2193373, baseEnd_2193373] using wordTrace_append hprefix tailTrace_2193373
  have hstable : (prefixWord ++ tailWord_2193373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2193373).length < 2 ^ (prefixWord ++ tailWord_2193373).sum := by decide
  have hdescent : baseEnd_2193373 < baseStart_2193373 := by decide
  rcases family_descends (prefixWord ++ tailWord_2193373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2193519 : List Nat := [1, 1, 2, 1, 3, 4, 1, 1, 4, 4]
def baseStart_2193519 : Nat := 118140960795 + 2193519 * 2 ^ 59
def prefixEnd_2193519 : Nat := 4983230072969 + 3 ^ 40 * 2193519 * 2
def baseEnd_2193519 : Nat := 750886381179805720349797

theorem tailTrace_2193519 : CollatzResearch.WordTrace tailWord_2193519 prefixEnd_2193519 750886381179805720349797 := by
  unfold tailWord_2193519
  simp only [CollatzResearch.WordTrace]
  refine ⟨80004210540262761065031611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53336140360175174043354407 80004210540262761065031611)
  ·
    refine ⟨120006315810394141597547417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80004210540262761065031611 120006315810394141597547417)
    ·
      refine ⟨90004736857795606198160563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120006315810394141597547417 90004736857795606198160563)
      ·
        refine ⟨135007105286693409297240845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90004736857795606198160563 135007105286693409297240845)
        ·
          refine ⟨50627664482510028486465317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 135007105286693409297240845 50627664482510028486465317)
          ·
            refine ⟨9492687090470630341212247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50627664482510028486465317 9492687090470630341212247)
            ·
              refine ⟨14239030635705945511818371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9492687090470630341212247 14239030635705945511818371)
              ·
                refine ⟨21358545953558918267727557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14239030635705945511818371 21358545953558918267727557)
                ·
                  refine ⟨4004727366292297175198917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21358545953558918267727557 4004727366292297175198917)
                  ·
                    refine ⟨750886381179805720349797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4004727366292297175198917 750886381179805720349797)
                    ·
                      rfl

theorem cell22_2193519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 1, 4, 4].length) (baseStart_2193519 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2193519 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2193519 prefixEnd_2193519 := by exact prefixLift 2193519
  have htrace : WordTrace (prefixWord ++ tailWord_2193519) baseStart_2193519 baseEnd_2193519 := by
    simpa [prefixWord, tailWord_2193519, baseEnd_2193519] using wordTrace_append hprefix tailTrace_2193519
  have hstable : (prefixWord ++ tailWord_2193519).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2193519).length < 2 ^ (prefixWord ++ tailWord_2193519).sum := by decide
  have hdescent : baseEnd_2193519 < baseStart_2193519 := by decide
  rcases family_descends (prefixWord ++ tailWord_2193519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2193521 : List Nat := [1, 2, 2, 2, 1, 1, 4, 4, 2, 3]
def baseStart_2193521 : Nat := 118140960795 + 2193521 * 2 ^ 59
def prefixEnd_2193521 : Nat := 4983230072969 + 3 ^ 40 * 2193521 * 2
def baseEnd_2193521 : Nat := 750887065820678381799791

theorem tailTrace_2193521 : CollatzResearch.WordTrace tailWord_2193521 prefixEnd_2193521 750887065820678381799791 := by
  unfold tailWord_2193521
  simp only [CollatzResearch.WordTrace]
  refine ⟨80004283486255515406604417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53336188990837010271069611 80004283486255515406604417)
  ·
    refine ⟨60003212614691636554953313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80004283486255515406604417 60003212614691636554953313)
    ·
      refine ⟨45002409461018727416214985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60003212614691636554953313 45002409461018727416214985)
      ·
        refine ⟨33751807095764045562161239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45002409461018727416214985 33751807095764045562161239)
        ·
          refine ⟨50627710643646068343241859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33751807095764045562161239 50627710643646068343241859)
          ·
            refine ⟨75941565965469102514862789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50627710643646068343241859 75941565965469102514862789)
            ·
              refine ⟨14239043618525456721536773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 75941565965469102514862789 14239043618525456721536773)
              ·
                refine ⟨2669820678473523135288145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14239043618525456721536773 2669820678473523135288145)
                ·
                  refine ⟨2002365508855142351466109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2669820678473523135288145 2002365508855142351466109)
                  ·
                    refine ⟨750887065820678381799791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2002365508855142351466109 750887065820678381799791)
                    ·
                      rfl

theorem cell22_2193521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 4, 2, 3].length) (baseStart_2193521 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2193521 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2193521 prefixEnd_2193521 := by exact prefixLift 2193521
  have htrace : WordTrace (prefixWord ++ tailWord_2193521) baseStart_2193521 baseEnd_2193521 := by
    simpa [prefixWord, tailWord_2193521, baseEnd_2193521] using wordTrace_append hprefix tailTrace_2193521
  have hstable : (prefixWord ++ tailWord_2193521).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2193521).length < 2 ^ (prefixWord ++ tailWord_2193521).sum := by decide
  have hdescent : baseEnd_2193521 < baseStart_2193521 := by decide
  rcases family_descends (prefixWord ++ tailWord_2193521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2193581 : List Nat := [1, 5, 2, 1, 2, 1, 1, 1, 2, 6]
def baseStart_2193581 : Nat := 118140960795 + 2193581 * 2 ^ 59
def prefixEnd_2193581 : Nat := 4983230072969 + 3 ^ 40 * 2193581 * 2
def baseEnd_2193581 : Nat := 750907605046858225299607

theorem tailTrace_2193581 : CollatzResearch.WordTrace tailWord_2193581 prefixEnd_2193581 750907605046858225299607 := by
  unfold tailWord_2193581
  simp only [CollatzResearch.WordTrace]
  refine ⟨80006471866038145653788597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53337647910692097102525731 80006471866038145653788597)
  ·
    refine ⟨7500606737441076155042681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 80006471866038145653788597 7500606737441076155042681)
    ·
      refine ⟨5625455053080807116282011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7500606737441076155042681 5625455053080807116282011)
      ·
        refine ⟨8438182579621210674423017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5625455053080807116282011 8438182579621210674423017)
        ·
          refine ⟨6328636934715908005817263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8438182579621210674423017 6328636934715908005817263)
          ·
            refine ⟨9492955402073862008725895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6328636934715908005817263 9492955402073862008725895)
            ·
              refine ⟨14239433103110793013088843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9492955402073862008725895 14239433103110793013088843)
              ·
                refine ⟨21359149654666189519633265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14239433103110793013088843 21359149654666189519633265)
                ·
                  refine ⟨16019362240999642139724949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21359149654666189519633265 16019362240999642139724949)
                  ·
                    refine ⟨750907605046858225299607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16019362240999642139724949 750907605046858225299607)
                    ·
                      rfl

theorem cell22_2193581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 1, 2, 6].length) (baseStart_2193581 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2193581 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2193581 prefixEnd_2193581 := by exact prefixLift 2193581
  have htrace : WordTrace (prefixWord ++ tailWord_2193581) baseStart_2193581 baseEnd_2193581 := by
    simpa [prefixWord, tailWord_2193581, baseEnd_2193581] using wordTrace_append hprefix tailTrace_2193581
  have hstable : (prefixWord ++ tailWord_2193581).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2193581).length < 2 ^ (prefixWord ++ tailWord_2193581).sum := by decide
  have hdescent : baseEnd_2193581 < baseStart_2193581 := by decide
  rcases family_descends (prefixWord ++ tailWord_2193581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2193594 : List Nat := [3, 1, 1, 1, 2, 2, 3, 1, 1, 7]
def baseStart_2193594 : Nat := 118140960795 + 2193594 * 2 ^ 59
def prefixEnd_2193594 : Nat := 4983230072969 + 3 ^ 40 * 2193594 * 2
def baseEnd_2193594 : Nat := 750912055212530524724567

theorem tailTrace_2193594 : CollatzResearch.WordTrace tailWord_2193594 prefixEnd_2193594 750912055212530524724567 := by
  unfold tailWord_2193594
  simp only [CollatzResearch.WordTrace]
  refine ⟨20001736503747762218502959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53337964009994032582674557 20001736503747762218502959)
  ·
    refine ⟨30002604755621643327754439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20001736503747762218502959 30002604755621643327754439)
    ·
      refine ⟨45003907133432464991631659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30002604755621643327754439 45003907133432464991631659)
      ·
        refine ⟨67505860700148697487447489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45003907133432464991631659 67505860700148697487447489)
        ·
          refine ⟨50629395525111523115585617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67505860700148697487447489 50629395525111523115585617)
          ·
            refine ⟨37972046643833642336689213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50629395525111523115585617 37972046643833642336689213)
            ·
              refine ⟨14239517491437615876258455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37972046643833642336689213 14239517491437615876258455)
              ·
                refine ⟨21359276237156423814387683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14239517491437615876258455 21359276237156423814387683)
                ·
                  refine ⟨32038914355734635721581525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21359276237156423814387683 32038914355734635721581525)
                  ·
                    refine ⟨750912055212530524724567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32038914355734635721581525 750912055212530524724567)
                    ·
                      rfl

theorem cell22_2193594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 1, 1, 7].length) (baseStart_2193594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2193594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2193594 prefixEnd_2193594 := by exact prefixLift 2193594
  have htrace : WordTrace (prefixWord ++ tailWord_2193594) baseStart_2193594 baseEnd_2193594 := by
    simpa [prefixWord, tailWord_2193594, baseEnd_2193594] using wordTrace_append hprefix tailTrace_2193594
  have hstable : (prefixWord ++ tailWord_2193594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2193594).length < 2 ^ (prefixWord ++ tailWord_2193594).sum := by decide
  have hdescent : baseEnd_2193594 < baseStart_2193594 := by decide
  rcases family_descends (prefixWord ++ tailWord_2193594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2193634 : List Nat := [3, 3, 4, 1, 1, 1, 2, 1, 3, 3]
def baseStart_2193634 : Nat := 118140960795 + 2193634 * 2 ^ 59
def prefixEnd_2193634 : Nat := 4983230072969 + 3 ^ 40 * 2193634 * 2
def baseEnd_2193634 : Nat := 750925748029983753724445

theorem tailTrace_2193634 : CollatzResearch.WordTrace tailWord_2193634 prefixEnd_2193634 750925748029983753724445 := by
  unfold tailWord_2193634
  simp only [CollatzResearch.WordTrace]
  refine ⟨20002101233711533926366989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53338936623230757136978637 20002101233711533926366989)
  ·
    refine ⟨7500787962641825222387621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20002101233711533926366989 7500787962641825222387621)
    ·
      refine ⟨1406397742995342229197679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7500787962641825222387621 1406397742995342229197679)
      ·
        refine ⟨2109596614493013343796519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1406397742995342229197679 2109596614493013343796519)
        ·
          refine ⟨3164394921739520015694779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2109596614493013343796519 3164394921739520015694779)
          ·
            refine ⟨4746592382609280023542169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3164394921739520015694779 4746592382609280023542169)
            ·
              refine ⟨3559944286956960017656627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4746592382609280023542169 3559944286956960017656627)
              ·
                refine ⟨5339916430435440026484941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3559944286956960017656627 5339916430435440026484941)
                ·
                  refine ⟨2002468661413290009931853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5339916430435440026484941 2002468661413290009931853)
                  ·
                    refine ⟨750925748029983753724445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2002468661413290009931853 750925748029983753724445)
                    ·
                      rfl

theorem cell22_2193634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_2193634 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2193634 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2193634 prefixEnd_2193634 := by exact prefixLift 2193634
  have htrace : WordTrace (prefixWord ++ tailWord_2193634) baseStart_2193634 baseEnd_2193634 := by
    simpa [prefixWord, tailWord_2193634, baseEnd_2193634] using wordTrace_append hprefix tailTrace_2193634
  have hstable : (prefixWord ++ tailWord_2193634).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2193634).length < 2 ^ (prefixWord ++ tailWord_2193634).sum := by decide
  have hdescent : baseEnd_2193634 < baseStart_2193634 := by decide
  rcases family_descends (prefixWord ++ tailWord_2193634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2193735 : List Nat := [1, 1, 4, 1, 2, 2, 2, 5, 1, 3]
def baseStart_2193735 : Nat := 118140960795 + 2193735 * 2 ^ 59
def prefixEnd_2193735 : Nat := 4983230072969 + 3 ^ 40 * 2193735 * 2
def baseEnd_2193735 : Nat := 750960322394053156949135

theorem tailTrace_2193735 : CollatzResearch.WordTrace tailWord_2193735 prefixEnd_2193735 750960322394053156949135 := by
  unfold tailWord_2193735
  simp only [CollatzResearch.WordTrace]
  refine ⟨80012088707480229954894659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53341392471653486636596439 80012088707480229954894659)
  ·
    refine ⟨120018133061220344932341989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80012088707480229954894659 120018133061220344932341989)
    ·
      refine ⟨22503399948978814674814123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 120018133061220344932341989 22503399948978814674814123)
      ·
        refine ⟨33755099923468222012221185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22503399948978814674814123 33755099923468222012221185)
        ·
          refine ⟨25316324942601166509165889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33755099923468222012221185 25316324942601166509165889)
          ·
            refine ⟨18987243706950874881874417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25316324942601166509165889 18987243706950874881874417)
            ·
              refine ⟨14240432780213156161405813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18987243706950874881874417 14240432780213156161405813)
              ·
                refine ⟨1335040573144983390131795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14240432780213156161405813 1335040573144983390131795)
                ·
                  refine ⟨2002560859717475085197693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1335040573144983390131795 2002560859717475085197693)
                  ·
                    refine ⟨750960322394053156949135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2002560859717475085197693 750960322394053156949135)
                    ·
                      rfl

theorem cell22_2193735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 5, 1, 3].length) (baseStart_2193735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2193735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2193735 prefixEnd_2193735 := by exact prefixLift 2193735
  have htrace : WordTrace (prefixWord ++ tailWord_2193735) baseStart_2193735 baseEnd_2193735 := by
    simpa [prefixWord, tailWord_2193735, baseEnd_2193735] using wordTrace_append hprefix tailTrace_2193735
  have hstable : (prefixWord ++ tailWord_2193735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2193735).length < 2 ^ (prefixWord ++ tailWord_2193735).sum := by decide
  have hdescent : baseEnd_2193735 < baseStart_2193735 := by decide
  rcases family_descends (prefixWord ++ tailWord_2193735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2193748 : List Nat := [2, 4, 1, 1, 2, 2, 1, 4, 5]
def baseStart_2193748 : Nat := 118140960795 + 2193748 * 2 ^ 59
def prefixEnd_2193748 : Nat := 4983230072969 + 3 ^ 40 * 2193748 * 2
def baseEnd_2193748 : Nat := 250321590853241818791365

theorem tailTrace_2193748 : CollatzResearch.WordTrace tailWord_2193748 prefixEnd_2193748 250321590853241818791365 := by
  unfold tailWord_2193748
  simp only [CollatzResearch.WordTrace]
  refine ⟨40006281428216566587558949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53341708570955422116745265 40006281428216566587558949)
  ·
    refine ⟨7501177767790606235167303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40006281428216566587558949 7501177767790606235167303)
    ·
      refine ⟨11251766651685909352750955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7501177767790606235167303 11251766651685909352750955)
      ·
        refine ⟨16877649977528864029126433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11251766651685909352750955 16877649977528864029126433)
        ·
          refine ⟨12658237483146648021844825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16877649977528864029126433 12658237483146648021844825)
          ·
            refine ⟨9493678112359986016383619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12658237483146648021844825 9493678112359986016383619)
            ·
              refine ⟨14240517168539979024575429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9493678112359986016383619 14240517168539979024575429)
              ·
                refine ⟨2670096969101246067107893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14240517168539979024575429 2670096969101246067107893)
                ·
                  refine ⟨250321590853241818791365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2670096969101246067107893 250321590853241818791365)
                  ·
                    rfl

theorem cell22_2193748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 4, 5].length) (baseStart_2193748 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2193748 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2193748 prefixEnd_2193748 := by exact prefixLift 2193748
  have htrace : WordTrace (prefixWord ++ tailWord_2193748) baseStart_2193748 baseEnd_2193748 := by
    simpa [prefixWord, tailWord_2193748, baseEnd_2193748] using wordTrace_append hprefix tailTrace_2193748
  have hstable : (prefixWord ++ tailWord_2193748).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2193748).length < 2 ^ (prefixWord ++ tailWord_2193748).sum := by decide
  have hdescent : baseEnd_2193748 < baseStart_2193748 := by decide
  rcases family_descends (prefixWord ++ tailWord_2193748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2193776 : List Nat := [2, 1, 1, 1, 4, 3, 1, 1, 8]
def baseStart_2193776 : Nat := 118140960795 + 2193776 * 2 ^ 59
def prefixEnd_2193776 : Nat := 4983230072969 + 3 ^ 40 * 2193776 * 2
def baseEnd_2193776 : Nat := 250324785843980905558003

theorem tailTrace_2193776 : CollatzResearch.WordTrace tailWord_2193776 prefixEnd_2193776 250324785843980905558003 := by
  unfold tailWord_2193776
  simp only [CollatzResearch.WordTrace]
  refine ⟨40006792050165846978568591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53342389400221129304758121 40006792050165846978568591)
  ·
    refine ⟨60010188075248770467852887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40006792050165846978568591 60010188075248770467852887)
    ·
      refine ⟨90015282112873155701779331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60010188075248770467852887 90015282112873155701779331)
      ·
        refine ⟨135022923169309733552668997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90015282112873155701779331 135022923169309733552668997)
        ·
          refine ⟨25316798094245575041125437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 135022923169309733552668997 25316798094245575041125437)
          ·
            refine ⟨9493799285342090640422039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25316798094245575041125437 9493799285342090640422039)
            ·
              refine ⟨14240698928013135960633059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9493799285342090640422039 14240698928013135960633059)
              ·
                refine ⟨21361048392019703940949589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14240698928013135960633059 21361048392019703940949589)
                ·
                  refine ⟨250324785843980905558003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21361048392019703940949589 250324785843980905558003)
                  ·
                    rfl

theorem cell22_2193776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 1, 8].length) (baseStart_2193776 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2193776 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2193776 prefixEnd_2193776 := by exact prefixLift 2193776
  have htrace : WordTrace (prefixWord ++ tailWord_2193776) baseStart_2193776 baseEnd_2193776 := by
    simpa [prefixWord, tailWord_2193776, baseEnd_2193776] using wordTrace_append hprefix tailTrace_2193776
  have hstable : (prefixWord ++ tailWord_2193776).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2193776).length < 2 ^ (prefixWord ++ tailWord_2193776).sum := by decide
  have hdescent : baseEnd_2193776 < baseStart_2193776 := by decide
  rcases family_descends (prefixWord ++ tailWord_2193776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2193778 : List Nat := [3, 2, 1, 2, 1, 3, 2, 1, 3, 4]
def baseStart_2193778 : Nat := 118140960795 + 2193778 * 2 ^ 59
def prefixEnd_2193778 : Nat := 4983230072969 + 3 ^ 40 * 2193778 * 2
def baseEnd_2193778 : Nat := 750975042172815378124003

theorem tailTrace_2193778 : CollatzResearch.WordTrace tailWord_2193778 prefixEnd_2193778 750975042172815378124003 := by
  unfold tailWord_2193778
  simp only [CollatzResearch.WordTrace]
  refine ⟨20003414261581112074677497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53342438030882965532473325 20003414261581112074677497)
  ·
    refine ⟨15002560696185834056008123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20003414261581112074677497 15002560696185834056008123)
    ·
      refine ⟨22503841044278751084012185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15002560696185834056008123 22503841044278751084012185)
      ·
        refine ⟨16877880783209063313009139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22503841044278751084012185 16877880783209063313009139)
        ·
          refine ⟨25316821174813594969513709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16877880783209063313009139 25316821174813594969513709)
          ·
            refine ⟨9493807940555098113567641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25316821174813594969513709 9493807940555098113567641)
            ·
              refine ⟨7120355955416323585175731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9493807940555098113567641 7120355955416323585175731)
              ·
                refine ⟨10680533933124485377763597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7120355955416323585175731 10680533933124485377763597)
                ·
                  refine ⟨4005200224921682016661349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10680533933124485377763597 4005200224921682016661349)
                  ·
                    refine ⟨750975042172815378124003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4005200224921682016661349 750975042172815378124003)
                    ·
                      rfl

theorem cell22_2193778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 1, 3, 4].length) (baseStart_2193778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2193778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2193778 prefixEnd_2193778 := by exact prefixLift 2193778
  have htrace : WordTrace (prefixWord ++ tailWord_2193778) baseStart_2193778 baseEnd_2193778 := by
    simpa [prefixWord, tailWord_2193778, baseEnd_2193778] using wordTrace_append hprefix tailTrace_2193778
  have hstable : (prefixWord ++ tailWord_2193778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2193778).length < 2 ^ (prefixWord ++ tailWord_2193778).sum := by decide
  have hdescent : baseEnd_2193778 < baseStart_2193778 := by decide
  rcases family_descends (prefixWord ++ tailWord_2193778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2193795 : List Nat := [1, 1, 1, 3, 6, 1, 1, 3, 1, 4]
def baseStart_2193795 : Nat := 118140960795 + 2193795 * 2 ^ 59
def prefixEnd_2193795 : Nat := 4983230072969 + 3 ^ 40 * 2193795 * 2
def baseEnd_2193795 : Nat := 750980861620233000448951

theorem tailTrace_2193795 : CollatzResearch.WordTrace tailWord_2193795 prefixEnd_2193795 750980861620233000448951 := by
  unfold tailWord_2193795
  simp only [CollatzResearch.WordTrace]
  refine ⟨80014277087262860202078839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53342851391508573468052559 80014277087262860202078839)
  ·
    refine ⟨120021415630894290303118259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80014277087262860202078839 120021415630894290303118259)
    ·
      refine ⟨180032123446341435454677389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120021415630894290303118259 180032123446341435454677389)
      ·
        refine ⟨67512046292378038295504021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 180032123446341435454677389 67512046292378038295504021)
        ·
          refine ⟨3164627169955220545101751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 67512046292378038295504021 3164627169955220545101751)
          ·
            refine ⟨4746940754932830817652627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3164627169955220545101751 4746940754932830817652627)
            ·
              refine ⟨7120411132399246226478941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4746940754932830817652627 7120411132399246226478941)
              ·
                refine ⟨2670154174649717334929603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7120411132399246226478941 2670154174649717334929603)
                ·
                  refine ⟨4005231261974576002394405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2670154174649717334929603 4005231261974576002394405)
                  ·
                    refine ⟨750980861620233000448951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4005231261974576002394405 750980861620233000448951)
                    ·
                      rfl

theorem cell22_2193795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 3, 1, 4].length) (baseStart_2193795 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2193795 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2193795 prefixEnd_2193795 := by exact prefixLift 2193795
  have htrace : WordTrace (prefixWord ++ tailWord_2193795) baseStart_2193795 baseEnd_2193795 := by
    simpa [prefixWord, tailWord_2193795, baseEnd_2193795] using wordTrace_append hprefix tailTrace_2193795
  have hstable : (prefixWord ++ tailWord_2193795).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2193795).length < 2 ^ (prefixWord ++ tailWord_2193795).sum := by decide
  have hdescent : baseEnd_2193795 < baseStart_2193795 := by decide
  rcases family_descends (prefixWord ++ tailWord_2193795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2193836 : List Nat := [2, 2, 1, 1, 1, 1, 3, 1, 1, 9]
def baseStart_2193836 : Nat := 118140960795 + 2193836 * 2 ^ 59
def prefixEnd_2193836 : Nat := 4983230072969 + 3 ^ 40 * 2193836 * 2
def baseEnd_2193836 : Nat := 750994896758122560173825

theorem tailTrace_2193836 : CollatzResearch.WordTrace tailWord_2193836 prefixEnd_2193836 750994896758122560173825 := by
  unfold tailWord_2193836
  simp only [CollatzResearch.WordTrace]
  refine ⟨40007886240057162102160681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53343848320076216136214241 40007886240057162102160681)
  ·
    refine ⟨30005914680042871576620511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40007886240057162102160681 30005914680042871576620511)
    ·
      refine ⟨45008872020064307364930767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30005914680042871576620511 45008872020064307364930767)
      ·
        refine ⟨67513308030096461047396151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45008872020064307364930767 67513308030096461047396151)
        ·
          refine ⟨101269962045144691571094227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67513308030096461047396151 101269962045144691571094227)
          ·
            refine ⟨151904943067717037356641341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101269962045144691571094227 151904943067717037356641341)
            ·
              refine ⟨56964353650393889008740503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 151904943067717037356641341 56964353650393889008740503)
              ·
                refine ⟨85446530475590833513110755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56964353650393889008740503 85446530475590833513110755)
                ·
                  refine ⟨128169795713386250269666133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 85446530475590833513110755 128169795713386250269666133)
                  ·
                    refine ⟨750994896758122560173825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 128169795713386250269666133 750994896758122560173825)
                    ·
                      rfl

theorem cell22_2193836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 9].length) (baseStart_2193836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2193836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2193836 prefixEnd_2193836 := by exact prefixLift 2193836
  have htrace : WordTrace (prefixWord ++ tailWord_2193836) baseStart_2193836 baseEnd_2193836 := by
    simpa [prefixWord, tailWord_2193836, baseEnd_2193836] using wordTrace_append hprefix tailTrace_2193836
  have hstable : (prefixWord ++ tailWord_2193836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2193836).length < 2 ^ (prefixWord ++ tailWord_2193836).sum := by decide
  have hdescent : baseEnd_2193836 < baseStart_2193836 := by decide
  rcases family_descends (prefixWord ++ tailWord_2193836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2193851 : List Nat := [1, 1, 1, 1, 1, 2, 2, 1, 6, 6]
def baseStart_2193851 : Nat := 118140960795 + 2193851 * 2 ^ 59
def prefixEnd_2193851 : Nat := 4983230072969 + 3 ^ 40 * 2193851 * 2
def baseEnd_2193851 : Nat := 751000031564667521048779

theorem tailTrace_2193851 : CollatzResearch.WordTrace tailWord_2193851 prefixEnd_2193851 751000031564667521048779 := by
  unfold tailWord_2193851
  simp only [CollatzResearch.WordTrace]
  refine ⟨80016319575059981766117407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53344213050039987844078271 80016319575059981766117407)
  ·
    refine ⟨120024479362589972649176111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80016319575059981766117407 120024479362589972649176111)
    ·
      refine ⟨180036719043884958973764167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120024479362589972649176111 180036719043884958973764167)
      ·
        refine ⟨270055078565827438460646251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180036719043884958973764167 270055078565827438460646251)
        ·
          refine ⟨405082617848741157690969377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 270055078565827438460646251 405082617848741157690969377)
          ·
            refine ⟨303811963386555868268227033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 405082617848741157690969377 303811963386555868268227033)
            ·
              refine ⟨227858972539916901201170275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 303811963386555868268227033 227858972539916901201170275)
              ·
                refine ⟨341788458809875351801755413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 227858972539916901201170275 341788458809875351801755413)
                ·
                  refine ⟨16021334006712907115707285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 341788458809875351801755413 16021334006712907115707285)
                  ·
                    refine ⟨751000031564667521048779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16021334006712907115707285 751000031564667521048779)
                    ·
                      rfl

theorem cell22_2193851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 6, 6].length) (baseStart_2193851 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2193851 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2193851 prefixEnd_2193851 := by exact prefixLift 2193851
  have htrace : WordTrace (prefixWord ++ tailWord_2193851) baseStart_2193851 baseEnd_2193851 := by
    simpa [prefixWord, tailWord_2193851, baseEnd_2193851] using wordTrace_append hprefix tailTrace_2193851
  have hstable : (prefixWord ++ tailWord_2193851).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2193851).length < 2 ^ (prefixWord ++ tailWord_2193851).sum := by decide
  have hdescent : baseEnd_2193851 < baseStart_2193851 := by decide
  rcases family_descends (prefixWord ++ tailWord_2193851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2193921 : List Nat := [1, 2, 4, 1, 3, 3, 2, 2, 1, 3]
def baseStart_2193921 : Nat := 118140960795 + 2193921 * 2 ^ 59
def prefixEnd_2193921 : Nat := 4983230072969 + 3 ^ 40 * 2193921 * 2
def baseEnd_2193921 : Nat := 751023993995210671798565

theorem tailTrace_2193921 : CollatzResearch.WordTrace tailWord_2193921 prefixEnd_2193921 751023993995210671798565 := by
  unfold tailWord_2193921
  simp only [CollatzResearch.WordTrace]
  refine ⟨80018872684806383721165617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53345915123204255814110411 80018872684806383721165617)
  ·
    refine ⟨60014154513604787790874213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80018872684806383721165617 60014154513604787790874213)
    ·
      refine ⟨11252653971300897710788915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 60014154513604787790874213 11252653971300897710788915)
      ·
        refine ⟨16878980956951346566183373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11252653971300897710788915 16878980956951346566183373)
        ·
          refine ⟨6329617858856754962318765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16878980956951346566183373 6329617858856754962318765)
          ·
            refine ⟨2373606697071283110869537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6329617858856754962318765 2373606697071283110869537)
            ·
              refine ⟨1780205022803462333152153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2373606697071283110869537 1780205022803462333152153)
              ·
                refine ⟨1335153767102596749864115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1780205022803462333152153 1335153767102596749864115)
                ·
                  refine ⟨2002730650653895124796173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1335153767102596749864115 2002730650653895124796173)
                  ·
                    refine ⟨751023993995210671798565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2002730650653895124796173 751023993995210671798565)
                    ·
                      rfl

theorem cell22_2193921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 2, 2, 1, 3].length) (baseStart_2193921 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2193921 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2193921 prefixEnd_2193921 := by exact prefixLift 2193921
  have htrace : WordTrace (prefixWord ++ tailWord_2193921) baseStart_2193921 baseEnd_2193921 := by
    simpa [prefixWord, tailWord_2193921, baseEnd_2193921] using wordTrace_append hprefix tailTrace_2193921
  have hstable : (prefixWord ++ tailWord_2193921).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2193921).length < 2 ^ (prefixWord ++ tailWord_2193921).sum := by decide
  have hdescent : baseEnd_2193921 < baseStart_2193921 := by decide
  rcases family_descends (prefixWord ++ tailWord_2193921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2193928 : List Nat := [2, 1, 3, 2, 1, 1, 1, 5, 6]
def baseStart_2193928 : Nat := 118140960795 + 2193928 * 2 ^ 59
def prefixEnd_2193928 : Nat := 4983230072969 + 3 ^ 40 * 2193928 * 2
def baseEnd_2193928 : Nat := 250342130079421662291181

theorem tailTrace_2193928 : CollatzResearch.WordTrace tailWord_2193928 prefixEnd_2193928 250342130079421662291181 := by
  unfold tailWord_2193928
  simp only [CollatzResearch.WordTrace]
  refine ⟨40009563997890511958335219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53346085330520682611113625 40009563997890511958335219)
  ·
    refine ⟨60014345996835767937502829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40009563997890511958335219 60014345996835767937502829)
    ·
      refine ⟨22505379748813412976563561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60014345996835767937502829 22505379748813412976563561)
      ·
        refine ⟨16879034811610059732422671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22505379748813412976563561 16879034811610059732422671)
        ·
          refine ⟨25318552217415089598634007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16879034811610059732422671 25318552217415089598634007)
          ·
            refine ⟨37977828326122634397951011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25318552217415089598634007 37977828326122634397951011)
            ·
              refine ⟨56966742489183951596926517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37977828326122634397951011 56966742489183951596926517)
              ·
                refine ⟨5340632108360995462211861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 56966742489183951596926517 5340632108360995462211861)
                ·
                  refine ⟨250342130079421662291181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5340632108360995462211861 250342130079421662291181)
                  ·
                    rfl

theorem cell22_2193928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 5, 6].length) (baseStart_2193928 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2193928 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2193928 prefixEnd_2193928 := by exact prefixLift 2193928
  have htrace : WordTrace (prefixWord ++ tailWord_2193928) baseStart_2193928 baseEnd_2193928 := by
    simpa [prefixWord, tailWord_2193928, baseEnd_2193928] using wordTrace_append hprefix tailTrace_2193928
  have hstable : (prefixWord ++ tailWord_2193928).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2193928).length < 2 ^ (prefixWord ++ tailWord_2193928).sum := by decide
  have hdescent : baseEnd_2193928 < baseStart_2193928 := by decide
  rcases family_descends (prefixWord ++ tailWord_2193928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2193962 : List Nat := [3, 1, 4, 1, 1, 2, 1, 5, 4]
def baseStart_2193962 : Nat := 118140960795 + 2193962 * 2 ^ 59
def prefixEnd_2193962 : Nat := 4983230072969 + 3 ^ 40 * 2193962 * 2
def baseEnd_2193962 : Nat := 250346009711033410507813

theorem tailTrace_2193962 : CollatzResearch.WordTrace tailWord_2193962 prefixEnd_2193962 250346009711033410507813 := by
  unfold tailWord_2193962
  simp only [CollatzResearch.WordTrace]
  refine ⟨20005092019414461930852035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53346912051771898482272093 20005092019414461930852035)
  ·
    refine ⟨30007638029121692896278053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20005092019414461930852035 30007638029121692896278053)
    ·
      refine ⟨5626432130460317418052135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30007638029121692896278053 5626432130460317418052135)
      ·
        refine ⟨8439648195690476127078203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5626432130460317418052135 8439648195690476127078203)
        ·
          refine ⟨12659472293535714190617305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8439648195690476127078203 12659472293535714190617305)
          ·
            refine ⟨9494604220151785642962979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12659472293535714190617305 9494604220151785642962979)
            ·
              refine ⟨14241906330227678464444469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9494604220151785642962979 14241906330227678464444469)
              ·
                refine ⟨1335178718458844856041669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14241906330227678464444469 1335178718458844856041669)
                ·
                  refine ⟨250346009711033410507813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1335178718458844856041669 250346009711033410507813)
                  ·
                    rfl

theorem cell22_2193962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 5, 4].length) (baseStart_2193962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2193962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2193962 prefixEnd_2193962 := by exact prefixLift 2193962
  have htrace : WordTrace (prefixWord ++ tailWord_2193962) baseStart_2193962 baseEnd_2193962 := by
    simpa [prefixWord, tailWord_2193962, baseEnd_2193962] using wordTrace_append hprefix tailTrace_2193962
  have hstable : (prefixWord ++ tailWord_2193962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2193962).length < 2 ^ (prefixWord ++ tailWord_2193962).sum := by decide
  have hdescent : baseEnd_2193962 < baseStart_2193962 := by decide
  rcases family_descends (prefixWord ++ tailWord_2193962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2193973 : List Nat := [1, 3, 3, 1, 1, 2, 11]
def baseStart_2193973 : Nat := 118140960795 + 2193973 * 2 ^ 59
def prefixEnd_2193973 : Nat := 4983230072969 + 3 ^ 40 * 2193973 * 2
def baseEnd_2193973 : Nat := 27816362765107402574015

theorem tailTrace_2193973 : CollatzResearch.WordTrace tailWord_2193973 prefixEnd_2193973 27816362765107402574015 := by
  unfold tailWord_2193973
  simp only [CollatzResearch.WordTrace]
  refine ⟨80020769280617996602058573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53347179520411997734705715 80020769280617996602058573)
  ·
    refine ⟨30007788480231748725771965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80020769280617996602058573 30007788480231748725771965)
    ·
      refine ⟨11252920680086905772164487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30007788480231748725771965 11252920680086905772164487)
      ·
        refine ⟨16879381020130358658246731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11252920680086905772164487 16879381020130358658246731)
        ·
          refine ⟨25319071530195537987370097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16879381020130358658246731 25319071530195537987370097)
          ·
            refine ⟨18989303647646653490527573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25319071530195537987370097 18989303647646653490527573)
            ·
              refine ⟨27816362765107402574015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 18989303647646653490527573 27816362765107402574015)
              ·
                rfl

theorem cell22_2193973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 11].length) (baseStart_2193973 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2193973 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2193973 prefixEnd_2193973 := by exact prefixLift 2193973
  have htrace : WordTrace (prefixWord ++ tailWord_2193973) baseStart_2193973 baseEnd_2193973 := by
    simpa [prefixWord, tailWord_2193973, baseEnd_2193973] using wordTrace_append hprefix tailTrace_2193973
  have hstable : (prefixWord ++ tailWord_2193973).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2193973).length < 2 ^ (prefixWord ++ tailWord_2193973).sum := by decide
  have hdescent : baseEnd_2193973 < baseStart_2193973 := by decide
  rcases family_descends (prefixWord ++ tailWord_2193973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2193994 : List Nat := [3, 1, 2, 1, 1, 5, 3, 1, 2, 3]
def baseStart_2193994 : Nat := 118140960795 + 2193994 * 2 ^ 59
def prefixEnd_2193994 : Nat := 4983230072969 + 3 ^ 40 * 2193994 * 2
def baseEnd_2193994 : Nat := 751048983387062814723341

theorem tailTrace_2193994 : CollatzResearch.WordTrace tailWord_2193994 prefixEnd_2193994 751048983387062814723341 := by
  unfold tailWord_2193994
  simp only [CollatzResearch.WordTrace]
  refine ⟨20005383803385479297143259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53347690142361278125715357 20005383803385479297143259)
  ·
    refine ⟨30008075705078218945714889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20005383803385479297143259 30008075705078218945714889)
    ·
      refine ⟨22506056778808664209286167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30008075705078218945714889 22506056778808664209286167)
      ·
        refine ⟨33759085168212996313929251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22506056778808664209286167 33759085168212996313929251)
        ·
          refine ⟨50638627752319494470893877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33759085168212996313929251 50638627752319494470893877)
          ·
            refine ⟨4747371351779952606646301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 50638627752319494470893877 4747371351779952606646301)
            ·
              refine ⟨1780264256917482227492363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4747371351779952606646301 1780264256917482227492363)
              ·
                refine ⟨2670396385376223341238545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1780264256917482227492363 2670396385376223341238545)
                ·
                  refine ⟨2002797289032167505928909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2670396385376223341238545 2002797289032167505928909)
                  ·
                    refine ⟨751048983387062814723341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2002797289032167505928909 751048983387062814723341)
                    ·
                      rfl

theorem cell22_2193994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 3, 1, 2, 3].length) (baseStart_2193994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2193994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2193994 prefixEnd_2193994 := by exact prefixLift 2193994
  have htrace : WordTrace (prefixWord ++ tailWord_2193994) baseStart_2193994 baseEnd_2193994 := by
    simpa [prefixWord, tailWord_2193994, baseEnd_2193994] using wordTrace_append hprefix tailTrace_2193994
  have hstable : (prefixWord ++ tailWord_2193994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2193994).length < 2 ^ (prefixWord ++ tailWord_2193994).sum := by decide
  have hdescent : baseEnd_2193994 < baseStart_2193994 := by decide
  rcases family_descends (prefixWord ++ tailWord_2193994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2194052 : List Nat := [2, 3, 2, 1, 3, 2, 1, 3, 5]
def baseStart_2194052 : Nat := 118140960795 + 2194052 * 2 ^ 59
def prefixEnd_2194052 : Nat := 4983230072969 + 3 ^ 40 * 2194052 * 2
def baseEnd_2194052 : Nat := 250356279324123332257721

theorem tailTrace_2194052 : CollatzResearch.WordTrace tailWord_2194052 prefixEnd_2194052 250356279324123332257721 := by
  unfold tailWord_2194052
  simp only [CollatzResearch.WordTrace]
  refine ⟨40011825323665896547092205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53349100431554528729456273 40011825323665896547092205)
  ·
    refine ⟨15004434496374711205159577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40011825323665896547092205 15004434496374711205159577)
    ·
      refine ⟨11253325872281033403869683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15004434496374711205159577 11253325872281033403869683)
      ·
        refine ⟨16879988808421550105804525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11253325872281033403869683 16879988808421550105804525)
        ·
          refine ⟨6329995803158081289676697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16879988808421550105804525 6329995803158081289676697)
          ·
            refine ⟨4747496852368560967257523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6329995803158081289676697 4747496852368560967257523)
            ·
              refine ⟨7121245278552841450886285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4747496852368560967257523 7121245278552841450886285)
              ·
                refine ⟨2670466979457315544082357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7121245278552841450886285 2670466979457315544082357)
                ·
                  refine ⟨250356279324123332257721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2670466979457315544082357 250356279324123332257721)
                  ·
                    rfl

theorem cell22_2194052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 3, 5].length) (baseStart_2194052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2194052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2194052 prefixEnd_2194052 := by exact prefixLift 2194052
  have htrace : WordTrace (prefixWord ++ tailWord_2194052) baseStart_2194052 baseEnd_2194052 := by
    simpa [prefixWord, tailWord_2194052, baseEnd_2194052] using wordTrace_append hprefix tailTrace_2194052
  have hstable : (prefixWord ++ tailWord_2194052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2194052).length < 2 ^ (prefixWord ++ tailWord_2194052).sum := by decide
  have hdescent : baseEnd_2194052 < baseStart_2194052 := by decide
  rcases family_descends (prefixWord ++ tailWord_2194052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2194112 : List Nat := [2, 1, 1, 2, 4, 3, 2, 1, 1, 5]
def baseStart_2194112 : Nat := 118140960795 + 2194112 * 2 ^ 59
def prefixEnd_2194112 : Nat := 4983230072969 + 3 ^ 40 * 2194112 * 2
def baseEnd_2194112 : Nat := 751089377198549840272979

theorem tailTrace_2194112 : CollatzResearch.WordTrace tailWord_2194112 prefixEnd_2194112 751089377198549840272979 := by
  unfold tailWord_2194112
  simp only [CollatzResearch.WordTrace]
  refine ⟨40012919513557211670684295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53350559351409615560912393 40012919513557211670684295)
  ·
    refine ⟨60019379270335817506026443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40012919513557211670684295 60019379270335817506026443)
    ·
      refine ⟨90029068905503726259039665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60019379270335817506026443 90029068905503726259039665)
      ·
        refine ⟨67521801679127794694279749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90029068905503726259039665 67521801679127794694279749)
        ·
          refine ⟨12660337814836461505177453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 67521801679127794694279749 12660337814836461505177453)
          ·
            refine ⟨4747626680563673064441545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12660337814836461505177453 4747626680563673064441545)
            ·
              refine ⟨3560720010422754798331159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4747626680563673064441545 3560720010422754798331159)
              ·
                refine ⟨5341080015634132197496739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3560720010422754798331159 5341080015634132197496739)
                ·
                  refine ⟨8011620023451198296245109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5341080015634132197496739 8011620023451198296245109)
                  ·
                    refine ⟨751089377198549840272979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8011620023451198296245109 751089377198549840272979)
                    ·
                      rfl

theorem cell22_2194112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 2, 1, 1, 5].length) (baseStart_2194112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2194112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2194112 prefixEnd_2194112 := by exact prefixLift 2194112
  have htrace : WordTrace (prefixWord ++ tailWord_2194112) baseStart_2194112 baseEnd_2194112 := by
    simpa [prefixWord, tailWord_2194112, baseEnd_2194112] using wordTrace_append hprefix tailTrace_2194112
  have hstable : (prefixWord ++ tailWord_2194112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2194112).length < 2 ^ (prefixWord ++ tailWord_2194112).sum := by decide
  have hdescent : baseEnd_2194112 < baseStart_2194112 := by decide
  rcases family_descends (prefixWord ++ tailWord_2194112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2194133 : List Nat := [1, 3, 2, 5, 1, 2, 2, 1, 1, 4]
def baseStart_2194133 : Nat := 118140960795 + 2194133 * 2 ^ 59
def prefixEnd_2194133 : Nat := 4983230072969 + 3 ^ 40 * 2194133 * 2
def baseEnd_2194133 : Nat := 751096565927712785497915

theorem tailTrace_2194133 : CollatzResearch.WordTrace tailWord_2194133 prefixEnd_2194133 751096565927712785497915 := by
  unfold tailWord_2194133
  simp only [CollatzResearch.WordTrace]
  refine ⟨80026604960038343927883053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53351069973358895951922035 80026604960038343927883053)
  ·
    refine ⟨30009976860014378972956145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80026604960038343927883053 30009976860014378972956145)
    ·
      refine ⟨22507482645010784229717109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30009976860014378972956145 22507482645010784229717109)
      ·
        refine ⟨2110076497969761021535979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 22507482645010784229717109 2110076497969761021535979)
        ·
          refine ⟨3165114746954641532303969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2110076497969761021535979 3165114746954641532303969)
          ·
            refine ⟨2373836060215981149227977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3165114746954641532303969 2373836060215981149227977)
            ·
              refine ⟨1780377045161985861920983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2373836060215981149227977 1780377045161985861920983)
              ·
                refine ⟨2670565567742978792881475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1780377045161985861920983 2670565567742978792881475)
                ·
                  refine ⟨4005848351614468189322213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2670565567742978792881475 4005848351614468189322213)
                  ·
                    refine ⟨751096565927712785497915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4005848351614468189322213 751096565927712785497915)
                    ·
                      rfl

theorem cell22_2194133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 2, 1, 1, 4].length) (baseStart_2194133 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2194133 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2194133 prefixEnd_2194133 := by exact prefixLift 2194133
  have htrace : WordTrace (prefixWord ++ tailWord_2194133) baseStart_2194133 baseEnd_2194133 := by
    simpa [prefixWord, tailWord_2194133, baseEnd_2194133] using wordTrace_append hprefix tailTrace_2194133
  have hstable : (prefixWord ++ tailWord_2194133).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2194133).length < 2 ^ (prefixWord ++ tailWord_2194133).sum := by decide
  have hdescent : baseEnd_2194133 < baseStart_2194133 := by decide
  rcases family_descends (prefixWord ++ tailWord_2194133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2194185 : List Nat := [1, 2, 1, 1, 3, 2, 2, 2, 1, 7]
def baseStart_2194185 : Nat := 118140960795 + 2194185 * 2 ^ 59
def prefixEnd_2194185 : Nat := 4983230072969 + 3 ^ 40 * 2194185 * 2
def baseEnd_2194185 : Nat := 751114366590401983197755

theorem tailTrace_2194185 : CollatzResearch.WordTrace tailWord_2194185 prefixEnd_2194185 751114366590401983197755 := by
  unfold tailWord_2194185
  simp only [CollatzResearch.WordTrace]
  refine ⟨80028501555849956808776009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53352334370566637872517339 80028501555849956808776009)
  ·
    refine ⟨60021376166887467606582007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80028501555849956808776009 60021376166887467606582007)
    ·
      refine ⟨90032064250331201409873011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60021376166887467606582007 90032064250331201409873011)
      ·
        refine ⟨135048096375496802114809517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90032064250331201409873011 135048096375496802114809517)
        ·
          refine ⟨50643036140811300793053569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 135048096375496802114809517 50643036140811300793053569)
          ·
            refine ⟨37982277105608475594790177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50643036140811300793053569 37982277105608475594790177)
            ·
              refine ⟨28486707829206356696092633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37982277105608475594790177 28486707829206356696092633)
              ·
                refine ⟨21365030871904767522069475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28486707829206356696092633 21365030871904767522069475)
                ·
                  refine ⟨32047546307857151283104213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21365030871904767522069475 32047546307857151283104213)
                  ·
                    refine ⟨751114366590401983197755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32047546307857151283104213 751114366590401983197755)
                    ·
                      rfl

theorem cell22_2194185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 2, 1, 7].length) (baseStart_2194185 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2194185 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2194185 prefixEnd_2194185 := by exact prefixLift 2194185
  have htrace : WordTrace (prefixWord ++ tailWord_2194185) baseStart_2194185 baseEnd_2194185 := by
    simpa [prefixWord, tailWord_2194185, baseEnd_2194185] using wordTrace_append hprefix tailTrace_2194185
  have hstable : (prefixWord ++ tailWord_2194185).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2194185).length < 2 ^ (prefixWord ++ tailWord_2194185).sum := by decide
  have hdescent : baseEnd_2194185 < baseStart_2194185 := by decide
  rcases family_descends (prefixWord ++ tailWord_2194185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2194208 : List Nat := [2, 1, 1, 5, 1, 3, 3, 2, 1, 3]
def baseStart_2194208 : Nat := 118140960795 + 2194208 * 2 ^ 59
def prefixEnd_2194208 : Nat := 4983230072969 + 3 ^ 40 * 2194208 * 2
def baseEnd_2194208 : Nat := 751122239960437589872685

theorem tailTrace_2194208 : CollatzResearch.WordTrace tailWord_2194208 prefixEnd_2194208 751122239960437589872685 := by
  unfold tailWord_2194208
  simp only [CollatzResearch.WordTrace]
  refine ⟨40014670217383315868431639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53352893623177754491242185 40014670217383315868431639)
  ·
    refine ⟨60022005326074973802647459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40014670217383315868431639 60022005326074973802647459)
    ·
      refine ⟨90033007989112460703971189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60022005326074973802647459 90033007989112460703971189)
      ·
        refine ⟨8440594498979293190997299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 90033007989112460703971189 8440594498979293190997299)
        ·
          refine ⟨12660891748468939786495949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8440594498979293190997299 12660891748468939786495949)
          ·
            refine ⟨4747834405675852419935981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12660891748468939786495949 4747834405675852419935981)
            ·
              refine ⟨1780437902128444657475993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4747834405675852419935981 1780437902128444657475993)
              ·
                refine ⟨1335328426596333493106995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1780437902128444657475993 1335328426596333493106995)
                ·
                  refine ⟨2002992639894500239660493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1335328426596333493106995 2002992639894500239660493)
                  ·
                    refine ⟨751122239960437589872685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2002992639894500239660493 751122239960437589872685)
                    ·
                      rfl

theorem cell22_2194208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 3, 2, 1, 3].length) (baseStart_2194208 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2194208 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2194208 prefixEnd_2194208 := by exact prefixLift 2194208
  have htrace : WordTrace (prefixWord ++ tailWord_2194208) baseStart_2194208 baseEnd_2194208 := by
    simpa [prefixWord, tailWord_2194208, baseEnd_2194208] using wordTrace_append hprefix tailTrace_2194208
  have hstable : (prefixWord ++ tailWord_2194208).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2194208).length < 2 ^ (prefixWord ++ tailWord_2194208).sum := by decide
  have hdescent : baseEnd_2194208 < baseStart_2194208 := by decide
  rcases family_descends (prefixWord ++ tailWord_2194208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2194234 : List Nat := [3, 1, 1, 1, 6, 1, 1, 1, 3, 4]
def baseStart_2194234 : Nat := 118140960795 + 2194234 * 2 ^ 59
def prefixEnd_2194234 : Nat := 4983230072969 + 3 ^ 40 * 2194234 * 2
def baseEnd_2194234 : Nat := 751131140291782188722605

theorem tailTrace_2194234 : CollatzResearch.WordTrace tailWord_2194234 prefixEnd_2194234 751131140291782188722605 := by
  unfold tailWord_2194234
  simp only [CollatzResearch.WordTrace]
  refine ⟨20007572183168109544327439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53353525821781625451539837 20007572183168109544327439)
  ·
    refine ⟨30011358274752164316491159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20007572183168109544327439 30011358274752164316491159)
    ·
      refine ⟨45017037412128246474736739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30011358274752164316491159 45017037412128246474736739)
      ·
        refine ⟨67525556118192369712105109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45017037412128246474736739 67525556118192369712105109)
        ·
          refine ⟨3165260443040267330254927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 67525556118192369712105109 3165260443040267330254927)
          ·
            refine ⟨4747890664560400995382391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3165260443040267330254927 4747890664560400995382391)
            ·
              refine ⟨7121835996840601493073587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4747890664560400995382391 7121835996840601493073587)
              ·
                refine ⟨10682753995260902239610381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7121835996840601493073587 10682753995260902239610381)
                ·
                  refine ⟨4006032748222838339853893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10682753995260902239610381 4006032748222838339853893)
                  ·
                    refine ⟨751131140291782188722605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4006032748222838339853893 751131140291782188722605)
                    ·
                      rfl

theorem cell22_2194234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 1, 3, 4].length) (baseStart_2194234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2194234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2194234 prefixEnd_2194234 := by exact prefixLift 2194234
  have htrace : WordTrace (prefixWord ++ tailWord_2194234) baseStart_2194234 baseEnd_2194234 := by
    simpa [prefixWord, tailWord_2194234, baseEnd_2194234] using wordTrace_append hprefix tailTrace_2194234
  have hstable : (prefixWord ++ tailWord_2194234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2194234).length < 2 ^ (prefixWord ++ tailWord_2194234).sum := by decide
  have hdescent : baseEnd_2194234 < baseStart_2194234 := by decide
  rcases family_descends (prefixWord ++ tailWord_2194234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2194266 : List Nat := [3, 1, 1, 2, 1, 4, 4, 2, 4]
def baseStart_2194266 : Nat := 118140960795 + 2194266 * 2 ^ 59
def prefixEnd_2194266 : Nat := 4983230072969 + 3 ^ 40 * 2194266 * 2
def baseEnd_2194266 : Nat := 250380698181914923974169

theorem tailTrace_2194266 : CollatzResearch.WordTrace tailWord_2194266 prefixEnd_2194266 250380698181914923974169 := by
  unfold tailWord_2194266
  simp only [CollatzResearch.WordTrace]
  refine ⟨20007863967139126910618663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53354303912371005094983101 20007863967139126910618663)
  ·
    refine ⟨30011795950708690365927995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20007863967139126910618663 30011795950708690365927995)
    ·
      refine ⟨45017693926063035548891993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30011795950708690365927995 45017693926063035548891993)
      ·
        refine ⟨33763270444547276661668995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45017693926063035548891993 33763270444547276661668995)
        ·
          refine ⟨50644905666820914992503493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33763270444547276661668995 50644905666820914992503493)
          ·
            refine ⟨9495919812528921561094405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50644905666820914992503493 9495919812528921561094405)
            ·
              refine ⟨1780484964849172792705201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9495919812528921561094405 1780484964849172792705201)
              ·
                refine ⟨1335363723636879594528901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1780484964849172792705201 1335363723636879594528901)
                ·
                  refine ⟨250380698181914923974169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1335363723636879594528901 250380698181914923974169)
                  ·
                    rfl

theorem cell22_2194266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 4, 2, 4].length) (baseStart_2194266 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2194266 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2194266 prefixEnd_2194266 := by exact prefixLift 2194266
  have htrace : WordTrace (prefixWord ++ tailWord_2194266) baseStart_2194266 baseEnd_2194266 := by
    simpa [prefixWord, tailWord_2194266, baseEnd_2194266] using wordTrace_append hprefix tailTrace_2194266
  have hstable : (prefixWord ++ tailWord_2194266).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2194266).length < 2 ^ (prefixWord ++ tailWord_2194266).sum := by decide
  have hdescent : baseEnd_2194266 < baseStart_2194266 := by decide
  rcases family_descends (prefixWord ++ tailWord_2194266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2194277 : List Nat := [1, 3, 1, 3, 1, 1, 5, 7]
def baseStart_2194277 : Nat := 118140960795 + 2194277 * 2 ^ 59
def prefixEnd_2194277 : Nat := 4983230072969 + 3 ^ 40 * 2194277 * 2
def baseEnd_2194277 : Nat := 83460651118949378877497

theorem tailTrace_2194277 : CollatzResearch.WordTrace tailWord_2194277 prefixEnd_2194277 83460651118949378877497 := by
  unfold tailWord_2194277
  simp only [CollatzResearch.WordTrace]
  refine ⟨80031857071516656521125085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53354571381011104347416723 80031857071516656521125085)
  ·
    refine ⟨30011946401818746195421907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80031857071516656521125085 30011946401818746195421907)
    ·
      refine ⟨45017919602728119293132861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30011946401818746195421907 45017919602728119293132861)
      ·
        refine ⟨16881719851023044734924823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45017919602728119293132861 16881719851023044734924823)
        ·
          refine ⟨25322579776534567102387235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16881719851023044734924823 25322579776534567102387235)
          ·
            refine ⟨37983869664801850653580853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25322579776534567102387235 37983869664801850653580853)
            ·
              refine ⟨3560987781075173498773205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 37983869664801850653580853 3560987781075173498773205)
              ·
                refine ⟨83460651118949378877497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3560987781075173498773205 83460651118949378877497)
                ·
                  rfl

theorem cell22_2194277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 5, 7].length) (baseStart_2194277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2194277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2194277 prefixEnd_2194277 := by exact prefixLift 2194277
  have htrace : WordTrace (prefixWord ++ tailWord_2194277) baseStart_2194277 baseEnd_2194277 := by
    simpa [prefixWord, tailWord_2194277, baseEnd_2194277] using wordTrace_append hprefix tailTrace_2194277
  have hstable : (prefixWord ++ tailWord_2194277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2194277).length < 2 ^ (prefixWord ++ tailWord_2194277).sum := by decide
  have hdescent : baseEnd_2194277 < baseStart_2194277 := by decide
  rcases family_descends (prefixWord ++ tailWord_2194277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2194302 : List Nat := [4, 2, 3, 1, 3, 1, 2, 1, 1, 4]
def baseStart_2194302 : Nat := 118140960795 + 2194302 * 2 ^ 59
def prefixEnd_2194302 : Nat := 4983230072969 + 3 ^ 40 * 2194302 * 2
def baseEnd_2194302 : Nat := 751154418081452678022397

theorem tailTrace_2194302 : CollatzResearch.WordTrace tailWord_2194302 prefixEnd_2194302 751154418081452678022397 := by
  unfold tailWord_2194302
  simp only [CollatzResearch.WordTrace]
  refine ⟨10004096112053260723848145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53355179264284057193856773 10004096112053260723848145)
  ·
    refine ⟨7503072084039945542886109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10004096112053260723848145 7503072084039945542886109)
    ·
      refine ⟨2813652031514979578582291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7503072084039945542886109 2813652031514979578582291)
      ·
        refine ⟨4220478047272469367873437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2813652031514979578582291 4220478047272469367873437)
        ·
          refine ⟨1582679267727176012952539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4220478047272469367873437 1582679267727176012952539)
          ·
            refine ⟨2374018901590764019428809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1582679267727176012952539 2374018901590764019428809)
            ·
              refine ⟨1780514176193073014571607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2374018901590764019428809 1780514176193073014571607)
              ·
                refine ⟨2670771264289609521857411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1780514176193073014571607 2670771264289609521857411)
                ·
                  refine ⟨4006156896434414282786117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2670771264289609521857411 4006156896434414282786117)
                  ·
                    refine ⟨751154418081452678022397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4006156896434414282786117 751154418081452678022397)
                    ·
                      rfl

theorem cell22_2194302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 2, 1, 1, 4].length) (baseStart_2194302 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2194302 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2194302 prefixEnd_2194302 := by exact prefixLift 2194302
  have htrace : WordTrace (prefixWord ++ tailWord_2194302) baseStart_2194302 baseEnd_2194302 := by
    simpa [prefixWord, tailWord_2194302, baseEnd_2194302] using wordTrace_append hprefix tailTrace_2194302
  have hstable : (prefixWord ++ tailWord_2194302).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2194302).length < 2 ^ (prefixWord ++ tailWord_2194302).sum := by decide
  have hdescent : baseEnd_2194302 < baseStart_2194302 := by decide
  rcases family_descends (prefixWord ++ tailWord_2194302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2194356 : List Nat := [2, 5, 2, 1, 1, 1, 1, 2, 7]
def baseStart_2194356 : Nat := 118140960795 + 2194356 * 2 ^ 59
def prefixEnd_2194356 : Nat := 4983230072969 + 3 ^ 40 * 2194356 * 2
def baseEnd_2194356 : Nat := 250390967795004845724077

theorem tailTrace_2194356 : CollatzResearch.WordTrace tailWord_2194356 prefixEnd_2194356 250390967795004845724077 := by
  unfold tailWord_2194356
  simp only [CollatzResearch.WordTrace]
  refine ⟨40017369219115226506625461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53356492292153635342167281 40017369219115226506625461)
  ·
    refine ⟨3751628364292052484996137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 40017369219115226506625461 3751628364292052484996137)
    ·
      refine ⟨2813721273219039363747103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3751628364292052484996137 2813721273219039363747103)
      ·
        refine ⟨4220581909828559045620655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2813721273219039363747103 4220581909828559045620655)
        ·
          refine ⟨6330872864742838568430983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4220581909828559045620655 6330872864742838568430983)
          ·
            refine ⟨9496309297114257852646475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6330872864742838568430983 9496309297114257852646475)
            ·
              refine ⟨14244463945671386778969713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9496309297114257852646475 14244463945671386778969713)
              ·
                refine ⟨10683347959253540084227285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14244463945671386778969713 10683347959253540084227285)
                ·
                  refine ⟨250390967795004845724077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10683347959253540084227285 250390967795004845724077)
                  ·
                    rfl

theorem cell22_2194356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 2, 7].length) (baseStart_2194356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2194356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2194356 prefixEnd_2194356 := by exact prefixLift 2194356
  have htrace : WordTrace (prefixWord ++ tailWord_2194356) baseStart_2194356 baseEnd_2194356 := by
    simpa [prefixWord, tailWord_2194356, baseEnd_2194356] using wordTrace_append hprefix tailTrace_2194356
  have hstable : (prefixWord ++ tailWord_2194356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2194356).length < 2 ^ (prefixWord ++ tailWord_2194356).sum := by decide
  have hdescent : baseEnd_2194356 < baseStart_2194356 := by decide
  rcases family_descends (prefixWord ++ tailWord_2194356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2194390 : List Nat := [5, 2, 1, 1, 2, 3, 2, 1, 5]
def baseStart_2194390 : Nat := 118140960795 + 2194390 * 2 ^ 59
def prefixEnd_2194390 : Nat := 4983230072969 + 3 ^ 40 * 2194390 * 2
def baseEnd_2194390 : Nat := 250394847426616593940709

theorem tailTrace_2194390 : CollatzResearch.WordTrace tailWord_2194390 prefixEnd_2194390 250394847426616593940709 := by
  unfold tailWord_2194390
  simp only [CollatzResearch.WordTrace]
  refine ⟨5002248657506704801249289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 53357319013404851213325749 5002248657506704801249289)
  ·
    refine ⟨3751686493130028600936967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5002248657506704801249289 3751686493130028600936967)
    ·
      refine ⟨5627529739695042901405451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3751686493130028600936967 5627529739695042901405451)
      ·
        refine ⟨8441294609542564352108177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5627529739695042901405451 8441294609542564352108177)
        ·
          refine ⟨6330970957156923264081133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8441294609542564352108177 6330970957156923264081133)
          ·
            refine ⟨2374114108933846224030425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6330970957156923264081133 2374114108933846224030425)
            ·
              refine ⟨1780585581700384668022819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2374114108933846224030425 1780585581700384668022819)
              ·
                refine ⟨2670878372550577002034229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1780585581700384668022819 2670878372550577002034229)
                ·
                  refine ⟨250394847426616593940709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2670878372550577002034229 250394847426616593940709)
                  ·
                    rfl

theorem cell22_2194390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 2, 1, 5].length) (baseStart_2194390 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2194390 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2194390 prefixEnd_2194390 := by exact prefixLift 2194390
  have htrace : WordTrace (prefixWord ++ tailWord_2194390) baseStart_2194390 baseEnd_2194390 := by
    simpa [prefixWord, tailWord_2194390, baseEnd_2194390] using wordTrace_append hprefix tailTrace_2194390
  have hstable : (prefixWord ++ tailWord_2194390).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2194390).length < 2 ^ (prefixWord ++ tailWord_2194390).sum := by decide
  have hdescent : baseEnd_2194390 < baseStart_2194390 := by decide
  rcases family_descends (prefixWord ++ tailWord_2194390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2194433 : List Nat := [1, 2, 4, 1, 2, 3, 2, 2, 2, 3]
def baseStart_2194433 : Nat := 118140960795 + 2194433 * 2 ^ 59
def prefixEnd_2194433 : Nat := 4983230072969 + 3 ^ 40 * 2194433 * 2
def baseEnd_2194433 : Nat := 751199262058612002996995

theorem tailTrace_2194433 : CollatzResearch.WordTrace tailWord_2194433 prefixEnd_2194433 751199262058612002996995 := by
  unfold tailWord_2194433
  simp only [CollatzResearch.WordTrace]
  refine ⟨80037546858951495163803953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53358364572634330109202635 80037546858951495163803953)
  ·
    refine ⟨60028160144213621372852965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80037546858951495163803953 60028160144213621372852965)
    ·
      refine ⟨11255280027040054007409931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 60028160144213621372852965 11255280027040054007409931)
      ·
        refine ⟨16882920040560081011114897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11255280027040054007409931 16882920040560081011114897)
        ·
          refine ⟨12662190030420060758336173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16882920040560081011114897 12662190030420060758336173)
          ·
            refine ⟨4748321261407522784376065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12662190030420060758336173 4748321261407522784376065)
            ·
              refine ⟨3561240946055642088282049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4748321261407522784376065 3561240946055642088282049)
              ·
                refine ⟨2670930709541731566211537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3561240946055642088282049 2670930709541731566211537)
                ·
                  refine ⟨2003198032156298674658653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2670930709541731566211537 2003198032156298674658653)
                  ·
                    refine ⟨751199262058612002996995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2003198032156298674658653 751199262058612002996995)
                    ·
                      rfl

theorem cell22_2194433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 2, 2, 2, 3].length) (baseStart_2194433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2194433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2194433 prefixEnd_2194433 := by exact prefixLift 2194433
  have htrace : WordTrace (prefixWord ++ tailWord_2194433) baseStart_2194433 baseEnd_2194433 := by
    simpa [prefixWord, tailWord_2194433, baseEnd_2194433] using wordTrace_append hprefix tailTrace_2194433
  have hstable : (prefixWord ++ tailWord_2194433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2194433).length < 2 ^ (prefixWord ++ tailWord_2194433).sum := by decide
  have hdescent : baseEnd_2194433 < baseStart_2194433 := by decide
  rcases family_descends (prefixWord ++ tailWord_2194433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2194446 : List Nat := [4, 1, 1, 2, 2, 4, 1, 7]
def baseStart_2194446 : Nat := 118140960795 + 2194446 * 2 ^ 59
def prefixEnd_2194446 : Nat := 4983230072969 + 3 ^ 40 * 2194446 * 2
def baseEnd_2194446 : Nat := 83467079136031589157995

theorem tailTrace_2194446 : CollatzResearch.WordTrace tailWord_2194446 prefixEnd_2194446 83467079136031589157995 := by
  unfold tailWord_2194446
  simp only [CollatzResearch.WordTrace]
  refine ⟨10004752625988049798003399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53358680671936265589351461 10004752625988049798003399)
  ·
    refine ⟨15007128938982074697005099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10004752625988049798003399 15007128938982074697005099)
    ·
      refine ⟨22510693408473112045507649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15007128938982074697005099 22510693408473112045507649)
      ·
        refine ⟨16883020056354834034130737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22510693408473112045507649 16883020056354834034130737)
        ·
          refine ⟨12662265042266125525598053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16883020056354834034130737 12662265042266125525598053)
          ·
            refine ⟨2374174695424898536049635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12662265042266125525598053 2374174695424898536049635)
            ·
              refine ⟨3561262043137347804074453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2374174695424898536049635 3561262043137347804074453)
              ·
                refine ⟨83467079136031589157995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3561262043137347804074453 83467079136031589157995)
                ·
                  rfl

theorem cell22_2194446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 1, 7].length) (baseStart_2194446 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2194446 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2194446 prefixEnd_2194446 := by exact prefixLift 2194446
  have htrace : WordTrace (prefixWord ++ tailWord_2194446) baseStart_2194446 baseEnd_2194446 := by
    simpa [prefixWord, tailWord_2194446, baseEnd_2194446] using wordTrace_append hprefix tailTrace_2194446
  have hstable : (prefixWord ++ tailWord_2194446).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2194446).length < 2 ^ (prefixWord ++ tailWord_2194446).sum := by decide
  have hdescent : baseEnd_2194446 < baseStart_2194446 := by decide
  rcases family_descends (prefixWord ++ tailWord_2194446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2194538 : List Nat := [3, 1, 3, 2, 2, 1, 2, 3, 1, 4]
def baseStart_2194538 : Nat := 118140960795 + 2194538 * 2 ^ 59
def prefixEnd_2194538 : Nat := 4983230072969 + 3 ^ 40 * 2194538 * 2
def baseEnd_2194538 : Nat := 751235205704426729121673

theorem tailTrace_2194538 : CollatzResearch.WordTrace tailWord_2194538 prefixEnd_2194538 751235205704426729121673 := by
  unfold tailWord_2194538
  simp only [CollatzResearch.WordTrace]
  refine ⟨20010344130892774524094067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53360917682380732064250845 20010344130892774524094067)
  ·
    refine ⟨30015516196339161786141101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20010344130892774524094067 30015516196339161786141101)
    ·
      refine ⟨11255818573627185669802913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30015516196339161786141101 11255818573627185669802913)
      ·
        refine ⟨8441863930220389252352185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11255818573627185669802913 8441863930220389252352185)
        ·
          refine ⟨6331397947665291939264139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8441863930220389252352185 6331397947665291939264139)
          ·
            refine ⟨9497096921497937908896209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6331397947665291939264139 9497096921497937908896209)
            ·
              refine ⟨7122822691123453431672157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9497096921497937908896209 7122822691123453431672157)
              ·
                refine ⟨2671058509171295036877059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7122822691123453431672157 2671058509171295036877059)
                ·
                  refine ⟨4006587763756942555315589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2671058509171295036877059 4006587763756942555315589)
                  ·
                    refine ⟨751235205704426729121673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4006587763756942555315589 751235205704426729121673)
                    ·
                      rfl

theorem cell22_2194538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 3, 1, 4].length) (baseStart_2194538 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2194538 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2194538 prefixEnd_2194538 := by exact prefixLift 2194538
  have htrace : WordTrace (prefixWord ++ tailWord_2194538) baseStart_2194538 baseEnd_2194538 := by
    simpa [prefixWord, tailWord_2194538, baseEnd_2194538] using wordTrace_append hprefix tailTrace_2194538
  have hstable : (prefixWord ++ tailWord_2194538).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2194538).length < 2 ^ (prefixWord ++ tailWord_2194538).sum := by decide
  have hdescent : baseEnd_2194538 < baseStart_2194538 := by decide
  rcases family_descends (prefixWord ++ tailWord_2194538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2194551 : List Nat := [1, 1, 3, 1, 1, 4, 1, 3, 4, 3]
def baseStart_2194551 : Nat := 118140960795 + 2194551 * 2 ^ 59
def prefixEnd_2194551 : Nat := 4983230072969 + 3 ^ 40 * 2194551 * 2
def baseEnd_2194551 : Nat := 751239655870099028546633

theorem tailTrace_2194551 : CollatzResearch.WordTrace tailWord_2194551 prefixEnd_2194551 751239655870099028546633 := by
  unfold tailWord_2194551
  simp only [CollatzResearch.WordTrace]
  refine ⟨80041850672524001316599507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53361233781682667544399671 80041850672524001316599507)
  ·
    refine ⟨120062776008786001974899261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80041850672524001316599507 120062776008786001974899261)
    ·
      refine ⟨45023541003294750740587223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 120062776008786001974899261 45023541003294750740587223)
      ·
        refine ⟨67535311504942126110880835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45023541003294750740587223 67535311504942126110880835)
        ·
          refine ⟨101302967257413189166321253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67535311504942126110880835 101302967257413189166321253)
          ·
            refine ⟨18994306360764972968685235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 101302967257413189166321253 18994306360764972968685235)
            ·
              refine ⟨28491459541147459453027853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18994306360764972968685235 28491459541147459453027853)
              ·
                refine ⟨10684297327930297294885445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28491459541147459453027853 10684297327930297294885445)
                ·
                  refine ⟨2003305748986930742791021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10684297327930297294885445 2003305748986930742791021)
                  ·
                    refine ⟨751239655870099028546633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2003305748986930742791021 751239655870099028546633)
                    ·
                      rfl

theorem cell22_2194551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 3, 4, 3].length) (baseStart_2194551 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2194551 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2194551 prefixEnd_2194551 := by exact prefixLift 2194551
  have htrace : WordTrace (prefixWord ++ tailWord_2194551) baseStart_2194551 baseEnd_2194551 := by
    simpa [prefixWord, tailWord_2194551, baseEnd_2194551] using wordTrace_append hprefix tailTrace_2194551
  have hstable : (prefixWord ++ tailWord_2194551).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2194551).length < 2 ^ (prefixWord ++ tailWord_2194551).sum := by decide
  have hdescent : baseEnd_2194551 < baseStart_2194551 := by decide
  rcases family_descends (prefixWord ++ tailWord_2194551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2194553 : List Nat := [1, 2, 1, 3, 5, 2, 1, 1, 6]
def baseStart_2194553 : Nat := 118140960795 + 2194553 * 2 ^ 59
def prefixEnd_2194553 : Nat := 4983230072969 + 3 ^ 40 * 2194553 * 2
def baseEnd_2194553 : Nat := 250413446836990563332209

theorem tailTrace_2194553 : CollatzResearch.WordTrace tailWord_2194553 prefixEnd_2194553 250413446836990563332209 := by
  unfold tailWord_2194553
  simp only [CollatzResearch.WordTrace]
  refine ⟨80041923618516755658172313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53361282412344503772114875 80041923618516755658172313)
  ·
    refine ⟨60031442713887566743629235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80041923618516755658172313 60031442713887566743629235)
    ·
      refine ⟨90047164070831350115443853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60031442713887566743629235 90047164070831350115443853)
      ·
        refine ⟨33767686526561756293291445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90047164070831350115443853 33767686526561756293291445)
        ·
          refine ⟨3165720611865164652496073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 33767686526561756293291445 3165720611865164652496073)
          ·
            refine ⟨2374290458898873489372055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3165720611865164652496073 2374290458898873489372055)
            ·
              refine ⟨3561435688348310234058083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2374290458898873489372055 3561435688348310234058083)
              ·
                refine ⟨5342153532522465351087125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3561435688348310234058083 5342153532522465351087125)
                ·
                  refine ⟨250413446836990563332209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5342153532522465351087125 250413446836990563332209)
                  ·
                    rfl

theorem cell22_2194553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 1, 1, 6].length) (baseStart_2194553 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2194553 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2194553 prefixEnd_2194553 := by exact prefixLift 2194553
  have htrace : WordTrace (prefixWord ++ tailWord_2194553) baseStart_2194553 baseEnd_2194553 := by
    simpa [prefixWord, tailWord_2194553, baseEnd_2194553] using wordTrace_append hprefix tailTrace_2194553
  have hstable : (prefixWord ++ tailWord_2194553).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2194553).length < 2 ^ (prefixWord ++ tailWord_2194553).sum := by decide
  have hdescent : baseEnd_2194553 < baseStart_2194553 := by decide
  rcases family_descends (prefixWord ++ tailWord_2194553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2194579 : List Nat := [1, 1, 1, 2, 1, 2, 4, 1, 2, 7]
def baseStart_2194579 : Nat := 118140960795 + 2194579 * 2 ^ 59
def prefixEnd_2194579 : Nat := 4983230072969 + 3 ^ 40 * 2194579 * 2
def baseEnd_2194579 : Nat := 751249240842316288846547

theorem tailTrace_2194579 : CollatzResearch.WordTrace tailWord_2194579 prefixEnd_2194579 751249240842316288846547 := by
  unfold tailWord_2194579
  simp only [CollatzResearch.WordTrace]
  refine ⟨80042871916422562098618791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53361914610948374732412527 80042871916422562098618791)
  ·
    refine ⟨120064307874633843147928187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80042871916422562098618791 120064307874633843147928187)
    ·
      refine ⟨180096461811950764721892281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120064307874633843147928187 180096461811950764721892281)
      ·
        refine ⟨135072346358963073541419211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 180096461811950764721892281 135072346358963073541419211)
        ·
          refine ⟨202608519538444610312128817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135072346358963073541419211 202608519538444610312128817)
          ·
            refine ⟨151956389653833457734096613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 202608519538444610312128817 151956389653833457734096613)
            ·
              refine ⟨28491823060093773325143115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 151956389653833457734096613 28491823060093773325143115)
              ·
                refine ⟨42737734590140659987714673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28491823060093773325143115 42737734590140659987714673)
                ·
                  refine ⟨32053300942605494990786005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42737734590140659987714673 32053300942605494990786005)
                  ·
                    refine ⟨751249240842316288846547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32053300942605494990786005 751249240842316288846547)
                    ·
                      rfl

theorem cell22_2194579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 1, 2, 7].length) (baseStart_2194579 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2194579 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2194579 prefixEnd_2194579 := by exact prefixLift 2194579
  have htrace : WordTrace (prefixWord ++ tailWord_2194579) baseStart_2194579 baseEnd_2194579 := by
    simpa [prefixWord, tailWord_2194579, baseEnd_2194579] using wordTrace_append hprefix tailTrace_2194579
  have hstable : (prefixWord ++ tailWord_2194579).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2194579).length < 2 ^ (prefixWord ++ tailWord_2194579).sum := by decide
  have hdescent : baseEnd_2194579 < baseStart_2194579 := by decide
  rcases family_descends (prefixWord ++ tailWord_2194579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2194583 : List Nat := [1, 1, 3, 3, 3, 2, 2, 1, 2, 4]
def baseStart_2194583 : Nat := 118140960795 + 2194583 * 2 ^ 59
def prefixEnd_2194583 : Nat := 4983230072969 + 3 ^ 40 * 2194583 * 2
def baseEnd_2194583 : Nat := 751250610124061611746535

theorem tailTrace_2194583 : CollatzResearch.WordTrace tailWord_2194583 prefixEnd_2194583 751250610124061611746535 := by
  unfold tailWord_2194583
  simp only [CollatzResearch.WordTrace]
  refine ⟨80043017808408070781764403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53362011872272047187842935 80043017808408070781764403)
  ·
    refine ⟨120064526712612106172646605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80043017808408070781764403 120064526712612106172646605)
    ·
      refine ⟨45024197517229539814742477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 120064526712612106172646605 45024197517229539814742477)
      ·
        refine ⟨16884074068961077430528429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45024197517229539814742477 16884074068961077430528429)
        ·
          refine ⟨6331527775860404036448161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16884074068961077430528429 6331527775860404036448161)
          ·
            refine ⟨4748645831895303027336121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6331527775860404036448161 4748645831895303027336121)
            ·
              refine ⟨3561484373921477270502091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4748645831895303027336121 3561484373921477270502091)
              ·
                refine ⟨5342226560882215905753137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3561484373921477270502091 5342226560882215905753137)
                ·
                  refine ⟨4006669920661661929314853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5342226560882215905753137 4006669920661661929314853)
                  ·
                    refine ⟨751250610124061611746535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4006669920661661929314853 751250610124061611746535)
                    ·
                      rfl

theorem cell22_2194583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 2, 1, 2, 4].length) (baseStart_2194583 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2194583 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2194583 prefixEnd_2194583 := by exact prefixLift 2194583
  have htrace : WordTrace (prefixWord ++ tailWord_2194583) baseStart_2194583 baseEnd_2194583 := by
    simpa [prefixWord, tailWord_2194583, baseEnd_2194583] using wordTrace_append hprefix tailTrace_2194583
  have hstable : (prefixWord ++ tailWord_2194583).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2194583).length < 2 ^ (prefixWord ++ tailWord_2194583).sum := by decide
  have hdescent : baseEnd_2194583 < baseStart_2194583 := by decide
  rcases family_descends (prefixWord ++ tailWord_2194583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2194602 : List Nat := [3, 1, 5, 1, 1, 2, 2, 2, 2, 3]
def baseStart_2194602 : Nat := 118140960795 + 2194602 * 2 ^ 59
def prefixEnd_2194602 : Nat := 4983230072969 + 3 ^ 40 * 2194602 * 2
def baseEnd_2194602 : Nat := 751257114212351895521477

theorem tailTrace_2194602 : CollatzResearch.WordTrace tailWord_2194602 prefixEnd_2194602 751257114212351895521477 := by
  unfold tailWord_2194602
  simp only [CollatzResearch.WordTrace]
  refine ⟨20010927698834809256676515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53362473863559491351137373 20010927698834809256676515)
  ·
    refine ⟨30016391548252213885014773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20010927698834809256676515 30016391548252213885014773)
    ·
      refine ⟨2814036707648645051720135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 30016391548252213885014773 2814036707648645051720135)
      ·
        refine ⟨4221055061472967577580203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2814036707648645051720135 4221055061472967577580203)
        ·
          refine ⟨6331582592209451366370305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4221055061472967577580203 6331582592209451366370305)
          ·
            refine ⟨4748686944157088524777729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6331582592209451366370305 4748686944157088524777729)
            ·
              refine ⟨3561515208117816393583297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4748686944157088524777729 3561515208117816393583297)
              ·
                refine ⟨2671136406088362295187473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3561515208117816393583297 2671136406088362295187473)
                ·
                  refine ⟨2003352304566271721390605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2671136406088362295187473 2003352304566271721390605)
                  ·
                    refine ⟨751257114212351895521477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2003352304566271721390605 751257114212351895521477)
                    ·
                      rfl

theorem cell22_2194602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 2, 2, 2, 3].length) (baseStart_2194602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2194602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2194602 prefixEnd_2194602 := by exact prefixLift 2194602
  have htrace : WordTrace (prefixWord ++ tailWord_2194602) baseStart_2194602 baseEnd_2194602 := by
    simpa [prefixWord, tailWord_2194602, baseEnd_2194602] using wordTrace_append hprefix tailTrace_2194602
  have hstable : (prefixWord ++ tailWord_2194602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2194602).length < 2 ^ (prefixWord ++ tailWord_2194602).sum := by decide
  have hdescent : baseEnd_2194602 < baseStart_2194602 := by decide
  rcases family_descends (prefixWord ++ tailWord_2194602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2194716 : List Nat := [2, 2, 3, 1, 1, 1, 12]
def baseStart_2194716 : Nat := 118140960795 + 2194716 * 2 ^ 59
def prefixEnd_2194716 : Nat := 4983230072969 + 3 ^ 40 * 2194716 * 2
def baseEnd_2194716 : Nat := 27825782916373836969301

theorem tailTrace_2194716 : CollatzResearch.WordTrace tailWord_2194716 prefixEnd_2194716 27825782916373836969301 := by
  unfold tailWord_2194716
  simp only [CollatzResearch.WordTrace]
  refine ⟨40023934358463117248178001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53365245811284156330904001 40023934358463117248178001)
  ·
    refine ⟨30017950768847337936133501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40023934358463117248178001 30017950768847337936133501)
    ·
      refine ⟨11256731538317751726050063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30017950768847337936133501 11256731538317751726050063)
      ·
        refine ⟨16885097307476627589075095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11256731538317751726050063 16885097307476627589075095)
        ·
          refine ⟨25327645961214941383612643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16885097307476627589075095 25327645961214941383612643)
          ·
            refine ⟨37991468941822412075418965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25327645961214941383612643 37991468941822412075418965)
            ·
              refine ⟨27825782916373836969301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 37991468941822412075418965 27825782916373836969301)
              ·
                rfl

theorem cell22_2194716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 12].length) (baseStart_2194716 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2194716 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2194716 prefixEnd_2194716 := by exact prefixLift 2194716
  have htrace : WordTrace (prefixWord ++ tailWord_2194716) baseStart_2194716 baseEnd_2194716 := by
    simpa [prefixWord, tailWord_2194716, baseEnd_2194716] using wordTrace_append hprefix tailTrace_2194716
  have hstable : (prefixWord ++ tailWord_2194716).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2194716).length < 2 ^ (prefixWord ++ tailWord_2194716).sum := by decide
  have hdescent : baseEnd_2194716 < baseStart_2194716 := by decide
  rcases family_descends (prefixWord ++ tailWord_2194716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2194722 : List Nat := [3, 3, 1, 1, 5, 1, 1, 1, 6]
def baseStart_2194722 : Nat := 118140960795 + 2194722 * 2 ^ 59
def prefixEnd_2194722 : Nat := 4983230072969 + 3 ^ 40 * 2194722 * 2
def baseEnd_2194722 : Nat := 250432730888237194173703

theorem tailTrace_2194722 : CollatzResearch.WordTrace tailWord_2194722 prefixEnd_2194722 250432730888237194173703 := by
  unfold tailWord_2194722
  simp only [CollatzResearch.WordTrace]
  refine ⟨20012021888726124380268605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53365391703269665014049613 20012021888726124380268605)
  ·
    refine ⟨7504508208272296642600727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20012021888726124380268605 7504508208272296642600727)
    ·
      refine ⟨11256762312408444963901091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7504508208272296642600727 11256762312408444963901091)
      ·
        refine ⟨16885143468612667445851637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11256762312408444963901091 16885143468612667445851637)
        ·
          refine ⟨1582982200182437573048591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16885143468612667445851637 1582982200182437573048591)
          ·
            refine ⟨2374473300273656359572887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1582982200182437573048591 2374473300273656359572887)
            ·
              refine ⟨3561709950410484539359331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2374473300273656359572887 3561709950410484539359331)
              ·
                refine ⟨5342564925615726809038997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3561709950410484539359331 5342564925615726809038997)
                ·
                  refine ⟨250432730888237194173703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5342564925615726809038997 250432730888237194173703)
                  ·
                    rfl

theorem cell22_2194722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 1, 1, 6].length) (baseStart_2194722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2194722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2194722 prefixEnd_2194722 := by exact prefixLift 2194722
  have htrace : WordTrace (prefixWord ++ tailWord_2194722) baseStart_2194722 baseEnd_2194722 := by
    simpa [prefixWord, tailWord_2194722, baseEnd_2194722] using wordTrace_append hprefix tailTrace_2194722
  have hstable : (prefixWord ++ tailWord_2194722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2194722).length < 2 ^ (prefixWord ++ tailWord_2194722).sum := by decide
  have hdescent : baseEnd_2194722 < baseStart_2194722 := by decide
  rcases family_descends (prefixWord ++ tailWord_2194722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2194737 : List Nat := [1, 2, 2, 3, 3, 1, 4, 1, 2, 3]
def baseStart_2194737 : Nat := 118140960795 + 2194737 * 2 ^ 59
def prefixEnd_2194737 : Nat := 4983230072969 + 3 ^ 40 * 2194737 * 2
def baseEnd_2194737 : Nat := 751303327471256543396063

theorem tailTrace_2194737 : CollatzResearch.WordTrace tailWord_2194737 prefixEnd_2194737 751303327471256543396063 := by
  unfold tailWord_2194737
  simp only [CollatzResearch.WordTrace]
  refine ⟨80048634649850155082870465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53365756433233436721913643 80048634649850155082870465)
  ·
    refine ⟨60036475987387616312152849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80048634649850155082870465 60036475987387616312152849)
    ·
      refine ⟨45027356990540712234114637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60036475987387616312152849 45027356990540712234114637)
      ·
        refine ⟨16885258871452767087792989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45027356990540712234114637 16885258871452767087792989)
        ·
          refine ⟨6331972076794787657922371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16885258871452767087792989 6331972076794787657922371)
          ·
            refine ⟨9497958115192181486883557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6331972076794787657922371 9497958115192181486883557)
            ·
              refine ⟨1780867146598534028790667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9497958115192181486883557 1780867146598534028790667)
              ·
                refine ⟨2671300719897801043186001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1780867146598534028790667 2671300719897801043186001)
                ·
                  refine ⟨2003475539923350782389501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2671300719897801043186001 2003475539923350782389501)
                  ·
                    refine ⟨751303327471256543396063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2003475539923350782389501 751303327471256543396063)
                    ·
                      rfl

theorem cell22_2194737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 4, 1, 2, 3].length) (baseStart_2194737 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2194737 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2194737 prefixEnd_2194737 := by exact prefixLift 2194737
  have htrace : WordTrace (prefixWord ++ tailWord_2194737) baseStart_2194737 baseEnd_2194737 := by
    simpa [prefixWord, tailWord_2194737, baseEnd_2194737] using wordTrace_append hprefix tailTrace_2194737
  have hstable : (prefixWord ++ tailWord_2194737).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2194737).length < 2 ^ (prefixWord ++ tailWord_2194737).sum := by decide
  have hdescent : baseEnd_2194737 < baseStart_2194737 := by decide
  rcases family_descends (prefixWord ++ tailWord_2194737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2194761 : List Nat := [1, 2, 1, 1, 2, 3, 2, 1, 9]
def baseStart_2194761 : Nat := 118140960795 + 2194761 * 2 ^ 59
def prefixEnd_2194761 : Nat := 4983230072969 + 3 ^ 40 * 2194761 * 2
def baseEnd_2194761 : Nat := 250437181053909493598663

theorem tailTrace_2194761 : CollatzResearch.WordTrace tailWord_2194761 prefixEnd_2194761 250437181053909493598663 := by
  unfold tailWord_2194761
  simp only [CollatzResearch.WordTrace]
  refine ⟨80049510001763207181744137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53366340001175471454496091 80049510001763207181744137)
  ·
    refine ⟨60037132501322405386308103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80049510001763207181744137 60037132501322405386308103)
    ·
      refine ⟨90055698751983608079462155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60037132501322405386308103 90055698751983608079462155)
      ·
        refine ⟨135083548127975412119193233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90055698751983608079462155 135083548127975412119193233)
        ·
          refine ⟨101312661095981559089394925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 135083548127975412119193233 101312661095981559089394925)
          ·
            refine ⟨37992247910993084658523097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 101312661095981559089394925 37992247910993084658523097)
            ·
              refine ⟨28494185933244813493892323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37992247910993084658523097 28494185933244813493892323)
              ·
                refine ⟨42741278899867220240838485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28494185933244813493892323 42741278899867220240838485)
                ·
                  refine ⟨250437181053909493598663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 42741278899867220240838485 250437181053909493598663)
                  ·
                    rfl

theorem cell22_2194761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 1, 9].length) (baseStart_2194761 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2194761 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2194761 prefixEnd_2194761 := by exact prefixLift 2194761
  have htrace : WordTrace (prefixWord ++ tailWord_2194761) baseStart_2194761 baseEnd_2194761 := by
    simpa [prefixWord, tailWord_2194761, baseEnd_2194761] using wordTrace_append hprefix tailTrace_2194761
  have hstable : (prefixWord ++ tailWord_2194761).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2194761).length < 2 ^ (prefixWord ++ tailWord_2194761).sum := by decide
  have hdescent : baseEnd_2194761 < baseStart_2194761 := by decide
  rcases family_descends (prefixWord ++ tailWord_2194761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2194778 : List Nat := [3, 1, 1, 2, 1, 2, 3, 4, 5]
def baseStart_2194778 : Nat := 118140960795 + 2194778 * 2 ^ 59
def prefixEnd_2194778 : Nat := 4983230072969 + 3 ^ 40 * 2194778 * 2
def baseEnd_2194778 : Nat := 250439120869715367706979

theorem tailTrace_2194778 : CollatzResearch.WordTrace tailWord_2194778 prefixEnd_2194778 250439120869715367706979 := by
  unfold tailWord_2194778
  simp only [CollatzResearch.WordTrace]
  refine ⟨20012532510675404771278247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53366753361801079390075325 20012532510675404771278247)
  ·
    refine ⟨30018798766013107156917371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20012532510675404771278247 30018798766013107156917371)
    ·
      refine ⟨45028198149019660735376057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30018798766013107156917371 45028198149019660735376057)
      ·
        refine ⟨33771148611764745551532043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45028198149019660735376057 33771148611764745551532043)
        ·
          refine ⟨50656722917647118327298065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33771148611764745551532043 50656722917647118327298065)
          ·
            refine ⟨37992542188235338745473549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50656722917647118327298065 37992542188235338745473549)
            ·
              refine ⟨14247203320588252029552581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37992542188235338745473549 14247203320588252029552581)
              ·
                refine ⟨2671350622610297255541109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14247203320588252029552581 2671350622610297255541109)
                ·
                  refine ⟨250439120869715367706979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2671350622610297255541109 250439120869715367706979)
                  ·
                    rfl

theorem cell22_2194778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 4, 5].length) (baseStart_2194778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2194778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2194778 prefixEnd_2194778 := by exact prefixLift 2194778
  have htrace : WordTrace (prefixWord ++ tailWord_2194778) baseStart_2194778 baseEnd_2194778 := by
    simpa [prefixWord, tailWord_2194778, baseEnd_2194778] using wordTrace_append hprefix tailTrace_2194778
  have hstable : (prefixWord ++ tailWord_2194778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2194778).length < 2 ^ (prefixWord ++ tailWord_2194778).sum := by decide
  have hdescent : baseEnd_2194778 < baseStart_2194778 := by decide
  rcases family_descends (prefixWord ++ tailWord_2194778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2194853 : List Nat := [1, 3, 1, 2, 1, 1, 2, 1, 6, 4]
def baseStart_2194853 : Nat := 118140960795 + 2194853 * 2 ^ 59
def prefixEnd_2194853 : Nat := 4983230072969 + 3 ^ 40 * 2194853 * 2
def baseEnd_2194853 : Nat := 751343036641870907495707

theorem tailTrace_2194853 : CollatzResearch.WordTrace tailWord_2194853 prefixEnd_2194853 751343036641870907495707 := by
  unfold tailWord_2194853
  simp only [CollatzResearch.WordTrace]
  refine ⟨80052865517429906894093213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53368577011619937929395475 80052865517429906894093213)
  ·
    refine ⟨30019824569036215085284955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80052865517429906894093213 30019824569036215085284955)
    ·
      refine ⟨45029736853554322627927433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30019824569036215085284955 45029736853554322627927433)
      ·
        refine ⟨33772302640165741970945575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45029736853554322627927433 33772302640165741970945575)
        ·
          refine ⟨50658453960248612956418363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33772302640165741970945575 50658453960248612956418363)
          ·
            refine ⟨75987680940372919434627545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50658453960248612956418363 75987680940372919434627545)
            ·
              refine ⟨56990760705279689575970659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75987680940372919434627545 56990760705279689575970659)
              ·
                refine ⟨85486141057919534363955989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56990760705279689575970659 85486141057919534363955989)
                ·
                  refine ⟨4007162862089978173310437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 85486141057919534363955989 4007162862089978173310437)
                  ·
                    refine ⟨751343036641870907495707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4007162862089978173310437 751343036641870907495707)
                    ·
                      rfl

theorem cell22_2194853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 1, 6, 4].length) (baseStart_2194853 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2194853 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2194853 prefixEnd_2194853 := by exact prefixLift 2194853
  have htrace : WordTrace (prefixWord ++ tailWord_2194853) baseStart_2194853 baseEnd_2194853 := by
    simpa [prefixWord, tailWord_2194853, baseEnd_2194853] using wordTrace_append hprefix tailTrace_2194853
  have hstable : (prefixWord ++ tailWord_2194853).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2194853).length < 2 ^ (prefixWord ++ tailWord_2194853).sum := by decide
  have hdescent : baseEnd_2194853 < baseStart_2194853 := by decide
  rcases family_descends (prefixWord ++ tailWord_2194853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2194902 : List Nat := [5, 2, 1, 1, 1, 3, 2, 7]
def baseStart_2194902 : Nat := 118140960795 + 2194902 * 2 ^ 59
def prefixEnd_2194902 : Nat := 4983230072969 + 3 ^ 40 * 2194902 * 2
def baseEnd_2194902 : Nat := 83484423371472345891173

theorem tailTrace_2194902 : CollatzResearch.WordTrace tailWord_2194902 prefixEnd_2194902 83484423371472345891173 := by
  unfold tailWord_2194902
  simp only [CollatzResearch.WordTrace]
  refine ⟨5003415793390774266414185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 53369768462834925508417973 5003415793390774266414185)
  ·
    refine ⟨3752561845043080699810639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5003415793390774266414185 3752561845043080699810639)
    ·
      refine ⟨5628842767564621049715959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3752561845043080699810639 5628842767564621049715959)
      ·
        refine ⟨8443264151346931574573939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5628842767564621049715959 8443264151346931574573939)
        ·
          refine ⟨12664896227020397361860909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8443264151346931574573939 12664896227020397361860909)
          ·
            refine ⟨4749336085132649010697841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12664896227020397361860909 4749336085132649010697841)
            ·
              refine ⟨3562002063849486758023381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4749336085132649010697841 3562002063849486758023381)
              ·
                refine ⟨83484423371472345891173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3562002063849486758023381 83484423371472345891173)
                ·
                  rfl

theorem cell22_2194902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 2, 7].length) (baseStart_2194902 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2194902 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2194902 prefixEnd_2194902 := by exact prefixLift 2194902
  have htrace : WordTrace (prefixWord ++ tailWord_2194902) baseStart_2194902 baseEnd_2194902 := by
    simpa [prefixWord, tailWord_2194902, baseEnd_2194902] using wordTrace_append hprefix tailTrace_2194902
  have hstable : (prefixWord ++ tailWord_2194902).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2194902).length < 2 ^ (prefixWord ++ tailWord_2194902).sum := by decide
  have hdescent : baseEnd_2194902 < baseStart_2194902 := by decide
  rcases family_descends (prefixWord ++ tailWord_2194902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2194951 : List Nat := [1, 1, 4, 3, 2, 1, 4, 2, 1, 3]
def baseStart_2194951 : Nat := 118140960795 + 2194951 * 2 ^ 59
def prefixEnd_2194951 : Nat := 4983230072969 + 3 ^ 40 * 2194951 * 2
def baseEnd_2194951 : Nat := 751376584044631318545407

theorem tailTrace_2194951 : CollatzResearch.WordTrace tailWord_2194951 prefixEnd_2194951 751376584044631318545407 := by
  unfold tailWord_2194951
  simp only [CollatzResearch.WordTrace]
  refine ⟨80056439871074869631160707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53370959914049913087440471 80056439871074869631160707)
  ·
    refine ⟨120084659806612304446741061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80056439871074869631160707 120084659806612304446741061)
    ·
      refine ⟨22515873713739807083763949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 120084659806612304446741061 22515873713739807083763949)
      ·
        refine ⟨8443452642652427656411481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22515873713739807083763949 8443452642652427656411481)
        ·
          refine ⟨6332589481989320742308611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8443452642652427656411481 6332589481989320742308611)
          ·
            refine ⟨9498884222983981113462917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6332589481989320742308611 9498884222983981113462917)
            ·
              refine ⟨1781040791809496458774297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9498884222983981113462917 1781040791809496458774297)
              ·
                refine ⟨1335780593857122344080723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1781040791809496458774297 1335780593857122344080723)
                ·
                  refine ⟨2003670890785683516121085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1335780593857122344080723 2003670890785683516121085)
                  ·
                    refine ⟨751376584044631318545407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2003670890785683516121085 751376584044631318545407)
                    ·
                      rfl

theorem cell22_2194951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 4, 2, 1, 3].length) (baseStart_2194951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2194951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2194951 prefixEnd_2194951 := by exact prefixLift 2194951
  have htrace : WordTrace (prefixWord ++ tailWord_2194951) baseStart_2194951 baseEnd_2194951 := by
    simpa [prefixWord, tailWord_2194951, baseEnd_2194951] using wordTrace_append hprefix tailTrace_2194951
  have hstable : (prefixWord ++ tailWord_2194951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2194951).length < 2 ^ (prefixWord ++ tailWord_2194951).sum := by decide
  have hdescent : baseEnd_2194951 < baseStart_2194951 := by decide
  rcases family_descends (prefixWord ++ tailWord_2194951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2195007 : List Nat := [1, 1, 2, 2, 3, 4, 1, 1, 4, 3]
def baseStart_2195007 : Nat := 118140960795 + 2195007 * 2 ^ 59
def prefixEnd_2195007 : Nat := 4983230072969 + 3 ^ 40 * 2195007 * 2
def baseEnd_2195007 : Nat := 751395753989065839145235

theorem tailTrace_2195007 : CollatzResearch.WordTrace tailWord_2195007 prefixEnd_2195007 751395753989065839145235 := by
  unfold tailWord_2195007
  simp only [CollatzResearch.WordTrace]
  refine ⟨80058482358871991195199275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53372321572581327463466183 80058482358871991195199275)
  ·
    refine ⟨120087723538307986792798913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80058482358871991195199275 120087723538307986792798913)
    ·
      refine ⟨90065792653730990094599185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120087723538307986792798913 90065792653730990094599185)
      ·
        refine ⟨67549344490298242570949389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90065792653730990094599185 67549344490298242570949389)
        ·
          refine ⟨25331004183861840964106021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67549344490298242570949389 25331004183861840964106021)
          ·
            refine ⟨4749563284474095180769879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25331004183861840964106021 4749563284474095180769879)
            ·
              refine ⟨7124344926711142771154819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4749563284474095180769879 7124344926711142771154819)
              ·
                refine ⟨10686517390066714156732229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7124344926711142771154819 10686517390066714156732229)
                ·
                  refine ⟨2003722010637508904387293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10686517390066714156732229 2003722010637508904387293)
                  ·
                    refine ⟨751395753989065839145235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2003722010637508904387293 751395753989065839145235)
                    ·
                      rfl

theorem cell22_2195007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 1, 4, 3].length) (baseStart_2195007 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2195007 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2195007 prefixEnd_2195007 := by exact prefixLift 2195007
  have htrace : WordTrace (prefixWord ++ tailWord_2195007) baseStart_2195007 baseEnd_2195007 := by
    simpa [prefixWord, tailWord_2195007, baseEnd_2195007] using wordTrace_append hprefix tailTrace_2195007
  have hstable : (prefixWord ++ tailWord_2195007).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2195007).length < 2 ^ (prefixWord ++ tailWord_2195007).sum := by decide
  have hdescent : baseEnd_2195007 < baseStart_2195007 := by decide
  rcases family_descends (prefixWord ++ tailWord_2195007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2195024 : List Nat := [2, 1, 1, 1, 1, 3, 7, 1, 2, 3]
def baseStart_2195024 : Nat := 118140960795 + 2195024 * 2 ^ 59
def prefixEnd_2195024 : Nat := 4983230072969 + 3 ^ 40 * 2195024 * 2
def baseEnd_2195024 : Nat := 751401573436483461470183

theorem tailTrace_2195024 : CollatzResearch.WordTrace tailWord_2195024 prefixEnd_2195024 751401573436483461470183 := by
  unfold tailWord_2195024
  simp only [CollatzResearch.WordTrace]
  refine ⟨40029551199905201549284063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53372734933206935399045417 40029551199905201549284063)
  ·
    refine ⟨60044326799857802323926095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40029551199905201549284063 60044326799857802323926095)
    ·
      refine ⟨90066490199786703485889143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60044326799857802323926095 90066490199786703485889143)
      ·
        refine ⟨135099735299680055228833715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90066490199786703485889143 135099735299680055228833715)
        ·
          refine ⟨202649602949520082843250573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135099735299680055228833715 202649602949520082843250573)
          ·
            refine ⟨75993601106070031066218965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 202649602949520082843250573 75993601106070031066218965)
            ·
              refine ⟨1781100025923516353114507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 75993601106070031066218965 1781100025923516353114507)
              ·
                refine ⟨2671650038885274529671761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1781100025923516353114507 2671650038885274529671761)
                ·
                  refine ⟨2003737529163955897253821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2671650038885274529671761 2003737529163955897253821)
                  ·
                    refine ⟨751401573436483461470183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2003737529163955897253821 751401573436483461470183)
                    ·
                      rfl

theorem cell22_2195024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 7, 1, 2, 3].length) (baseStart_2195024 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2195024 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2195024 prefixEnd_2195024 := by exact prefixLift 2195024
  have htrace : WordTrace (prefixWord ++ tailWord_2195024) baseStart_2195024 baseEnd_2195024 := by
    simpa [prefixWord, tailWord_2195024, baseEnd_2195024] using wordTrace_append hprefix tailTrace_2195024
  have hstable : (prefixWord ++ tailWord_2195024).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2195024).length < 2 ^ (prefixWord ++ tailWord_2195024).sum := by decide
  have hdescent : baseEnd_2195024 < baseStart_2195024 := by decide
  rcases family_descends (prefixWord ++ tailWord_2195024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2195054 : List Nat := [4, 1, 2, 2, 4, 1, 8]
def baseStart_2195054 : Nat := 118140960795 + 2195054 * 2 ^ 59
def prefixEnd_2195054 : Nat := 4983230072969 + 3 ^ 40 * 2195054 * 2
def baseEnd_2195054 : Nat := 27830068261095310489633

theorem tailTrace_2195054 : CollatzResearch.WordTrace tailWord_2195054 prefixEnd_2195054 27830068261095310489633 := by
  unfold tailWord_2195054
  simp only [CollatzResearch.WordTrace]
  refine ⟨10007524573712714777770027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53373464393134478814773477 10007524573712714777770027)
  ·
    refine ⟨15011286860569072166655041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10007524573712714777770027 15011286860569072166655041)
    ·
      refine ⟨11258465145426804124991281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15011286860569072166655041 11258465145426804124991281)
      ·
        refine ⟨8443848859070103093743461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11258465145426804124991281 8443848859070103093743461)
        ·
          refine ⟨1583221661075644330076899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8443848859070103093743461 1583221661075644330076899)
          ·
            refine ⟨2374832491613466495115349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1583221661075644330076899 2374832491613466495115349)
            ·
              refine ⟨27830068261095310489633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2374832491613466495115349 27830068261095310489633)
              ·
                rfl

theorem cell22_2195054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 8].length) (baseStart_2195054 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2195054 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2195054 prefixEnd_2195054 := by exact prefixLift 2195054
  have htrace : WordTrace (prefixWord ++ tailWord_2195054) baseStart_2195054 baseEnd_2195054 := by
    simpa [prefixWord, tailWord_2195054, baseEnd_2195054] using wordTrace_append hprefix tailTrace_2195054
  have hstable : (prefixWord ++ tailWord_2195054).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2195054).length < 2 ^ (prefixWord ++ tailWord_2195054).sum := by decide
  have hdescent : baseEnd_2195054 < baseStart_2195054 := by decide
  rcases family_descends (prefixWord ++ tailWord_2195054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2195065 : List Nat := [1, 2, 1, 3, 3, 1, 1, 3, 7]
def baseStart_2195065 : Nat := 118140960795 + 2195065 * 2 ^ 59
def prefixEnd_2195065 : Nat := 4983230072969 + 3 ^ 40 * 2195065 * 2
def baseEnd_2195065 : Nat := 250471869524791007065019

theorem tailTrace_2195065 : CollatzResearch.WordTrace tailWord_2195065 prefixEnd_2195065 250471869524791007065019 := by
  unfold tailWord_2195065
  simp only [CollatzResearch.WordTrace]
  refine ⟨80060597792661867100810649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53373731861774578067207099 80060597792661867100810649)
  ·
    refine ⟨60045448344496400325607987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80060597792661867100810649 60045448344496400325607987)
    ·
      refine ⟨90068172516744600488411981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60045448344496400325607987 90068172516744600488411981)
      ·
        refine ⟨33775564693779225183154493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90068172516744600488411981 33775564693779225183154493)
        ·
          refine ⟨12665836760167209443682935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33775564693779225183154493 12665836760167209443682935)
          ·
            refine ⟨18998755140250814165524403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12665836760167209443682935 18998755140250814165524403)
            ·
              refine ⟨28498132710376221248286605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18998755140250814165524403 28498132710376221248286605)
              ·
                refine ⟨10686799766391082968107477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28498132710376221248286605 10686799766391082968107477)
                ·
                  refine ⟨250471869524791007065019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10686799766391082968107477 250471869524791007065019)
                  ·
                    rfl

theorem cell22_2195065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 3, 7].length) (baseStart_2195065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2195065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2195065 prefixEnd_2195065 := by exact prefixLift 2195065
  have htrace : WordTrace (prefixWord ++ tailWord_2195065) baseStart_2195065 baseEnd_2195065 := by
    simpa [prefixWord, tailWord_2195065, baseEnd_2195065] using wordTrace_append hprefix tailTrace_2195065
  have hstable : (prefixWord ++ tailWord_2195065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2195065).length < 2 ^ (prefixWord ++ tailWord_2195065).sum := by decide
  have hdescent : baseEnd_2195065 < baseStart_2195065 := by decide
  rcases family_descends (prefixWord ++ tailWord_2195065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2195069 : List Nat := [1, 4, 1, 1, 4, 1, 3, 1, 3, 3]
def baseStart_2195069 : Nat := 118140960795 + 2195069 * 2 ^ 59
def prefixEnd_2195069 : Nat := 4983230072969 + 3 ^ 40 * 2195069 * 2
def baseEnd_2195069 : Nat := 751416977856118344095045

theorem tailTrace_2195069 : CollatzResearch.WordTrace tailWord_2195069 prefixEnd_2195069 751416977856118344095045 := by
  unfold tailWord_2195069
  simp only [CollatzResearch.WordTrace]
  refine ⟨80060743684647375783956261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53373829123098250522637507 80060743684647375783956261)
  ·
    refine ⟨15011389440871382959491799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 80060743684647375783956261 15011389440871382959491799)
    ·
      refine ⟨22517084161307074439237699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15011389440871382959491799 22517084161307074439237699)
      ·
        refine ⟨33775626241960611658856549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22517084161307074439237699 33775626241960611658856549)
        ·
          refine ⟨6332929920367614686035603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33775626241960611658856549 6332929920367614686035603)
          ·
            refine ⟨9499394880551422029053405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6332929920367614686035603 9499394880551422029053405)
            ·
              refine ⟨3562273080206783260895027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9499394880551422029053405 3562273080206783260895027)
              ·
                refine ⟨5343409620310174891342541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3562273080206783260895027 5343409620310174891342541)
                ·
                  refine ⟨2003778607616315584253453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5343409620310174891342541 2003778607616315584253453)
                  ·
                    refine ⟨751416977856118344095045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2003778607616315584253453 751416977856118344095045)
                    ·
                      rfl

theorem cell22_2195069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 3, 1, 3, 3].length) (baseStart_2195069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2195069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2195069 prefixEnd_2195069 := by exact prefixLift 2195069
  have htrace : WordTrace (prefixWord ++ tailWord_2195069) baseStart_2195069 baseEnd_2195069 := by
    simpa [prefixWord, tailWord_2195069, baseEnd_2195069] using wordTrace_append hprefix tailTrace_2195069
  have hstable : (prefixWord ++ tailWord_2195069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2195069).length < 2 ^ (prefixWord ++ tailWord_2195069).sum := by decide
  have hdescent : baseEnd_2195069 < baseStart_2195069 := by decide
  rcases family_descends (prefixWord ++ tailWord_2195069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2195176 : List Nat := [2, 1, 4, 1, 3, 1, 3, 2, 2, 3]
def baseStart_2195176 : Nat := 118140960795 + 2195176 * 2 ^ 59
def prefixEnd_2195176 : Nat := 4983230072969 + 3 ^ 40 * 2195176 * 2
def baseEnd_2195176 : Nat := 751453606142805731669717

theorem tailTrace_2195176 : CollatzResearch.WordTrace tailWord_2195176 prefixEnd_2195176 751453606142805731669717 := by
  unfold tailWord_2195176
  simp only [CollatzResearch.WordTrace]
  refine ⟨40032323147629866529050691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53376430863506488705400921 40032323147629866529050691)
  ·
    refine ⟨60048484721444799793576037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40032323147629866529050691 60048484721444799793576037)
    ·
      refine ⟨11259090885270899961295507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 60048484721444799793576037 11259090885270899961295507)
      ·
        refine ⟨16888636327906349941943261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11259090885270899961295507 16888636327906349941943261)
        ·
          refine ⟨6333238622964881228228723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16888636327906349941943261 6333238622964881228228723)
          ·
            refine ⟨9499857934447321842343085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6333238622964881228228723 9499857934447321842343085)
            ·
              refine ⟨3562446725417745690878657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9499857934447321842343085 3562446725417745690878657)
              ·
                refine ⟨2671835044063309268158993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3562446725417745690878657 2671835044063309268158993)
                ·
                  refine ⟨2003876283047481951119245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2671835044063309268158993 2003876283047481951119245)
                  ·
                    refine ⟨751453606142805731669717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2003876283047481951119245 751453606142805731669717)
                    ·
                      rfl

theorem cell22_2195176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 3, 2, 2, 3].length) (baseStart_2195176 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2195176 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2195176 prefixEnd_2195176 := by exact prefixLift 2195176
  have htrace : WordTrace (prefixWord ++ tailWord_2195176) baseStart_2195176 baseEnd_2195176 := by
    simpa [prefixWord, tailWord_2195176, baseEnd_2195176] using wordTrace_append hprefix tailTrace_2195176
  have hstable : (prefixWord ++ tailWord_2195176).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2195176).length < 2 ^ (prefixWord ++ tailWord_2195176).sum := by decide
  have hdescent : baseEnd_2195176 < baseStart_2195176 := by decide
  rcases family_descends (prefixWord ++ tailWord_2195176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2195234 : List Nat := [3, 3, 1, 1, 2, 1, 2, 4, 5]
def baseStart_2195234 : Nat := 118140960795 + 2195234 * 2 ^ 59
def prefixEnd_2195234 : Nat := 4983230072969 + 3 ^ 40 * 2195234 * 2
def baseEnd_2195234 : Nat := 250491153576037637906513

theorem tailTrace_2195234 : CollatzResearch.WordTrace tailWord_2195234 prefixEnd_2195234 250491153576037637906513 := by
  unfold tailWord_2195234
  simp only [CollatzResearch.WordTrace]
  refine ⟨20016690432262402240928189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53377841152699739309141837 20016690432262402240928189)
  ·
    refine ⟨7506258912098400840348071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20016690432262402240928189 7506258912098400840348071)
    ·
      refine ⟨11259388368147601260522107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7506258912098400840348071 11259388368147601260522107)
      ·
        refine ⟨16889082552221401890783161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11259388368147601260522107 16889082552221401890783161)
        ·
          refine ⟨12666811914166051418087371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16889082552221401890783161 12666811914166051418087371)
          ·
            refine ⟨19000217871249077127131057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12666811914166051418087371 19000217871249077127131057)
            ·
              refine ⟨14250163403436807845348293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19000217871249077127131057 14250163403436807845348293)
              ·
                refine ⟨2671905638144401471002805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14250163403436807845348293 2671905638144401471002805)
                ·
                  refine ⟨250491153576037637906513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2671905638144401471002805 250491153576037637906513)
                  ·
                    rfl

theorem cell22_2195234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 4, 5].length) (baseStart_2195234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2195234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2195234 prefixEnd_2195234 := by exact prefixLift 2195234
  have htrace : WordTrace (prefixWord ++ tailWord_2195234) baseStart_2195234 baseEnd_2195234 := by
    simpa [prefixWord, tailWord_2195234, baseEnd_2195234] using wordTrace_append hprefix tailTrace_2195234
  have hstable : (prefixWord ++ tailWord_2195234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2195234).length < 2 ^ (prefixWord ++ tailWord_2195234).sum := by decide
  have hdescent : baseEnd_2195234 < baseStart_2195234 := by decide
  rcases family_descends (prefixWord ++ tailWord_2195234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2195247 : List Nat := [1, 1, 2, 1, 2, 1, 2, 3, 5, 4]
def baseStart_2195247 : Nat := 118140960795 + 2195247 * 2 ^ 59
def prefixEnd_2195247 : Nat := 4983230072969 + 3 ^ 40 * 2195247 * 2
def baseEnd_2195247 : Nat := 751477910893785213144499

theorem tailTrace_2195247 : CollatzResearch.WordTrace tailWord_2195247 prefixEnd_2195247 751477910893785213144499 := by
  unfold tailWord_2195247
  simp only [CollatzResearch.WordTrace]
  refine ⟨80067235878002512183935995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53378157252001674789290663 80067235878002512183935995)
  ·
    refine ⟨120100853817003768275903993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80067235878002512183935995 120100853817003768275903993)
    ·
      refine ⟨90075640362752826206927995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120100853817003768275903993 90075640362752826206927995)
      ·
        refine ⟨135113460544129239310391993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90075640362752826206927995 135113460544129239310391993)
        ·
          refine ⟨101335095408096929482793995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 135113460544129239310391993 101335095408096929482793995)
          ·
            refine ⟨152002643112145394224190993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101335095408096929482793995 152002643112145394224190993)
            ·
              refine ⟨114001982334109045668143245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 152002643112145394224190993 114001982334109045668143245)
              ·
                refine ⟨42750743375290892125553717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 114001982334109045668143245 42750743375290892125553717)
                ·
                  refine ⟨4007882191433521136770661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 42750743375290892125553717 4007882191433521136770661)
                  ·
                    refine ⟨751477910893785213144499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4007882191433521136770661 751477910893785213144499)
                    ·
                      rfl

theorem cell22_2195247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 3, 5, 4].length) (baseStart_2195247 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2195247 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2195247 prefixEnd_2195247 := by exact prefixLift 2195247
  have htrace : WordTrace (prefixWord ++ tailWord_2195247) baseStart_2195247 baseEnd_2195247 := by
    simpa [prefixWord, tailWord_2195247, baseEnd_2195247] using wordTrace_append hprefix tailTrace_2195247
  have hstable : (prefixWord ++ tailWord_2195247).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2195247).length < 2 ^ (prefixWord ++ tailWord_2195247).sum := by decide
  have hdescent : baseEnd_2195247 < baseStart_2195247 := by decide
  rcases family_descends (prefixWord ++ tailWord_2195247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2195296 : List Nat := [2, 1, 1, 3, 3, 3, 1, 4, 4]
def baseStart_2195296 : Nat := 118140960795 + 2195296 * 2 ^ 59
def prefixEnd_2195296 : Nat := 4983230072969 + 3 ^ 40 * 2195296 * 2
def baseEnd_2195296 : Nat := 250498228198388472889783

theorem tailTrace_2195296 : CollatzResearch.WordTrace tailWord_2195296 prefixEnd_2195296 250498228198388472889783 := by
  unfold tailWord_2195296
  simp only [CollatzResearch.WordTrace]
  refine ⟨40034511527412496776234871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53379348703216662368313161 40034511527412496776234871)
  ·
    refine ⟨60051767291118745164352307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40034511527412496776234871 60051767291118745164352307)
    ·
      refine ⟨90077650936678117746528461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60051767291118745164352307 90077650936678117746528461)
      ·
        refine ⟨33779119101254294154948173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90077650936678117746528461 33779119101254294154948173)
        ·
          refine ⟨12667169662970360308105565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33779119101254294154948173 12667169662970360308105565)
          ·
            refine ⟨4750188623613885115539587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12667169662970360308105565 4750188623613885115539587)
            ·
              refine ⟨7125282935420827673309381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4750188623613885115539587 7125282935420827673309381)
              ·
                refine ⟨1335990550391405188745509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7125282935420827673309381 1335990550391405188745509)
                ·
                  refine ⟨250498228198388472889783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1335990550391405188745509 250498228198388472889783)
                  ·
                    rfl

theorem cell22_2195296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 4, 4].length) (baseStart_2195296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2195296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2195296 prefixEnd_2195296 := by exact prefixLift 2195296
  have htrace : WordTrace (prefixWord ++ tailWord_2195296) baseStart_2195296 baseEnd_2195296 := by
    simpa [prefixWord, tailWord_2195296, baseEnd_2195296] using wordTrace_append hprefix tailTrace_2195296
  have hstable : (prefixWord ++ tailWord_2195296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2195296).length < 2 ^ (prefixWord ++ tailWord_2195296).sum := by decide
  have hdescent : baseEnd_2195296 < baseStart_2195296 := by decide
  rcases family_descends (prefixWord ++ tailWord_2195296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2195309 : List Nat := [1, 5, 1, 1, 1, 1, 2, 2, 4, 4]
def baseStart_2195309 : Nat := 118140960795 + 2195309 * 2 ^ 59
def prefixEnd_2195309 : Nat := 4983230072969 + 3 ^ 40 * 2195309 * 2
def baseEnd_2195309 : Nat := 751499134760837718094309

theorem tailTrace_2195309 : CollatzResearch.WordTrace tailWord_2195309 prefixEnd_2195309 751499134760837718094309 := by
  unfold tailWord_2195309
  simp only [CollatzResearch.WordTrace]
  refine ⟨80069497203777896772692981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53379664802518597848461987 80069497203777896772692981)
  ·
    refine ⟨7506515362854177822439967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 80069497203777896772692981 7506515362854177822439967)
    ·
      refine ⟨11259773044281266733659951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7506515362854177822439967 11259773044281266733659951)
      ·
        refine ⟨16889659566421900100489927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11259773044281266733659951 16889659566421900100489927)
        ·
          refine ⟨25334489349632850150734891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16889659566421900100489927 25334489349632850150734891)
          ·
            refine ⟨38001734024449275226102337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25334489349632850150734891 38001734024449275226102337)
            ·
              refine ⟨28501300518336956419576753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38001734024449275226102337 28501300518336956419576753)
              ·
                refine ⟨21375975388752717314682565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28501300518336956419576753 21375975388752717314682565)
                ·
                  refine ⟨4007995385391134496502981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21375975388752717314682565 4007995385391134496502981)
                  ·
                    refine ⟨751499134760837718094309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4007995385391134496502981 751499134760837718094309)
                    ·
                      rfl

theorem cell22_2195309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 2, 4, 4].length) (baseStart_2195309 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2195309 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2195309 prefixEnd_2195309 := by exact prefixLift 2195309
  have htrace : WordTrace (prefixWord ++ tailWord_2195309) baseStart_2195309 baseEnd_2195309 := by
    simpa [prefixWord, tailWord_2195309, baseEnd_2195309] using wordTrace_append hprefix tailTrace_2195309
  have hstable : (prefixWord ++ tailWord_2195309).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2195309).length < 2 ^ (prefixWord ++ tailWord_2195309).sum := by decide
  have hdescent : baseEnd_2195309 < baseStart_2195309 := by decide
  rcases family_descends (prefixWord ++ tailWord_2195309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2195339 : List Nat := [1, 1, 1, 1, 4, 2, 1, 1, 7, 3]
def baseStart_2195339 : Nat := 118140960795 + 2195339 * 2 ^ 59
def prefixEnd_2195339 : Nat := 4983230072969 + 3 ^ 40 * 2195339 * 2
def baseEnd_2195339 : Nat := 751509404373927639844217

theorem tailTrace_2195339 : CollatzResearch.WordTrace tailWord_2195339 prefixEnd_2195339 751509404373927639844217 := by
  unfold tailWord_2195339
  simp only [CollatzResearch.WordTrace]
  refine ⟨80070591393669211896285071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53380394262446141264190047 80070591393669211896285071)
  ·
    refine ⟨120105887090503817844427607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80070591393669211896285071 120105887090503817844427607)
    ·
      refine ⟨180158830635755726766641411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120105887090503817844427607 180158830635755726766641411)
      ·
        refine ⟨270238245953633590149962117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180158830635755726766641411 270238245953633590149962117)
        ·
          refine ⟨50669671116306298153117897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 270238245953633590149962117 50669671116306298153117897)
          ·
            refine ⟨38002253337229723614838423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50669671116306298153117897 38002253337229723614838423)
            ·
              refine ⟨57003380005844585422257635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38002253337229723614838423 57003380005844585422257635)
              ·
                refine ⟨85505070008766878133386453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57003380005844585422257635 85505070008766878133386453)
                ·
                  refine ⟨2004025078330473706251245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 85505070008766878133386453 2004025078330473706251245)
                  ·
                    refine ⟨751509404373927639844217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2004025078330473706251245 751509404373927639844217)
                    ·
                      rfl

theorem cell22_2195339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 1, 7, 3].length) (baseStart_2195339 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2195339 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2195339 prefixEnd_2195339 := by exact prefixLift 2195339
  have htrace : WordTrace (prefixWord ++ tailWord_2195339) baseStart_2195339 baseEnd_2195339 := by
    simpa [prefixWord, tailWord_2195339, baseEnd_2195339] using wordTrace_append hprefix tailTrace_2195339
  have hstable : (prefixWord ++ tailWord_2195339).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2195339).length < 2 ^ (prefixWord ++ tailWord_2195339).sum := by decide
  have hdescent : baseEnd_2195339 < baseStart_2195339 := by decide
  rcases family_descends (prefixWord ++ tailWord_2195339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2195390 : List Nat := [4, 2, 1, 1, 1, 3, 3, 3, 1, 3]
def baseStart_2195390 : Nat := 118140960795 + 2195390 * 2 ^ 59
def prefixEnd_2195390 : Nat := 4983230072969 + 3 ^ 40 * 2195390 * 2
def baseEnd_2195390 : Nat := 751526862716180506819061

theorem tailTrace_2195390 : CollatzResearch.WordTrace tailWord_2195390 prefixEnd_2195390 751526862716180506819061 := by
  unfold tailWord_2195390
  simp only [CollatzResearch.WordTrace]
  refine ⟨10009056439560555950798953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53381634344322965070927749 10009056439560555950798953)
  ·
    refine ⟨7506792329670416963099215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10009056439560555950798953 7506792329670416963099215)
    ·
      refine ⟨11260188494505625444648823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7506792329670416963099215 11260188494505625444648823)
      ·
        refine ⟨16890282741758438166973235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11260188494505625444648823 16890282741758438166973235)
        ·
          refine ⟨25335424112637657250459853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16890282741758438166973235 25335424112637657250459853)
          ·
            refine ⟨9500784042239121468922445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25335424112637657250459853 9500784042239121468922445)
            ·
              refine ⟨3562794015839670550845917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9500784042239121468922445 3562794015839670550845917)
              ·
                refine ⟨1336047755939876456567219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3562794015839670550845917 1336047755939876456567219)
                ·
                  refine ⟨2004071633909814684850829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1336047755939876456567219 2004071633909814684850829)
                  ·
                    refine ⟨751526862716180506819061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2004071633909814684850829 751526862716180506819061)
                    ·
                      rfl

theorem cell22_2195390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 3, 3, 1, 3].length) (baseStart_2195390 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2195390 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2195390 prefixEnd_2195390 := by exact prefixLift 2195390
  have htrace : WordTrace (prefixWord ++ tailWord_2195390) baseStart_2195390 baseEnd_2195390 := by
    simpa [prefixWord, tailWord_2195390, baseEnd_2195390] using wordTrace_append hprefix tailTrace_2195390
  have hstable : (prefixWord ++ tailWord_2195390).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2195390).length < 2 ^ (prefixWord ++ tailWord_2195390).sum := by decide
  have hdescent : baseEnd_2195390 < baseStart_2195390 := by decide
  rcases family_descends (prefixWord ++ tailWord_2195390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
