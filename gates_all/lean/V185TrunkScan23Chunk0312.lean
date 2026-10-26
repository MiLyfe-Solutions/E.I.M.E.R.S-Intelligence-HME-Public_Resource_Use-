import V185TrunkScan23Chunk0311

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1846089 : List Nat := [1, 2, 1, 1, 2, 6, 1, 1, 1, 7]
def baseStart_1846089 : Nat := 118140960795 + 1846089 * 2 ^ 59
def prefixEnd_1846089 : Nat := 4983230072969 + 3 ^ 40 * 1846089 * 2
def baseEnd_1846089 : Nat := 315976995992710967332499

theorem tailTrace_1846089 : CollatzResearch.WordTrace tailWord_1846089 prefixEnd_1846089 315976995992710967332499 := by
  unfold tailWord_1846089
  simp only [CollatzResearch.WordTrace]
  refine ⟨67332397408942314745037321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44888264939294876496691547 67332397408942314745037321)
  ·
    refine ⟨50499298056706736058777991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67332397408942314745037321 50499298056706736058777991)
    ·
      refine ⟨75748947085060104088166987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50499298056706736058777991 75748947085060104088166987)
      ·
        refine ⟨113623420627590156132250481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75748947085060104088166987 113623420627590156132250481)
        ·
          refine ⟨85217565470692617099187861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113623420627590156132250481 85217565470692617099187861)
          ·
            refine ⟨3994573381438716426524431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 85217565470692617099187861 3994573381438716426524431)
            ·
              refine ⟨5991860072158074639786647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3994573381438716426524431 5991860072158074639786647)
              ·
                refine ⟨8987790108237111959679971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5991860072158074639786647 8987790108237111959679971)
                ·
                  refine ⟨13481685162355667939519957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8987790108237111959679971 13481685162355667939519957)
                  ·
                    refine ⟨315976995992710967332499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13481685162355667939519957 315976995992710967332499)
                    ·
                      rfl

theorem cell23_1846089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 1, 1, 7].length) (baseStart_1846089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1846089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1846089 prefixEnd_1846089 := by exact prefixLift 1846089
  have htrace : WordTrace (prefixWord ++ tailWord_1846089) baseStart_1846089 baseEnd_1846089 := by
    simpa [prefixWord, tailWord_1846089, baseEnd_1846089] using wordTrace_append hprefix tailTrace_1846089
  have hstable : (prefixWord ++ tailWord_1846089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1846089).length < 2 ^ (prefixWord ++ tailWord_1846089).sum := by decide
  have hdescent : baseEnd_1846089 < baseStart_1846089 := by decide
  rcases family_descends (prefixWord ++ tailWord_1846089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1846149 : List Nat := [1, 3, 1, 1, 3, 3, 1, 2, 8]
def baseStart_1846149 : Nat := 118140960795 + 1846149 * 2 ^ 59
def prefixEnd_1846149 : Nat := 4983230072969 + 3 ^ 40 * 1846149 * 2
def baseEnd_1846149 : Nat := 105329088535266963027469

theorem tailTrace_1846149 : CollatzResearch.WordTrace tailWord_1846149 prefixEnd_1846149 105329088535266963027469 := by
  unfold tailWord_1846149
  simp only [CollatzResearch.WordTrace]
  refine ⟨67334585788724944992221501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44889723859149963328147667 67334585788724944992221501)
  ·
    refine ⟨25250469670771854372083063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67334585788724944992221501 25250469670771854372083063)
    ·
      refine ⟨37875704506157781558124595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25250469670771854372083063 37875704506157781558124595)
      ·
        refine ⟨56813556759236672337186893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37875704506157781558124595 56813556759236672337186893)
        ·
          refine ⟨21305083784713752126445085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56813556759236672337186893 21305083784713752126445085)
          ·
            refine ⟨7989406419267657047416907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21305083784713752126445085 7989406419267657047416907)
            ·
              refine ⟨11984109628901485571125361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7989406419267657047416907 11984109628901485571125361)
              ·
                refine ⟨8988082221676114178344021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11984109628901485571125361 8988082221676114178344021)
                ·
                  refine ⟨105329088535266963027469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8988082221676114178344021 105329088535266963027469)
                  ·
                    rfl

theorem cell23_1846149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 2, 8].length) (baseStart_1846149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1846149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1846149 prefixEnd_1846149 := by exact prefixLift 1846149
  have htrace : WordTrace (prefixWord ++ tailWord_1846149) baseStart_1846149 baseEnd_1846149 := by
    simpa [prefixWord, tailWord_1846149, baseEnd_1846149] using wordTrace_append hprefix tailTrace_1846149
  have hstable : (prefixWord ++ tailWord_1846149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1846149).length < 2 ^ (prefixWord ++ tailWord_1846149).sum := by decide
  have hdescent : baseEnd_1846149 < baseStart_1846149 := by decide
  rcases family_descends (prefixWord ++ tailWord_1846149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1846170 : List Nat := [3, 1, 1, 4, 3, 2, 1, 1, 3, 4]
def baseStart_1846170 : Nat := 118140960795 + 1846170 * 2 ^ 59
def prefixEnd_1846170 : Nat := 4983230072969 + 3 ^ 40 * 1846170 * 2
def baseEnd_1846170 : Nat := 315990859970382361694875

theorem tailTrace_1846170 : CollatzResearch.WordTrace tailWord_1846170 prefixEnd_1846170 315990859970382361694875 := by
  unfold tailWord_1846170
  simp only [CollatzResearch.WordTrace]
  refine ⟨16833837930412216394683991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44890234481099243719157309 16833837930412216394683991)
  ·
    refine ⟨25250756895618324592025987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16833837930412216394683991 25250756895618324592025987)
    ·
      refine ⟨37876135343427486888038981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25250756895618324592025987 37876135343427486888038981)
      ·
        refine ⟨7101775376892653791507309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37876135343427486888038981 7101775376892653791507309)
        ·
          refine ⟨2663165766334745171815241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7101775376892653791507309 2663165766334745171815241)
          ·
            refine ⟨1997374324751058878861431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2663165766334745171815241 1997374324751058878861431)
            ·
              refine ⟨2996061487126588318292147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1997374324751058878861431 2996061487126588318292147)
              ·
                refine ⟨4494092230689882477438221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2996061487126588318292147 4494092230689882477438221)
                ·
                  refine ⟨1685284586508705929039333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4494092230689882477438221 1685284586508705929039333)
                  ·
                    refine ⟨315990859970382361694875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1685284586508705929039333 315990859970382361694875)
                    ·
                      rfl

theorem cell23_1846170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 1, 1, 3, 4].length) (baseStart_1846170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1846170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1846170 prefixEnd_1846170 := by exact prefixLift 1846170
  have htrace : WordTrace (prefixWord ++ tailWord_1846170) baseStart_1846170 baseEnd_1846170 := by
    simpa [prefixWord, tailWord_1846170, baseEnd_1846170] using wordTrace_append hprefix tailTrace_1846170
  have hstable : (prefixWord ++ tailWord_1846170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1846170).length < 2 ^ (prefixWord ++ tailWord_1846170).sum := by decide
  have hdescent : baseEnd_1846170 < baseStart_1846170 := by decide
  rcases family_descends (prefixWord ++ tailWord_1846170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1846183 : List Nat := [1, 1, 6, 1, 3, 1, 1, 3, 6]
def baseStart_1846183 : Nat := 118140960795 + 1846183 * 2 ^ 59
def prefixEnd_1846183 : Nat := 4983230072969 + 3 ^ 40 * 1846183 * 2
def baseEnd_1846183 : Nat := 105331028351072837135785

theorem tailTrace_1846183 : CollatzResearch.WordTrace tailWord_1846183 prefixEnd_1846183 105331028351072837135785 := by
  unfold tailWord_1846183
  simp only [CollatzResearch.WordTrace]
  refine ⟨67335825870601768798959203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44890550580401179199306135 67335825870601768798959203)
  ·
    refine ⟨101003738805902653198438805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67335825870601768798959203 101003738805902653198438805)
    ·
      refine ⟨4734550256526686868676819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 101003738805902653198438805 4734550256526686868676819)
      ·
        refine ⟨7101825384790030303015229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4734550256526686868676819 7101825384790030303015229)
        ·
          refine ⟨2663184519296261363630711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7101825384790030303015229 2663184519296261363630711)
          ·
            refine ⟨3994776778944392045446067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2663184519296261363630711 3994776778944392045446067)
            ·
              refine ⟨5992165168416588068169101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3994776778944392045446067 5992165168416588068169101)
              ·
                refine ⟨2247061938156220525563413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5992165168416588068169101 2247061938156220525563413)
                ·
                  refine ⟨105331028351072837135785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2247061938156220525563413 105331028351072837135785)
                  ·
                    rfl

theorem cell23_1846183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 3, 6].length) (baseStart_1846183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1846183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1846183 prefixEnd_1846183 := by exact prefixLift 1846183
  have htrace : WordTrace (prefixWord ++ tailWord_1846183) baseStart_1846183 baseEnd_1846183 := by
    simpa [prefixWord, tailWord_1846183, baseEnd_1846183] using wordTrace_append hprefix tailTrace_1846183
  have hstable : (prefixWord ++ tailWord_1846183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1846183).length < 2 ^ (prefixWord ++ tailWord_1846183).sum := by decide
  have hdescent : baseEnd_1846183 < baseStart_1846183 := by decide
  rcases family_descends (prefixWord ++ tailWord_1846183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1846221 : List Nat := [1, 6, 3, 1, 1, 1, 1, 4, 1, 4]
def baseStart_1846221 : Nat := 118140960795 + 1846221 * 2 ^ 59
def prefixEnd_1846221 : Nat := 4983230072969 + 3 ^ 40 * 1846221 * 2
def baseEnd_1846221 : Nat := 315999589141508795182297

theorem tailTrace_1846221 : CollatzResearch.WordTrace tailWord_1846221 prefixEnd_1846221 315999589141508795182297 := by
  unfold tailWord_1846221
  simp only [CollatzResearch.WordTrace]
  refine ⟨67337211844464101288842517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44891474562976067525895011 67337211844464101288842517)
  ·
    refine ⟨3156431805209254747914493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 67337211844464101288842517 3156431805209254747914493)
    ·
      refine ⟨1183661926953470530467935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3156431805209254747914493 1183661926953470530467935)
      ·
        refine ⟨1775492890430205795701903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1183661926953470530467935 1775492890430205795701903)
        ·
          refine ⟨2663239335645308693552855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1775492890430205795701903 2663239335645308693552855)
          ·
            refine ⟨3994859003467963040329283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2663239335645308693552855 3994859003467963040329283)
            ·
              refine ⟨5992288505201944560493925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3994859003467963040329283 5992288505201944560493925)
              ·
                refine ⟨1123554094725364605092611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5992288505201944560493925 1123554094725364605092611)
                ·
                  refine ⟨1685331142088046907638917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1123554094725364605092611 1685331142088046907638917)
                  ·
                    refine ⟨315999589141508795182297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1685331142088046907638917 315999589141508795182297)
                    ·
                      rfl

theorem cell23_1846221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_1846221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1846221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1846221 prefixEnd_1846221 := by exact prefixLift 1846221
  have htrace : WordTrace (prefixWord ++ tailWord_1846221) baseStart_1846221 baseEnd_1846221 := by
    simpa [prefixWord, tailWord_1846221, baseEnd_1846221] using wordTrace_append hprefix tailTrace_1846221
  have hstable : (prefixWord ++ tailWord_1846221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1846221).length < 2 ^ (prefixWord ++ tailWord_1846221).sum := by decide
  have hdescent : baseEnd_1846221 < baseStart_1846221 := by decide
  rcases family_descends (prefixWord ++ tailWord_1846221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1846243 : List Nat := [1, 1, 1, 6, 1, 1, 1, 5, 2, 4]
def baseStart_1846243 : Nat := 118140960795 + 1846243 * 2 ^ 59
def prefixEnd_1846243 : Nat := 4983230072969 + 3 ^ 40 * 1846243 * 2
def baseEnd_1846243 : Nat := 316003354666308433157263

theorem tailTrace_1846243 : CollatzResearch.WordTrace tailWord_1846243 prefixEnd_1846243 316003354666308433157263 := by
  unfold tailWord_1846243
  simp only [CollatzResearch.WordTrace]
  refine ⟨67338014250384399046143383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44892009500256266030762255 67338014250384399046143383)
  ·
    refine ⟨101007021375576598569215075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67338014250384399046143383 101007021375576598569215075)
    ·
      refine ⟨151510532063364897853822613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101007021375576598569215075 151510532063364897853822613)
      ·
        refine ⟨7102056190470229586897935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 151510532063364897853822613 7102056190470229586897935)
        ·
          refine ⟨10653084285705344380346903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7102056190470229586897935 10653084285705344380346903)
          ·
            refine ⟨15979626428558016570520355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10653084285705344380346903 15979626428558016570520355)
            ·
              refine ⟨23969439642837024855780533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15979626428558016570520355 23969439642837024855780533)
              ·
                refine ⟨2247134966515971080229425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23969439642837024855780533 2247134966515971080229425)
                ·
                  refine ⟨1685351224886978310172069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2247134966515971080229425 1685351224886978310172069)
                  ·
                    refine ⟨316003354666308433157263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1685351224886978310172069 316003354666308433157263)
                    ·
                      rfl

theorem cell23_1846243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 5, 2, 4].length) (baseStart_1846243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1846243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1846243 prefixEnd_1846243 := by exact prefixLift 1846243
  have htrace : WordTrace (prefixWord ++ tailWord_1846243) baseStart_1846243 baseEnd_1846243 := by
    simpa [prefixWord, tailWord_1846243, baseEnd_1846243] using wordTrace_append hprefix tailTrace_1846243
  have hstable : (prefixWord ++ tailWord_1846243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1846243).length < 2 ^ (prefixWord ++ tailWord_1846243).sum := by decide
  have hdescent : baseEnd_1846243 < baseStart_1846243 := by decide
  rcases family_descends (prefixWord ++ tailWord_1846243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1846249 : List Nat := [1, 2, 1, 1, 1, 2, 1, 1, 4, 2, 7]
def baseStart_1846249 : Nat := 118140960795 + 1846249 * 2 ^ 59
def prefixEnd_1846249 : Nat := 4983230072969 + 3 ^ 40 * 1846249 * 2
def baseEnd_1846249 : Nat := 948013144882852275996761

theorem tailTrace_1846249 : CollatzResearch.WordTrace tailWord_1846249 prefixEnd_1846249 948013144882852275996761 := by
  unfold tailWord_1846249
  simp only [CollatzResearch.WordTrace]
  refine ⟨67338233088362662070861801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44892155392241774713907867 67338233088362662070861801)
  ·
    refine ⟨50503674816271996553146351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67338233088362662070861801 50503674816271996553146351)
    ·
      refine ⟨75755512224407994829719527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50503674816271996553146351 75755512224407994829719527)
      ·
        refine ⟨113633268336611992244579291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75755512224407994829719527 113633268336611992244579291)
        ·
          refine ⟨170449902504917988366868937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113633268336611992244579291 170449902504917988366868937)
          ·
            refine ⟨127837426878688491275151703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170449902504917988366868937 127837426878688491275151703)
            ·
              refine ⟨191756140318032736912727555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127837426878688491275151703 191756140318032736912727555)
              ·
                refine ⟨287634210477049105369091333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 191756140318032736912727555 287634210477049105369091333)
                ·
                  refine ⟨53931414464446707256704625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 287634210477049105369091333 53931414464446707256704625)
                  ·
                    refine ⟨40448560848335030442528469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 53931414464446707256704625 40448560848335030442528469)
                    ·
                      refine ⟨948013144882852275996761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 40448560848335030442528469 948013144882852275996761)
                      ·
                        rfl

theorem cell23_1846249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 4, 2, 7].length) (baseStart_1846249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1846249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1846249 prefixEnd_1846249 := by exact prefixLift 1846249
  have htrace : WordTrace (prefixWord ++ tailWord_1846249) baseStart_1846249 baseEnd_1846249 := by
    simpa [prefixWord, tailWord_1846249, baseEnd_1846249] using wordTrace_append hprefix tailTrace_1846249
  have hstable : (prefixWord ++ tailWord_1846249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1846249).length < 2 ^ (prefixWord ++ tailWord_1846249).sum := by decide
  have hdescent : baseEnd_1846249 < baseStart_1846249 := by decide
  rcases family_descends (prefixWord ++ tailWord_1846249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1846250 : List Nat := [3, 1, 3, 1, 2, 2, 1, 1, 5, 2, 2]
def baseStart_1846250 : Nat := 118140960795 + 1846250 * 2 ^ 59
def prefixEnd_1846250 : Nat := 4983230072969 + 3 ^ 40 * 1846250 * 2
def baseEnd_1846250 : Nat := 948013658363506772084257

theorem tailTrace_1846250 : CollatzResearch.WordTrace tailWord_1846250 prefixEnd_1846250 948013658363506772084257 := by
  unfold tailWord_1846250
  simp only [CollatzResearch.WordTrace]
  refine ⟨16834567390339759810412051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44892179707572692827765469 16834567390339759810412051)
  ·
    refine ⟨25251851085509639715618077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16834567390339759810412051 25251851085509639715618077)
    ·
      refine ⟨9469444157066114893356779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25251851085509639715618077 9469444157066114893356779)
      ·
        refine ⟨14204166235599172340035169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9469444157066114893356779 14204166235599172340035169)
        ·
          refine ⟨10653124676699379255026377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14204166235599172340035169 10653124676699379255026377)
          ·
            refine ⟨7989843507524534441269783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10653124676699379255026377 7989843507524534441269783)
            ·
              refine ⟨11984765261286801661904675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7989843507524534441269783 11984765261286801661904675)
              ·
                refine ⟨17977147891930202492857013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11984765261286801661904675 17977147891930202492857013)
                ·
                  refine ⟨1685357614868456483705345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17977147891930202492857013 1685357614868456483705345)
                  ·
                    refine ⟨1264018211151342362779009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1685357614868456483705345 1264018211151342362779009)
                    ·
                      refine ⟨948013658363506772084257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1264018211151342362779009 948013658363506772084257)
                      ·
                        rfl

theorem cell23_1846250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 1, 5, 2, 2].length) (baseStart_1846250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1846250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1846250 prefixEnd_1846250 := by exact prefixLift 1846250
  have htrace : WordTrace (prefixWord ++ tailWord_1846250) baseStart_1846250 baseEnd_1846250 := by
    simpa [prefixWord, tailWord_1846250, baseEnd_1846250] using wordTrace_append hprefix tailTrace_1846250
  have hstable : (prefixWord ++ tailWord_1846250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1846250).length < 2 ^ (prefixWord ++ tailWord_1846250).sum := by decide
  have hdescent : baseEnd_1846250 < baseStart_1846250 := by decide
  rcases family_descends (prefixWord ++ tailWord_1846250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1846254 : List Nat := [4, 1, 2, 1, 5, 1, 1, 1, 2, 3, 2]
def baseStart_1846254 : Nat := 118140960795 + 1846254 * 2 ^ 59
def prefixEnd_1846254 : Nat := 4983230072969 + 3 ^ 40 * 1846254 * 2
def baseEnd_1846254 : Nat := 948015712286124756434239

theorem tailTrace_1846254 : CollatzResearch.WordTrace tailWord_1846254 prefixEnd_1846254 948015712286124756434239 := by
  unfold tailWord_1846254
  simp only [CollatzResearch.WordTrace]
  refine ⟨8417301931668068490599227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44892276968896365283195877 8417301931668068490599227)
  ·
    refine ⟨12625952897502102735898841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8417301931668068490599227 12625952897502102735898841)
    ·
      refine ⟨9469464673126577051924131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12625952897502102735898841 9469464673126577051924131)
      ·
        refine ⟨14204197009689865577886197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9469464673126577051924131 14204197009689865577886197)
        ·
          refine ⟨1331643469658424897926831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14204197009689865577886197 1331643469658424897926831)
          ·
            refine ⟨1997465204487637346890247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1331643469658424897926831 1997465204487637346890247)
            ·
              refine ⟨2996197806731456020335371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1997465204487637346890247 2996197806731456020335371)
              ·
                refine ⟨4494296710097184030503057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2996197806731456020335371 4494296710097184030503057)
                ·
                  refine ⟨3370722532572888022877293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4494296710097184030503057 3370722532572888022877293)
                  ·
                    refine ⟨1264020949714833008578985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3370722532572888022877293 1264020949714833008578985)
                    ·
                      refine ⟨948015712286124756434239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1264020949714833008578985 948015712286124756434239)
                      ·
                        rfl

theorem cell23_1846254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 1, 1, 2, 3, 2].length) (baseStart_1846254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1846254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1846254 prefixEnd_1846254 := by exact prefixLift 1846254
  have htrace : WordTrace (prefixWord ++ tailWord_1846254) baseStart_1846254 baseEnd_1846254 := by
    simpa [prefixWord, tailWord_1846254, baseEnd_1846254] using wordTrace_append hprefix tailTrace_1846254
  have hstable : (prefixWord ++ tailWord_1846254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1846254).length < 2 ^ (prefixWord ++ tailWord_1846254).sum := by decide
  have hdescent : baseEnd_1846254 < baseStart_1846254 := by decide
  rcases family_descends (prefixWord ++ tailWord_1846254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1846261 : List Nat := [1, 3, 5, 2, 1, 1, 2, 3, 1, 1, 3]
def baseStart_1846261 : Nat := 118140960795 + 1846261 * 2 ^ 59
def prefixEnd_1846261 : Nat := 4983230072969 + 3 ^ 40 * 1846261 * 2
def baseEnd_1846261 : Nat := 948019306650706229046707

theorem tailTrace_1846261 : CollatzResearch.WordTrace tailWord_1846261 prefixEnd_1846261 948019306650706229046707 := by
  unfold tailWord_1846261
  simp only [CollatzResearch.WordTrace]
  refine ⟨67338670764319188120298637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44892447176212792080199091 67338670764319188120298637)
  ·
    refine ⟨25252001536619695545111989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67338670764319188120298637 25252001536619695545111989)
    ·
      refine ⟨2367375144058096457354249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25252001536619695545111989 2367375144058096457354249)
      ·
        refine ⟨1775531358043572343015687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2367375144058096457354249 1775531358043572343015687)
        ·
          refine ⟨2663297037065358514523531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1775531358043572343015687 2663297037065358514523531)
          ·
            refine ⟨3994945555598037771785297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2663297037065358514523531 3994945555598037771785297)
            ·
              refine ⟨2996209166698528328838973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3994945555598037771785297 2996209166698528328838973)
              ·
                refine ⟨1123578437511948123314615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2996209166698528328838973 1123578437511948123314615)
                ·
                  refine ⟨1685367656267922184971923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1123578437511948123314615 1685367656267922184971923)
                  ·
                    refine ⟨2528051484401883277457885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1685367656267922184971923 2528051484401883277457885)
                    ·
                      refine ⟨948019306650706229046707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2528051484401883277457885 948019306650706229046707)
                      ·
                        rfl

theorem cell23_1846261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 2, 3, 1, 1, 3].length) (baseStart_1846261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1846261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1846261 prefixEnd_1846261 := by exact prefixLift 1846261
  have htrace : WordTrace (prefixWord ++ tailWord_1846261) baseStart_1846261 baseEnd_1846261 := by
    simpa [prefixWord, tailWord_1846261, baseEnd_1846261] using wordTrace_append hprefix tailTrace_1846261
  have hstable : (prefixWord ++ tailWord_1846261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1846261).length < 2 ^ (prefixWord ++ tailWord_1846261).sum := by decide
  have hdescent : baseEnd_1846261 < baseStart_1846261 := by decide
  rcases family_descends (prefixWord ++ tailWord_1846261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1846323 : List Nat := [1, 1, 1, 2, 4, 1, 1, 3, 3, 4, 2]
def baseStart_1846323 : Nat := 118140960795 + 1846323 * 2 ^ 59
def prefixEnd_1846323 : Nat := 4983230072969 + 3 ^ 40 * 1846323 * 2
def baseEnd_1846323 : Nat := 948051142451284986471421

theorem tailTrace_1846323 : CollatzResearch.WordTrace tailWord_1846323 prefixEnd_1846323 948051142451284986471421 := by
  unfold tailWord_1846323
  simp only [CollatzResearch.WordTrace]
  refine ⟨67340932090094572709055623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44893954726729715139370415 67340932090094572709055623)
  ·
    refine ⟨101011398135141859063583435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67340932090094572709055623 101011398135141859063583435)
    ·
      refine ⟨151517097202712788595375153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101011398135141859063583435 151517097202712788595375153)
      ·
        refine ⟨113637822902034591446531365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151517097202712788595375153 113637822902034591446531365)
        ·
          refine ⟨21307091794131485896224631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 113637822902034591446531365 21307091794131485896224631)
          ·
            refine ⟨31960637691197228844336947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21307091794131485896224631 31960637691197228844336947)
            ·
              refine ⟨47940956536795843266505421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31960637691197228844336947 47940956536795843266505421)
              ·
                refine ⟨17977858701298441224939533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47940956536795843266505421 17977858701298441224939533)
                ·
                  refine ⟨6741697012986915459352325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17977858701298441224939533 6741697012986915459352325)
                  ·
                    refine ⟨1264068189935046648628561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6741697012986915459352325 1264068189935046648628561)
                    ·
                      refine ⟨948051142451284986471421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1264068189935046648628561 948051142451284986471421)
                      ·
                        rfl

theorem cell23_1846323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 3, 3, 4, 2].length) (baseStart_1846323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1846323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1846323 prefixEnd_1846323 := by exact prefixLift 1846323
  have htrace : WordTrace (prefixWord ++ tailWord_1846323) baseStart_1846323 baseEnd_1846323 := by
    simpa [prefixWord, tailWord_1846323, baseEnd_1846323] using wordTrace_append hprefix tailTrace_1846323
  have hstable : (prefixWord ++ tailWord_1846323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1846323).length < 2 ^ (prefixWord ++ tailWord_1846323).sum := by decide
  have hdescent : baseEnd_1846323 < baseStart_1846323 := by decide
  rcases family_descends (prefixWord ++ tailWord_1846323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1846357 : List Nat := [1, 3, 2, 2, 1, 2, 3, 3, 2, 2, 2]
def baseStart_1846357 : Nat := 118140960795 + 1846357 * 2 ^ 59
def prefixEnd_1846357 : Nat := 4983230072969 + 3 ^ 40 * 1846357 * 2
def baseEnd_1846357 : Nat := 948068600793537853446265

theorem tailTrace_1846357 : CollatzResearch.WordTrace tailWord_1846357 prefixEnd_1846357 948068600793537853446265 := by
  unfold tailWord_1846357
  simp only [CollatzResearch.WordTrace]
  refine ⟨67342172171971396515793325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44894781447980931010528883 67342172171971396515793325)
  ·
    refine ⟨25253314564489273693422497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67342172171971396515793325 25253314564489273693422497)
    ·
      refine ⟨18939985923366955270066873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25253314564489273693422497 18939985923366955270066873)
      ·
        refine ⟨14204989442525216452550155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18939985923366955270066873 14204989442525216452550155)
        ·
          refine ⟨21307484163787824678825233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14204989442525216452550155 21307484163787824678825233)
          ·
            refine ⟨15980613122840868509118925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21307484163787824678825233 15980613122840868509118925)
            ·
              refine ⟨5992729921065325690919597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15980613122840868509118925 5992729921065325690919597)
              ·
                refine ⟨2247273720399497134094849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5992729921065325690919597 2247273720399497134094849)
                ·
                  refine ⟨1685455290299622850571137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2247273720399497134094849 1685455290299622850571137)
                  ·
                    refine ⟨1264091467724717137928353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1685455290299622850571137 1264091467724717137928353)
                    ·
                      refine ⟨948068600793537853446265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1264091467724717137928353 948068600793537853446265)
                      ·
                        rfl

theorem cell23_1846357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 3, 2, 2, 2].length) (baseStart_1846357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1846357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1846357 prefixEnd_1846357 := by exact prefixLift 1846357
  have htrace : WordTrace (prefixWord ++ tailWord_1846357) baseStart_1846357 baseEnd_1846357 := by
    simpa [prefixWord, tailWord_1846357, baseEnd_1846357] using wordTrace_append hprefix tailTrace_1846357
  have hstable : (prefixWord ++ tailWord_1846357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1846357).length < 2 ^ (prefixWord ++ tailWord_1846357).sum := by decide
  have hdescent : baseEnd_1846357 < baseStart_1846357 := by decide
  rcases family_descends (prefixWord ++ tailWord_1846357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1846390 : List Nat := [5, 1, 1, 2, 1, 1, 2, 2, 2, 3, 3]
def baseStart_1846390 : Nat := 118140960795 + 1846390 * 2 ^ 59
def prefixEnd_1846390 : Nat := 4983230072969 + 3 ^ 40 * 1846390 * 2
def baseEnd_1846390 : Nat := 948085545655136224333613

theorem tailTrace_1846390 : CollatzResearch.WordTrace tailWord_1846390 prefixEnd_1846390 948085545655136224333613 := by
  unfold tailWord_1846390
  simp only [CollatzResearch.WordTrace]
  refine ⟨4208960986303240196984039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 44895583853901228767829749 4208960986303240196984039)
  ·
    refine ⟨6313441479454860295476059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4208960986303240196984039 6313441479454860295476059)
    ·
      refine ⟨9470162219182290443214089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6313441479454860295476059 9470162219182290443214089)
      ·
        refine ⟨7102621664386717832410567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9470162219182290443214089 7102621664386717832410567)
        ·
          refine ⟨10653932496580076748615851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7102621664386717832410567 10653932496580076748615851)
          ·
            refine ⟨15980898744870115122923777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10653932496580076748615851 15980898744870115122923777)
            ·
              refine ⟨11985674058652586342192833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15980898744870115122923777 11985674058652586342192833)
              ·
                refine ⟨8989255543989439756644625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11985674058652586342192833 8989255543989439756644625)
                ·
                  refine ⟨6741941657992079817483469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8989255543989439756644625 6741941657992079817483469)
                  ·
                    refine ⟨2528228121747029931556301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6741941657992079817483469 2528228121747029931556301)
                    ·
                      refine ⟨948085545655136224333613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2528228121747029931556301 948085545655136224333613)
                      ·
                        rfl

theorem cell23_1846390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 2, 2, 3, 3].length) (baseStart_1846390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1846390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1846390 prefixEnd_1846390 := by exact prefixLift 1846390
  have htrace : WordTrace (prefixWord ++ tailWord_1846390) baseStart_1846390 baseEnd_1846390 := by
    simpa [prefixWord, tailWord_1846390, baseEnd_1846390] using wordTrace_append hprefix tailTrace_1846390
  have hstable : (prefixWord ++ tailWord_1846390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1846390).length < 2 ^ (prefixWord ++ tailWord_1846390).sum := by decide
  have hdescent : baseEnd_1846390 < baseStart_1846390 := by decide
  rcases family_descends (prefixWord ++ tailWord_1846390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1846457 : List Nat := [1, 2, 1, 4, 1, 3, 2, 4, 1, 4]
def baseStart_1846457 : Nat := 118140960795 + 1846457 * 2 ^ 59
def prefixEnd_1846457 : Nat := 4983230072969 + 3 ^ 40 * 1846457 * 2
def baseEnd_1846457 : Nat := 316039982952995820731935

theorem tailTrace_1846457 : CollatzResearch.WordTrace tailWord_1846457 prefixEnd_1846457 316039982952995820731935 := by
  unfold tailWord_1846457
  simp only [CollatzResearch.WordTrace]
  refine ⟨67345819471609113594433625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44897212981072742396289083 67345819471609113594433625)
  ·
    refine ⟨50509364603706835195825219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67345819471609113594433625 50509364603706835195825219)
    ·
      refine ⟨75764046905560252793737829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50509364603706835195825219 75764046905560252793737829)
      ·
        refine ⟨14205758794792547398825843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75764046905560252793737829 14205758794792547398825843)
        ·
          refine ⟨21308638192188821098238765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14205758794792547398825843 21308638192188821098238765)
          ·
            refine ⟨7990739322070807911839537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21308638192188821098238765 7990739322070807911839537)
            ·
              refine ⟨5993054491553105933879653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7990739322070807911839537 5993054491553105933879653)
              ·
                refine ⟨1123697717166207362602435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5993054491553105933879653 1123697717166207362602435)
                ·
                  refine ⟨1685546575749311043903653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1123697717166207362602435 1685546575749311043903653)
                  ·
                    refine ⟨316039982952995820731935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1685546575749311043903653 316039982952995820731935)
                    ·
                      rfl

theorem cell23_1846457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 4, 1, 4].length) (baseStart_1846457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1846457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1846457 prefixEnd_1846457 := by exact prefixLift 1846457
  have htrace : WordTrace (prefixWord ++ tailWord_1846457) baseStart_1846457 baseEnd_1846457 := by
    simpa [prefixWord, tailWord_1846457, baseEnd_1846457] using wordTrace_append hprefix tailTrace_1846457
  have hstable : (prefixWord ++ tailWord_1846457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1846457).length < 2 ^ (prefixWord ++ tailWord_1846457).sum := by decide
  have hdescent : baseEnd_1846457 < baseStart_1846457 := by decide
  rcases family_descends (prefixWord ++ tailWord_1846457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1846500 : List Nat := [2, 3, 1, 1, 1, 2, 4, 3, 1, 5]
def baseStart_1846500 : Nat := 118140960795 + 1846500 * 2 ^ 59
def prefixEnd_1846500 : Nat := 4983230072969 + 3 ^ 40 * 1846500 * 2
def baseEnd_1846500 : Nat := 316047342842376931319369

theorem tailTrace_1846500 : CollatzResearch.WordTrace tailWord_1846500 prefixEnd_1846500 316047342842376931319369 := by
  unfold tailWord_1846500
  simp only [CollatzResearch.WordTrace]
  refine ⟨33673693905226665969124477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44898258540302221292165969 33673693905226665969124477)
  ·
    refine ⟨12627635214459999738421679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33673693905226665969124477 12627635214459999738421679)
    ·
      refine ⟨18941452821689999607632519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12627635214459999738421679 18941452821689999607632519)
      ·
        refine ⟨28412179232534999411448779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18941452821689999607632519 28412179232534999411448779)
        ·
          refine ⟨42618268848802499117173169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28412179232534999411448779 42618268848802499117173169)
          ·
            refine ⟨31963701636601874337879877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42618268848802499117173169 31963701636601874337879877)
            ·
              refine ⟨5993194056862851438352477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31963701636601874337879877 5993194056862851438352477)
              ·
                refine ⟨2247447771323569289382179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5993194056862851438352477 2247447771323569289382179)
                ·
                  refine ⟨3371171656985353934073269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2247447771323569289382179 3371171656985353934073269)
                  ·
                    refine ⟨316047342842376931319369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3371171656985353934073269 316047342842376931319369)
                    ·
                      rfl

theorem cell23_1846500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 3, 1, 5].length) (baseStart_1846500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1846500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1846500 prefixEnd_1846500 := by exact prefixLift 1846500
  have htrace : WordTrace (prefixWord ++ tailWord_1846500) baseStart_1846500 baseEnd_1846500 := by
    simpa [prefixWord, tailWord_1846500, baseEnd_1846500] using wordTrace_append hprefix tailTrace_1846500
  have hstable : (prefixWord ++ tailWord_1846500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1846500).length < 2 ^ (prefixWord ++ tailWord_1846500).sum := by decide
  have hdescent : baseEnd_1846500 < baseStart_1846500 := by decide
  rcases family_descends (prefixWord ++ tailWord_1846500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1846507 : List Nat := [1, 1, 1, 1, 2, 7, 1, 2, 2, 3, 2]
def baseStart_1846507 : Nat := 118140960795 + 1846507 * 2 ^ 59
def prefixEnd_1846507 : Nat := 4983230072969 + 3 ^ 40 * 1846507 * 2
def baseEnd_1846507 : Nat := 948145622891712266570575

theorem tailTrace_1846507 : CollatzResearch.WordTrace tailWord_1846507 prefixEnd_1846507 948145622891712266570575 := by
  unfold tailWord_1846507
  simp only [CollatzResearch.WordTrace]
  refine ⟨67347643121427972133753775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44898428747618648089169183 67347643121427972133753775)
  ·
    refine ⟨101021464682141958200630663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67347643121427972133753775 101021464682141958200630663)
    ·
      refine ⟨151532197023212937300945995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101021464682141958200630663 151532197023212937300945995)
      ·
        refine ⟨227298295534819405951418993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151532197023212937300945995 227298295534819405951418993)
        ·
          refine ⟨170473721651114554463564245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 227298295534819405951418993 170473721651114554463564245)
          ·
            refine ⟨3995477851197997370239787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 170473721651114554463564245 3995477851197997370239787)
            ·
              refine ⟨5993216776796996055359681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3995477851197997370239787 5993216776796996055359681)
              ·
                refine ⟨4494912582597747041519761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5993216776796996055359681 4494912582597747041519761)
                ·
                  refine ⟨3371184436948310281139821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4494912582597747041519761 3371184436948310281139821)
                  ·
                    refine ⟨1264194163855616355427433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3371184436948310281139821 1264194163855616355427433)
                    ·
                      refine ⟨948145622891712266570575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1264194163855616355427433 948145622891712266570575)
                      ·
                        rfl

theorem cell23_1846507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 2, 2, 3, 2].length) (baseStart_1846507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1846507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1846507 prefixEnd_1846507 := by exact prefixLift 1846507
  have htrace : WordTrace (prefixWord ++ tailWord_1846507) baseStart_1846507 baseEnd_1846507 := by
    simpa [prefixWord, tailWord_1846507, baseEnd_1846507] using wordTrace_append hprefix tailTrace_1846507
  have hstable : (prefixWord ++ tailWord_1846507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1846507).length < 2 ^ (prefixWord ++ tailWord_1846507).sum := by decide
  have hdescent : baseEnd_1846507 < baseStart_1846507 := by decide
  rcases family_descends (prefixWord ++ tailWord_1846507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1846533 : List Nat := [1, 3, 1, 1, 2, 1, 3, 3, 1, 1, 6]
def baseStart_1846533 : Nat := 118140960795 + 1846533 * 2 ^ 59
def prefixEnd_1846533 : Nat := 4983230072969 + 3 ^ 40 * 1846533 * 2
def baseEnd_1846533 : Nat := 948158973388729164845455

theorem tailTrace_1846533 : CollatzResearch.WordTrace tailWord_1846533 prefixEnd_1846533 948158973388729164845455 := by
  unfold tailWord_1846533
  simp only [CollatzResearch.WordTrace]
  refine ⟨67348591419333778574200253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44899060946222519049466835 67348591419333778574200253)
  ·
    refine ⟨25255721782250166965325095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67348591419333778574200253 25255721782250166965325095)
    ·
      refine ⟨37883582673375250447987643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25255721782250166965325095 37883582673375250447987643)
      ·
        refine ⟨56825374010062875671981465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37883582673375250447987643 56825374010062875671981465)
        ·
          refine ⟨42619030507547156753986099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56825374010062875671981465 42619030507547156753986099)
          ·
            refine ⟨63928545761320735130979149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42619030507547156753986099 63928545761320735130979149)
            ·
              refine ⟨23973204660495275674117181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63928545761320735130979149 23973204660495275674117181)
              ·
                refine ⟨8989951747685728377793943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23973204660495275674117181 8989951747685728377793943)
                ·
                  refine ⟨13484927621528592566690915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8989951747685728377793943 13484927621528592566690915)
                  ·
                    refine ⟨20227391432292888850036373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13484927621528592566690915 20227391432292888850036373)
                    ·
                      refine ⟨948158973388729164845455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 20227391432292888850036373 948158973388729164845455)
                      ·
                        rfl

theorem cell23_1846533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 3, 1, 1, 6].length) (baseStart_1846533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1846533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1846533 prefixEnd_1846533 := by exact prefixLift 1846533
  have htrace : WordTrace (prefixWord ++ tailWord_1846533) baseStart_1846533 baseEnd_1846533 := by
    simpa [prefixWord, tailWord_1846533, baseEnd_1846533] using wordTrace_append hprefix tailTrace_1846533
  have hstable : (prefixWord ++ tailWord_1846533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1846533).length < 2 ^ (prefixWord ++ tailWord_1846533).sum := by decide
  have hdescent : baseEnd_1846533 < baseStart_1846533 := by decide
  rcases family_descends (prefixWord ++ tailWord_1846533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1846537 : List Nat := [1, 2, 1, 1, 3, 3, 2, 1, 5, 2, 2]
def baseStart_1846537 : Nat := 118140960795 + 1846537 * 2 ^ 59
def prefixEnd_1846537 : Nat := 4983230072969 + 3 ^ 40 * 1846537 * 2
def baseEnd_1846537 : Nat := 948161027311347149195437

theorem tailTrace_1846537 : CollatzResearch.WordTrace tailWord_1846537 prefixEnd_1846537 948161027311347149195437 := by
  unfold tailWord_1846537
  simp only [CollatzResearch.WordTrace]
  refine ⟨67348737311319287257345865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44899158207546191504897243 67348737311319287257345865)
  ·
    refine ⟨50511552983489465443009399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67348737311319287257345865 50511552983489465443009399)
    ·
      refine ⟨75767329475234198164514099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50511552983489465443009399 75767329475234198164514099)
      ·
        refine ⟨113650994212851297246771149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75767329475234198164514099 113650994212851297246771149)
        ·
          refine ⟨42619122829819236467539181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113650994212851297246771149 42619122829819236467539181)
          ·
            refine ⟨15982171061182213675327193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42619122829819236467539181 15982171061182213675327193)
            ·
              refine ⟨11986628295886660256495395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15982171061182213675327193 11986628295886660256495395)
              ·
                refine ⟨17979942443829990384743093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11986628295886660256495395 17979942443829990384743093)
                ·
                  refine ⟨1685619604109061598569665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17979942443829990384743093 1685619604109061598569665)
                  ·
                    refine ⟨1264214703081796198927249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1685619604109061598569665 1264214703081796198927249)
                    ·
                      refine ⟨948161027311347149195437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1264214703081796198927249 948161027311347149195437)
                      ·
                        rfl

theorem cell23_1846537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 1, 5, 2, 2].length) (baseStart_1846537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1846537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1846537 prefixEnd_1846537 := by exact prefixLift 1846537
  have htrace : WordTrace (prefixWord ++ tailWord_1846537) baseStart_1846537 baseEnd_1846537 := by
    simpa [prefixWord, tailWord_1846537, baseEnd_1846537] using wordTrace_append hprefix tailTrace_1846537
  have hstable : (prefixWord ++ tailWord_1846537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1846537).length < 2 ^ (prefixWord ++ tailWord_1846537).sum := by decide
  have hdescent : baseEnd_1846537 < baseStart_1846537 := by decide
  rcases family_descends (prefixWord ++ tailWord_1846537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1846554 : List Nat := [3, 1, 1, 3, 3, 2, 3, 1, 1, 1, 4]
def baseStart_1846554 : Nat := 118140960795 + 1846554 * 2 ^ 59
def prefixEnd_1846554 : Nat := 4983230072969 + 3 ^ 40 * 1846554 * 2
def baseEnd_1846554 : Nat := 948169756482473582682859

theorem tailTrace_1846554 : CollatzResearch.WordTrace tailWord_1846554 prefixEnd_1846554 948169756482473582682859 := by
  unfold tailWord_1846554
  simp only [CollatzResearch.WordTrace]
  refine ⟨16837339338064424790178679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44899571568171799440476477 16837339338064424790178679)
  ·
    refine ⟨25256009007096637185268019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16837339338064424790178679 25256009007096637185268019)
    ·
      refine ⟨37884013510644955777902029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25256009007096637185268019 37884013510644955777902029)
      ·
        refine ⟨14206505066491858416713261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37884013510644955777902029 14206505066491858416713261)
        ·
          refine ⟨5327439399934446906267473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14206505066491858416713261 5327439399934446906267473)
          ·
            refine ⟨3995579549950835179700605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5327439399934446906267473 3995579549950835179700605)
            ·
              refine ⟨1498342331231563192387727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3995579549950835179700605 1498342331231563192387727)
              ·
                refine ⟨2247513496847344788581591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1498342331231563192387727 2247513496847344788581591)
                ·
                  refine ⟨3371270245271017182872387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2247513496847344788581591 3371270245271017182872387)
                  ·
                    refine ⟨5056905367906525774308581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3371270245271017182872387 5056905367906525774308581)
                    ·
                      refine ⟨948169756482473582682859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5056905367906525774308581 948169756482473582682859)
                      ·
                        rfl

theorem cell23_1846554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 3, 1, 1, 1, 4].length) (baseStart_1846554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1846554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1846554 prefixEnd_1846554 := by exact prefixLift 1846554
  have htrace : WordTrace (prefixWord ++ tailWord_1846554) baseStart_1846554 baseEnd_1846554 := by
    simpa [prefixWord, tailWord_1846554, baseEnd_1846554] using wordTrace_append hprefix tailTrace_1846554
  have hstable : (prefixWord ++ tailWord_1846554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1846554).length < 2 ^ (prefixWord ++ tailWord_1846554).sum := by decide
  have hdescent : baseEnd_1846554 < baseStart_1846554 := by decide
  rcases family_descends (prefixWord ++ tailWord_1846554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1846557 : List Nat := [1, 4, 2, 3, 1, 1, 3, 1, 1, 1, 5]
def baseStart_1846557 : Nat := 118140960795 + 1846557 * 2 ^ 59
def prefixEnd_1846557 : Nat := 4983230072969 + 3 ^ 40 * 1846557 * 2
def baseEnd_1846557 : Nat := 948171296924437070945345

theorem tailTrace_1846557 : CollatzResearch.WordTrace tailWord_1846557 prefixEnd_1846557 948171296924437070945345 := by
  unfold tailWord_1846557
  simp only [CollatzResearch.WordTrace]
  refine ⟨67349466771246830673073925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44899644514164553782049283 67349466771246830673073925)
  ·
    refine ⟨12628025019608780751201361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67349466771246830673073925 12628025019608780751201361)
    ·
      refine ⟨9471018764706585563401021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12628025019608780751201361 9471018764706585563401021)
      ·
        refine ⟨3551632036764969586275383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9471018764706585563401021 3551632036764969586275383)
        ·
          refine ⟨5327448055147454379413075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3551632036764969586275383 5327448055147454379413075)
          ·
            refine ⟨7991172082721181569119613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5327448055147454379413075 7991172082721181569119613)
            ·
              refine ⟨2996689531020443088419855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7991172082721181569119613 2996689531020443088419855)
              ·
                refine ⟨4495034296530664632629783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2996689531020443088419855 4495034296530664632629783)
                ·
                  refine ⟨6742551444795996948944675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4495034296530664632629783 6742551444795996948944675)
                  ·
                    refine ⟨10113827167193995423417013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6742551444795996948944675 10113827167193995423417013)
                    ·
                      refine ⟨948171296924437070945345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10113827167193995423417013 948171296924437070945345)
                      ·
                        rfl

theorem cell23_1846557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 3, 1, 1, 1, 5].length) (baseStart_1846557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1846557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1846557 prefixEnd_1846557 := by exact prefixLift 1846557
  have htrace : WordTrace (prefixWord ++ tailWord_1846557) baseStart_1846557 baseEnd_1846557 := by
    simpa [prefixWord, tailWord_1846557, baseEnd_1846557] using wordTrace_append hprefix tailTrace_1846557
  have hstable : (prefixWord ++ tailWord_1846557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1846557).length < 2 ^ (prefixWord ++ tailWord_1846557).sum := by decide
  have hdescent : baseEnd_1846557 < baseStart_1846557 := by decide
  rcases family_descends (prefixWord ++ tailWord_1846557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1846560 : List Nat := [2, 1, 1, 5, 4, 10]
def baseStart_1846560 : Nat := 118140960795 + 1846560 * 2 ^ 59
def prefixEnd_1846560 : Nat := 4983230072969 + 3 ^ 40 * 1846560 * 2
def baseEnd_1846560 : Nat := 3901945832783541395917

theorem tailTrace_1846560 : CollatzResearch.WordTrace tailWord_1846560 prefixEnd_1846560 3901945832783541395917 := by
  unfold tailWord_1846560
  simp only [CollatzResearch.WordTrace]
  refine ⟨33674788095117981092716567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44899717460157308123622089 33674788095117981092716567)
  ·
    refine ⟨50512182142676971639074851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33674788095117981092716567 50512182142676971639074851)
    ·
      refine ⟨75768273214015457458612277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50512182142676971639074851 75768273214015457458612277)
      ·
        refine ⟨7103275613813949136744901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 75768273214015457458612277 7103275613813949136744901)
        ·
          refine ⟨1331864177590115463139669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7103275613813949136744901 1331864177590115463139669)
          ·
            refine ⟨3901945832783541395917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1331864177590115463139669 3901945832783541395917)
            ·
              rfl

theorem cell23_1846560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 10].length) (baseStart_1846560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1846560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1846560 prefixEnd_1846560 := by exact prefixLift 1846560
  have htrace : WordTrace (prefixWord ++ tailWord_1846560) baseStart_1846560 baseEnd_1846560 := by
    simpa [prefixWord, tailWord_1846560, baseEnd_1846560] using wordTrace_append hprefix tailTrace_1846560
  have hstable : (prefixWord ++ tailWord_1846560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1846560).length < 2 ^ (prefixWord ++ tailWord_1846560).sum := by decide
  have hdescent : baseEnd_1846560 < baseStart_1846560 := by decide
  rcases family_descends (prefixWord ++ tailWord_1846560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1846583 : List Nat := [1, 1, 3, 1, 2, 1, 1, 1, 3, 4, 5]
def baseStart_1846583 : Nat := 118140960795 + 1846583 * 2 ^ 59
def prefixEnd_1846583 : Nat := 4983230072969 + 3 ^ 40 * 1846583 * 2
def baseEnd_1846583 : Nat := 948184647421453969220225

theorem tailTrace_1846583 : CollatzResearch.WordTrace tailWord_1846583 prefixEnd_1846583 948184647421453969220225 := by
  unfold tailWord_1846583
  simp only [CollatzResearch.WordTrace]
  refine ⟨67350415069152637113520403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44900276712768424742346935 67350415069152637113520403)
  ·
    refine ⟨101025622603728955670280605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67350415069152637113520403 101025622603728955670280605)
    ·
      refine ⟨37884608476398358376355227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101025622603728955670280605 37884608476398358376355227)
      ·
        refine ⟨56826912714597537564532841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37884608476398358376355227 56826912714597537564532841)
        ·
          refine ⟨42620184535948153173399631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56826912714597537564532841 42620184535948153173399631)
          ·
            refine ⟨63930276803922229760099447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42620184535948153173399631 63930276803922229760099447)
            ·
              refine ⟨95895415205883344640149171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63930276803922229760099447 95895415205883344640149171)
              ·
                refine ⟨143843122808825016960223757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95895415205883344640149171 143843122808825016960223757)
                ·
                  refine ⟨53941171053309381360083909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 143843122808825016960223757 53941171053309381360083909)
                  ·
                    refine ⟨10113969572495509005015733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53941171053309381360083909 10113969572495509005015733)
                    ·
                      refine ⟨948184647421453969220225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10113969572495509005015733 948184647421453969220225)
                      ·
                        rfl

theorem cell23_1846583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 3, 4, 5].length) (baseStart_1846583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1846583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1846583 prefixEnd_1846583 := by exact prefixLift 1846583
  have htrace : WordTrace (prefixWord ++ tailWord_1846583) baseStart_1846583 baseEnd_1846583 := by
    simpa [prefixWord, tailWord_1846583, baseEnd_1846583] using wordTrace_append hprefix tailTrace_1846583
  have hstable : (prefixWord ++ tailWord_1846583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1846583).length < 2 ^ (prefixWord ++ tailWord_1846583).sum := by decide
  have hdescent : baseEnd_1846583 < baseStart_1846583 := by decide
  rcases family_descends (prefixWord ++ tailWord_1846583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1846590 : List Nat := [4, 2, 1, 2, 1, 1, 1, 2, 2, 7]
def baseStart_1846590 : Nat := 118140960795 + 1846590 * 2 ^ 59
def prefixEnd_1846590 : Nat := 4983230072969 + 3 ^ 40 * 1846590 * 2
def baseEnd_1846590 : Nat := 316062747262011813944231

theorem tailTrace_1846590 : CollatzResearch.WordTrace tailWord_1846590 prefixEnd_1846590 316062747262011813944231 := by
  unfold tailWord_1846590
  simp only [CollatzResearch.WordTrace]
  refine ⟨8418833797515909663628153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44900446920084851539350149 8418833797515909663628153)
  ·
    refine ⟨6314125348136932247721115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8418833797515909663628153 6314125348136932247721115)
    ·
      refine ⟨9471188022205398371581673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6314125348136932247721115 9471188022205398371581673)
      ·
        refine ⟨7103391016654048778686255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9471188022205398371581673 7103391016654048778686255)
        ·
          refine ⟨10655086524981073168029383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7103391016654048778686255 10655086524981073168029383)
          ·
            refine ⟨15982629787471609752044075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10655086524981073168029383 15982629787471609752044075)
            ·
              refine ⟨23973944681207414628066113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15982629787471609752044075 23973944681207414628066113)
              ·
                refine ⟨17980458510905560971049585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23973944681207414628066113 17980458510905560971049585)
                ·
                  refine ⟨13485343883179170728287189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17980458510905560971049585 13485343883179170728287189)
                  ·
                    refine ⟨316062747262011813944231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13485343883179170728287189 316062747262011813944231)
                    ·
                      rfl

theorem cell23_1846590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 2, 2, 7].length) (baseStart_1846590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1846590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1846590 prefixEnd_1846590 := by exact prefixLift 1846590
  have htrace : WordTrace (prefixWord ++ tailWord_1846590) baseStart_1846590 baseEnd_1846590 := by
    simpa [prefixWord, tailWord_1846590, baseEnd_1846590] using wordTrace_append hprefix tailTrace_1846590
  have hstable : (prefixWord ++ tailWord_1846590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1846590).length < 2 ^ (prefixWord ++ tailWord_1846590).sum := by decide
  have hdescent : baseEnd_1846590 < baseStart_1846590 := by decide
  rcases family_descends (prefixWord ++ tailWord_1846590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1846605 : List Nat := [1, 6, 1, 3, 2, 1, 2, 1, 1, 1, 4]
def baseStart_1846605 : Nat := 118140960795 + 1846605 * 2 ^ 59
def prefixEnd_1846605 : Nat := 4983230072969 + 3 ^ 40 * 1846605 * 2
def baseEnd_1846605 : Nat := 948195943995852883145125

theorem tailTrace_1846605 : CollatzResearch.WordTrace tailWord_1846605 prefixEnd_1846605 948195943995852883145125 := by
  unfold tailWord_1846605
  simp only [CollatzResearch.WordTrace]
  refine ⟨67351217475072934870821269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44900811650048623247214179 67351217475072934870821269)
  ·
    refine ⟨3157088319144043822069747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 67351217475072934870821269 3157088319144043822069747)
    ·
      refine ⟨4735632478716065733104621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3157088319144043822069747 4735632478716065733104621)
      ·
        refine ⟨1775862179518524649914233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4735632478716065733104621 1775862179518524649914233)
        ·
          refine ⟨1331896634638893487435675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1775862179518524649914233 1331896634638893487435675)
          ·
            refine ⟨1997844951958340231153513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1331896634638893487435675 1997844951958340231153513)
            ·
              refine ⟨1498383713968755173365135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1997844951958340231153513 1498383713968755173365135)
              ·
                refine ⟨2247575570953132760047703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1498383713968755173365135 2247575570953132760047703)
                ·
                  refine ⟨3371363356429699140071555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2247575570953132760047703 3371363356429699140071555)
                  ·
                    refine ⟨5057045034644548710107333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3371363356429699140071555 5057045034644548710107333)
                    ·
                      refine ⟨948195943995852883145125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5057045034644548710107333 948195943995852883145125)
                      ·
                        rfl

theorem cell23_1846605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 2, 1, 1, 1, 4].length) (baseStart_1846605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1846605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1846605 prefixEnd_1846605 := by exact prefixLift 1846605
  have htrace : WordTrace (prefixWord ++ tailWord_1846605) baseStart_1846605 baseEnd_1846605 := by
    simpa [prefixWord, tailWord_1846605, baseEnd_1846605] using wordTrace_append hprefix tailTrace_1846605
  have hstable : (prefixWord ++ tailWord_1846605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1846605).length < 2 ^ (prefixWord ++ tailWord_1846605).sum := by decide
  have hdescent : baseEnd_1846605 < baseStart_1846605 := by decide
  rcases family_descends (prefixWord ++ tailWord_1846605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1846638 : List Nat := [4, 1, 2, 4, 2, 1, 1, 1, 1, 3, 3]
def baseStart_1846638 : Nat := 118140960795 + 1846638 * 2 ^ 59
def prefixEnd_1846638 : Nat := 4983230072969 + 3 ^ 40 * 1846638 * 2
def baseEnd_1846638 : Nat := 948212888857451254032473

theorem tailTrace_1846638 : CollatzResearch.WordTrace tailWord_1846638 prefixEnd_1846638 948212888857451254032473 := by
  unfold tailWord_1846638
  simp only [CollatzResearch.WordTrace]
  refine ⟨8419052635494172688346571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44901614055968921004515045 8419052635494172688346571)
  ·
    refine ⟨12628578953241259032519857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8419052635494172688346571 12628578953241259032519857)
    ·
      refine ⟨9471434214930944274389893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12628578953241259032519857 9471434214930944274389893)
      ·
        refine ⟨1775893915299552051448105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9471434214930944274389893 1775893915299552051448105)
        ·
          refine ⟨1331920436474664038586079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1775893915299552051448105 1331920436474664038586079)
          ·
            refine ⟨1997880654711996057879119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1331920436474664038586079 1997880654711996057879119)
            ·
              refine ⟨2996820982067994086818679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1997880654711996057879119 2996820982067994086818679)
              ·
                refine ⟨4495231473101991130228019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2996820982067994086818679 4495231473101991130228019)
                ·
                  refine ⟨6742847209652986695342029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4495231473101991130228019 6742847209652986695342029)
                  ·
                    refine ⟨2528567703619870010753261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6742847209652986695342029 2528567703619870010753261)
                    ·
                      refine ⟨948212888857451254032473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2528567703619870010753261 948212888857451254032473)
                      ·
                        rfl

theorem cell23_1846638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 1, 1, 1, 3, 3].length) (baseStart_1846638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1846638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1846638 prefixEnd_1846638 := by exact prefixLift 1846638
  have htrace : WordTrace (prefixWord ++ tailWord_1846638) baseStart_1846638 baseEnd_1846638 := by
    simpa [prefixWord, tailWord_1846638, baseEnd_1846638] using wordTrace_append hprefix tailTrace_1846638
  have hstable : (prefixWord ++ tailWord_1846638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1846638).length < 2 ^ (prefixWord ++ tailWord_1846638).sum := by decide
  have hdescent : baseEnd_1846638 < baseStart_1846638 := by decide
  rcases family_descends (prefixWord ++ tailWord_1846638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1846640 : List Nat := [2, 1, 1, 1, 4, 2, 1, 3, 2, 2, 4]
def baseStart_1846640 : Nat := 118140960795 + 1846640 * 2 ^ 59
def prefixEnd_1846640 : Nat := 4983230072969 + 3 ^ 40 * 1846640 * 2
def baseEnd_1846640 : Nat := 948213915818760246207463

theorem tailTrace_1846640 : CollatzResearch.WordTrace tailWord_1846640 prefixEnd_1846640 948213915818760246207463 := by
  unfold tailWord_1846640
  simp only [CollatzResearch.WordTrace]
  refine ⟨33676247014973067924172687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44901662686630757232230249 33676247014973067924172687)
  ·
    refine ⟨50514370522459601886259031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33676247014973067924172687 50514370522459601886259031)
    ·
      refine ⟨75771555783689402829388547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50514370522459601886259031 75771555783689402829388547)
      ·
        refine ⟨113657333675534104244082821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75771555783689402829388547 113657333675534104244082821)
        ·
          refine ⟨21310750064162644545765529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 113657333675534104244082821 21310750064162644545765529)
          ·
            refine ⟨15983062548121983409324147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21310750064162644545765529 15983062548121983409324147)
            ·
              refine ⟨23974593822182975113986221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15983062548121983409324147 23974593822182975113986221)
              ·
                refine ⟨8990472683318615667744833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23974593822182975113986221 8990472683318615667744833)
                ·
                  refine ⟨6742854512488961750808625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8990472683318615667744833 6742854512488961750808625)
                  ·
                    refine ⟨5057140884366721313106469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6742854512488961750808625 5057140884366721313106469)
                    ·
                      refine ⟨948213915818760246207463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5057140884366721313106469 948213915818760246207463)
                      ·
                        rfl

theorem cell23_1846640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 3, 2, 2, 4].length) (baseStart_1846640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1846640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1846640 prefixEnd_1846640 := by exact prefixLift 1846640
  have htrace : WordTrace (prefixWord ++ tailWord_1846640) baseStart_1846640 baseEnd_1846640 := by
    simpa [prefixWord, tailWord_1846640, baseEnd_1846640] using wordTrace_append hprefix tailTrace_1846640
  have hstable : (prefixWord ++ tailWord_1846640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1846640).length < 2 ^ (prefixWord ++ tailWord_1846640).sum := by decide
  have hdescent : baseEnd_1846640 < baseStart_1846640 := by decide
  rcases family_descends (prefixWord ++ tailWord_1846640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1846700 : List Nat := [2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 4]
def baseStart_1846700 : Nat := 118140960795 + 1846700 * 2 ^ 59
def prefixEnd_1846700 : Nat := 4983230072969 + 3 ^ 40 * 1846700 * 2
def baseEnd_1846700 : Nat := 948244724658030011457187

theorem tailTrace_1846700 : CollatzResearch.WordTrace tailWord_1846700 prefixEnd_1846700 948244724658030011457187 := by
  unfold tailWord_1846700
  simp only [CollatzResearch.WordTrace]
  refine ⟨33677341204864383047764777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44903121606485844063686369 33677341204864383047764777)
  ·
    refine ⟨25258005903648287285823583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33677341204864383047764777 25258005903648287285823583)
    ·
      refine ⟨37887008855472430928735375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25258005903648287285823583 37887008855472430928735375)
      ·
        refine ⟨56830513283208646393103063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37887008855472430928735375 56830513283208646393103063)
        ·
          refine ⟨85245769924812969589654595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56830513283208646393103063 85245769924812969589654595)
          ·
            refine ⟨127868654887219454384481893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85245769924812969589654595 127868654887219454384481893)
            ·
              refine ⟨23975372791353647697090355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 127868654887219454384481893 23975372791353647697090355)
              ·
                refine ⟨35963059187030471545635533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23975372791353647697090355 35963059187030471545635533)
                ·
                  refine ⟨13486147195136426829613325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35963059187030471545635533 13486147195136426829613325)
                  ·
                    refine ⟨5057305198176160061104997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13486147195136426829613325 5057305198176160061104997)
                    ·
                      refine ⟨948244724658030011457187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5057305198176160061104997 948244724658030011457187)
                      ·
                        rfl

theorem cell23_1846700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 4].length) (baseStart_1846700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1846700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1846700 prefixEnd_1846700 := by exact prefixLift 1846700
  have htrace : WordTrace (prefixWord ++ tailWord_1846700) baseStart_1846700 baseEnd_1846700 := by
    simpa [prefixWord, tailWord_1846700, baseEnd_1846700] using wordTrace_append hprefix tailTrace_1846700
  have hstable : (prefixWord ++ tailWord_1846700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1846700).length < 2 ^ (prefixWord ++ tailWord_1846700).sum := by decide
  have hdescent : baseEnd_1846700 < baseStart_1846700 := by decide
  rcases family_descends (prefixWord ++ tailWord_1846700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1846801 : List Nat := [1, 2, 2, 1, 1, 2, 3, 6, 1, 1, 3]
def baseStart_1846801 : Nat := 118140960795 + 1846801 * 2 ^ 59
def prefixEnd_1846801 : Nat := 4983230072969 + 3 ^ 40 * 1846801 * 2
def baseEnd_1846801 : Nat := 948296586204134116294223

theorem tailTrace_1846801 : CollatzResearch.WordTrace tailWord_1846801 prefixEnd_1846801 948296586204134116294223 := by
  unfold tailWord_1846801
  simp only [CollatzResearch.WordTrace]
  refine ⟨67358366182362860344956257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44905577454908573563304171 67358366182362860344956257)
  ·
    refine ⟨50518774636772145258717193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67358366182362860344956257 50518774636772145258717193)
    ·
      refine ⟨37889080977579108944037895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50518774636772145258717193 37889080977579108944037895)
      ·
        refine ⟨56833621466368663416056843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37889080977579108944037895 56833621466368663416056843)
        ·
          refine ⟨85250432199552995124085265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56833621466368663416056843 85250432199552995124085265)
          ·
            refine ⟨63937824149664746343063949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85250432199552995124085265 63937824149664746343063949)
            ·
              refine ⟨23976684056124279878648981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63937824149664746343063949 23976684056124279878648981)
              ·
                refine ⟨1123907065130825619311671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 23976684056124279878648981 1123907065130825619311671)
                ·
                  refine ⟨1685860597696238428967507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1123907065130825619311671 1685860597696238428967507)
                  ·
                    refine ⟨2528790896544357643451261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1685860597696238428967507 2528790896544357643451261)
                    ·
                      refine ⟨948296586204134116294223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2528790896544357643451261 948296586204134116294223)
                      ·
                        rfl

theorem cell23_1846801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 6, 1, 1, 3].length) (baseStart_1846801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1846801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1846801 prefixEnd_1846801 := by exact prefixLift 1846801
  have htrace : WordTrace (prefixWord ++ tailWord_1846801) baseStart_1846801 baseEnd_1846801 := by
    simpa [prefixWord, tailWord_1846801, baseEnd_1846801] using wordTrace_append hprefix tailTrace_1846801
  have hstable : (prefixWord ++ tailWord_1846801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1846801).length < 2 ^ (prefixWord ++ tailWord_1846801).sum := by decide
  have hdescent : baseEnd_1846801 < baseStart_1846801 := by decide
  rcases family_descends (prefixWord ++ tailWord_1846801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1846847 : List Nat := [1, 1, 2, 2, 3, 5, 9]
def baseStart_1846847 : Nat := 118140960795 + 1846847 * 2 ^ 59
def prefixEnd_1846847 : Nat := 4983230072969 + 3 ^ 40 * 1846847 * 2
def baseEnd_1846847 : Nat := 11707656868077048596531

theorem tailTrace_1846847 : CollatzResearch.WordTrace tailWord_1846847 prefixEnd_1846847 11707656868077048596531 := by
  unfold tailWord_1846847
  simp only [CollatzResearch.WordTrace]
  refine ⟨67360043940196210201130795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44906695960130806800753863 67360043940196210201130795)
  ·
    refine ⟨101040065910294315301696193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67360043940196210201130795 101040065910294315301696193)
    ·
      refine ⟨75780049432720736476272145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101040065910294315301696193 75780049432720736476272145)
      ·
        refine ⟨56835037074540552357204109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75780049432720736476272145 56835037074540552357204109)
        ·
          refine ⟨21313138902952707133951541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56835037074540552357204109 21313138902952707133951541)
          ·
            refine ⟨1998106772151816293807957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21313138902952707133951541 1998106772151816293807957)
            ·
              refine ⟨11707656868077048596531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1998106772151816293807957 11707656868077048596531)
              ·
                rfl

theorem cell23_1846847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 9].length) (baseStart_1846847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1846847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1846847 prefixEnd_1846847 := by exact prefixLift 1846847
  have htrace : WordTrace (prefixWord ++ tailWord_1846847) baseStart_1846847 baseEnd_1846847 := by
    simpa [prefixWord, tailWord_1846847, baseEnd_1846847] using wordTrace_append hprefix tailTrace_1846847
  have hstable : (prefixWord ++ tailWord_1846847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1846847).length < 2 ^ (prefixWord ++ tailWord_1846847).sum := by decide
  have hdescent : baseEnd_1846847 < baseStart_1846847 := by decide
  rcases family_descends (prefixWord ++ tailWord_1846847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1846887 : List Nat := [1, 1, 5, 1, 1, 1, 2, 1, 1, 4, 5]
def baseStart_1846887 : Nat := 118140960795 + 1846887 * 2 ^ 59
def prefixEnd_1846887 : Nat := 4983230072969 + 3 ^ 40 * 1846887 * 2
def baseEnd_1846887 : Nat := 948340745540420779818827

theorem tailTrace_1846887 : CollatzResearch.WordTrace tailWord_1846887 prefixEnd_1846887 948340745540420779818827 := by
  unfold tailWord_1846887
  simp only [CollatzResearch.WordTrace]
  refine ⟨67361502860051297032586915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44907668573367531355057943 67361502860051297032586915)
  ·
    refine ⟨101042254290076945548880373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67361502860051297032586915 101042254290076945548880373)
    ·
      refine ⟨9472711339694713645207535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 101042254290076945548880373 9472711339694713645207535)
      ·
        refine ⟨14209067009542070467811303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9472711339694713645207535 14209067009542070467811303)
        ·
          refine ⟨21313600514313105701716955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14209067009542070467811303 21313600514313105701716955)
          ·
            refine ⟨31970400771469658552575433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21313600514313105701716955 31970400771469658552575433)
            ·
              refine ⟨23977800578602243914431575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31970400771469658552575433 23977800578602243914431575)
              ·
                refine ⟨35966700867903365871647363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23977800578602243914431575 35966700867903365871647363)
                ·
                  refine ⟨53950051301855048807471045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35966700867903365871647363 53950051301855048807471045)
                  ·
                    refine ⟨10115634619097821651400821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53950051301855048807471045 10115634619097821651400821)
                    ·
                      refine ⟨948340745540420779818827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10115634619097821651400821 948340745540420779818827)
                      ·
                        rfl

theorem cell23_1846887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 1, 1, 4, 5].length) (baseStart_1846887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1846887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1846887 prefixEnd_1846887 := by exact prefixLift 1846887
  have htrace : WordTrace (prefixWord ++ tailWord_1846887) baseStart_1846887 baseEnd_1846887 := by
    simpa [prefixWord, tailWord_1846887, baseEnd_1846887] using wordTrace_append hprefix tailTrace_1846887
  have hstable : (prefixWord ++ tailWord_1846887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1846887).length < 2 ^ (prefixWord ++ tailWord_1846887).sum := by decide
  have hdescent : baseEnd_1846887 < baseStart_1846887 := by decide
  rcases family_descends (prefixWord ++ tailWord_1846887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1846897 : List Nat := [1, 2, 2, 2, 1, 1, 1, 2, 4, 3, 4]
def baseStart_1846897 : Nat := 118140960795 + 1846897 * 2 ^ 59
def prefixEnd_1846897 : Nat := 4983230072969 + 3 ^ 40 * 1846897 * 2
def baseEnd_1846897 : Nat := 948345880346965740693781

theorem tailTrace_1846897 : CollatzResearch.WordTrace tailWord_1846897 prefixEnd_1846897 948345880346965740693781 := by
  unfold tailWord_1846897
  simp only [CollatzResearch.WordTrace]
  refine ⟨67361867590015068740450945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44907911726676712493633963 67361867590015068740450945)
  ·
    refine ⟨50521400692511301555338209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67361867590015068740450945 50521400692511301555338209)
    ·
      refine ⟨37891050519383476166503657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50521400692511301555338209 37891050519383476166503657)
      ·
        refine ⟨28418287889537607124877743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37891050519383476166503657 28418287889537607124877743)
        ·
          refine ⟨42627431834306410687316615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28418287889537607124877743 42627431834306410687316615)
          ·
            refine ⟨63941147751459616030974923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42627431834306410687316615 63941147751459616030974923)
            ·
              refine ⟨95911721627189424046462385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63941147751459616030974923 95911721627189424046462385)
              ·
                refine ⟨71933791220392068034846789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95911721627189424046462385 71933791220392068034846789)
                ·
                  refine ⟨13487585853823512756533773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71933791220392068034846789 13487585853823512756533773)
                  ·
                    refine ⟨5057844695183817283700165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13487585853823512756533773 5057844695183817283700165)
                    ·
                      refine ⟨948345880346965740693781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5057844695183817283700165 948345880346965740693781)
                      ·
                        rfl

theorem cell23_1846897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 4, 3, 4].length) (baseStart_1846897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1846897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1846897 prefixEnd_1846897 := by exact prefixLift 1846897
  have htrace : WordTrace (prefixWord ++ tailWord_1846897) baseStart_1846897 baseEnd_1846897 := by
    simpa [prefixWord, tailWord_1846897, baseEnd_1846897] using wordTrace_append hprefix tailTrace_1846897
  have hstable : (prefixWord ++ tailWord_1846897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1846897).length < 2 ^ (prefixWord ++ tailWord_1846897).sum := by decide
  have hdescent : baseEnd_1846897 < baseStart_1846897 := by decide
  rcases family_descends (prefixWord ++ tailWord_1846897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1846907 : List Nat := [1, 1, 1, 1, 1, 4, 4, 2, 2, 6]
def baseStart_1846907 : Nat := 118140960795 + 1846907 * 2 ^ 59
def prefixEnd_1846907 : Nat := 4983230072969 + 3 ^ 40 * 1846907 * 2
def baseEnd_1846907 : Nat := 316117005051170233856245

theorem tailTrace_1846907 : CollatzResearch.WordTrace tailWord_1846907 prefixEnd_1846907 316117005051170233856245 := by
  unfold tailWord_1846907
  simp only [CollatzResearch.WordTrace]
  refine ⟨67362232319978840448314975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44908154879985893632209983 67362232319978840448314975)
  ·
    refine ⟨101043348479968260672472463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67362232319978840448314975 101043348479968260672472463)
    ·
      refine ⟨151565022719952391008708695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101043348479968260672472463 151565022719952391008708695)
      ·
        refine ⟨227347534079928586513063043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151565022719952391008708695 227347534079928586513063043)
        ·
          refine ⟨341021301119892879769594565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227347534079928586513063043 341021301119892879769594565)
          ·
            refine ⟨63941493959979914956798981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 341021301119892879769594565 63941493959979914956798981)
            ·
              refine ⟨11989030117496234054399809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63941493959979914956798981 11989030117496234054399809)
              ·
                refine ⟨8991772588122175540799857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11989030117496234054399809 8991772588122175540799857)
                ·
                  refine ⟨6743829441091631655599893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8991772588122175540799857 6743829441091631655599893)
                  ·
                    refine ⟨316117005051170233856245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6743829441091631655599893 316117005051170233856245)
                    ·
                      rfl

theorem cell23_1846907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 2, 2, 6].length) (baseStart_1846907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1846907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1846907 prefixEnd_1846907 := by exact prefixLift 1846907
  have htrace : WordTrace (prefixWord ++ tailWord_1846907) baseStart_1846907 baseEnd_1846907 := by
    simpa [prefixWord, tailWord_1846907, baseEnd_1846907] using wordTrace_append hprefix tailTrace_1846907
  have hstable : (prefixWord ++ tailWord_1846907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1846907).length < 2 ^ (prefixWord ++ tailWord_1846907).sum := by decide
  have hdescent : baseEnd_1846907 < baseStart_1846907 := by decide
  rcases family_descends (prefixWord ++ tailWord_1846907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1846965 : List Nat := [1, 3, 3, 3, 2, 1, 1, 1, 4, 2, 2]
def baseStart_1846965 : Nat := 118140960795 + 1846965 * 2 ^ 59
def prefixEnd_1846965 : Nat := 4983230072969 + 3 ^ 40 * 1846965 * 2
def baseEnd_1846965 : Nat := 948380797031471474643469

theorem tailTrace_1846965 : CollatzResearch.WordTrace tailWord_1846965 prefixEnd_1846965 948380797031471474643469 := by
  unfold tailWord_1846965
  simp only [CollatzResearch.WordTrace]
  refine ⟨67364347753768716353926349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44909565169179144235950899 67364347753768716353926349)
  ·
    refine ⟨25261630407663268632722381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67364347753768716353926349 25261630407663268632722381)
    ·
      refine ⟨9473111402873725737270893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25261630407663268632722381 9473111402873725737270893)
      ·
        refine ⟨3552416776077647151476585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9473111402873725737270893 3552416776077647151476585)
        ·
          refine ⟨2664312582058235363607439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3552416776077647151476585 2664312582058235363607439)
          ·
            refine ⟨3996468873087353045411159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2664312582058235363607439 3996468873087353045411159)
            ·
              refine ⟨5994703309631029568116739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3996468873087353045411159 5994703309631029568116739)
              ·
                refine ⟨8992054964446544352175109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5994703309631029568116739 8992054964446544352175109)
                ·
                  refine ⟨1686010305833727066032833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8992054964446544352175109 1686010305833727066032833)
                  ·
                    refine ⟨1264507729375295299524625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1686010305833727066032833 1264507729375295299524625)
                    ·
                      refine ⟨948380797031471474643469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1264507729375295299524625 948380797031471474643469)
                      ·
                        rfl

theorem cell23_1846965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 1, 4, 2, 2].length) (baseStart_1846965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1846965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1846965 prefixEnd_1846965 := by exact prefixLift 1846965
  have htrace : WordTrace (prefixWord ++ tailWord_1846965) baseStart_1846965 baseEnd_1846965 := by
    simpa [prefixWord, tailWord_1846965, baseEnd_1846965] using wordTrace_append hprefix tailTrace_1846965
  have hstable : (prefixWord ++ tailWord_1846965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1846965).length < 2 ^ (prefixWord ++ tailWord_1846965).sum := by decide
  have hdescent : baseEnd_1846965 < baseStart_1846965 := by decide
  rcases family_descends (prefixWord ++ tailWord_1846965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1846982 : List Nat := [6, 1, 2, 1, 1, 1, 3, 1, 1, 4, 2]
def baseStart_1846982 : Nat := 118140960795 + 1846982 * 2 ^ 59
def prefixEnd_1846982 : Nat := 4983230072969 + 3 ^ 40 * 1846982 * 2
def baseEnd_1846982 : Nat := 948389526202597908130891

theorem tailTrace_1846982 : CollatzResearch.WordTrace tailWord_1846982 prefixEnd_1846982 948389526202597908130891 := by
  unfold tailWord_1846982
  simp only [CollatzResearch.WordTrace]
  refine ⟨2105155243584597758040475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 44909978529804752171530133 2105155243584597758040475)
  ·
    refine ⟨3157732865376896637060713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2105155243584597758040475 3157732865376896637060713)
    ·
      refine ⟨2368299649032672477795535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3157732865376896637060713 2368299649032672477795535)
      ·
        refine ⟨3552449473549008716693303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2368299649032672477795535 3552449473549008716693303)
        ·
          refine ⟨5328674210323513075039955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3552449473549008716693303 5328674210323513075039955)
          ·
            refine ⟨7993011315485269612559933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5328674210323513075039955 7993011315485269612559933)
            ·
              refine ⟨2997379243306976104709975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7993011315485269612559933 2997379243306976104709975)
              ·
                refine ⟨4496068864960464157064963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2997379243306976104709975 4496068864960464157064963)
                ·
                  refine ⟨6744103297440696235597445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4496068864960464157064963 6744103297440696235597445)
                  ·
                    refine ⟨1264519368270130544174521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6744103297440696235597445 1264519368270130544174521)
                    ·
                      refine ⟨948389526202597908130891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1264519368270130544174521 948389526202597908130891)
                      ·
                        rfl

theorem cell23_1846982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 3, 1, 1, 4, 2].length) (baseStart_1846982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1846982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1846982 prefixEnd_1846982 := by exact prefixLift 1846982
  have htrace : WordTrace (prefixWord ++ tailWord_1846982) baseStart_1846982 baseEnd_1846982 := by
    simpa [prefixWord, tailWord_1846982, baseEnd_1846982] using wordTrace_append hprefix tailTrace_1846982
  have hstable : (prefixWord ++ tailWord_1846982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1846982).length < 2 ^ (prefixWord ++ tailWord_1846982).sum := by decide
  have hdescent : baseEnd_1846982 < baseStart_1846982 := by decide
  rcases family_descends (prefixWord ++ tailWord_1846982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1847021 : List Nat := [1, 5, 1, 2, 1, 2, 1, 1, 4, 1, 4]
def baseStart_1847021 : Nat := 118140960795 + 1847021 * 2 ^ 59
def prefixEnd_1847021 : Nat := 4983230072969 + 3 ^ 40 * 1847021 * 2
def baseEnd_1847021 : Nat := 948409551948123255543211

theorem tailTrace_1847021 : CollatzResearch.WordTrace tailWord_1847021 prefixEnd_1847021 948409551948123255543211 := by
  unfold tailWord_1847021
  simp only [CollatzResearch.WordTrace]
  refine ⟨67366390241565837917964917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44910926827710558611976611 67366390241565837917964917)
  ·
    refine ⟨6315599085146797304809211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 67366390241565837917964917 6315599085146797304809211)
    ·
      refine ⟨9473398627720195957213817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6315599085146797304809211 9473398627720195957213817)
      ·
        refine ⟨7105048970790146967910363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9473398627720195957213817 7105048970790146967910363)
        ·
          refine ⟨10657573456185220451865545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7105048970790146967910363 10657573456185220451865545)
          ·
            refine ⟨7993180092138915338899159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10657573456185220451865545 7993180092138915338899159)
            ·
              refine ⟨11989770138208373008348739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7993180092138915338899159 11989770138208373008348739)
              ·
                refine ⟨17984655207312559512523109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11989770138208373008348739 17984655207312559512523109)
                ·
                  refine ⟨3372122851371104908598083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17984655207312559512523109 3372122851371104908598083)
                  ·
                    refine ⟨5058184277056657362897125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3372122851371104908598083 5058184277056657362897125)
                    ·
                      refine ⟨948409551948123255543211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5058184277056657362897125 948409551948123255543211)
                      ·
                        rfl

theorem cell23_1847021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 1, 4, 1, 4].length) (baseStart_1847021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1847021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1847021 prefixEnd_1847021 := by exact prefixLift 1847021
  have htrace : WordTrace (prefixWord ++ tailWord_1847021) baseStart_1847021 baseEnd_1847021 := by
    simpa [prefixWord, tailWord_1847021, baseEnd_1847021] using wordTrace_append hprefix tailTrace_1847021
  have hstable : (prefixWord ++ tailWord_1847021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1847021).length < 2 ^ (prefixWord ++ tailWord_1847021).sum := by decide
  have hdescent : baseEnd_1847021 < baseStart_1847021 := by decide
  rcases family_descends (prefixWord ++ tailWord_1847021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1847024 : List Nat := [2, 1, 1, 1, 3, 1, 2, 2, 3, 4, 3]
def baseStart_1847024 : Nat := 118140960795 + 1847024 * 2 ^ 59
def prefixEnd_1847024 : Nat := 4983230072969 + 3 ^ 40 * 1847024 * 2
def baseEnd_1847024 : Nat := 948411092390086743805697

theorem tailTrace_1847024 : CollatzResearch.WordTrace tailWord_1847024 prefixEnd_1847024 948411092390086743805697 := by
  unfold tailWord_1847024
  simp only [CollatzResearch.WordTrace]
  refine ⟨33683249830277484715162063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44910999773703312953549417 33683249830277484715162063)
  ·
    refine ⟨50524874745416227072743095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33683249830277484715162063 50524874745416227072743095)
    ·
      refine ⟨75787312118124340609114643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50524874745416227072743095 75787312118124340609114643)
      ·
        refine ⟨113680968177186510913671965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75787312118124340609114643 113680968177186510913671965)
        ·
          refine ⟨42630363066444941592626987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113680968177186510913671965 42630363066444941592626987)
          ·
            refine ⟨63945544599667412388940481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42630363066444941592626987 63945544599667412388940481)
            ·
              refine ⟨47959158449750559291705361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63945544599667412388940481 47959158449750559291705361)
              ·
                refine ⟨35969368837312919468779021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47959158449750559291705361 35969368837312919468779021)
                ·
                  refine ⟨13488513313992344800792133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35969368837312919468779021 13488513313992344800792133)
                  ·
                    refine ⟨2529096246373564650148525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13488513313992344800792133 2529096246373564650148525)
                    ·
                      refine ⟨948411092390086743805697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2529096246373564650148525 948411092390086743805697)
                      ·
                        rfl

theorem cell23_1847024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 2, 3, 4, 3].length) (baseStart_1847024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1847024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1847024 prefixEnd_1847024 := by exact prefixLift 1847024
  have htrace : WordTrace (prefixWord ++ tailWord_1847024) baseStart_1847024 baseEnd_1847024 := by
    simpa [prefixWord, tailWord_1847024, baseEnd_1847024] using wordTrace_append hprefix tailTrace_1847024
  have hstable : (prefixWord ++ tailWord_1847024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1847024).length < 2 ^ (prefixWord ++ tailWord_1847024).sum := by decide
  have hdescent : baseEnd_1847024 < baseStart_1847024 := by decide
  rcases family_descends (prefixWord ++ tailWord_1847024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1847028 : List Nat := [2, 6, 1, 1, 1, 1, 1, 1, 1, 1, 7]
def baseStart_1847028 : Nat := 118140960795 + 1847028 * 2 ^ 59
def prefixEnd_1847028 : Nat := 4983230072969 + 3 ^ 40 * 1847028 * 2
def baseEnd_1847028 : Nat := 948413146312704728155679

theorem tailTrace_1847028 : CollatzResearch.WordTrace tailWord_1847028 prefixEnd_1847028 948413146312704728155679 := by
  unfold tailWord_1847028
  simp only [CollatzResearch.WordTrace]
  refine ⟨33683322776270239056734869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44911097035026985408979825 33683322776270239056734869)
  ·
    refine ⟨1578905755137667455784447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 33683322776270239056734869 1578905755137667455784447)
    ·
      refine ⟨2368358632706501183676671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1578905755137667455784447 2368358632706501183676671)
      ·
        refine ⟨3552537949059751775515007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2368358632706501183676671 3552537949059751775515007)
        ·
          refine ⟨5328806923589627663272511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3552537949059751775515007 5328806923589627663272511)
          ·
            refine ⟨7993210385384441494908767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5328806923589627663272511 7993210385384441494908767)
            ·
              refine ⟨11989815578076662242363151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7993210385384441494908767 11989815578076662242363151)
              ·
                refine ⟨17984723367114993363544727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11989815578076662242363151 17984723367114993363544727)
                ·
                  refine ⟨26977085050672490045317091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17984723367114993363544727 26977085050672490045317091)
                  ·
                    refine ⟨40465627576008735067975637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26977085050672490045317091 40465627576008735067975637)
                    ·
                      refine ⟨948413146312704728155679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 40465627576008735067975637 948413146312704728155679)
                      ·
                        rfl

theorem cell23_1847028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_1847028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1847028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1847028 prefixEnd_1847028 := by exact prefixLift 1847028
  have htrace : WordTrace (prefixWord ++ tailWord_1847028) baseStart_1847028 baseEnd_1847028 := by
    simpa [prefixWord, tailWord_1847028, baseEnd_1847028] using wordTrace_append hprefix tailTrace_1847028
  have hstable : (prefixWord ++ tailWord_1847028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1847028).length < 2 ^ (prefixWord ++ tailWord_1847028).sum := by decide
  have hdescent : baseEnd_1847028 < baseStart_1847028 := by decide
  rcases family_descends (prefixWord ++ tailWord_1847028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1847031 : List Nat := [1, 1, 3, 1, 1, 1, 7, 1, 3, 4]
def baseStart_1847031 : Nat := 118140960795 + 1847031 * 2 ^ 59
def prefixEnd_1847031 : Nat := 4983230072969 + 3 ^ 40 * 1847031 * 2
def baseEnd_1847031 : Nat := 316138228918222738806055

theorem tailTrace_1847031 : CollatzResearch.WordTrace tailWord_1847031 prefixEnd_1847031 316138228918222738806055 := by
  unfold tailWord_1847031
  simp only [CollatzResearch.WordTrace]
  refine ⟨67366754971529609625828947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44911169981019739750552631 67366754971529609625828947)
  ·
    refine ⟨101050132457294414438743421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67366754971529609625828947 101050132457294414438743421)
    ·
      refine ⟨37893799671485405414528783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101050132457294414438743421 37893799671485405414528783)
      ·
        refine ⟨56840699507228108121793175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37893799671485405414528783 56840699507228108121793175)
        ·
          refine ⟨85261049260842162182689763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56840699507228108121793175 85261049260842162182689763)
          ·
            refine ⟨127891573891263243274034645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85261049260842162182689763 127891573891263243274034645)
            ·
              refine ⟨2997458763076482264235187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 127891573891263243274034645 2997458763076482264235187)
              ·
                refine ⟨4496188144614723396352781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2997458763076482264235187 4496188144614723396352781)
                ·
                  refine ⟨1686070554230521273632293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4496188144614723396352781 1686070554230521273632293)
                  ·
                    refine ⟨316138228918222738806055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1686070554230521273632293 316138228918222738806055)
                    ·
                      rfl

theorem cell23_1847031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 7, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 7, 1, 3, 4].length) (baseStart_1847031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1847031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1847031 prefixEnd_1847031 := by exact prefixLift 1847031
  have htrace : WordTrace (prefixWord ++ tailWord_1847031) baseStart_1847031 baseEnd_1847031 := by
    simpa [prefixWord, tailWord_1847031, baseEnd_1847031] using wordTrace_append hprefix tailTrace_1847031
  have hstable : (prefixWord ++ tailWord_1847031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1847031).length < 2 ^ (prefixWord ++ tailWord_1847031).sum := by decide
  have hdescent : baseEnd_1847031 < baseStart_1847031 := by decide
  rcases family_descends (prefixWord ++ tailWord_1847031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1847111 : List Nat := [1, 1, 4, 1, 2, 1, 4, 1, 3, 1, 4]
def baseStart_1847111 : Nat := 118140960795 + 1847111 * 2 ^ 59
def prefixEnd_1847111 : Nat := 4983230072969 + 3 ^ 40 * 1847111 * 2
def baseEnd_1847111 : Nat := 948455765207027903417797

theorem tailTrace_1847111 : CollatzResearch.WordTrace tailWord_1847111 prefixEnd_1847111 948455765207027903417797 := by
  unfold tailWord_1847111
  simp only [CollatzResearch.WordTrace]
  refine ⟨67369672811239783288741187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44913115207493188859160791 67369672811239783288741187)
  ·
    refine ⟨101054509216859674933111781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67369672811239783288741187 101054509216859674933111781)
    ·
      refine ⟨18947720478161189049958459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101054509216859674933111781 18947720478161189049958459)
      ·
        refine ⟨28421580717241783574937689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18947720478161189049958459 28421580717241783574937689)
        ·
          refine ⟨21316185537931337681203267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28421580717241783574937689 21316185537931337681203267)
          ·
            refine ⟨31974278306897006521804901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21316185537931337681203267 31974278306897006521804901)
            ·
              refine ⟨5995177182543188722838419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31974278306897006521804901 5995177182543188722838419)
              ·
                refine ⟨8992765773814783084257629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5995177182543188722838419 8992765773814783084257629)
                ·
                  refine ⟨3372287165180543656596611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8992765773814783084257629 3372287165180543656596611)
                  ·
                    refine ⟨5058430747770815484894917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3372287165180543656596611 5058430747770815484894917)
                    ·
                      refine ⟨948455765207027903417797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5058430747770815484894917 948455765207027903417797)
                      ·
                        rfl

theorem cell23_1847111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 1, 3, 1, 4].length) (baseStart_1847111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1847111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1847111 prefixEnd_1847111 := by exact prefixLift 1847111
  have htrace : WordTrace (prefixWord ++ tailWord_1847111) baseStart_1847111 baseEnd_1847111 := by
    simpa [prefixWord, tailWord_1847111, baseEnd_1847111] using wordTrace_append hprefix tailTrace_1847111
  have hstable : (prefixWord ++ tailWord_1847111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1847111).length < 2 ^ (prefixWord ++ tailWord_1847111).sum := by decide
  have hdescent : baseEnd_1847111 < baseStart_1847111 := by decide
  rcases family_descends (prefixWord ++ tailWord_1847111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1847121 : List Nat := [1, 2, 2, 1, 5, 1, 2, 2, 1, 6]
def baseStart_1847121 : Nat := 118140960795 + 1847121 * 2 ^ 59
def prefixEnd_1847121 : Nat := 4983230072969 + 3 ^ 40 * 1847121 * 2
def baseEnd_1847121 : Nat := 316153633337857621430917

theorem tailTrace_1847121 : CollatzResearch.WordTrace tailWord_1847121 prefixEnd_1847121 316153633337857621430917 := by
  unfold tailWord_1847121
  simp only [CollatzResearch.WordTrace]
  refine ⟨67370037541203554996605217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44913358360802369997736811 67370037541203554996605217)
  ·
    refine ⟨50527528155902666247453913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67370037541203554996605217 50527528155902666247453913)
    ·
      refine ⟨37895646116926999685590435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50527528155902666247453913 37895646116926999685590435)
      ·
        refine ⟨56843469175390499528385653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37895646116926999685590435 56843469175390499528385653)
        ·
          refine ⟨5329075235192859330786155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 56843469175390499528385653 5329075235192859330786155)
          ·
            refine ⟨7993612852789288996179233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5329075235192859330786155 7993612852789288996179233)
            ·
              refine ⟨5995209639591966747134425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7993612852789288996179233 5995209639591966747134425)
              ·
                refine ⟨4496407229693975060350819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5995209639591966747134425 4496407229693975060350819)
                ·
                  refine ⟨6744610844540962590526229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4496407229693975060350819 6744610844540962590526229)
                  ·
                    refine ⟨316153633337857621430917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6744610844540962590526229 316153633337857621430917)
                    ·
                      rfl

theorem cell23_1847121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 2, 1, 6].length) (baseStart_1847121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1847121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1847121 prefixEnd_1847121 := by exact prefixLift 1847121
  have htrace : WordTrace (prefixWord ++ tailWord_1847121) baseStart_1847121 baseEnd_1847121 := by
    simpa [prefixWord, tailWord_1847121, baseEnd_1847121] using wordTrace_append hprefix tailTrace_1847121
  have hstable : (prefixWord ++ tailWord_1847121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1847121).length < 2 ^ (prefixWord ++ tailWord_1847121).sum := by decide
  have hdescent : baseEnd_1847121 < baseStart_1847121 := by decide
  rcases family_descends (prefixWord ++ tailWord_1847121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1847122 : List Nat := [3, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3]
def baseStart_1847122 : Nat := 118140960795 + 1847122 * 2 ^ 59
def prefixEnd_1847122 : Nat := 4983230072969 + 3 ^ 40 * 1847122 * 2
def baseEnd_1847122 : Nat := 948461413494227360380247

theorem tailTrace_1847122 : CollatzResearch.WordTrace tailWord_1847122 prefixEnd_1847122 948461413494227360380247 := by
  unfold tailWord_1847122
  simp only [CollatzResearch.WordTrace]
  refine ⟨16842518503549983041847905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44913382676133288111594413 16842518503549983041847905)
  ·
    refine ⟨12631888877662487281385929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16842518503549983041847905 12631888877662487281385929)
    ·
      refine ⟨9473916658246865461039447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12631888877662487281385929 9473916658246865461039447)
      ·
        refine ⟨14210874987370298191559171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9473916658246865461039447 14210874987370298191559171)
        ·
          refine ⟨21316312481055447287338757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14210874987370298191559171 21316312481055447287338757)
          ·
            refine ⟨3996808590197896366376017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21316312481055447287338757 3996808590197896366376017)
            ·
              refine ⟨2997606442648422274782013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3996808590197896366376017 2997606442648422274782013)
              ·
                refine ⟨1124102415993158353043255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2997606442648422274782013 1124102415993158353043255)
                ·
                  refine ⟨1686153623989737529564883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1124102415993158353043255 1686153623989737529564883)
                  ·
                    refine ⟨2529230435984606294347325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1686153623989737529564883 2529230435984606294347325)
                    ·
                      refine ⟨948461413494227360380247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2529230435984606294347325 948461413494227360380247)
                      ·
                        rfl

theorem cell23_1847122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3].length) (baseStart_1847122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1847122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1847122 prefixEnd_1847122 := by exact prefixLift 1847122
  have htrace : WordTrace (prefixWord ++ tailWord_1847122) baseStart_1847122 baseEnd_1847122 := by
    simpa [prefixWord, tailWord_1847122, baseEnd_1847122] using wordTrace_append hprefix tailTrace_1847122
  have hstable : (prefixWord ++ tailWord_1847122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1847122).length < 2 ^ (prefixWord ++ tailWord_1847122).sum := by decide
  have hdescent : baseEnd_1847122 < baseStart_1847122 := by decide
  rcases family_descends (prefixWord ++ tailWord_1847122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1847125 : List Nat := [1, 3, 2, 2, 2, 4, 2, 1, 1, 5]
def baseStart_1847125 : Nat := 118140960795 + 1847125 * 2 ^ 59
def prefixEnd_1847125 : Nat := 4983230072969 + 3 ^ 40 * 1847125 * 2
def baseEnd_1847125 : Nat := 316154317978730282880911

theorem tailTrace_1847125 : CollatzResearch.WordTrace tailWord_1847125 prefixEnd_1847125 316154317978730282880911 := by
  unfold tailWord_1847125
  simp only [CollatzResearch.WordTrace]
  refine ⟨67370183433189063679750829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44913455622126042453167219 67370183433189063679750829)
  ·
    refine ⟨25263818787445898879906561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67370183433189063679750829 25263818787445898879906561)
    ·
      refine ⟨18947864090584424159929921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25263818787445898879906561 18947864090584424159929921)
      ·
        refine ⟨14210898067938318119947441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18947864090584424159929921 14210898067938318119947441)
        ·
          refine ⟨10658173550953738589960581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14210898067938318119947441 10658173550953738589960581)
          ·
            refine ⟨1998407540803825985617609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10658173550953738589960581 1998407540803825985617609)
            ·
              refine ⟨1498805655602869489213207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1998407540803825985617609 1498805655602869489213207)
              ·
                refine ⟨2248208483404304233819811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1498805655602869489213207 2248208483404304233819811)
                ·
                  refine ⟨3372312725106456350729717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2248208483404304233819811 3372312725106456350729717)
                  ·
                    refine ⟨316154317978730282880911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3372312725106456350729717 316154317978730282880911)
                    ·
                      rfl

theorem cell23_1847125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 2, 1, 1, 5].length) (baseStart_1847125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1847125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1847125 prefixEnd_1847125 := by exact prefixLift 1847125
  have htrace : WordTrace (prefixWord ++ tailWord_1847125) baseStart_1847125 baseEnd_1847125 := by
    simpa [prefixWord, tailWord_1847125, baseEnd_1847125] using wordTrace_append hprefix tailTrace_1847125
  have hstable : (prefixWord ++ tailWord_1847125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1847125).length < 2 ^ (prefixWord ++ tailWord_1847125).sum := by decide
  have hdescent : baseEnd_1847125 < baseStart_1847125 := by decide
  rcases family_descends (prefixWord ++ tailWord_1847125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1847196 : List Nat := [2, 2, 3, 3, 1, 2, 3, 2, 1, 2, 2]
def baseStart_1847196 : Nat := 118140960795 + 1847196 * 2 ^ 59
def prefixEnd_1847196 : Nat := 4983230072969 + 3 ^ 40 * 1847196 * 2
def baseEnd_1847196 : Nat := 948499411062660070854907

theorem tailTrace_1847196 : CollatzResearch.WordTrace tailWord_1847196 prefixEnd_1847196 948499411062660070854907 := by
  unfold tailWord_1847196
  simp only [CollatzResearch.WordTrace]
  refine ⟨33686386507965921402792721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44915182010621228537056961 33686386507965921402792721)
  ·
    refine ⟨25264789880974441052094541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33686386507965921402792721 25264789880974441052094541)
    ·
      refine ⟨9474296205365415394535453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25264789880974441052094541 9474296205365415394535453)
      ·
        refine ⟨3552861077012030772950795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9474296205365415394535453 3552861077012030772950795)
        ·
          refine ⟨5329291615518046159426193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3552861077012030772950795 5329291615518046159426193)
          ·
            refine ⟨3996968711638534619569645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5329291615518046159426193 3996968711638534619569645)
            ·
              refine ⟨1498863266864450482338617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3996968711638534619569645 1498863266864450482338617)
              ·
                refine ⟨1124147450148337861753963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1498863266864450482338617 1124147450148337861753963)
                ·
                  refine ⟨1686221175222506792630945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1124147450148337861753963 1686221175222506792630945)
                  ·
                    refine ⟨1264665881416880094473209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1686221175222506792630945 1264665881416880094473209)
                    ·
                      refine ⟨948499411062660070854907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1264665881416880094473209 948499411062660070854907)
                      ·
                        rfl

theorem cell23_1847196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 3, 2, 1, 2, 2].length) (baseStart_1847196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1847196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1847196 prefixEnd_1847196 := by exact prefixLift 1847196
  have htrace : WordTrace (prefixWord ++ tailWord_1847196) baseStart_1847196 baseEnd_1847196 := by
    simpa [prefixWord, tailWord_1847196, baseEnd_1847196] using wordTrace_append hprefix tailTrace_1847196
  have hstable : (prefixWord ++ tailWord_1847196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1847196).length < 2 ^ (prefixWord ++ tailWord_1847196).sum := by decide
  have hdescent : baseEnd_1847196 < baseStart_1847196 := by decide
  rcases family_descends (prefixWord ++ tailWord_1847196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1847218 : List Nat := [3, 2, 1, 1, 1, 1, 1, 2, 5, 4, 2]
def baseStart_1847218 : Nat := 118140960795 + 1847218 * 2 ^ 59
def prefixEnd_1847218 : Nat := 4983230072969 + 3 ^ 40 * 1847218 * 2
def baseEnd_1847218 : Nat := 948510707637058984779805

theorem tailTrace_1847218 : CollatzResearch.WordTrace tailWord_1847218 prefixEnd_1847218 948510707637058984779805 := by
  unfold tailWord_1847218
  simp only [CollatzResearch.WordTrace]
  refine ⟨16843393855463035140721577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44915716947901427041924205 16843393855463035140721577)
  ·
    refine ⟨12632545391597276355541183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16843393855463035140721577 12632545391597276355541183)
    ·
      refine ⟨18948818087395914533311775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12632545391597276355541183 18948818087395914533311775)
      ·
        refine ⟨28423227131093871799967663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18948818087395914533311775 28423227131093871799967663)
        ·
          refine ⟨42634840696640807699951495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28423227131093871799967663 42634840696640807699951495)
          ·
            refine ⟨63952261044961211549927243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42634840696640807699951495 63952261044961211549927243)
            ·
              refine ⟨95928391567441817324890865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63952261044961211549927243 95928391567441817324890865)
              ·
                refine ⟨71946293675581362993668149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95928391567441817324890865 71946293675581362993668149)
                ·
                  refine ⟨6744965032085752780656389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 71946293675581362993668149 6744965032085752780656389)
                  ·
                    refine ⟨1264680943516078646373073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6744965032085752780656389 1264680943516078646373073)
                    ·
                      refine ⟨948510707637058984779805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1264680943516078646373073 948510707637058984779805)
                      ·
                        rfl

theorem cell23_1847218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 2, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 2, 5, 4, 2].length) (baseStart_1847218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1847218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1847218 prefixEnd_1847218 := by exact prefixLift 1847218
  have htrace : WordTrace (prefixWord ++ tailWord_1847218) baseStart_1847218 baseEnd_1847218 := by
    simpa [prefixWord, tailWord_1847218, baseEnd_1847218] using wordTrace_append hprefix tailTrace_1847218
  have hstable : (prefixWord ++ tailWord_1847218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1847218).length < 2 ^ (prefixWord ++ tailWord_1847218).sum := by decide
  have hdescent : baseEnd_1847218 < baseStart_1847218 := by decide
  rcases family_descends (prefixWord ++ tailWord_1847218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1847268 : List Nat := [2, 3, 1, 1, 1, 1, 5, 1, 2, 3, 3]
def baseStart_1847268 : Nat := 118140960795 + 1847268 * 2 ^ 59
def prefixEnd_1847268 : Nat := 4983230072969 + 3 ^ 40 * 1847268 * 2
def baseEnd_1847268 : Nat := 948536381669783789154575

theorem tailTrace_1847268 : CollatzResearch.WordTrace tailWord_1847268 prefixEnd_1847268 948536381669783789154575 := by
  unfold tailWord_1847268
  simp only [CollatzResearch.WordTrace]
  refine ⟨33687699535835499551103229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44916932714447332734804305 33687699535835499551103229)
  ·
    refine ⟨12632887325938312331663711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33687699535835499551103229 12632887325938312331663711)
    ·
      refine ⟨18949330988907468497495567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12632887325938312331663711 18949330988907468497495567)
      ·
        refine ⟨28423996483361202746243351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18949330988907468497495567 28423996483361202746243351)
        ·
          refine ⟨42635994725041804119365027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28423996483361202746243351 42635994725041804119365027)
          ·
            refine ⟨63953992087562706179047541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42635994725041804119365027 63953992087562706179047541)
            ·
              refine ⟨5995686758209003704285707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 63953992087562706179047541 5995686758209003704285707)
              ·
                refine ⟨8993530137313505556428561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5995686758209003704285707 8993530137313505556428561)
                ·
                  refine ⟨6745147602985129167321421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8993530137313505556428561 6745147602985129167321421)
                  ·
                    refine ⟨2529430351119423437745533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6745147602985129167321421 2529430351119423437745533)
                    ·
                      refine ⟨948536381669783789154575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2529430351119423437745533 948536381669783789154575)
                      ·
                        rfl

theorem cell23_1847268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 1, 2, 3, 3].length) (baseStart_1847268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1847268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1847268 prefixEnd_1847268 := by exact prefixLift 1847268
  have htrace : WordTrace (prefixWord ++ tailWord_1847268) baseStart_1847268 baseEnd_1847268 := by
    simpa [prefixWord, tailWord_1847268, baseEnd_1847268] using wordTrace_append hprefix tailTrace_1847268
  have hstable : (prefixWord ++ tailWord_1847268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1847268).length < 2 ^ (prefixWord ++ tailWord_1847268).sum := by decide
  have hdescent : baseEnd_1847268 < baseStart_1847268 := by decide
  rcases family_descends (prefixWord ++ tailWord_1847268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1847288 : List Nat := [2, 1, 2, 1, 1, 3, 5, 1, 2, 5]
def baseStart_1847288 : Nat := 118140960795 + 1847288 * 2 ^ 59
def prefixEnd_1847288 : Nat := 4983230072969 + 3 ^ 40 * 1847288 * 2
def baseEnd_1847288 : Nat := 316182217094291236968161

theorem tailTrace_1847288 : CollatzResearch.WordTrace tailWord_1847288 prefixEnd_1847288 316182217094291236968161 := by
  unfold tailWord_1847288
  simp only [CollatzResearch.WordTrace]
  refine ⟨33688064265799271258967259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44917419021065695011956345 33688064265799271258967259)
  ·
    refine ⟨50532096398698906888450889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33688064265799271258967259 50532096398698906888450889)
    ·
      refine ⟨37899072299024180166338167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50532096398698906888450889 37899072299024180166338167)
      ·
        refine ⟨56848608448536270249507251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37899072299024180166338167 56848608448536270249507251)
        ·
          refine ⟨85272912672804405374260877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56848608448536270249507251 85272912672804405374260877)
          ·
            refine ⟨31977342252301652015347829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85272912672804405374260877 31977342252301652015347829)
            ·
              refine ⟨2997875836153279876438859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31977342252301652015347829 2997875836153279876438859)
              ·
                refine ⟨4496813754229919814658289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2997875836153279876438859 4496813754229919814658289)
                ·
                  refine ⟨3372610315672439860993717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4496813754229919814658289 3372610315672439860993717)
                  ·
                    refine ⟨316182217094291236968161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3372610315672439860993717 316182217094291236968161)
                    ·
                      rfl

theorem cell23_1847288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 5, 1, 2, 5].length) (baseStart_1847288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1847288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1847288 prefixEnd_1847288 := by exact prefixLift 1847288
  have htrace : WordTrace (prefixWord ++ tailWord_1847288) baseStart_1847288 baseEnd_1847288 := by
    simpa [prefixWord, tailWord_1847288, baseEnd_1847288] using wordTrace_append hprefix tailTrace_1847288
  have hstable : (prefixWord ++ tailWord_1847288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1847288).length < 2 ^ (prefixWord ++ tailWord_1847288).sum := by decide
  have hdescent : baseEnd_1847288 < baseStart_1847288 := by decide
  rcases family_descends (prefixWord ++ tailWord_1847288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1847308 : List Nat := [2, 2, 1, 2, 3, 1, 2, 1, 4, 1, 4]
def baseStart_1847308 : Nat := 118140960795 + 1847308 * 2 ^ 59
def prefixEnd_1847308 : Nat := 4983230072969 + 3 ^ 40 * 1847308 * 2
def baseEnd_1847308 : Nat := 948556920895963632654391

theorem tailTrace_1847308 : CollatzResearch.WordTrace tailWord_1847308 prefixEnd_1847308 948556920895963632654391 := by
  unfold tailWord_1847308
  simp only [CollatzResearch.WordTrace]
  refine ⟨33688428995763042966831289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44917905327684057289108385 33688428995763042966831289)
  ·
    refine ⟨25266321746822282225123467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33688428995763042966831289 25266321746822282225123467)
    ·
      refine ⟨37899482620233423337685201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25266321746822282225123467 37899482620233423337685201)
      ·
        refine ⟨28424611965175067503263901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37899482620233423337685201 28424611965175067503263901)
        ·
          refine ⟨10659229486940650313723963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28424611965175067503263901 10659229486940650313723963)
          ·
            refine ⟨15988844230410975470585945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10659229486940650313723963 15988844230410975470585945)
            ·
              refine ⟨11991633172808231602939459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15988844230410975470585945 11991633172808231602939459)
              ·
                refine ⟨17987449759212347404409189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11991633172808231602939459 17987449759212347404409189)
                ·
                  refine ⟨3372646829852315138326723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17987449759212347404409189 3372646829852315138326723)
                  ·
                    refine ⟨5058970244778472707490085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3372646829852315138326723 5058970244778472707490085)
                    ·
                      refine ⟨948556920895963632654391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5058970244778472707490085 948556920895963632654391)
                      ·
                        rfl

theorem cell23_1847308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 1, 4, 1, 4].length) (baseStart_1847308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1847308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1847308 prefixEnd_1847308 := by exact prefixLift 1847308
  have htrace : WordTrace (prefixWord ++ tailWord_1847308) baseStart_1847308 baseEnd_1847308 := by
    simpa [prefixWord, tailWord_1847308, baseEnd_1847308] using wordTrace_append hprefix tailTrace_1847308
  have hstable : (prefixWord ++ tailWord_1847308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1847308).length < 2 ^ (prefixWord ++ tailWord_1847308).sum := by decide
  have hdescent : baseEnd_1847308 < baseStart_1847308 := by decide
  rcases family_descends (prefixWord ++ tailWord_1847308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1847309 : List Nat := [1, 7, 1, 2, 1, 1, 2, 1, 7]
def baseStart_1847309 : Nat := 118140960795 + 1847309 * 2 ^ 59
def prefixEnd_1847309 : Nat := 4983230072969 + 3 ^ 40 * 1847309 * 2
def baseEnd_1847309 : Nat := 105395270486290903193543

theorem tailTrace_1847309 : CollatzResearch.WordTrace tailWord_1847309 prefixEnd_1847309 105395270486290903193543 := by
  unfold tailWord_1847309
  simp only [CollatzResearch.WordTrace]
  refine ⟨67376894464522463104448981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44917929643014975402965987 67376894464522463104448981)
  ·
    refine ⟨1579145964012245229010523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 67376894464522463104448981 1579145964012245229010523)
    ·
      refine ⟨2368718946018367843515785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1579145964012245229010523 2368718946018367843515785)
      ·
        refine ⟨1776539209513775882636839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2368718946018367843515785 1776539209513775882636839)
        ·
          refine ⟨2664808814270663823955259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1776539209513775882636839 2664808814270663823955259)
          ·
            refine ⟨3997213221405995735932889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2664808814270663823955259 3997213221405995735932889)
            ·
              refine ⟨2997909916054496801949667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3997213221405995735932889 2997909916054496801949667)
              ·
                refine ⟨4496864874081745202924501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2997909916054496801949667 4496864874081745202924501)
                ·
                  refine ⟨105395270486290903193543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4496864874081745202924501 105395270486290903193543)
                  ·
                    rfl

theorem cell23_1847309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 2, 1, 7].length) (baseStart_1847309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1847309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1847309 prefixEnd_1847309 := by exact prefixLift 1847309
  have htrace : WordTrace (prefixWord ++ tailWord_1847309) baseStart_1847309 baseEnd_1847309 := by
    simpa [prefixWord, tailWord_1847309, baseEnd_1847309] using wordTrace_append hprefix tailTrace_1847309
  have hstable : (prefixWord ++ tailWord_1847309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1847309).length < 2 ^ (prefixWord ++ tailWord_1847309).sum := by decide
  have hdescent : baseEnd_1847309 < baseStart_1847309 := by decide
  rcases family_descends (prefixWord ++ tailWord_1847309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1847321 : List Nat := [1, 2, 1, 2, 1, 1, 3, 1, 4, 1, 6]
def baseStart_1847321 : Nat := 118140960795 + 1847321 * 2 ^ 59
def prefixEnd_1847321 : Nat := 4983230072969 + 3 ^ 40 * 1847321 * 2
def baseEnd_1847321 : Nat := 948563596144472081791831

theorem tailTrace_1847321 : CollatzResearch.WordTrace tailWord_1847321 prefixEnd_1847321 948563596144472081791831 := by
  unfold tailWord_1847321
  simp only [CollatzResearch.WordTrace]
  refine ⟨67377332140478989153885817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44918221426985992769257211 67377332140478989153885817)
  ·
    refine ⟨50532999105359241865414363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67377332140478989153885817 50532999105359241865414363)
    ·
      refine ⟨75799498658038862798121545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50532999105359241865414363 75799498658038862798121545)
      ·
        refine ⟨56849623993529147098591159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75799498658038862798121545 56849623993529147098591159)
        ·
          refine ⟨85274435990293720647886739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56849623993529147098591159 85274435990293720647886739)
          ·
            refine ⟨127911653985440580971830109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85274435990293720647886739 127911653985440580971830109)
            ·
              refine ⟨47966870244540217864436291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 127911653985440580971830109 47966870244540217864436291)
              ·
                refine ⟨71950305366810326796654437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47966870244540217864436291 71950305366810326796654437)
                ·
                  refine ⟨13490682256276936274372707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71950305366810326796654437 13490682256276936274372707)
                  ·
                    refine ⟨20236023384415404411559061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13490682256276936274372707 20236023384415404411559061)
                    ·
                      refine ⟨948563596144472081791831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 20236023384415404411559061 948563596144472081791831)
                      ·
                        rfl

theorem cell23_1847321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 4, 1, 6].length) (baseStart_1847321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1847321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1847321 prefixEnd_1847321 := by exact prefixLift 1847321
  have htrace : WordTrace (prefixWord ++ tailWord_1847321) baseStart_1847321 baseEnd_1847321 := by
    simpa [prefixWord, tailWord_1847321, baseEnd_1847321] using wordTrace_append hprefix tailTrace_1847321
  have hstable : (prefixWord ++ tailWord_1847321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1847321).length < 2 ^ (prefixWord ++ tailWord_1847321).sum := by decide
  have hdescent : baseEnd_1847321 < baseStart_1847321 := by decide
  rcases family_descends (prefixWord ++ tailWord_1847321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1847385 : List Nat := [1, 2, 1, 2, 2, 1, 3, 2, 4, 3, 2]
def baseStart_1847385 : Nat := 118140960795 + 1847385 * 2 ^ 59
def prefixEnd_1847385 : Nat := 4983230072969 + 3 ^ 40 * 1847385 * 2
def baseEnd_1847385 : Nat := 948596458906359831391537

theorem tailTrace_1847385 : CollatzResearch.WordTrace tailWord_1847385 prefixEnd_1847385 948596458906359831391537 := by
  unfold tailWord_1847385
  simp only [CollatzResearch.WordTrace]
  refine ⟨67379666412247128084215609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44919777608164752056143739 67379666412247128084215609)
  ·
    refine ⟨50534749809185346063161707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67379666412247128084215609 50534749809185346063161707)
    ·
      refine ⟨75802124713778019094742561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50534749809185346063161707 75802124713778019094742561)
      ·
        refine ⟨56851593535333514321056921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75802124713778019094742561 56851593535333514321056921)
        ·
          refine ⟨42638695151500135740792691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56851593535333514321056921 42638695151500135740792691)
          ·
            refine ⟨63958042727250203611189037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42638695151500135740792691 63958042727250203611189037)
            ·
              refine ⟨23984266022718826354195889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63958042727250203611189037 23984266022718826354195889)
              ·
                refine ⟨17988199517039119765646917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23984266022718826354195889 17988199517039119765646917)
                ·
                  refine ⟨3372787409444834956058797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17988199517039119765646917 3372787409444834956058797)
                  ·
                    refine ⟨1264795278541813108522049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3372787409444834956058797 1264795278541813108522049)
                    ·
                      refine ⟨948596458906359831391537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1264795278541813108522049 948596458906359831391537)
                      ·
                        rfl

theorem cell23_1847385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 2, 4, 3, 2].length) (baseStart_1847385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1847385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1847385 prefixEnd_1847385 := by exact prefixLift 1847385
  have htrace : WordTrace (prefixWord ++ tailWord_1847385) baseStart_1847385 baseEnd_1847385 := by
    simpa [prefixWord, tailWord_1847385, baseEnd_1847385] using wordTrace_append hprefix tailTrace_1847385
  have hstable : (prefixWord ++ tailWord_1847385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1847385).length < 2 ^ (prefixWord ++ tailWord_1847385).sum := by decide
  have hdescent : baseEnd_1847385 < baseStart_1847385 := by decide
  rcases family_descends (prefixWord ++ tailWord_1847385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1847395 : List Nat := [1, 1, 1, 5, 1, 1, 5, 2, 1, 5]
def baseStart_1847395 : Nat := 118140960795 + 1847395 * 2 ^ 59
def prefixEnd_1847395 : Nat := 4983230072969 + 3 ^ 40 * 1847395 * 2
def baseEnd_1847395 : Nat := 316200531237634930755497

theorem tailTrace_1847395 : CollatzResearch.WordTrace tailWord_1847395 prefixEnd_1847395 316200531237634930755497 := by
  unfold tailWord_1847395
  simp only [CollatzResearch.WordTrace]
  refine ⟨67380031142210899792079639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44920020761473933194719759 67380031142210899792079639)
  ·
    refine ⟨101070046713316349688119459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67380031142210899792079639 101070046713316349688119459)
    ·
      refine ⟨151605070069974524532179189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101070046713316349688119459 151605070069974524532179189)
      ·
        refine ⟨14212975319060111674891799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 151605070069974524532179189 14212975319060111674891799)
        ·
          refine ⟨21319462978590167512337699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14212975319060111674891799 21319462978590167512337699)
          ·
            refine ⟨31979194467885251268506549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21319462978590167512337699 31979194467885251268506549)
            ·
              refine ⟨2998049481364242306422489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31979194467885251268506549 2998049481364242306422489)
              ·
                refine ⟨2248537111023181729816867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2998049481364242306422489 2248537111023181729816867)
                ·
                  refine ⟨3372805666534772594725301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2248537111023181729816867 3372805666534772594725301)
                  ·
                    refine ⟨316200531237634930755497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3372805666534772594725301 316200531237634930755497)
                    ·
                      rfl

theorem cell23_1847395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 5, 2, 1, 5].length) (baseStart_1847395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1847395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1847395 prefixEnd_1847395 := by exact prefixLift 1847395
  have htrace : WordTrace (prefixWord ++ tailWord_1847395) baseStart_1847395 baseEnd_1847395 := by
    simpa [prefixWord, tailWord_1847395, baseEnd_1847395] using wordTrace_append hprefix tailTrace_1847395
  have hstable : (prefixWord ++ tailWord_1847395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1847395).length < 2 ^ (prefixWord ++ tailWord_1847395).sum := by decide
  have hdescent : baseEnd_1847395 < baseStart_1847395 := by decide
  rcases family_descends (prefixWord ++ tailWord_1847395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1847408 : List Nat := [2, 1, 1, 1, 5, 2, 1, 1, 3, 6]
def baseStart_1847408 : Nat := 118140960795 + 1847408 * 2 ^ 59
def prefixEnd_1847408 : Nat := 4983230072969 + 3 ^ 40 * 1847408 * 2
def baseEnd_1847408 : Nat := 316202756320471080467977

theorem tailTrace_1847408 : CollatzResearch.WordTrace tailWord_1847408 prefixEnd_1847408 316202756320471080467977 := by
  unfold tailWord_1847408
  simp only [CollatzResearch.WordTrace]
  refine ⟨33690252645581901506151439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44920336860775868674868585 33690252645581901506151439)
  ·
    refine ⟨50535378968372852259227159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33690252645581901506151439 50535378968372852259227159)
    ·
      refine ⟨75803068452559278388840739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50535378968372852259227159 75803068452559278388840739)
      ·
        refine ⟨113704602678838917583261109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75803068452559278388840739 113704602678838917583261109)
        ·
          refine ⟨10659806501141148523430729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 113704602678838917583261109 10659806501141148523430729)
          ·
            refine ⟨7994854875855861392573047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10659806501141148523430729 7994854875855861392573047)
            ·
              refine ⟨11992282313783792088859571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7994854875855861392573047 11992282313783792088859571)
              ·
                refine ⟨17988423470675688133289357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11992282313783792088859571 17988423470675688133289357)
                ·
                  refine ⟨6745658801503383049983509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17988423470675688133289357 6745658801503383049983509)
                  ·
                    refine ⟨316202756320471080467977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6745658801503383049983509 316202756320471080467977)
                    ·
                      rfl

theorem cell23_1847408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 1, 3, 6].length) (baseStart_1847408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1847408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1847408 prefixEnd_1847408 := by exact prefixLift 1847408
  have htrace : WordTrace (prefixWord ++ tailWord_1847408) baseStart_1847408 baseEnd_1847408 := by
    simpa [prefixWord, tailWord_1847408, baseEnd_1847408] using wordTrace_append hprefix tailTrace_1847408
  have hstable : (prefixWord ++ tailWord_1847408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1847408).length < 2 ^ (prefixWord ++ tailWord_1847408).sum := by decide
  have hdescent : baseEnd_1847408 < baseStart_1847408 := by decide
  rcases family_descends (prefixWord ++ tailWord_1847408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1847442 : List Nat := [3, 2, 3, 1, 1, 1, 1, 5, 2, 4]
def baseStart_1847442 : Nat := 118140960795 + 1847442 * 2 ^ 59
def prefixEnd_1847442 : Nat := 4983230072969 + 3 ^ 40 * 1847442 * 2
def baseEnd_1847442 : Nat := 316208575767888702792925

theorem tailTrace_1847442 : CollatzResearch.WordTrace tailWord_1847442 prefixEnd_1847442 316208575767888702792925 := by
  unfold tailWord_1847442
  simp only [CollatzResearch.WordTrace]
  refine ⟨16845436343260156704760145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44921163582027084546027053 16845436343260156704760145)
  ·
    refine ⟨12634077257445117528570109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16845436343260156704760145 12634077257445117528570109)
    ·
      refine ⟨4737778971541919073213791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12634077257445117528570109 4737778971541919073213791)
      ·
        refine ⟨7106668457312878609820687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4737778971541919073213791 7106668457312878609820687)
        ·
          refine ⟨10660002685969317914731031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7106668457312878609820687 10660002685969317914731031)
          ·
            refine ⟨15990004028953976872096547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10660002685969317914731031 15990004028953976872096547)
            ·
              refine ⟨23985006043430965308144821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15990004028953976872096547 23985006043430965308144821)
              ·
                refine ⟨2248594316571652997638577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23985006043430965308144821 2248594316571652997638577)
                ·
                  refine ⟨1686445737428739748228933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2248594316571652997638577 1686445737428739748228933)
                  ·
                    refine ⟨316208575767888702792925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1686445737428739748228933 316208575767888702792925)
                    ·
                      rfl

theorem cell23_1847442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 5, 2, 4].length) (baseStart_1847442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1847442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1847442 prefixEnd_1847442 := by exact prefixLift 1847442
  have htrace : WordTrace (prefixWord ++ tailWord_1847442) baseStart_1847442 baseEnd_1847442 := by
    simpa [prefixWord, tailWord_1847442, baseEnd_1847442] using wordTrace_append hprefix tailTrace_1847442
  have hstable : (prefixWord ++ tailWord_1847442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1847442).length < 2 ^ (prefixWord ++ tailWord_1847442).sum := by decide
  have hdescent : baseEnd_1847442 < baseStart_1847442 := by decide
  rcases family_descends (prefixWord ++ tailWord_1847442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1847445 : List Nat := [1, 3, 2, 1, 1, 1, 6, 1, 1, 2, 4]
def baseStart_1847445 : Nat := 118140960795 + 1847445 * 2 ^ 59
def prefixEnd_1847445 : Nat := 4983230072969 + 3 ^ 40 * 1847445 * 2
def baseEnd_1847445 : Nat := 948627267745629596641261

theorem tailTrace_1847445 : CollatzResearch.WordTrace tailWord_1847445 prefixEnd_1847445 948627267745629596641261 := by
  unfold tailWord_1847445
  simp only [CollatzResearch.WordTrace]
  refine ⟨67381854792029758331399789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44921236528019838887599859 67381854792029758331399789)
  ·
    refine ⟨25268195547011159374274921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67381854792029758331399789 25268195547011159374274921)
    ·
      refine ⟨18951146660258369530706191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25268195547011159374274921 18951146660258369530706191)
      ·
        refine ⟨28426719990387554296059287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18951146660258369530706191 28426719990387554296059287)
        ·
          refine ⟨42640079985581331444088931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28426719990387554296059287 42640079985581331444088931)
          ·
            refine ⟨63960119978371997166133397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42640079985581331444088931 63960119978371997166133397)
            ·
              refine ⟨2998130623986187367162503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 63960119978371997166133397 2998130623986187367162503)
              ·
                refine ⟨4497195935979281050743755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2998130623986187367162503 4497195935979281050743755)
                ·
                  refine ⟨6745793903968921576115633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4497195935979281050743755 6745793903968921576115633)
                  ·
                    refine ⟨5059345427976691182086725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6745793903968921576115633 5059345427976691182086725)
                    ·
                      refine ⟨948627267745629596641261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5059345427976691182086725 948627267745629596641261)
                      ·
                        rfl

theorem cell23_1847445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 6, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 6, 1, 1, 2, 4].length) (baseStart_1847445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1847445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1847445 prefixEnd_1847445 := by exact prefixLift 1847445
  have htrace : WordTrace (prefixWord ++ tailWord_1847445) baseStart_1847445 baseEnd_1847445 := by
    simpa [prefixWord, tailWord_1847445, baseEnd_1847445] using wordTrace_append hprefix tailTrace_1847445
  have hstable : (prefixWord ++ tailWord_1847445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1847445).length < 2 ^ (prefixWord ++ tailWord_1847445).sum := by decide
  have hdescent : baseEnd_1847445 < baseStart_1847445 := by decide
  rcases family_descends (prefixWord ++ tailWord_1847445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1847452 : List Nat := [2, 2, 3, 2, 1, 1, 2, 4, 1, 2, 3]
def baseStart_1847452 : Nat := 118140960795 + 1847452 * 2 ^ 59
def prefixEnd_1847452 : Nat := 4983230072969 + 3 ^ 40 * 1847452 * 2
def baseEnd_1847452 : Nat := 948630862110211069253729

theorem tailTrace_1847452 : CollatzResearch.WordTrace tailWord_1847452 prefixEnd_1847452 948630862110211069253729 := by
  unfold tailWord_1847452
  simp only [CollatzResearch.WordTrace]
  refine ⟨33691055051502199263452305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44921406735336265684603073 33691055051502199263452305)
  ·
    refine ⟨25268291288626649447589229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33691055051502199263452305 25268291288626649447589229)
    ·
      refine ⟨9475609233234993542845961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25268291288626649447589229 9475609233234993542845961)
      ·
        refine ⟨7106706924926245157134471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9475609233234993542845961 7106706924926245157134471)
        ·
          refine ⟨10660060387389367735701707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7106706924926245157134471 10660060387389367735701707)
          ·
            refine ⟨15990090581084051603552561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10660060387389367735701707 15990090581084051603552561)
            ·
              refine ⟨11992567935813038702664421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15990090581084051603552561 11992567935813038702664421)
              ·
                refine ⟨2248606487964944756749579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11992567935813038702664421 2248606487964944756749579)
                ·
                  refine ⟨3372909731947417135124369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2248606487964944756749579 3372909731947417135124369)
                  ·
                    refine ⟨2529682298960562851343277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3372909731947417135124369 2529682298960562851343277)
                    ·
                      refine ⟨948630862110211069253729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2529682298960562851343277 948630862110211069253729)
                      ·
                        rfl

theorem cell23_1847452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 4, 1, 2, 3].length) (baseStart_1847452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1847452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1847452 prefixEnd_1847452 := by exact prefixLift 1847452
  have htrace : WordTrace (prefixWord ++ tailWord_1847452) baseStart_1847452 baseEnd_1847452 := by
    simpa [prefixWord, tailWord_1847452, baseEnd_1847452] using wordTrace_append hprefix tailTrace_1847452
  have hstable : (prefixWord ++ tailWord_1847452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1847452).length < 2 ^ (prefixWord ++ tailWord_1847452).sum := by decide
  have hdescent : baseEnd_1847452 < baseStart_1847452 := by decide
  rcases family_descends (prefixWord ++ tailWord_1847452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1847469 : List Nat := [1, 5, 2, 1, 2, 2, 1, 3, 1, 2, 3]
def baseStart_1847469 : Nat := 118140960795 + 1847469 * 2 ^ 59
def prefixEnd_1847469 : Nat := 4983230072969 + 3 ^ 40 * 1847469 * 2
def baseEnd_1847469 : Nat := 948639591281337502741151

theorem tailTrace_1847469 : CollatzResearch.WordTrace tailWord_1847469 prefixEnd_1847469 948639591281337502741151 := by
  unfold tailWord_1847469
  simp only [CollatzResearch.WordTrace]
  refine ⟨67382730143942810430273461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44921820095961873620182307 67382730143942810430273461)
  ·
    refine ⟨6317130950994638477838137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 67382730143942810430273461 6317130950994638477838137)
    ·
      refine ⟨4737848213245978858378603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6317130950994638477838137 4737848213245978858378603)
      ·
        refine ⟨7106772319868968287567905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4737848213245978858378603 7106772319868968287567905)
        ·
          refine ⟨5330079239901726215675929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7106772319868968287567905 5330079239901726215675929)
          ·
            refine ⟨3997559429926294661756947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5330079239901726215675929 3997559429926294661756947)
            ·
              refine ⟨5996339144889441992635421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3997559429926294661756947 5996339144889441992635421)
              ·
                refine ⟨2248627179333540747238283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5996339144889441992635421 2248627179333540747238283)
                ·
                  refine ⟨3372940769000311120857425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2248627179333540747238283 3372940769000311120857425)
                  ·
                    refine ⟨2529705576750233340643069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3372940769000311120857425 2529705576750233340643069)
                    ·
                      refine ⟨948639591281337502741151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2529705576750233340643069 948639591281337502741151)
                      ·
                        rfl

theorem cell23_1847469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 3, 1, 2, 3].length) (baseStart_1847469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1847469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1847469 prefixEnd_1847469 := by exact prefixLift 1847469
  have htrace : WordTrace (prefixWord ++ tailWord_1847469) baseStart_1847469 baseEnd_1847469 := by
    simpa [prefixWord, tailWord_1847469, baseEnd_1847469] using wordTrace_append hprefix tailTrace_1847469
  have hstable : (prefixWord ++ tailWord_1847469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1847469).length < 2 ^ (prefixWord ++ tailWord_1847469).sum := by decide
  have hdescent : baseEnd_1847469 < baseStart_1847469 := by decide
  rcases family_descends (prefixWord ++ tailWord_1847469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1847499 : List Nat := [1, 1, 1, 1, 3, 2, 7, 1, 2, 1, 3]
def baseStart_1847499 : Nat := 118140960795 + 1847499 * 2 ^ 59
def prefixEnd_1847499 : Nat := 4983230072969 + 3 ^ 40 * 1847499 * 2
def baseEnd_1847499 : Nat := 948654995700972385366013

theorem tailTrace_1847499 : CollatzResearch.WordTrace tailWord_1847499 prefixEnd_1847499 948654995700972385366013 := by
  unfold tailWord_1847499
  simp only [CollatzResearch.WordTrace]
  refine ⟨67383824333834125553865551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44922549555889417035910367 67383824333834125553865551)
  ·
    refine ⟨101075736500751188330798327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67383824333834125553865551 101075736500751188330798327)
    ·
      refine ⟨151613604751126782496197491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101075736500751188330798327 151613604751126782496197491)
      ·
        refine ⟨227420407126690173744296237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151613604751126782496197491 227420407126690173744296237)
        ·
          refine ⟨85282652672508815154111089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 227420407126690173744296237 85282652672508815154111089)
          ·
            refine ⟨63961989504381611365583317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85282652672508815154111089 63961989504381611365583317)
            ·
              refine ⟨1499109129008944016380859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 63961989504381611365583317 1499109129008944016380859)
              ·
                refine ⟨2248663693513416024571289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1499109129008944016380859 2248663693513416024571289)
                ·
                  refine ⟨1686497770135062018428467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2248663693513416024571289 1686497770135062018428467)
                  ·
                    refine ⟨2529746655202593027642701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1686497770135062018428467 2529746655202593027642701)
                    ·
                      refine ⟨948654995700972385366013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2529746655202593027642701 948654995700972385366013)
                      ·
                        rfl

theorem cell23_1847499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 7, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 7, 1, 2, 1, 3].length) (baseStart_1847499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1847499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1847499 prefixEnd_1847499 := by exact prefixLift 1847499
  have htrace : WordTrace (prefixWord ++ tailWord_1847499) baseStart_1847499 baseEnd_1847499 := by
    simpa [prefixWord, tailWord_1847499, baseEnd_1847499] using wordTrace_append hprefix tailTrace_1847499
  have hstable : (prefixWord ++ tailWord_1847499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1847499).length < 2 ^ (prefixWord ++ tailWord_1847499).sum := by decide
  have hdescent : baseEnd_1847499 < baseStart_1847499 := by decide
  rcases family_descends (prefixWord ++ tailWord_1847499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1847525 : List Nat := [1, 3, 1, 4, 2, 1, 1, 1, 1, 3, 5]
def baseStart_1847525 : Nat := 118140960795 + 1847525 * 2 ^ 59
def prefixEnd_1847525 : Nat := 4983230072969 + 3 ^ 40 * 1847525 * 2
def baseEnd_1847525 : Nat := 948668346197989283640893

theorem tailTrace_1847525 : CollatzResearch.WordTrace tailWord_1847525 prefixEnd_1847525 948668346197989283640893 := by
  unfold tailWord_1847525
  simp only [CollatzResearch.WordTrace]
  refine ⟨67384772631739931994312029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44923181754493287996208019 67384772631739931994312029)
  ·
    refine ⟨25269289736902474497867011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67384772631739931994312029 25269289736902474497867011)
    ·
      refine ⟨37903934605353711746800517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25269289736902474497867011 37903934605353711746800517)
      ·
        refine ⟨7106987738503820952525097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37903934605353711746800517 7106987738503820952525097)
        ·
          refine ⟨5330240803877865714393823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7106987738503820952525097 5330240803877865714393823)
          ·
            refine ⟨7995361205816798571590735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5330240803877865714393823 7995361205816798571590735)
            ·
              refine ⟨11993041808725197857386103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7995361205816798571590735 11993041808725197857386103)
              ·
                refine ⟨17989562713087796786079155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11993041808725197857386103 17989562713087796786079155)
                ·
                  refine ⟨26984344069631695179118733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17989562713087796786079155 26984344069631695179118733)
                  ·
                    refine ⟨10119129026111885692169525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26984344069631695179118733 10119129026111885692169525)
                    ·
                      refine ⟨948668346197989283640893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10119129026111885692169525 948668346197989283640893)
                      ·
                        rfl

theorem cell23_1847525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 1, 1, 3, 5].length) (baseStart_1847525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1847525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1847525 prefixEnd_1847525 := by exact prefixLift 1847525
  have htrace : WordTrace (prefixWord ++ tailWord_1847525) baseStart_1847525 baseEnd_1847525 := by
    simpa [prefixWord, tailWord_1847525, baseEnd_1847525] using wordTrace_append hprefix tailTrace_1847525
  have hstable : (prefixWord ++ tailWord_1847525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1847525).length < 2 ^ (prefixWord ++ tailWord_1847525).sum := by decide
  have hdescent : baseEnd_1847525 < baseStart_1847525 := by decide
  rcases family_descends (prefixWord ++ tailWord_1847525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1847539 : List Nat := [1, 1, 1, 2, 2, 4, 2, 4, 2, 2, 2]
def baseStart_1847539 : Nat := 118140960795 + 1847539 * 2 ^ 59
def prefixEnd_1847539 : Nat := 4983230072969 + 3 ^ 40 * 1847539 * 2
def baseEnd_1847539 : Nat := 948675534927152228865829

theorem tailTrace_1847539 : CollatzResearch.WordTrace tailWord_1847539 prefixEnd_1847539 948675534927152228865829 := by
  unfold tailWord_1847539
  simp only [CollatzResearch.WordTrace]
  refine ⟨67385283253689212385321671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44923522169126141590214447 67385283253689212385321671)
  ·
    refine ⟨101077924880533818577982507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67385283253689212385321671 101077924880533818577982507)
    ·
      refine ⟨151616887320800727866973761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101077924880533818577982507 151616887320800727866973761)
      ·
        refine ⟨113712665490600545900230321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151616887320800727866973761 113712665490600545900230321)
        ·
          refine ⟨85284499117950409425172741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113712665490600545900230321 85284499117950409425172741)
          ·
            refine ⟨15990843584615701767219889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85284499117950409425172741 15990843584615701767219889)
            ·
              refine ⟨11993132688461776325414917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15990843584615701767219889 11993132688461776325414917)
              ·
                refine ⟨2248712379086583061015297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11993132688461776325414917 2248712379086583061015297)
                ·
                  refine ⟨1686534284314937295761473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2248712379086583061015297 1686534284314937295761473)
                  ·
                    refine ⟨1264900713236202971821105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1686534284314937295761473 1264900713236202971821105)
                    ·
                      refine ⟨948675534927152228865829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1264900713236202971821105 948675534927152228865829)
                      ·
                        rfl

theorem cell23_1847539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 4, 2, 2, 2].length) (baseStart_1847539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1847539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1847539 prefixEnd_1847539 := by exact prefixLift 1847539
  have htrace : WordTrace (prefixWord ++ tailWord_1847539) baseStart_1847539 baseEnd_1847539 := by
    simpa [prefixWord, tailWord_1847539, baseEnd_1847539] using wordTrace_append hprefix tailTrace_1847539
  have hstable : (prefixWord ++ tailWord_1847539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1847539).length < 2 ^ (prefixWord ++ tailWord_1847539).sum := by decide
  have hdescent : baseEnd_1847539 < baseStart_1847539 := by decide
  rcases family_descends (prefixWord ++ tailWord_1847539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1847555 : List Nat := [1, 1, 1, 3, 2, 3, 2, 1, 1, 5, 3]
def baseStart_1847555 : Nat := 118140960795 + 1847555 * 2 ^ 59
def prefixEnd_1847555 : Nat := 4983230072969 + 3 ^ 40 * 1847555 * 2
def baseEnd_1847555 : Nat := 948683750617624166265755

theorem tailTrace_1847555 : CollatzResearch.WordTrace tailWord_1847555 prefixEnd_1847555 948683750617624166265755 := by
  unfold tailWord_1847555
  simp only [CollatzResearch.WordTrace]
  refine ⟨67385866821631247117904119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44923911214420831411936079 67385866821631247117904119)
  ·
    refine ⟨101078800232446870676856179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67385866821631247117904119 101078800232446870676856179)
    ·
      refine ⟨151618200348670306015284269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101078800232446870676856179 151618200348670306015284269)
      ·
        refine ⟨56856825130751364755731601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151618200348670306015284269 56856825130751364755731601)
        ·
          refine ⟨42642618848063523566798701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56856825130751364755731601 42642618848063523566798701)
          ·
            refine ⟨15990982068023821337549513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42642618848063523566798701 15990982068023821337549513)
            ·
              refine ⟨11993236551017866003162135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15990982068023821337549513 11993236551017866003162135)
              ·
                refine ⟨17989854826526799004743203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11993236551017866003162135 17989854826526799004743203)
                ·
                  refine ⟨26984782239790198507114805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17989854826526799004743203 26984782239790198507114805)
                  ·
                    refine ⟨2529823334980331110042013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26984782239790198507114805 2529823334980331110042013)
                    ·
                      refine ⟨948683750617624166265755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2529823334980331110042013 948683750617624166265755)
                      ·
                        rfl

theorem cell23_1847555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 1, 1, 5, 3].length) (baseStart_1847555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1847555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1847555 prefixEnd_1847555 := by exact prefixLift 1847555
  have htrace : WordTrace (prefixWord ++ tailWord_1847555) baseStart_1847555 baseEnd_1847555 := by
    simpa [prefixWord, tailWord_1847555, baseEnd_1847555] using wordTrace_append hprefix tailTrace_1847555
  have hstable : (prefixWord ++ tailWord_1847555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1847555).length < 2 ^ (prefixWord ++ tailWord_1847555).sum := by decide
  have hdescent : baseEnd_1847555 < baseStart_1847555 := by decide
  rcases family_descends (prefixWord ++ tailWord_1847555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1847585 : List Nat := [1, 2, 3, 2, 1, 1, 3, 2, 1, 2, 5]
def baseStart_1847585 : Nat := 118140960795 + 1847585 * 2 ^ 59
def prefixEnd_1847585 : Nat := 4983230072969 + 3 ^ 40 * 1847585 * 2
def baseEnd_1847585 : Nat := 948699155037259048890617

theorem tailTrace_1847585 : CollatzResearch.WordTrace tailWord_1847585 prefixEnd_1847585 948699155037259048890617 := by
  unfold tailWord_1847585
  simp only [CollatzResearch.WordTrace]
  refine ⟨67386961011522562241496209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44924640674348374827664139 67386961011522562241496209)
  ·
    refine ⟨50540220758641921681122157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67386961011522562241496209 50540220758641921681122157)
    ·
      refine ⟨18952582784490720630420809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50540220758641921681122157 18952582784490720630420809)
      ·
        refine ⟨14214437088368040472815607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18952582784490720630420809 14214437088368040472815607)
        ·
          refine ⟨21321655632552060709223411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14214437088368040472815607 21321655632552060709223411)
          ·
            refine ⟨31982483448828091063835117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21321655632552060709223411 31982483448828091063835117)
            ·
              refine ⟨11993431293310534148938169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31982483448828091063835117 11993431293310534148938169)
              ·
                refine ⟨8995073469982900611703627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11993431293310534148938169 8995073469982900611703627)
                ·
                  refine ⟨13492610204974350917555441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8995073469982900611703627 13492610204974350917555441)
                  ·
                    refine ⟨10119457653730763188166581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13492610204974350917555441 10119457653730763188166581)
                    ·
                      refine ⟨948699155037259048890617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10119457653730763188166581 948699155037259048890617)
                      ·
                        rfl

theorem cell23_1847585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 2, 1, 2, 5].length) (baseStart_1847585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1847585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1847585 prefixEnd_1847585 := by exact prefixLift 1847585
  have htrace : WordTrace (prefixWord ++ tailWord_1847585) baseStart_1847585 baseEnd_1847585 := by
    simpa [prefixWord, tailWord_1847585, baseEnd_1847585] using wordTrace_append hprefix tailTrace_1847585
  have hstable : (prefixWord ++ tailWord_1847585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1847585).length < 2 ^ (prefixWord ++ tailWord_1847585).sum := by decide
  have hdescent : baseEnd_1847585 < baseStart_1847585 := by decide
  rcases family_descends (prefixWord ++ tailWord_1847585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1847632 : List Nat := [2, 1, 1, 1, 1, 7, 1, 1, 1, 4, 3]
def baseStart_1847632 : Nat := 118140960795 + 1847632 * 2 ^ 59
def prefixEnd_1847632 : Nat := 4983230072969 + 3 ^ 40 * 1847632 * 2
def baseEnd_1847632 : Nat := 948723288628020365002901

theorem tailTrace_1847632 : CollatzResearch.WordTrace tailWord_1847632 prefixEnd_1847632 948723288628020365002901 := by
  unfold tailWord_1847632
  simp only [CollatzResearch.WordTrace]
  refine ⟨33694337621176144634228575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44925783494901526178971433 33694337621176144634228575)
  ·
    refine ⟨50541506431764216951342863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33694337621176144634228575 50541506431764216951342863)
    ·
      refine ⟨75812259647646325427014295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50541506431764216951342863 75812259647646325427014295)
      ·
        refine ⟨113718389471469488140521443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75812259647646325427014295 113718389471469488140521443)
        ·
          refine ⟨170577584207204232210782165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113718389471469488140521443 170577584207204232210782165)
          ·
            refine ⟨3997912129856349192440207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 170577584207204232210782165 3997912129856349192440207)
            ·
              refine ⟨5996868194784523788660311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3997912129856349192440207 5996868194784523788660311)
              ·
                refine ⟨8995302292176785682990467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5996868194784523788660311 8995302292176785682990467)
                ·
                  refine ⟨13492953438265178524485701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8995302292176785682990467 13492953438265178524485701)
                  ·
                    refine ⟨2529928769674720973341069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13492953438265178524485701 2529928769674720973341069)
                    ·
                      refine ⟨948723288628020365002901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2529928769674720973341069 948723288628020365002901)
                      ·
                        rfl

theorem cell23_1847632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 1, 1, 4, 3].length) (baseStart_1847632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1847632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1847632 prefixEnd_1847632 := by exact prefixLift 1847632
  have htrace : WordTrace (prefixWord ++ tailWord_1847632) baseStart_1847632 baseEnd_1847632 := by
    simpa [prefixWord, tailWord_1847632, baseEnd_1847632] using wordTrace_append hprefix tailTrace_1847632
  have hstable : (prefixWord ++ tailWord_1847632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1847632).length < 2 ^ (prefixWord ++ tailWord_1847632).sum := by decide
  have hdescent : baseEnd_1847632 < baseStart_1847632 := by decide
  rcases family_descends (prefixWord ++ tailWord_1847632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1847656 : List Nat := [2, 1, 4, 2, 2, 1, 2, 4, 1, 4]
def baseStart_1847656 : Nat := 118140960795 + 1847656 * 2 ^ 59
def prefixEnd_1847656 : Nat := 4983230072969 + 3 ^ 40 * 1847656 * 2
def baseEnd_1847656 : Nat := 316245204054576090367597

theorem tailTrace_1847656 : CollatzResearch.WordTrace tailWord_1847656 prefixEnd_1847656 316245204054576090367597 := by
  unfold tailWord_1847656
  simp only [CollatzResearch.WordTrace]
  refine ⟨33694775297132670683665411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44926367062843560911553881 33694775297132670683665411)
  ·
    refine ⟨50542162945699006025498117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33694775297132670683665411 50542162945699006025498117)
    ·
      refine ⟨9476655552318563629780897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50542162945699006025498117 9476655552318563629780897)
      ·
        refine ⟨7107491664238922722335673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9476655552318563629780897 7107491664238922722335673)
        ·
          refine ⟨5330618748179192041751755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7107491664238922722335673 5330618748179192041751755)
          ·
            refine ⟨7995928122268788062627633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5330618748179192041751755 7995928122268788062627633)
            ·
              refine ⟨5996946091701591046970725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7995928122268788062627633 5996946091701591046970725)
              ·
                refine ⟨1124427392194048321307011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5996946091701591046970725 1124427392194048321307011)
                ·
                  refine ⟨1686641088291072481960517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1124427392194048321307011 1686641088291072481960517)
                  ·
                    refine ⟨316245204054576090367597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1686641088291072481960517 316245204054576090367597)
                    ·
                      rfl

theorem cell23_1847656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 4, 1, 4].length) (baseStart_1847656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1847656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1847656 prefixEnd_1847656 := by exact prefixLift 1847656
  have htrace : WordTrace (prefixWord ++ tailWord_1847656) baseStart_1847656 baseEnd_1847656 := by
    simpa [prefixWord, tailWord_1847656, baseEnd_1847656] using wordTrace_append hprefix tailTrace_1847656
  have hstable : (prefixWord ++ tailWord_1847656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1847656).length < 2 ^ (prefixWord ++ tailWord_1847656).sum := by decide
  have hdescent : baseEnd_1847656 < baseStart_1847656 := by decide
  rcases family_descends (prefixWord ++ tailWord_1847656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1847689 : List Nat := [1, 2, 1, 1, 6, 1, 2, 1, 1, 5, 2]
def baseStart_1847689 : Nat := 118140960795 + 1847689 * 2 ^ 59
def prefixEnd_1847689 : Nat := 4983230072969 + 3 ^ 40 * 1847689 * 2
def baseEnd_1847689 : Nat := 948752557025326641990139

theorem tailTrace_1847689 : CollatzResearch.WordTrace tailWord_1847689 prefixEnd_1847689 948752557025326641990139 := by
  unfold tailWord_1847689
  simp only [CollatzResearch.WordTrace]
  refine ⟨67390754203145788003282121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44927169468763858668854747 67390754203145788003282121)
  ·
    refine ⟨50543065652359341002461591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67390754203145788003282121 50543065652359341002461591)
    ·
      refine ⟨75814598478539011503692387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50543065652359341002461591 75814598478539011503692387)
      ·
        refine ⟨113721897717808517255538581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75814598478539011503692387 113721897717808517255538581)
        ·
          refine ⟨5330713955522274246353371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 113721897717808517255538581 5330713955522274246353371)
          ·
            refine ⟨7996070933283411369530057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5330713955522274246353371 7996070933283411369530057)
            ·
              refine ⟨5997053199962558527147543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7996070933283411369530057 5997053199962558527147543)
              ·
                refine ⟨8995579799943837790721315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5997053199962558527147543 8995579799943837790721315)
                ·
                  refine ⟨13493369699915756686081973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8995579799943837790721315 13493369699915756686081973)
                  ·
                    refine ⟨1265003409367102189320185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13493369699915756686081973 1265003409367102189320185)
                    ·
                      refine ⟨948752557025326641990139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1265003409367102189320185 948752557025326641990139)
                      ·
                        rfl

theorem cell23_1847689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 1, 1, 5, 2].length) (baseStart_1847689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1847689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1847689 prefixEnd_1847689 := by exact prefixLift 1847689
  have htrace : WordTrace (prefixWord ++ tailWord_1847689) baseStart_1847689 baseEnd_1847689 := by
    simpa [prefixWord, tailWord_1847689, baseEnd_1847689] using wordTrace_append hprefix tailTrace_1847689
  have hstable : (prefixWord ++ tailWord_1847689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1847689).length < 2 ^ (prefixWord ++ tailWord_1847689).sum := by decide
  have hdescent : baseEnd_1847689 < baseStart_1847689 := by decide
  rcases family_descends (prefixWord ++ tailWord_1847689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1847690 : List Nat := [3, 1, 2, 5, 1, 2, 1, 3, 1, 4]
def baseStart_1847690 : Nat := 118140960795 + 1847690 * 2 ^ 59
def prefixEnd_1847690 : Nat := 4983230072969 + 3 ^ 40 * 1847690 * 2
def baseEnd_1847690 : Nat := 316251023501993712692545

theorem tailTrace_1847690 : CollatzResearch.WordTrace tailWord_1847690 prefixEnd_1847690 316251023501993712692545 := by
  unfold tailWord_1847690
  simp only [CollatzResearch.WordTrace]
  refine ⟨16847697669035541293517131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44927193784094776782712349 16847697669035541293517131)
  ·
    refine ⟨25271546503553311940275697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16847697669035541293517131 25271546503553311940275697)
    ·
      refine ⟨18953659877664983955206773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25271546503553311940275697 18953659877664983955206773)
      ·
        refine ⟨1776905613531092245800635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18953659877664983955206773 1776905613531092245800635)
        ·
          refine ⟨2665358420296638368700953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1776905613531092245800635 2665358420296638368700953)
          ·
            refine ⟨1999018815222478776525715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2665358420296638368700953 1999018815222478776525715)
            ·
              refine ⟨2998528222833718164788573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1999018815222478776525715 2998528222833718164788573)
              ·
                refine ⟨1124448083562644311795715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2998528222833718164788573 1124448083562644311795715)
                ·
                  refine ⟨1686672125343966467693573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1124448083562644311795715 1686672125343966467693573)
                  ·
                    refine ⟨316251023501993712692545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1686672125343966467693573 316251023501993712692545)
                    ·
                      rfl

theorem cell23_1847690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 1, 3, 1, 4].length) (baseStart_1847690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1847690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1847690 prefixEnd_1847690 := by exact prefixLift 1847690
  have htrace : WordTrace (prefixWord ++ tailWord_1847690) baseStart_1847690 baseEnd_1847690 := by
    simpa [prefixWord, tailWord_1847690, baseEnd_1847690] using wordTrace_append hprefix tailTrace_1847690
  have hstable : (prefixWord ++ tailWord_1847690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1847690).length < 2 ^ (prefixWord ++ tailWord_1847690).sum := by decide
  have hdescent : baseEnd_1847690 < baseStart_1847690 := by decide
  rcases family_descends (prefixWord ++ tailWord_1847690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1847706 : List Nat := [3, 1, 1, 4, 1, 3, 1, 2, 2, 3, 2]
def baseStart_1847706 : Nat := 118140960795 + 1847706 * 2 ^ 59
def prefixEnd_1847706 : Nat := 4983230072969 + 3 ^ 40 * 1847706 * 2
def baseEnd_1847706 : Nat := 948761286196453075477561

theorem tailTrace_1847706 : CollatzResearch.WordTrace tailWord_1847706 prefixEnd_1847706 948761286196453075477561 := by
  unfold tailWord_1847706
  simp only [CollatzResearch.WordTrace]
  refine ⟨16847843561021049976662743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44927582829389466604433981 16847843561021049976662743)
  ·
    refine ⟨25271765341531574964994115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16847843561021049976662743 25271765341531574964994115)
    ·
      refine ⟨37907648012297362447491173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25271765341531574964994115 37907648012297362447491173)
      ·
        refine ⟨7107684002305755458904595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37907648012297362447491173 7107684002305755458904595)
        ·
          refine ⟨10661526003458633188356893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7107684002305755458904595 10661526003458633188356893)
          ·
            refine ⟨3998072251296987445633835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10661526003458633188356893 3998072251296987445633835)
            ·
              refine ⟨5997108376945481168450753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3998072251296987445633835 5997108376945481168450753)
              ·
                refine ⟨4497831282709110876338065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5997108376945481168450753 4497831282709110876338065)
                ·
                  refine ⟨3373373462031833157253549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4497831282709110876338065 3373373462031833157253549)
                  ·
                    refine ⟨1265015048261937433970081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3373373462031833157253549 1265015048261937433970081)
                    ·
                      refine ⟨948761286196453075477561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1265015048261937433970081 948761286196453075477561)
                      ·
                        rfl

theorem cell23_1847706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 2, 2, 3, 2].length) (baseStart_1847706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1847706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1847706 prefixEnd_1847706 := by exact prefixLift 1847706
  have htrace : WordTrace (prefixWord ++ tailWord_1847706) baseStart_1847706 baseEnd_1847706 := by
    simpa [prefixWord, tailWord_1847706, baseEnd_1847706] using wordTrace_append hprefix tailTrace_1847706
  have hstable : (prefixWord ++ tailWord_1847706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1847706).length < 2 ^ (prefixWord ++ tailWord_1847706).sum := by decide
  have hdescent : baseEnd_1847706 < baseStart_1847706 := by decide
  rcases family_descends (prefixWord ++ tailWord_1847706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1847733 : List Nat := [1, 3, 3, 2, 4, 1, 1, 2, 1, 5]
def baseStart_1847733 : Nat := 118140960795 + 1847733 * 2 ^ 59
def prefixEnd_1847733 : Nat := 4983230072969 + 3 ^ 40 * 1847733 * 2
def baseEnd_1847733 : Nat := 316258383391374823279979

theorem tailTrace_1847733 : CollatzResearch.WordTrace tailWord_1847733 prefixEnd_1847733 316258383391374823279979 := by
  unfold tailWord_1847733
  simp only [CollatzResearch.WordTrace]
  refine ⟨67392359014986383517883853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44928239343324255678589235 67392359014986383517883853)
  ·
    refine ⟨25272134630619893819206445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67392359014986383517883853 25272134630619893819206445)
    ·
      refine ⟨9477050486482460182202417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25272134630619893819206445 9477050486482460182202417)
      ·
        refine ⟨7107787864861845136651813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9477050486482460182202417 7107787864861845136651813)
        ·
          refine ⟨1332710224661595963122215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7107787864861845136651813 1332710224661595963122215)
          ·
            refine ⟨1999065336992393944683323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1332710224661595963122215 1999065336992393944683323)
            ·
              refine ⟨2998598005488590917024985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1999065336992393944683323 2998598005488590917024985)
              ·
                refine ⟨2248948504116443187768739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2998598005488590917024985 2248948504116443187768739)
                ·
                  refine ⟨3373422756174664781653109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2248948504116443187768739 3373422756174664781653109)
                  ·
                    refine ⟨316258383391374823279979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3373422756174664781653109 316258383391374823279979)
                    ·
                      rfl

theorem cell23_1847733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 1, 2, 1, 5].length) (baseStart_1847733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1847733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1847733 prefixEnd_1847733 := by exact prefixLift 1847733
  have htrace : WordTrace (prefixWord ++ tailWord_1847733) baseStart_1847733 baseEnd_1847733 := by
    simpa [prefixWord, tailWord_1847733, baseEnd_1847733] using wordTrace_append hprefix tailTrace_1847733
  have hstable : (prefixWord ++ tailWord_1847733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1847733).length < 2 ^ (prefixWord ++ tailWord_1847733).sum := by decide
  have hdescent : baseEnd_1847733 < baseStart_1847733 := by decide
  rcases family_descends (prefixWord ++ tailWord_1847733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1847742 : List Nat := [4, 2, 1, 1, 1, 1, 4, 9]
def baseStart_1847742 : Nat := 118140960795 + 1847742 * 2 ^ 59
def prefixEnd_1847742 : Nat := 4983230072969 + 3 ^ 40 * 1847742 * 2
def baseEnd_1847742 : Nat := 35139991537037590171385

theorem tailTrace_1847742 : CollatzResearch.WordTrace tailWord_1847742 prefixEnd_1847742 35139991537037590171385 := by
  unfold tailWord_1847742
  simp only [CollatzResearch.WordTrace]
  refine ⟨8424085908994222256870185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44928458181302518703307653 8424085908994222256870185)
  ·
    refine ⟨6318064431745666692652639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8424085908994222256870185 6318064431745666692652639)
    ·
      refine ⟨9477096647618500038978959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6318064431745666692652639 9477096647618500038978959)
      ·
        refine ⟨14215644971427750058468439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9477096647618500038978959 14215644971427750058468439)
        ·
          refine ⟨21323467457141625087702659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14215644971427750058468439 21323467457141625087702659)
          ·
            refine ⟨31985201185712437631553989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21323467457141625087702659 31985201185712437631553989)
            ·
              refine ⟨5997225222321082055916373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31985201185712437631553989 5997225222321082055916373)
              ·
                refine ⟨35139991537037590171385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 5997225222321082055916373 35139991537037590171385)
                ·
                  rfl

theorem cell23_1847742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 9].length) (baseStart_1847742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1847742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1847742 prefixEnd_1847742 := by exact prefixLift 1847742
  have htrace : WordTrace (prefixWord ++ tailWord_1847742) baseStart_1847742 baseEnd_1847742 := by
    simpa [prefixWord, tailWord_1847742, baseEnd_1847742] using wordTrace_append hprefix tailTrace_1847742
  have hstable : (prefixWord ++ tailWord_1847742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1847742).length < 2 ^ (prefixWord ++ tailWord_1847742).sum := by decide
  have hdescent : baseEnd_1847742 < baseStart_1847742 := by decide
  rcases family_descends (prefixWord ++ tailWord_1847742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1847756 : List Nat := [2, 2, 1, 4, 3, 2, 1, 1, 1, 1, 5]
def baseStart_1847756 : Nat := 118140960795 + 1847756 * 2 ^ 59
def prefixEnd_1847756 : Nat := 4983230072969 + 3 ^ 40 * 1847756 * 2
def baseEnd_1847756 : Nat := 948786960229177879852331

theorem tailTrace_1847756 : CollatzResearch.WordTrace tailWord_1847756 prefixEnd_1847756 948786960229177879852331 := by
  unfold tailWord_1847756
  simp only [CollatzResearch.WordTrace]
  refine ⟨33696598946951529222985561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44928798595935372297314081 33696598946951529222985561)
  ·
    refine ⟨25272449210213646917239171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33696598946951529222985561 25272449210213646917239171)
    ·
      refine ⟨37908673815320470375858757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25272449210213646917239171 37908673815320470375858757)
      ·
        refine ⟨7107876340372588195473517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37908673815320470375858757 7107876340372588195473517)
        ·
          refine ⟨2665453627639720573302569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7107876340372588195473517 2665453627639720573302569)
          ·
            refine ⟨1999090220729790429976927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2665453627639720573302569 1999090220729790429976927)
            ·
              refine ⟨2998635331094685644965391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1999090220729790429976927 2998635331094685644965391)
              ·
                refine ⟨4497952996642028467448087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2998635331094685644965391 4497952996642028467448087)
                ·
                  refine ⟨6746929494963042701172131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4497952996642028467448087 6746929494963042701172131)
                  ·
                    refine ⟨10120394242444564051758197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6746929494963042701172131 10120394242444564051758197)
                    ·
                      refine ⟨948786960229177879852331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10120394242444564051758197 948786960229177879852331)
                      ·
                        rfl

theorem cell23_1847756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 1, 1, 1, 1, 5].length) (baseStart_1847756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1847756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1847756 prefixEnd_1847756 := by exact prefixLift 1847756
  have htrace : WordTrace (prefixWord ++ tailWord_1847756) baseStart_1847756 baseEnd_1847756 := by
    simpa [prefixWord, tailWord_1847756, baseEnd_1847756] using wordTrace_append hprefix tailTrace_1847756
  have hstable : (prefixWord ++ tailWord_1847756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1847756).length < 2 ^ (prefixWord ++ tailWord_1847756).sum := by decide
  have hdescent : baseEnd_1847756 < baseStart_1847756 := by decide
  rcases family_descends (prefixWord ++ tailWord_1847756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1847786 : List Nat := [3, 1, 3, 1, 3, 2, 2, 1, 1, 3, 3]
def baseStart_1847786 : Nat := 118140960795 + 1847786 * 2 ^ 59
def prefixEnd_1847786 : Nat := 4983230072969 + 3 ^ 40 * 1847786 * 2
def baseEnd_1847786 : Nat := 948802364648812762477193

theorem tailTrace_1847786 : CollatzResearch.WordTrace tailWord_1847786 prefixEnd_1847786 948802364648812762477193 := by
  unfold tailWord_1847786
  simp only [CollatzResearch.WordTrace]
  refine ⟨16848573020948593392390803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44929528055862915713042141 16848573020948593392390803)
  ·
    refine ⟨25272859531422890088586205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16848573020948593392390803 25272859531422890088586205)
    ·
      refine ⟨9477322324283583783219827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25272859531422890088586205 9477322324283583783219827)
      ·
        refine ⟨14215983486425375674829741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9477322324283583783219827 14215983486425375674829741)
        ·
          refine ⟨5330993807409515878061153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14215983486425375674829741 5330993807409515878061153)
          ·
            refine ⟨3998245355557136908545865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5330993807409515878061153 3998245355557136908545865)
            ·
              refine ⟨2998684016667852681409399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3998245355557136908545865 2998684016667852681409399)
              ·
                refine ⟨4498026025001779022114099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2998684016667852681409399 4498026025001779022114099)
                ·
                  refine ⟨6747039037502668533171149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4498026025001779022114099 6747039037502668533171149)
                  ·
                    refine ⟨2530139639063500699939181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6747039037502668533171149 2530139639063500699939181)
                    ·
                      refine ⟨948802364648812762477193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2530139639063500699939181 948802364648812762477193)
                      ·
                        rfl

theorem cell23_1847786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 2, 1, 1, 3, 3].length) (baseStart_1847786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1847786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1847786 prefixEnd_1847786 := by exact prefixLift 1847786
  have htrace : WordTrace (prefixWord ++ tailWord_1847786) baseStart_1847786 baseEnd_1847786 := by
    simpa [prefixWord, tailWord_1847786, baseEnd_1847786] using wordTrace_append hprefix tailTrace_1847786
  have hstable : (prefixWord ++ tailWord_1847786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1847786).length < 2 ^ (prefixWord ++ tailWord_1847786).sum := by decide
  have hdescent : baseEnd_1847786 < baseStart_1847786 := by decide
  rcases family_descends (prefixWord ++ tailWord_1847786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1847792 : List Nat := [2, 1, 1, 1, 3, 3, 1, 2, 2, 3, 4]
def baseStart_1847792 : Nat := 118140960795 + 1847792 * 2 ^ 59
def prefixEnd_1847792 : Nat := 4983230072969 + 3 ^ 40 * 1847792 * 2
def baseEnd_1847792 : Nat := 948805445532739739002165

theorem tailTrace_1847792 : CollatzResearch.WordTrace tailWord_1847792 prefixEnd_1847792 948805445532739739002165 := by
  unfold tailWord_1847792
  simp only [CollatzResearch.WordTrace]
  refine ⟨33697255460886318297140815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44929673947848424396187753 33697255460886318297140815)
  ·
    refine ⟨50545883191329477445711223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33697255460886318297140815 50545883191329477445711223)
    ·
      refine ⟨75818824786994216168566835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50545883191329477445711223 75818824786994216168566835)
      ·
        refine ⟨113728237180491324252850253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75818824786994216168566835 113728237180491324252850253)
        ·
          refine ⟨42648088942684246594818845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113728237180491324252850253 42648088942684246594818845)
          ·
            refine ⟨15993033353506592473057067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42648088942684246594818845 15993033353506592473057067)
            ·
              refine ⟨23989550030259888709585601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15993033353506592473057067 23989550030259888709585601)
              ·
                refine ⟨17992162522694916532189201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23989550030259888709585601 17992162522694916532189201)
                ·
                  refine ⟨13494121892021187399141901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17992162522694916532189201 13494121892021187399141901)
                  ·
                    refine ⟨5060295709507945274678213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13494121892021187399141901 5060295709507945274678213)
                    ·
                      refine ⟨948805445532739739002165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5060295709507945274678213 948805445532739739002165)
                      ·
                        rfl

theorem cell23_1847792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 2, 2, 3, 4].length) (baseStart_1847792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1847792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1847792 prefixEnd_1847792 := by exact prefixLift 1847792
  have htrace : WordTrace (prefixWord ++ tailWord_1847792) baseStart_1847792 baseEnd_1847792 := by
    simpa [prefixWord, tailWord_1847792, baseEnd_1847792] using wordTrace_append hprefix tailTrace_1847792
  have hstable : (prefixWord ++ tailWord_1847792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1847792).length < 2 ^ (prefixWord ++ tailWord_1847792).sum := by decide
  have hdescent : baseEnd_1847792 < baseStart_1847792 := by decide
  rcases family_descends (prefixWord ++ tailWord_1847792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1847813 : List Nat := [1, 3, 1, 1, 2, 2, 6, 1, 1, 3, 2]
def baseStart_1847813 : Nat := 118140960795 + 1847813 * 2 ^ 59
def prefixEnd_1847813 : Nat := 4983230072969 + 3 ^ 40 * 1847813 * 2
def baseEnd_1847813 : Nat := 948816228626484156839569

theorem tailTrace_1847813 : CollatzResearch.WordTrace tailWord_1847813 prefixEnd_1847813 948816228626484156839569 := by
  unfold tailWord_1847813
  simp only [CollatzResearch.WordTrace]
  refine ⟨67395276854696557180796093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44930184569797704787197395 67395276854696557180796093)
  ·
    refine ⟨25273228820511208942798535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67395276854696557180796093 25273228820511208942798535)
    ·
      refine ⟨37909843230766813414197803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25273228820511208942798535 37909843230766813414197803)
      ·
        refine ⟨56864764846150220121296705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37909843230766813414197803 56864764846150220121296705)
        ·
          refine ⟨42648573634612665090972529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56864764846150220121296705 42648573634612665090972529)
          ·
            refine ⟨31986430225959498818229397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42648573634612665090972529 31986430225959498818229397)
            ·
              refine ⟨1499363916841851507104503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 31986430225959498818229397 1499363916841851507104503)
              ·
                refine ⟨2249045875262777260656755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1499363916841851507104503 2249045875262777260656755)
                ·
                  refine ⟨3373568812894165890985133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2249045875262777260656755 3373568812894165890985133)
                  ·
                    refine ⟨1265088304835312209119425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3373568812894165890985133 1265088304835312209119425)
                    ·
                      refine ⟨948816228626484156839569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1265088304835312209119425 948816228626484156839569)
                      ·
                        rfl

theorem cell23_1847813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 6, 1, 1, 3, 2].length) (baseStart_1847813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1847813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1847813 prefixEnd_1847813 := by exact prefixLift 1847813
  have htrace : WordTrace (prefixWord ++ tailWord_1847813) baseStart_1847813 baseEnd_1847813 := by
    simpa [prefixWord, tailWord_1847813, baseEnd_1847813] using wordTrace_append hprefix tailTrace_1847813
  have hstable : (prefixWord ++ tailWord_1847813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1847813).length < 2 ^ (prefixWord ++ tailWord_1847813).sum := by decide
  have hdescent : baseEnd_1847813 < baseStart_1847813 := by decide
  rcases family_descends (prefixWord ++ tailWord_1847813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1847843 : List Nat := [1, 1, 1, 4, 4, 3, 1, 1, 1, 4, 2]
def baseStart_1847843 : Nat := 118140960795 + 1847843 * 2 ^ 59
def prefixEnd_1847843 : Nat := 4983230072969 + 3 ^ 40 * 1847843 * 2
def baseEnd_1847843 : Nat := 948831633046119039464431

theorem tailTrace_1847843 : CollatzResearch.WordTrace tailWord_1847843 prefixEnd_1847843 948831633046119039464431 := by
  unfold tailWord_1847843
  simp only [CollatzResearch.WordTrace]
  refine ⟨67396371044587872304388183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44930914029725248202925455 67396371044587872304388183)
  ·
    refine ⟨101094556566881808456582275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67396371044587872304388183 101094556566881808456582275)
    ·
      refine ⟨151641834850322712684873413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101094556566881808456582275 151641834850322712684873413)
      ·
        refine ⟨28432844034435508628413765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 151641834850322712684873413 28432844034435508628413765)
        ·
          refine ⟨5331158256456657867827581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28432844034435508628413765 5331158256456657867827581)
          ·
            refine ⟨1999184346171246700435343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5331158256456657867827581 1999184346171246700435343)
            ·
              refine ⟨2998776519256870050653015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1999184346171246700435343 2998776519256870050653015)
              ·
                refine ⟨4498164778885305075979523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2998776519256870050653015 4498164778885305075979523)
                ·
                  refine ⟨6747247168327957613969285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4498164778885305075979523 6747247168327957613969285)
                  ·
                    refine ⟨1265108844061492052619241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6747247168327957613969285 1265108844061492052619241)
                    ·
                      refine ⟨948831633046119039464431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1265108844061492052619241 948831633046119039464431)
                      ·
                        rfl

theorem cell23_1847843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 1, 1, 1, 4, 2].length) (baseStart_1847843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1847843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1847843 prefixEnd_1847843 := by exact prefixLift 1847843
  have htrace : WordTrace (prefixWord ++ tailWord_1847843) baseStart_1847843 baseEnd_1847843 := by
    simpa [prefixWord, tailWord_1847843, baseEnd_1847843] using wordTrace_append hprefix tailTrace_1847843
  have hstable : (prefixWord ++ tailWord_1847843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1847843).length < 2 ^ (prefixWord ++ tailWord_1847843).sum := by decide
  have hdescent : baseEnd_1847843 < baseStart_1847843 := by decide
  rcases family_descends (prefixWord ++ tailWord_1847843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1847847 : List Nat := [1, 1, 7, 2, 1, 1, 2, 2, 1, 3, 2]
def baseStart_1847847 : Nat := 118140960795 + 1847847 * 2 ^ 59
def prefixEnd_1847847 : Nat := 4983230072969 + 3 ^ 40 * 1847847 * 2
def baseEnd_1847847 : Nat := 948833686968737023814413

theorem tailTrace_1847847 : CollatzResearch.WordTrace tailWord_1847847 prefixEnd_1847847 948833686968737023814413 := by
  unfold tailWord_1847847
  simp only [CollatzResearch.WordTrace]
  refine ⟨67396516936573380987533795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44931011291048920658355863 67396516936573380987533795)
  ·
    refine ⟨101094775404860071481300693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67396516936573380987533795 101094775404860071481300693)
    ·
      refine ⟨2369408798551407925342985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 101094775404860071481300693 2369408798551407925342985)
      ·
        refine ⟨1777056598913555944007239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2369408798551407925342985 1777056598913555944007239)
        ·
          refine ⟨2665584898370333916010859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1777056598913555944007239 2665584898370333916010859)
          ·
            refine ⟨3998377347555500874016289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2665584898370333916010859 3998377347555500874016289)
            ·
              refine ⟨2998783010666625655512217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3998377347555500874016289 2998783010666625655512217)
              ·
                refine ⟨2249087257999969241634163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2998783010666625655512217 2249087257999969241634163)
                ·
                  refine ⟨3373630886999953862451245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2249087257999969241634163 3373630886999953862451245)
                  ·
                    refine ⟨1265111582624982698419217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3373630886999953862451245 1265111582624982698419217)
                    ·
                      refine ⟨948833686968737023814413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1265111582624982698419217 948833686968737023814413)
                      ·
                        rfl

theorem cell23_1847847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 2, 2, 1, 3, 2].length) (baseStart_1847847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1847847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1847847 prefixEnd_1847847 := by exact prefixLift 1847847
  have htrace : WordTrace (prefixWord ++ tailWord_1847847) baseStart_1847847 baseEnd_1847847 := by
    simpa [prefixWord, tailWord_1847847, baseEnd_1847847] using wordTrace_append hprefix tailTrace_1847847
  have hstable : (prefixWord ++ tailWord_1847847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1847847).length < 2 ^ (prefixWord ++ tailWord_1847847).sum := by decide
  have hdescent : baseEnd_1847847 < baseStart_1847847 := by decide
  rcases family_descends (prefixWord ++ tailWord_1847847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1847866 : List Nat := [3, 1, 1, 1, 3, 3, 3, 3, 5]
def baseStart_1847866 : Nat := 118140960795 + 1847866 * 2 ^ 59
def prefixEnd_1847866 : Nat := 4983230072969 + 3 ^ 40 * 1847866 * 2
def baseEnd_1847866 : Nat := 105427049233463605497425

theorem tailTrace_1847866 : CollatzResearch.WordTrace tailWord_1847866 prefixEnd_1847866 105427049233463605497425 := by
  unfold tailWord_1847866
  simp only [CollatzResearch.WordTrace]
  refine ⟨16849302480876136808118863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44931473282336364821650301 16849302480876136808118863)
  ·
    refine ⟨25273953721314205212178295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16849302480876136808118863 25273953721314205212178295)
    ·
      refine ⟨37910930581971307818267443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25273953721314205212178295 37910930581971307818267443)
      ·
        refine ⟨56866395872956961727401165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37910930581971307818267443 56866395872956961727401165)
        ·
          refine ⟨21324898452358860647775437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56866395872956961727401165 21324898452358860647775437)
          ·
            refine ⟨7996836919634572742915789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21324898452358860647775437 7996836919634572742915789)
            ·
              refine ⟨2998813844862964778593421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7996836919634572742915789 2998813844862964778593421)
              ·
                refine ⟨1124555191823611791972533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2998813844862964778593421 1124555191823611791972533)
                ·
                  refine ⟨105427049233463605497425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1124555191823611791972533 105427049233463605497425)
                  ·
                    rfl

theorem cell23_1847866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 3, 3, 5].length) (baseStart_1847866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1847866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1847866 prefixEnd_1847866 := by exact prefixLift 1847866
  have htrace : WordTrace (prefixWord ++ tailWord_1847866) baseStart_1847866 baseEnd_1847866 := by
    simpa [prefixWord, tailWord_1847866, baseEnd_1847866] using wordTrace_append hprefix tailTrace_1847866
  have hstable : (prefixWord ++ tailWord_1847866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1847866).length < 2 ^ (prefixWord ++ tailWord_1847866).sum := by decide
  have hdescent : baseEnd_1847866 < baseStart_1847866 := by decide
  rcases family_descends (prefixWord ++ tailWord_1847866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1847879 : List Nat := [1, 1, 4, 1, 4, 1, 1, 1, 4, 5]
def baseStart_1847879 : Nat := 118140960795 + 1847879 * 2 ^ 59
def prefixEnd_1847879 : Nat := 4983230072969 + 3 ^ 40 * 1847879 * 2
def baseEnd_1847879 : Nat := 316283372783226966204755

theorem tailTrace_1847879 : CollatzResearch.WordTrace tailWord_1847879 prefixEnd_1847879 316283372783226966204755 := by
  unfold tailWord_1847879
  simp only [CollatzResearch.WordTrace]
  refine ⟨67397684072457450452698691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44931789381638300301799127 67397684072457450452698691)
  ·
    refine ⟨101096526108686175679048037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67397684072457450452698691 101096526108686175679048037)
    ·
      refine ⟨18955598645378657939821507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101096526108686175679048037 18955598645378657939821507)
      ·
        refine ⟨28433397968067986909732261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18955598645378657939821507 28433397968067986909732261)
        ·
          refine ⟨5331262119012747545574799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28433397968067986909732261 5331262119012747545574799)
          ·
            refine ⟨7996893178519121318362199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5331262119012747545574799 7996893178519121318362199)
            ·
              refine ⟨11995339767778681977543299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7996893178519121318362199 11995339767778681977543299)
              ·
                refine ⟨17993009651668022966314949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11995339767778681977543299 17993009651668022966314949)
                ·
                  refine ⟨3373689309687754306184053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17993009651668022966314949 3373689309687754306184053)
                  ·
                    refine ⟨316283372783226966204755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3373689309687754306184053 316283372783226966204755)
                    ·
                      rfl

theorem cell23_1847879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 1, 4, 5].length) (baseStart_1847879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1847879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1847879 prefixEnd_1847879 := by exact prefixLift 1847879
  have htrace : WordTrace (prefixWord ++ tailWord_1847879) baseStart_1847879 baseEnd_1847879 := by
    simpa [prefixWord, tailWord_1847879, baseEnd_1847879] using wordTrace_append hprefix tailTrace_1847879
  have hstable : (prefixWord ++ tailWord_1847879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1847879).length < 2 ^ (prefixWord ++ tailWord_1847879).sum := by decide
  have hdescent : baseEnd_1847879 < baseStart_1847879 := by decide
  rcases family_descends (prefixWord ++ tailWord_1847879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1847889 : List Nat := [1, 2, 2, 1, 3, 4, 1, 1, 1, 2, 5]
def baseStart_1847889 : Nat := 118140960795 + 1847889 * 2 ^ 59
def prefixEnd_1847889 : Nat := 4983230072969 + 3 ^ 40 * 1847889 * 2
def baseEnd_1847889 : Nat := 948855253156225859489219

theorem tailTrace_1847889 : CollatzResearch.WordTrace tailWord_1847889 prefixEnd_1847889 948855253156225859489219 := by
  unfold tailWord_1847889
  simp only [CollatzResearch.WordTrace]
  refine ⟨67398048802421222160562721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44932032534947481440375147 67398048802421222160562721)
  ·
    refine ⟨50548536601815916620422041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67398048802421222160562721 50548536601815916620422041)
    ·
      refine ⟨37911402451361937465316531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50548536601815916620422041 37911402451361937465316531)
      ·
        refine ⟨56867103677042906197974797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37911402451361937465316531 56867103677042906197974797)
        ·
          refine ⟨21325163878891089824240549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56867103677042906197974797 21325163878891089824240549)
          ·
            refine ⟨3998468227292079342045103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21325163878891089824240549 3998468227292079342045103)
            ·
              refine ⟨5997702340938119013067655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3998468227292079342045103 5997702340938119013067655)
              ·
                refine ⟨8996553511407178519601483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5997702340938119013067655 8996553511407178519601483)
                ·
                  refine ⟨13494830267110767779402225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8996553511407178519601483 13494830267110767779402225)
                  ·
                    refine ⟨10121122700333075834551669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13494830267110767779402225 10121122700333075834551669)
                    ·
                      refine ⟨948855253156225859489219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10121122700333075834551669 948855253156225859489219)
                      ·
                        rfl

theorem cell23_1847889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 1, 1, 2, 5].length) (baseStart_1847889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1847889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1847889 prefixEnd_1847889 := by exact prefixLift 1847889
  have htrace : WordTrace (prefixWord ++ tailWord_1847889) baseStart_1847889 baseEnd_1847889 := by
    simpa [prefixWord, tailWord_1847889, baseEnd_1847889] using wordTrace_append hprefix tailTrace_1847889
  have hstable : (prefixWord ++ tailWord_1847889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1847889).length < 2 ^ (prefixWord ++ tailWord_1847889).sum := by decide
  have hdescent : baseEnd_1847889 < baseStart_1847889 := by decide
  rcases family_descends (prefixWord ++ tailWord_1847889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1847919 : List Nat := [1, 1, 2, 1, 3, 2, 2, 3, 1, 4, 3]
def baseStart_1847919 : Nat := 118140960795 + 1847919 * 2 ^ 59
def prefixEnd_1847919 : Nat := 4983230072969 + 3 ^ 40 * 1847919 * 2
def baseEnd_1847919 : Nat := 948870657575860742114081

theorem tailTrace_1847919 : CollatzResearch.WordTrace tailWord_1847919 prefixEnd_1847919 948870657575860742114081 := by
  unfold tailWord_1847919
  simp only [CollatzResearch.WordTrace]
  refine ⟨67399142992312537284154811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44932761994875024856103207 67399142992312537284154811)
  ·
    refine ⟨101098714488468805926232217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67399142992312537284154811 101098714488468805926232217)
    ·
      refine ⟨75824035866351604444674163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101098714488468805926232217 75824035866351604444674163)
      ·
        refine ⟨113736053799527406667011245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75824035866351604444674163 113736053799527406667011245)
        ·
          refine ⟨42651020174822777500129217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113736053799527406667011245 42651020174822777500129217)
          ·
            refine ⟨31988265131117083125096913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42651020174822777500129217 31988265131117083125096913)
            ·
              refine ⟨23991198848337812343822685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31988265131117083125096913 23991198848337812343822685)
              ·
                refine ⟨8996699568126679628933507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23991198848337812343822685 8996699568126679628933507)
                ·
                  refine ⟨13495049352190019443400261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8996699568126679628933507 13495049352190019443400261)
                  ·
                    refine ⟨2530321753535628645637549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13495049352190019443400261 2530321753535628645637549)
                    ·
                      refine ⟨948870657575860742114081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2530321753535628645637549 948870657575860742114081)
                      ·
                        rfl

theorem cell23_1847919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 3, 1, 4, 3].length) (baseStart_1847919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1847919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1847919 prefixEnd_1847919 := by exact prefixLift 1847919
  have htrace : WordTrace (prefixWord ++ tailWord_1847919) baseStart_1847919 baseEnd_1847919 := by
    simpa [prefixWord, tailWord_1847919, baseEnd_1847919] using wordTrace_append hprefix tailTrace_1847919
  have hstable : (prefixWord ++ tailWord_1847919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1847919).length < 2 ^ (prefixWord ++ tailWord_1847919).sum := by decide
  have hdescent : baseEnd_1847919 < baseStart_1847919 := by decide
  rcases family_descends (prefixWord ++ tailWord_1847919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1847936 : List Nat := [2, 1, 1, 2, 1, 5, 2, 2, 2, 2, 3]
def baseStart_1847936 : Nat := 118140960795 + 1847936 * 2 ^ 59
def prefixEnd_1847936 : Nat := 4983230072969 + 3 ^ 40 * 1847936 * 2
def baseEnd_1847936 : Nat := 948879386746987175601503

theorem tailTrace_1847936 : CollatzResearch.WordTrace tailWord_1847936 prefixEnd_1847936 948879386746987175601503 := by
  unfold tailWord_1847936
  simp only [CollatzResearch.WordTrace]
  refine ⟨33699881516625474593761831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44933175355500632791682441 33699881516625474593761831)
  ·
    refine ⟨50549822274938211890642747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33699881516625474593761831 50549822274938211890642747)
    ·
      refine ⟨75824733412407317835964121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50549822274938211890642747 75824733412407317835964121)
      ·
        refine ⟨56868550059305488376973091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75824733412407317835964121 56868550059305488376973091)
        ·
          refine ⟨85302825088958232565459637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56868550059305488376973091 85302825088958232565459637)
          ·
            refine ⟨7997139852089834303011841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 85302825088958232565459637 7997139852089834303011841)
            ·
              refine ⟨5997854889067375727258881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7997139852089834303011841 5997854889067375727258881)
              ·
                refine ⟨4498391166800531795444161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5997854889067375727258881 4498391166800531795444161)
                ·
                  refine ⟨3373793375100398846583121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4498391166800531795444161 3373793375100398846583121)
                  ·
                    refine ⟨2530345031325299134937341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3373793375100398846583121 2530345031325299134937341)
                    ·
                      refine ⟨948879386746987175601503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2530345031325299134937341 948879386746987175601503)
                      ·
                        rfl

theorem cell23_1847936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 2, 2, 2, 3].length) (baseStart_1847936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1847936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1847936 prefixEnd_1847936 := by exact prefixLift 1847936
  have htrace : WordTrace (prefixWord ++ tailWord_1847936) baseStart_1847936 baseEnd_1847936 := by
    simpa [prefixWord, tailWord_1847936, baseEnd_1847936] using wordTrace_append hprefix tailTrace_1847936
  have hstable : (prefixWord ++ tailWord_1847936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1847936).length < 2 ^ (prefixWord ++ tailWord_1847936).sum := by decide
  have hdescent : baseEnd_1847936 < baseStart_1847936 := by decide
  rcases family_descends (prefixWord ++ tailWord_1847936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1847939 : List Nat := [1, 1, 1, 3, 3, 1, 3, 4, 6]
def baseStart_1847939 : Nat := 118140960795 + 1847939 * 2 ^ 59
def prefixEnd_1847939 : Nat := 4983230072969 + 3 ^ 40 * 1847939 * 2
def baseEnd_1847939 : Nat := 105431214132105629318221

theorem tailTrace_1847939 : CollatzResearch.WordTrace tailWord_1847939 prefixEnd_1847939 105431214132105629318221 := by
  unfold tailWord_1847939
  simp only [CollatzResearch.WordTrace]
  refine ⟨67399872452240080699882871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44933248301493387133255247 67399872452240080699882871)
  ·
    refine ⟨101099808678360121049824307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67399872452240080699882871 101099808678360121049824307)
    ·
      refine ⟨151649713017540181574736461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101099808678360121049824307 151649713017540181574736461)
      ·
        refine ⟨56868642381577568090526173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151649713017540181574736461 56868642381577568090526173)
        ·
          refine ⟨21325740893091588033947315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56868642381577568090526173 21325740893091588033947315)
          ·
            refine ⟨31988611339637382050920973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21325740893091588033947315 31988611339637382050920973)
            ·
              refine ⟨11995729252364018269095365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31988611339637382050920973 11995729252364018269095365)
              ·
                refine ⟨2249199234818253425455381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11995729252364018269095365 2249199234818253425455381)
                ·
                  refine ⟨105431214132105629318221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2249199234818253425455381 105431214132105629318221)
                  ·
                    rfl

theorem cell23_1847939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 4, 6].length) (baseStart_1847939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1847939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1847939 prefixEnd_1847939 := by exact prefixLift 1847939
  have htrace : WordTrace (prefixWord ++ tailWord_1847939) baseStart_1847939 baseEnd_1847939 := by
    simpa [prefixWord, tailWord_1847939, baseEnd_1847939] using wordTrace_append hprefix tailTrace_1847939
  have hstable : (prefixWord ++ tailWord_1847939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1847939).length < 2 ^ (prefixWord ++ tailWord_1847939).sum := by decide
  have hdescent : baseEnd_1847939 < baseStart_1847939 := by decide
  rcases family_descends (prefixWord ++ tailWord_1847939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1847943 : List Nat := [1, 1, 4, 2, 1, 2, 3, 4, 1, 4]
def baseStart_1847943 : Nat := 118140960795 + 1847943 * 2 ^ 59
def prefixEnd_1847943 : Nat := 4983230072969 + 3 ^ 40 * 1847943 * 2
def baseEnd_1847943 : Nat := 316294327037189549404657

theorem tailTrace_1847943 : CollatzResearch.WordTrace tailWord_1847943 prefixEnd_1847943 316294327037189549404657 := by
  unfold tailWord_1847943
  simp only [CollatzResearch.WordTrace]
  refine ⟨67400018344225589383028483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44933345562817059588685655 67400018344225589383028483)
  ·
    refine ⟨101100027516338384074542725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67400018344225589383028483 101100027516338384074542725)
    ·
      refine ⟨18956255159313447013976761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101100027516338384074542725 18956255159313447013976761)
      ·
        refine ⟨14217191369485085260482571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18956255159313447013976761 14217191369485085260482571)
        ·
          refine ⟨21325787054227627890723857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14217191369485085260482571 21325787054227627890723857)
          ·
            refine ⟨15994340290670720918042893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21325787054227627890723857 15994340290670720918042893)
            ·
              refine ⟨5997877609001520344266085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15994340290670720918042893 5997877609001520344266085)
              ·
                refine ⟨1124602051687785064549891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5997877609001520344266085 1124602051687785064549891)
                ·
                  refine ⟨1686903077531677596824837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1124602051687785064549891 1686903077531677596824837)
                  ·
                    refine ⟨316294327037189549404657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1686903077531677596824837 316294327037189549404657)
                    ·
                      rfl

theorem cell23_1847943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 4, 1, 4].length) (baseStart_1847943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1847943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1847943 prefixEnd_1847943 := by exact prefixLift 1847943
  have htrace : WordTrace (prefixWord ++ tailWord_1847943) baseStart_1847943 baseEnd_1847943 := by
    simpa [prefixWord, tailWord_1847943, baseEnd_1847943] using wordTrace_append hprefix tailTrace_1847943
  have hstable : (prefixWord ++ tailWord_1847943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1847943).length < 2 ^ (prefixWord ++ tailWord_1847943).sum := by decide
  have hdescent : baseEnd_1847943 < baseStart_1847943 := by decide
  rcases family_descends (prefixWord ++ tailWord_1847943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1848000 : List Nat := [2, 1, 1, 2, 4, 2, 2, 4, 1, 1, 3]
def baseStart_1848000 : Nat := 118140960795 + 1848000 * 2 ^ 59
def prefixEnd_1848000 : Nat := 4983230072969 + 3 ^ 40 * 1848000 * 2
def baseEnd_1848000 : Nat := 948912249508874925201209

theorem tailTrace_1848000 : CollatzResearch.WordTrace tailWord_1848000 prefixEnd_1848000 948912249508874925201209 := by
  unfold tailWord_1848000
  simp only [CollatzResearch.WordTrace]
  refine ⟨33701048652509544058926727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44934731536679392078568969 33701048652509544058926727)
  ·
    refine ⟨50551572978764316088390091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33701048652509544058926727 50551572978764316088390091)
    ·
      refine ⟨75827359468146474132585137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50551572978764316088390091 75827359468146474132585137)
      ·
        refine ⟨56870519601109855599438853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75827359468146474132585137 56870519601109855599438853)
        ·
          refine ⟨10663222425208097924894785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56870519601109855599438853 10663222425208097924894785)
          ·
            refine ⟨7997416818906073443671089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10663222425208097924894785 7997416818906073443671089)
            ·
              refine ⟨5998062614179555082753317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7997416818906073443671089 5998062614179555082753317)
              ·
                refine ⟨1124636740158666578016247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5998062614179555082753317 1124636740158666578016247)
                ·
                  refine ⟨1686955110237999867024371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1124636740158666578016247 1686955110237999867024371)
                  ·
                    refine ⟨2530432665356999800536557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1686955110237999867024371 2530432665356999800536557)
                    ·
                      refine ⟨948912249508874925201209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2530432665356999800536557 948912249508874925201209)
                      ·
                        rfl

theorem cell23_1848000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 4, 1, 1, 3].length) (baseStart_1848000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1848000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1848000 prefixEnd_1848000 := by exact prefixLift 1848000
  have htrace : WordTrace (prefixWord ++ tailWord_1848000) baseStart_1848000 baseEnd_1848000 := by
    simpa [prefixWord, tailWord_1848000, baseEnd_1848000] using wordTrace_append hprefix tailTrace_1848000
  have hstable : (prefixWord ++ tailWord_1848000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1848000).length < 2 ^ (prefixWord ++ tailWord_1848000).sum := by decide
  have hdescent : baseEnd_1848000 < baseStart_1848000 := by decide
  rcases family_descends (prefixWord ++ tailWord_1848000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1848020 : List Nat := [2, 4, 1, 3, 2, 1, 2, 2, 1, 5]
def baseStart_1848020 : Nat := 118140960795 + 1848020 * 2 ^ 59
def prefixEnd_1848020 : Nat := 4983230072969 + 3 ^ 40 * 1848020 * 2
def baseEnd_1848020 : Nat := 316307506373988282317039

theorem tailTrace_1848020 : CollatzResearch.WordTrace tailWord_1848020 prefixEnd_1848020 316307506373988282317039 := by
  unfold tailWord_1848020
  simp only [CollatzResearch.WordTrace]
  refine ⟨33701413382473315766790757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44935217843297754355721009 33701413382473315766790757)
  ·
    refine ⟨6319015009213746706273267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33701413382473315766790757 6319015009213746706273267)
    ·
      refine ⟨9478522513820620059409901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6319015009213746706273267 9478522513820620059409901)
      ·
        refine ⟨3554445942682732522278713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9478522513820620059409901 3554445942682732522278713)
        ·
          refine ⟨2665834457012049391709035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3554445942682732522278713 2665834457012049391709035)
          ·
            refine ⟨3998751685518074087563553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2665834457012049391709035 3998751685518074087563553)
            ·
              refine ⟨2999063764138555565672665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3998751685518074087563553 2999063764138555565672665)
              ·
                refine ⟨2249297823103916674254499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2999063764138555565672665 2249297823103916674254499)
                ·
                  refine ⟨3373946734655875011381749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2249297823103916674254499 3373946734655875011381749)
                  ·
                    refine ⟨316307506373988282317039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3373946734655875011381749 316307506373988282317039)
                    ·
                      rfl

theorem cell23_1848020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 2, 2, 1, 5].length) (baseStart_1848020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1848020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1848020 prefixEnd_1848020 := by exact prefixLift 1848020
  have htrace : WordTrace (prefixWord ++ tailWord_1848020) baseStart_1848020 baseEnd_1848020 := by
    simpa [prefixWord, tailWord_1848020, baseEnd_1848020] using wordTrace_append hprefix tailTrace_1848020
  have hstable : (prefixWord ++ tailWord_1848020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1848020).length < 2 ^ (prefixWord ++ tailWord_1848020).sum := by decide
  have hdescent : baseEnd_1848020 < baseStart_1848020 := by decide
  rcases family_descends (prefixWord ++ tailWord_1848020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1848023 : List Nat := [1, 1, 3, 2, 1, 5, 2, 2, 1, 1, 4]
def baseStart_1848023 : Nat := 118140960795 + 1848023 * 2 ^ 59
def prefixEnd_1848023 : Nat := 4983230072969 + 3 ^ 40 * 1848023 * 2
def baseEnd_1848023 : Nat := 948924059563928335213603

theorem tailTrace_1848023 : CollatzResearch.WordTrace tailWord_1848023 prefixEnd_1848023 948924059563928335213603 := by
  unfold tailWord_1848023
  simp only [CollatzResearch.WordTrace]
  refine ⟨67402936183935763045940723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44935290789290508697293815 67402936183935763045940723)
  ·
    refine ⟨101104404275903644568911085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67402936183935763045940723 101104404275903644568911085)
    ·
      refine ⟨37914151603463866713341657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101104404275903644568911085 37914151603463866713341657)
      ·
        refine ⟨28435613702597900035006243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37914151603463866713341657 28435613702597900035006243)
        ·
          refine ⟨42653420553896850052509365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28435613702597900035006243 42653420553896850052509365)
          ·
            refine ⟨3998758176927829692422753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42653420553896850052509365 3998758176927829692422753)
            ·
              refine ⟨2999068632695872269317065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3998758176927829692422753 2999068632695872269317065)
              ·
                refine ⟨2249301474521904201987799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2999068632695872269317065 2249301474521904201987799)
                ·
                  refine ⟨3373952211782856302981699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2249301474521904201987799 3373952211782856302981699)
                  ·
                    refine ⟨5060928317674284454472549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3373952211782856302981699 5060928317674284454472549)
                    ·
                      refine ⟨948924059563928335213603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5060928317674284454472549 948924059563928335213603)
                      ·
                        rfl

theorem cell23_1848023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 2, 2, 1, 1, 4].length) (baseStart_1848023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1848023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1848023 prefixEnd_1848023 := by exact prefixLift 1848023
  have htrace : WordTrace (prefixWord ++ tailWord_1848023) baseStart_1848023 baseEnd_1848023 := by
    simpa [prefixWord, tailWord_1848023, baseEnd_1848023] using wordTrace_append hprefix tailTrace_1848023
  have hstable : (prefixWord ++ tailWord_1848023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1848023).length < 2 ^ (prefixWord ++ tailWord_1848023).sum := by decide
  have hdescent : baseEnd_1848023 < baseStart_1848023 := by decide
  rcases family_descends (prefixWord ++ tailWord_1848023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1848046 : List Nat := [4, 1, 2, 1, 1, 5, 9]
def baseStart_1848046 : Nat := 118140960795 + 1848046 * 2 ^ 59
def prefixEnd_1848046 : Nat := 4983230072969 + 3 ^ 40 * 1848046 * 2
def baseEnd_1848046 : Nat := 11715257649617058583037

theorem tailTrace_1848046 : CollatzResearch.WordTrace tailWord_1848046 prefixEnd_1848046 11715257649617058583037 := by
  unfold tailWord_1848046
  simp only [CollatzResearch.WordTrace]
  refine ⟨8425471882856554746753499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44935850041901625316018661 8425471882856554746753499)
  ·
    refine ⟨12638207824284832120130249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8425471882856554746753499 12638207824284832120130249)
    ·
      refine ⟨9478655868213624090097687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12638207824284832120130249 9478655868213624090097687)
      ·
        refine ⟨14217983802320436135146531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9478655868213624090097687 14217983802320436135146531)
        ·
          refine ⟨21326975703480654202719797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14217983802320436135146531 21326975703480654202719797)
          ·
            refine ⟨1999403972201311331504981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21326975703480654202719797 1999403972201311331504981)
            ·
              refine ⟨11715257649617058583037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1999403972201311331504981 11715257649617058583037)
              ·
                rfl

theorem cell23_1848046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 9].length) (baseStart_1848046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1848046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1848046 prefixEnd_1848046 := by exact prefixLift 1848046
  have htrace : WordTrace (prefixWord ++ tailWord_1848046) baseStart_1848046 baseEnd_1848046 := by
    simpa [prefixWord, tailWord_1848046, baseEnd_1848046] using wordTrace_append hprefix tailTrace_1848046
  have hstable : (prefixWord ++ tailWord_1848046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1848046).length < 2 ^ (prefixWord ++ tailWord_1848046).sum := by decide
  have hdescent : baseEnd_1848046 < baseStart_1848046 := by decide
  rcases family_descends (prefixWord ++ tailWord_1848046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1848083 : List Nat := [1, 1, 1, 2, 1, 3, 5, 1, 3, 3, 2]
def baseStart_1848083 : Nat := 118140960795 + 1848083 * 2 ^ 59
def prefixEnd_1848083 : Nat := 4983230072969 + 3 ^ 40 * 1848083 * 2
def baseEnd_1848083 : Nat := 948954868403198100463327

theorem tailTrace_1848083 : CollatzResearch.WordTrace tailWord_1848083 prefixEnd_1848083 948954868403198100463327 := by
  unfold tailWord_1848083
  simp only [CollatzResearch.WordTrace]
  refine ⟨67405124563718393293124903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44936749709145595528749935 67405124563718393293124903)
  ·
    refine ⟨101107686845577589939687355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67405124563718393293124903 101107686845577589939687355)
    ·
      refine ⟨151661530268366384909531033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101107686845577589939687355 151661530268366384909531033)
      ·
        refine ⟨113746147701274788682148275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151661530268366384909531033 113746147701274788682148275)
        ·
          refine ⟨170619221551912183023222413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113746147701274788682148275 170619221551912183023222413)
          ·
            refine ⟨63982208081967068633708405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 170619221551912183023222413 63982208081967068633708405)
            ·
              refine ⟨5998332007684412684410163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 63982208081967068633708405 5998332007684412684410163)
              ·
                refine ⟨8997498011526619026615245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5998332007684412684410163 8997498011526619026615245)
                ·
                  refine ⟨3374061754322482134980717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8997498011526619026615245 3374061754322482134980717)
                  ·
                    refine ⟨1265273157870930800617769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3374061754322482134980717 1265273157870930800617769)
                    ·
                      refine ⟨948954868403198100463327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1265273157870930800617769 948954868403198100463327)
                      ·
                        rfl

theorem cell23_1848083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 1, 3, 3, 2].length) (baseStart_1848083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1848083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1848083 prefixEnd_1848083 := by exact prefixLift 1848083
  have htrace : WordTrace (prefixWord ++ tailWord_1848083) baseStart_1848083 baseEnd_1848083 := by
    simpa [prefixWord, tailWord_1848083, baseEnd_1848083] using wordTrace_append hprefix tailTrace_1848083
  have hstable : (prefixWord ++ tailWord_1848083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1848083).length < 2 ^ (prefixWord ++ tailWord_1848083).sum := by decide
  have hdescent : baseEnd_1848083 < baseStart_1848083 := by decide
  rcases family_descends (prefixWord ++ tailWord_1848083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1848089 : List Nat := [1, 2, 1, 2, 1, 1, 1, 3, 3, 8]
def baseStart_1848089 : Nat := 118140960795 + 1848089 * 2 ^ 59
def prefixEnd_1848089 : Nat := 4983230072969 + 3 ^ 40 * 1848089 * 2
def baseEnd_1848089 : Nat := 316319316429041692329433

theorem tailTrace_1848089 : CollatzResearch.WordTrace tailWord_1848089 prefixEnd_1848089 316319316429041692329433 := by
  unfold tailWord_1848089
  simp only [CollatzResearch.WordTrace]
  refine ⟨67405343401696656317843321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44936895601131104211895547 67405343401696656317843321)
  ·
    refine ⟨50554007551272492238382491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67405343401696656317843321 50554007551272492238382491)
    ·
      refine ⟨75831011326908738357573737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50554007551272492238382491 75831011326908738357573737)
      ·
        refine ⟨56873258495181553768180303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75831011326908738357573737 56873258495181553768180303)
        ·
          refine ⟨85309887742772330652270455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56873258495181553768180303 85309887742772330652270455)
          ·
            refine ⟨127964831614158495978405683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85309887742772330652270455 127964831614158495978405683)
            ·
              refine ⟨191947247421237743967608525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127964831614158495978405683 191947247421237743967608525)
              ·
                refine ⟨71980217782964153987853197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 191947247421237743967608525 71980217782964153987853197)
                ·
                  refine ⟨26992581668611557745444949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71980217782964153987853197 26992581668611557745444949)
                  ·
                    refine ⟨316319316429041692329433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 26992581668611557745444949 316319316429041692329433)
                    ·
                      rfl

theorem cell23_1848089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 3, 3, 8].length) (baseStart_1848089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1848089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1848089 prefixEnd_1848089 := by exact prefixLift 1848089
  have htrace : WordTrace (prefixWord ++ tailWord_1848089) baseStart_1848089 baseEnd_1848089 := by
    simpa [prefixWord, tailWord_1848089, baseEnd_1848089] using wordTrace_append hprefix tailTrace_1848089
  have hstable : (prefixWord ++ tailWord_1848089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1848089).length < 2 ^ (prefixWord ++ tailWord_1848089).sum := by decide
  have hdescent : baseEnd_1848089 < baseStart_1848089 := by decide
  rcases family_descends (prefixWord ++ tailWord_1848089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1848113 : List Nat := [1, 2, 2, 3, 2, 1, 1, 2, 3, 4, 2]
def baseStart_1848113 : Nat := 118140960795 + 1848113 * 2 ^ 59
def prefixEnd_1848113 : Nat := 4983230072969 + 3 ^ 40 * 1848113 * 2
def baseEnd_1848113 : Nat := 948970272822832983088189

theorem tailTrace_1848113 : CollatzResearch.WordTrace tailWord_1848113 prefixEnd_1848113 948970272822832983088189 := by
  unfold tailWord_1848113
  simp only [CollatzResearch.WordTrace]
  refine ⟨67406218753609708416716993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44937479169073138944477995 67406218753609708416716993)
  ·
    refine ⟨50554664065207281312537745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67406218753609708416716993 50554664065207281312537745)
    ·
      refine ⟨37915998048905460984403309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50554664065207281312537745 37915998048905460984403309)
      ·
        refine ⟨14218499268339547869151241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37915998048905460984403309 14218499268339547869151241)
        ·
          refine ⟨10663874451254660901863431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14218499268339547869151241 10663874451254660901863431)
          ·
            refine ⟨15995811676881991352795147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10663874451254660901863431 15995811676881991352795147)
            ·
              refine ⟨23993717515322987029192721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15995811676881991352795147 23993717515322987029192721)
              ·
                refine ⟨17995288136492240271894541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23993717515322987029192721 17995288136492240271894541)
                ·
                  refine ⟨6748233051184590101960453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17995288136492240271894541 6748233051184590101960453)
                  ·
                    refine ⟨1265293697097110644117585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6748233051184590101960453 1265293697097110644117585)
                    ·
                      refine ⟨948970272822832983088189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1265293697097110644117585 948970272822832983088189)
                      ·
                        rfl

theorem cell23_1848113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 2, 3, 4, 2].length) (baseStart_1848113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1848113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1848113 prefixEnd_1848113 := by exact prefixLift 1848113
  have htrace : WordTrace (prefixWord ++ tailWord_1848113) baseStart_1848113 baseEnd_1848113 := by
    simpa [prefixWord, tailWord_1848113, baseEnd_1848113] using wordTrace_append hprefix tailTrace_1848113
  have hstable : (prefixWord ++ tailWord_1848113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1848113).length < 2 ^ (prefixWord ++ tailWord_1848113).sum := by decide
  have hdescent : baseEnd_1848113 < baseStart_1848113 := by decide
  rcases family_descends (prefixWord ++ tailWord_1848113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1848136 : List Nat := [2, 1, 3, 1, 1, 3, 3, 2, 7]
def baseStart_1848136 : Nat := 118140960795 + 1848136 * 2 ^ 59
def prefixEnd_1848136 : Nat := 4983230072969 + 3 ^ 40 * 1848136 * 2
def baseEnd_1848136 : Nat := 105442453653098488122287

theorem tailTrace_1848136 : CollatzResearch.WordTrace tailWord_1848136 prefixEnd_1848136 105442453653098488122287 := by
  unfold tailWord_1848136
  simp only [CollatzResearch.WordTrace]
  refine ⟨33703528816263191672402131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44938038421684255563202841 33703528816263191672402131)
  ·
    refine ⟨50555293224394787508603197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33703528816263191672402131 50555293224394787508603197)
    ·
      refine ⟨18958234959148045315726199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50555293224394787508603197 18958234959148045315726199)
      ·
        refine ⟨28437352438722067973589299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18958234959148045315726199 28437352438722067973589299)
        ·
          refine ⟨42656028658083101960383949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28437352438722067973589299 42656028658083101960383949)
          ·
            refine ⟨15996010746781163235143981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42656028658083101960383949 15996010746781163235143981)
            ·
              refine ⟨5998504030042936213178993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15996010746781163235143981 5998504030042936213178993)
              ·
                refine ⟨4498878022532202159884245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5998504030042936213178993 4498878022532202159884245)
                ·
                  refine ⟨105442453653098488122287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4498878022532202159884245 105442453653098488122287)
                  ·
                    rfl

theorem cell23_1848136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 2, 7].length) (baseStart_1848136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1848136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1848136 prefixEnd_1848136 := by exact prefixLift 1848136
  have htrace : WordTrace (prefixWord ++ tailWord_1848136) baseStart_1848136 baseEnd_1848136 := by
    simpa [prefixWord, tailWord_1848136, baseEnd_1848136] using wordTrace_append hprefix tailTrace_1848136
  have hstable : (prefixWord ++ tailWord_1848136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1848136).length < 2 ^ (prefixWord ++ tailWord_1848136).sum := by decide
  have hdescent : baseEnd_1848136 < baseStart_1848136 := by decide
  rcases family_descends (prefixWord ++ tailWord_1848136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1848153 : List Nat := [1, 2, 1, 2, 2, 4, 1, 5, 5]
def baseStart_1848153 : Nat := 118140960795 + 1848153 * 2 ^ 59
def prefixEnd_1848153 : Nat := 4983230072969 + 3 ^ 40 * 1848153 * 2
def baseEnd_1848153 : Nat := 105443423561001425176445

theorem tailTrace_1848153 : CollatzResearch.WordTrace tailWord_1848153 prefixEnd_1848153 105443423561001425176445 := by
  unfold tailWord_1848153
  simp only [CollatzResearch.WordTrace]
  refine ⟨67407677673464795248173113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44938451782309863498782075 67407677673464795248173113)
  ·
    refine ⟨50555758255098596436129835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67407677673464795248173113 50555758255098596436129835)
    ·
      refine ⟨75833637382647894654194753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50555758255098596436129835 75833637382647894654194753)
      ·
        refine ⟨56875228036985920990646065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75833637382647894654194753 56875228036985920990646065)
        ·
          refine ⟨42656421027739440742984549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56875228036985920990646065 42656421027739440742984549)
          ·
            refine ⟨7998078942701145139309603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42656421027739440742984549 7998078942701145139309603)
            ·
              refine ⟨11997118414051717708964405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7998078942701145139309603 11997118414051717708964405)
              ·
                refine ⟨1124729851317348535215413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11997118414051717708964405 1124729851317348535215413)
                ·
                  refine ⟨105443423561001425176445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1124729851317348535215413 105443423561001425176445)
                  ·
                    rfl

theorem cell23_1848153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 5, 5].length) (baseStart_1848153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1848153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1848153 prefixEnd_1848153 := by exact prefixLift 1848153
  have htrace : WordTrace (prefixWord ++ tailWord_1848153) baseStart_1848153 baseEnd_1848153 := by
    simpa [prefixWord, tailWord_1848153, baseEnd_1848153] using wordTrace_append hprefix tailTrace_1848153
  have hstable : (prefixWord ++ tailWord_1848153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1848153).length < 2 ^ (prefixWord ++ tailWord_1848153).sum := by decide
  have hdescent : baseEnd_1848153 < baseStart_1848153 := by decide
  rcases family_descends (prefixWord ++ tailWord_1848153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1848163 : List Nat := [1, 1, 1, 5, 3, 1, 1, 2, 2, 3, 3]
def baseStart_1848163 : Nat := 118140960795 + 1848163 * 2 ^ 59
def prefixEnd_1848163 : Nat := 4983230072969 + 3 ^ 40 * 1848163 * 2
def baseEnd_1848163 : Nat := 948995946855557787462959

theorem tailTrace_1848163 : CollatzResearch.WordTrace tailWord_1848163 prefixEnd_1848163 948995946855557787462959 := by
  unfold tailWord_1848163
  simp only [CollatzResearch.WordTrace]
  refine ⟨67408042403428566956037143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44938694935619044637358095 67408042403428566956037143)
  ·
    refine ⟨101112063605142850434055715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67408042403428566956037143 101112063605142850434055715)
    ·
      refine ⟨151668095407714275651083573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101112063605142850434055715 151668095407714275651083573)
      ·
        refine ⟨14218883944473213342289085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 151668095407714275651083573 14218883944473213342289085)
        ·
          refine ⟨5332081479177455003358407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14218883944473213342289085 5332081479177455003358407)
          ·
            refine ⟨7998122218766182505037611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5332081479177455003358407 7998122218766182505037611)
            ·
              refine ⟨11997183328149273757556417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7998122218766182505037611 11997183328149273757556417)
              ·
                refine ⟨8997887496111955318167313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11997183328149273757556417 8997887496111955318167313)
                ·
                  refine ⟨6748415622083966488625485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8997887496111955318167313 6748415622083966488625485)
                  ·
                    refine ⟨2530655858281487433234557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6748415622083966488625485 2530655858281487433234557)
                    ·
                      refine ⟨948995946855557787462959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2530655858281487433234557 948995946855557787462959)
                      ·
                        rfl

theorem cell23_1848163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 2, 2, 3, 3].length) (baseStart_1848163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1848163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1848163 prefixEnd_1848163 := by exact prefixLift 1848163
  have htrace : WordTrace (prefixWord ++ tailWord_1848163) baseStart_1848163 baseEnd_1848163 := by
    simpa [prefixWord, tailWord_1848163, baseEnd_1848163] using wordTrace_append hprefix tailTrace_1848163
  have hstable : (prefixWord ++ tailWord_1848163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1848163).length < 2 ^ (prefixWord ++ tailWord_1848163).sum := by decide
  have hdescent : baseEnd_1848163 < baseStart_1848163 := by decide
  rcases family_descends (prefixWord ++ tailWord_1848163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1848164 : List Nat := [2, 3, 1, 1, 4, 3, 1, 2, 2, 2, 2]
def baseStart_1848164 : Nat := 118140960795 + 1848164 * 2 ^ 59
def prefixEnd_1848164 : Nat := 4983230072969 + 3 ^ 40 * 1848164 * 2
def baseEnd_1848164 : Nat := 948996460336212283550455

theorem tailTrace_1848164 : CollatzResearch.WordTrace tailWord_1848164 prefixEnd_1848164 948996460336212283550455 := by
  unfold tailWord_1848164
  simp only [CollatzResearch.WordTrace]
  refine ⟨33704039438212472063411773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44938719250949962751215697 33704039438212472063411773)
  ·
    refine ⟨12639014789329677023779415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33704039438212472063411773 12639014789329677023779415)
    ·
      refine ⟨18958522183994515535669123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12639014789329677023779415 18958522183994515535669123)
      ·
        refine ⟨28437783275991773303503685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18958522183994515535669123 28437783275991773303503685)
        ·
          refine ⟨5332084364248457494406941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28437783275991773303503685 5332084364248457494406941)
          ·
            refine ⟨1999531636593171560402603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5332084364248457494406941 1999531636593171560402603)
            ·
              refine ⟨2999297454889757340603905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1999531636593171560402603 2999297454889757340603905)
              ·
                refine ⟨2249473091167318005452929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2999297454889757340603905 2249473091167318005452929)
                ·
                  refine ⟨1687104818375488504089697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2249473091167318005452929 1687104818375488504089697)
                  ·
                    refine ⟨1265328613781616378067273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1687104818375488504089697 1265328613781616378067273)
                    ·
                      refine ⟨948996460336212283550455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1265328613781616378067273 948996460336212283550455)
                      ·
                        rfl

theorem cell23_1848164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 1, 2, 2, 2, 2].length) (baseStart_1848164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1848164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1848164 prefixEnd_1848164 := by exact prefixLift 1848164
  have htrace : WordTrace (prefixWord ++ tailWord_1848164) baseStart_1848164 baseEnd_1848164 := by
    simpa [prefixWord, tailWord_1848164, baseEnd_1848164] using wordTrace_append hprefix tailTrace_1848164
  have hstable : (prefixWord ++ tailWord_1848164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1848164).length < 2 ^ (prefixWord ++ tailWord_1848164).sum := by decide
  have hdescent : baseEnd_1848164 < baseStart_1848164 := by decide
  rcases family_descends (prefixWord ++ tailWord_1848164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1848176 : List Nat := [2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 5]
def baseStart_1848176 : Nat := 118140960795 + 1848176 * 2 ^ 59
def prefixEnd_1848176 : Nat := 4983230072969 + 3 ^ 40 * 1848176 * 2
def baseEnd_1848176 : Nat := 949002622104066236600399

theorem tailTrace_1848176 : CollatzResearch.WordTrace tailWord_1848176 prefixEnd_1848176 949002622104066236600399 := by
  unfold tailWord_1848176
  simp only [CollatzResearch.WordTrace]
  refine ⟨33704258276190735088130191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44939011034920980117506921 33704258276190735088130191)
  ·
    refine ⟨50556387414286102632195287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33704258276190735088130191 50556387414286102632195287)
    ·
      refine ⟨75834581121429153948292931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50556387414286102632195287 75834581121429153948292931)
      ·
        refine ⟨113751871682143730922439397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75834581121429153948292931 113751871682143730922439397)
        ·
          refine ⟨21328475940401949547957387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 113751871682143730922439397 21328475940401949547957387)
          ·
            refine ⟨31992713910602924321936081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21328475940401949547957387 31992713910602924321936081)
            ·
              refine ⟨23994535432952193241452061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31992713910602924321936081 23994535432952193241452061)
              ·
                refine ⟨8997950787357072465544523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23994535432952193241452061 8997950787357072465544523)
                ·
                  refine ⟨13496926181035608698316785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8997950787357072465544523 13496926181035608698316785)
                  ·
                    refine ⟨10122694635776706523737589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13496926181035608698316785 10122694635776706523737589)
                    ·
                      refine ⟨949002622104066236600399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10122694635776706523737589 949002622104066236600399)
                      ·
                        rfl

theorem cell23_1848176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 5].length) (baseStart_1848176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1848176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1848176 prefixEnd_1848176 := by exact prefixLift 1848176
  have htrace : WordTrace (prefixWord ++ tailWord_1848176) baseStart_1848176 baseEnd_1848176 := by
    simpa [prefixWord, tailWord_1848176, baseEnd_1848176] using wordTrace_append hprefix tailTrace_1848176
  have hstable : (prefixWord ++ tailWord_1848176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1848176).length < 2 ^ (prefixWord ++ tailWord_1848176).sum := by decide
  have hdescent : baseEnd_1848176 < baseStart_1848176 := by decide
  rcases family_descends (prefixWord ++ tailWord_1848176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1848196 : List Nat := [2, 3, 2, 1, 1, 1, 1, 1, 1, 10]
def baseStart_1848196 : Nat := 118140960795 + 1848196 * 2 ^ 59
def prefixEnd_1848196 : Nat := 4983230072969 + 3 ^ 40 * 1848196 * 2
def baseEnd_1848196 : Nat := 316337630572385386116769

theorem tailTrace_1848196 : CollatzResearch.WordTrace tailWord_1848196 prefixEnd_1848196 316337630572385386116769 := by
  unfold tailWord_1848196
  simp only [CollatzResearch.WordTrace]
  refine ⟨33704623006154506795994221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44939497341539342394658961 33704623006154506795994221)
  ·
    refine ⟨12639233627307940048497833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33704623006154506795994221 12639233627307940048497833)
    ·
      refine ⟨9479425220480955036373375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12639233627307940048497833 9479425220480955036373375)
      ·
        refine ⟨14219137830721432554560063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9479425220480955036373375 14219137830721432554560063)
        ·
          refine ⟨21328706746082148831840095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14219137830721432554560063 21328706746082148831840095)
          ·
            refine ⟨31993060119123223247760143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21328706746082148831840095 31993060119123223247760143)
            ·
              refine ⟨47989590178684834871640215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31993060119123223247760143 47989590178684834871640215)
              ·
                refine ⟨71984385268027252307460323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47989590178684834871640215 71984385268027252307460323)
                ·
                  refine ⟨107976577902040878461190485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71984385268027252307460323 107976577902040878461190485)
                  ·
                    refine ⟨316337630572385386116769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 107976577902040878461190485 316337630572385386116769)
                    ·
                      rfl

theorem cell23_1848196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 1, 1, 10].length) (baseStart_1848196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1848196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1848196 prefixEnd_1848196 := by exact prefixLift 1848196
  have htrace : WordTrace (prefixWord ++ tailWord_1848196) baseStart_1848196 baseEnd_1848196 := by
    simpa [prefixWord, tailWord_1848196, baseEnd_1848196] using wordTrace_append hprefix tailTrace_1848196
  have hstable : (prefixWord ++ tailWord_1848196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1848196).length < 2 ^ (prefixWord ++ tailWord_1848196).sum := by decide
  have hdescent : baseEnd_1848196 < baseStart_1848196 := by decide
  rcases family_descends (prefixWord ++ tailWord_1848196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1848203 : List Nat := [1, 1, 1, 1, 4, 2, 2, 2, 1, 6, 2]
def baseStart_1848203 : Nat := 118140960795 + 1848203 * 2 ^ 59
def prefixEnd_1848203 : Nat := 4983230072969 + 3 ^ 40 * 1848203 * 2
def baseEnd_1848203 : Nat := 949016486081737630962775

theorem tailTrace_1848203 : CollatzResearch.WordTrace tailWord_1848203 prefixEnd_1848203 949016486081737630962775 := by
  unfold tailWord_1848203
  simp only [CollatzResearch.WordTrace]
  refine ⟨67409501323283653787493263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44939667548855769191662175 67409501323283653787493263)
  ·
    refine ⟨101114251984925480681239895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67409501323283653787493263 101114251984925480681239895)
    ·
      refine ⟨151671377977388221021859843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101114251984925480681239895 151671377977388221021859843)
      ·
        refine ⟨227507066966082331532789765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151671377977388221021859843 227507066966082331532789765)
        ·
          refine ⟨42657575056140437162398081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 227507066966082331532789765 42657575056140437162398081)
          ·
            refine ⟨31993181292105327871798561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42657575056140437162398081 31993181292105327871798561)
            ·
              refine ⟨23994885969078995903848921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31993181292105327871798561 23994885969078995903848921)
              ·
                refine ⟨17996164476809246927886691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23994885969078995903848921 17996164476809246927886691)
                ·
                  refine ⟨26994246715213870391830037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17996164476809246927886691 26994246715213870391830037)
                  ·
                    refine ⟨1265355314775650174617033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26994246715213870391830037 1265355314775650174617033)
                    ·
                      refine ⟨949016486081737630962775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1265355314775650174617033 949016486081737630962775)
                      ·
                        rfl

theorem cell23_1848203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 2, 1, 6, 2].length) (baseStart_1848203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1848203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1848203 prefixEnd_1848203 := by exact prefixLift 1848203
  have htrace : WordTrace (prefixWord ++ tailWord_1848203) baseStart_1848203 baseEnd_1848203 := by
    simpa [prefixWord, tailWord_1848203, baseEnd_1848203] using wordTrace_append hprefix tailTrace_1848203
  have hstable : (prefixWord ++ tailWord_1848203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1848203).length < 2 ^ (prefixWord ++ tailWord_1848203).sum := by decide
  have hdescent : baseEnd_1848203 < baseStart_1848203 := by decide
  rcases family_descends (prefixWord ++ tailWord_1848203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1848303 : List Nat := [1, 1, 2, 1, 4, 3, 1, 3, 1, 6]
def baseStart_1848303 : Nat := 118140960795 + 1848303 * 2 ^ 59
def prefixEnd_1848303 : Nat := 4983230072969 + 3 ^ 40 * 1848303 * 2
def baseEnd_1848303 : Nat := 316355944715729079904105

theorem tailTrace_1848303 : CollatzResearch.WordTrace tailWord_1848303 prefixEnd_1848303 316355944715729079904105 := by
  unfold tailWord_1848303
  simp only [CollatzResearch.WordTrace]
  refine ⟨67413148622921370866133563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44942099081947580577422375 67413148622921370866133563)
  ·
    refine ⟨101119722934382056299200345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67413148622921370866133563 101119722934382056299200345)
    ·
      refine ⟨75839792200786542224400259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101119722934382056299200345 75839792200786542224400259)
      ·
        refine ⟨113759688301179813336600389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75839792200786542224400259 113759688301179813336600389)
        ·
          refine ⟨21329941556471215000612573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 113759688301179813336600389 21329941556471215000612573)
          ·
            refine ⟨7998728083676705625229715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21329941556471215000612573 7998728083676705625229715)
            ·
              refine ⟨11998092125515058437844573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7998728083676705625229715 11998092125515058437844573)
              ·
                refine ⟨4499284547068146914191715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11998092125515058437844573 4499284547068146914191715)
                ·
                  refine ⟨6748926820602220371287573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4499284547068146914191715 6748926820602220371287573)
                  ·
                    refine ⟨316355944715729079904105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6748926820602220371287573 316355944715729079904105)
                    ·
                      rfl

theorem cell23_1848303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 3, 1, 6].length) (baseStart_1848303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1848303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1848303 prefixEnd_1848303 := by exact prefixLift 1848303
  have htrace : WordTrace (prefixWord ++ tailWord_1848303) baseStart_1848303 baseEnd_1848303 := by
    simpa [prefixWord, tailWord_1848303, baseEnd_1848303] using wordTrace_append hprefix tailTrace_1848303
  have hstable : (prefixWord ++ tailWord_1848303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1848303).length < 2 ^ (prefixWord ++ tailWord_1848303).sum := by decide
  have hdescent : baseEnd_1848303 < baseStart_1848303 := by decide
  rcases family_descends (prefixWord ++ tailWord_1848303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1848327 : List Nat := [1, 1, 4, 3, 1, 1, 1, 2, 5, 2, 2]
def baseStart_1848327 : Nat := 118140960795 + 1848327 * 2 ^ 59
def prefixEnd_1848327 : Nat := 4983230072969 + 3 ^ 40 * 1848327 * 2
def baseEnd_1848327 : Nat := 949080157682895145812205

theorem tailTrace_1848327 : CollatzResearch.WordTrace tailWord_1848327 prefixEnd_1848327 949080157682895145812205 := by
  unfold tailWord_1848327
  simp only [CollatzResearch.WordTrace]
  refine ⟨67414023974834422965007235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44942682649889615310004823 67414023974834422965007235)
  ·
    refine ⟨101121035962251634447510853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67414023974834422965007235 101121035962251634447510853)
    ·
      refine ⟨18960194242922181458908285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101121035962251634447510853 18960194242922181458908285)
      ·
        refine ⟨7110072841095818047090607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18960194242922181458908285 7110072841095818047090607)
        ·
          refine ⟨10665109261643727070635911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7110072841095818047090607 10665109261643727070635911)
          ·
            refine ⟨15997663892465590605953867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10665109261643727070635911 15997663892465590605953867)
            ·
              refine ⟨23996495838698385908930801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15997663892465590605953867 23996495838698385908930801)
              ·
                refine ⟨17997371879023789431698101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23996495838698385908930801 17997371879023789431698101)
                ·
                  refine ⟨1687253613658480259221697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17997371879023789431698101 1687253613658480259221697)
                  ·
                    refine ⟨1265440210243860194416273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1687253613658480259221697 1265440210243860194416273)
                    ·
                      refine ⟨949080157682895145812205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1265440210243860194416273 949080157682895145812205)
                      ·
                        rfl

theorem cell23_1848327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 2, 5, 2, 2].length) (baseStart_1848327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1848327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1848327 prefixEnd_1848327 := by exact prefixLift 1848327
  have htrace : WordTrace (prefixWord ++ tailWord_1848327) baseStart_1848327 baseEnd_1848327 := by
    simpa [prefixWord, tailWord_1848327, baseEnd_1848327] using wordTrace_append hprefix tailTrace_1848327
  have hstable : (prefixWord ++ tailWord_1848327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1848327).length < 2 ^ (prefixWord ++ tailWord_1848327).sum := by decide
  have hdescent : baseEnd_1848327 < baseStart_1848327 := by decide
  rcases family_descends (prefixWord ++ tailWord_1848327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1848338 : List Nat := [3, 2, 5, 1, 1, 1, 2, 1, 3, 1, 3]
def baseStart_1848338 : Nat := 118140960795 + 1848338 * 2 ^ 59
def prefixEnd_1848338 : Nat := 4983230072969 + 3 ^ 40 * 1848338 * 2
def baseEnd_1848338 : Nat := 949085805970094602774655

theorem tailTrace_1848338 : CollatzResearch.WordTrace tailWord_1848338 prefixEnd_1848338 949085805970094602774655 := by
  unfold tailWord_1848338
  simp only [CollatzResearch.WordTrace]
  refine ⟨16853606294448642960914417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44942950118529714562438445 16853606294448642960914417)
  ·
    refine ⟨12640204720836482220685813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16853606294448642960914417 12640204720836482220685813)
    ·
      refine ⟨1185019192578420208189295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12640204720836482220685813 1185019192578420208189295)
      ·
        refine ⟨1777528788867630312283943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1185019192578420208189295 1777528788867630312283943)
        ·
          refine ⟨2666293183301445468425915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1777528788867630312283943 2666293183301445468425915)
          ·
            refine ⟨3999439774952168202638873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2666293183301445468425915 3999439774952168202638873)
            ·
              refine ⟨2999579831214126151979155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3999439774952168202638873 2999579831214126151979155)
              ·
                refine ⟨4499369746821189227968733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2999579831214126151979155 4499369746821189227968733)
                ·
                  refine ⟨1687263655057945960488275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4499369746821189227968733 1687263655057945960488275)
                  ·
                    refine ⟨2530895482586918940732413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1687263655057945960488275 2530895482586918940732413)
                    ·
                      refine ⟨949085805970094602774655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2530895482586918940732413 949085805970094602774655)
                      ·
                        rfl

theorem cell23_1848338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_1848338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1848338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1848338 prefixEnd_1848338 := by exact prefixLift 1848338
  have htrace : WordTrace (prefixWord ++ tailWord_1848338) baseStart_1848338 baseEnd_1848338 := by
    simpa [prefixWord, tailWord_1848338, baseEnd_1848338] using wordTrace_append hprefix tailTrace_1848338
  have hstable : (prefixWord ++ tailWord_1848338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1848338).length < 2 ^ (prefixWord ++ tailWord_1848338).sum := by decide
  have hdescent : baseEnd_1848338 < baseStart_1848338 := by decide
  rcases family_descends (prefixWord ++ tailWord_1848338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1848344 : List Nat := [2, 1, 2, 3, 2, 3, 2, 1, 3, 2, 2]
def baseStart_1848344 : Nat := 118140960795 + 1848344 * 2 ^ 59
def prefixEnd_1848344 : Nat := 4983230072969 + 3 ^ 40 * 1848344 * 2
def baseEnd_1848344 : Nat := 949088886854021579299627

theorem tailTrace_1848344 : CollatzResearch.WordTrace tailWord_1848344 prefixEnd_1848344 949088886854021579299627 := by
  unfold tailWord_1848344
  simp only [CollatzResearch.WordTrace]
  refine ⟨33707322007886417434188043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44943096010515223245584057 33707322007886417434188043)
  ·
    refine ⟨50560983011829626151282065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33707322007886417434188043 50560983011829626151282065)
    ·
      refine ⟨37920737258872219613461549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50560983011829626151282065 37920737258872219613461549)
      ·
        refine ⟨14220276472077082355048081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37920737258872219613461549 14220276472077082355048081)
        ·
          refine ⟨10665207354057811766286061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14220276472077082355048081 10665207354057811766286061)
          ·
            refine ⟨3999452757771679412357273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10665207354057811766286061 3999452757771679412357273)
            ·
              refine ⟨2999589568328759559267955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3999452757771679412357273 2999589568328759559267955)
              ·
                refine ⟨4499384352493139338901933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2999589568328759559267955 4499384352493139338901933)
                ·
                  refine ⟨1687269132184927252088225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4499384352493139338901933 1687269132184927252088225)
                  ·
                    refine ⟨1265451849138695439066169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1687269132184927252088225 1265451849138695439066169)
                    ·
                      refine ⟨949088886854021579299627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1265451849138695439066169 949088886854021579299627)
                      ·
                        rfl

theorem cell23_1848344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 2, 1, 3, 2, 2].length) (baseStart_1848344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1848344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1848344 prefixEnd_1848344 := by exact prefixLift 1848344
  have htrace : WordTrace (prefixWord ++ tailWord_1848344) baseStart_1848344 baseEnd_1848344 := by
    simpa [prefixWord, tailWord_1848344, baseEnd_1848344] using wordTrace_append hprefix tailTrace_1848344
  have hstable : (prefixWord ++ tailWord_1848344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1848344).length < 2 ^ (prefixWord ++ tailWord_1848344).sum := by decide
  have hdescent : baseEnd_1848344 < baseStart_1848344 := by decide
  rcases family_descends (prefixWord ++ tailWord_1848344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1848354 : List Nat := [3, 3, 1, 1, 1, 4, 3, 1, 2, 4]
def baseStart_1848354 : Nat := 118140960795 + 1848354 * 2 ^ 59
def prefixEnd_1848354 : Nat := 4983230072969 + 3 ^ 40 * 1848354 * 2
def baseEnd_1848354 : Nat := 316364673886855513391527

theorem tailTrace_1848354 : CollatzResearch.WordTrace tailWord_1848354 prefixEnd_1848354 316364673886855513391527 := by
  unfold tailWord_1848354
  simp only [CollatzResearch.WordTrace]
  refine ⟨16853752186434151644060029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44943339163824404384160077 16853752186434151644060029)
  ·
    refine ⟨6320157069912806866522511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16853752186434151644060029 6320157069912806866522511)
    ·
      refine ⟨9480235604869210299783767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6320157069912806866522511 9480235604869210299783767)
      ·
        refine ⟨14220353407303815449675651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9480235604869210299783767 14220353407303815449675651)
        ·
          refine ⟨21330530110955723174513477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14220353407303815449675651 21330530110955723174513477)
          ·
            refine ⟨3999474395804198095221277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21330530110955723174513477 3999474395804198095221277)
            ·
              refine ⟨1499802898426574285707979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3999474395804198095221277 1499802898426574285707979)
              ·
                refine ⟨2249704347639861428561969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1499802898426574285707979 2249704347639861428561969)
                ·
                  refine ⟨1687278260729896071421477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2249704347639861428561969 1687278260729896071421477)
                  ·
                    refine ⟨316364673886855513391527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1687278260729896071421477 316364673886855513391527)
                    ·
                      rfl

theorem cell23_1848354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 3, 1, 2, 4].length) (baseStart_1848354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1848354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1848354 prefixEnd_1848354 := by exact prefixLift 1848354
  have htrace : WordTrace (prefixWord ++ tailWord_1848354) baseStart_1848354 baseEnd_1848354 := by
    simpa [prefixWord, tailWord_1848354, baseEnd_1848354] using wordTrace_append hprefix tailTrace_1848354
  have hstable : (prefixWord ++ tailWord_1848354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1848354).length < 2 ^ (prefixWord ++ tailWord_1848354).sum := by decide
  have hdescent : baseEnd_1848354 < baseStart_1848354 := by decide
  rcases family_descends (prefixWord ++ tailWord_1848354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1848377 : List Nat := [1, 2, 1, 5, 2, 1, 1, 2, 4, 1, 3]
def baseStart_1848377 : Nat := 118140960795 + 1848377 * 2 ^ 59
def prefixEnd_1848377 : Nat := 4983230072969 + 3 ^ 40 * 1848377 * 2
def baseEnd_1848377 : Nat := 949105831715619950186975

theorem tailTrace_1848377 : CollatzResearch.WordTrace tailWord_1848377 prefixEnd_1848377 949105831715619950186975 := by
  unfold tailWord_1848377
  simp only [CollatzResearch.WordTrace]
  refine ⟨67415847624653281504327385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44943898416435521002884923 67415847624653281504327385)
  ·
    refine ⟨50561885718489961128245539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67415847624653281504327385 50561885718489961128245539)
    ·
      refine ⟨75842828577734941692368309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50561885718489961128245539 75842828577734941692368309)
      ·
        refine ⟨7110265179162650783659529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 75842828577734941692368309 7110265179162650783659529)
        ·
          refine ⟨5332698884371988087744647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7110265179162650783659529 5332698884371988087744647)
          ·
            refine ⟨7999048326557982131616971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5332698884371988087744647 7999048326557982131616971)
            ·
              refine ⟨11998572489836973197425457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7999048326557982131616971 11998572489836973197425457)
              ·
                refine ⟨8998929367377729898069093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11998572489836973197425457 8998929367377729898069093)
                ·
                  refine ⟨1687299256383324355887955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8998929367377729898069093 1687299256383324355887955)
                  ·
                    refine ⟨2530948884574986533831933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1687299256383324355887955 2530948884574986533831933)
                    ·
                      refine ⟨949105831715619950186975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2530948884574986533831933 949105831715619950186975)
                      ·
                        rfl

theorem cell23_1848377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 2, 4, 1, 3].length) (baseStart_1848377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1848377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1848377 prefixEnd_1848377 := by exact prefixLift 1848377
  have htrace : WordTrace (prefixWord ++ tailWord_1848377) baseStart_1848377 baseEnd_1848377 := by
    simpa [prefixWord, tailWord_1848377, baseEnd_1848377] using wordTrace_append hprefix tailTrace_1848377
  have hstable : (prefixWord ++ tailWord_1848377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1848377).length < 2 ^ (prefixWord ++ tailWord_1848377).sum := by decide
  have hdescent : baseEnd_1848377 < baseStart_1848377 := by decide
  rcases family_descends (prefixWord ++ tailWord_1848377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1848383 : List Nat := [1, 1, 2, 2, 3, 1, 1, 2, 1, 5, 4]
def baseStart_1848383 : Nat := 118140960795 + 1848383 * 2 ^ 59
def prefixEnd_1848383 : Nat := 4983230072969 + 3 ^ 40 * 1848383 * 2
def baseEnd_1848383 : Nat := 949108912599546926711947

theorem tailTrace_1848383 : CollatzResearch.WordTrace tailWord_1848383 prefixEnd_1848383 949108912599546926711947 := by
  unfold tailWord_1848383
  simp only [CollatzResearch.WordTrace]
  refine ⟨67416066462631544529045803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44944044308421029686030535 67416066462631544529045803)
  ·
    refine ⟨101124099693947316793568705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67416066462631544529045803 101124099693947316793568705)
    ·
      refine ⟨75843074770460487595176529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101124099693947316793568705 75843074770460487595176529)
      ·
        refine ⟨56882306077845365696382397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75843074770460487595176529 56882306077845365696382397)
        ·
          refine ⟨21330864779192012136143399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56882306077845365696382397 21330864779192012136143399)
          ·
            refine ⟨31996297168788018204215099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21330864779192012136143399 31996297168788018204215099)
            ·
              refine ⟨47994445753182027306322649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31996297168788018204215099 47994445753182027306322649)
              ·
                refine ⟨35995834314886520479741987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47994445753182027306322649 35995834314886520479741987)
                ·
                  refine ⟨53993751472329780719612981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35995834314886520479741987 53993751472329780719612981)
                  ·
                    refine ⟨5061914200530916942463717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53993751472329780719612981 5061914200530916942463717)
                    ·
                      refine ⟨949108912599546926711947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5061914200530916942463717 949108912599546926711947)
                      ·
                        rfl

theorem cell23_1848383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 2, 1, 5, 4].length) (baseStart_1848383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1848383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1848383 prefixEnd_1848383 := by exact prefixLift 1848383
  have htrace : WordTrace (prefixWord ++ tailWord_1848383) baseStart_1848383 baseEnd_1848383 := by
    simpa [prefixWord, tailWord_1848383, baseEnd_1848383] using wordTrace_append hprefix tailTrace_1848383
  have hstable : (prefixWord ++ tailWord_1848383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1848383).length < 2 ^ (prefixWord ++ tailWord_1848383).sum := by decide
  have hdescent : baseEnd_1848383 < baseStart_1848383 := by decide
  rcases family_descends (prefixWord ++ tailWord_1848383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1848387 : List Nat := [1, 1, 1, 3, 1, 2, 3, 5, 1, 3, 2]
def baseStart_1848387 : Nat := 118140960795 + 1848387 * 2 ^ 59
def prefixEnd_1848387 : Nat := 4983230072969 + 3 ^ 40 * 1848387 * 2
def baseEnd_1848387 : Nat := 949110966522164911061929

theorem tailTrace_1848387 : CollatzResearch.WordTrace tailWord_1848387 prefixEnd_1848387 949110966522164911061929 := by
  unfold tailWord_1848387
  simp only [CollatzResearch.WordTrace]
  refine ⟨67416212354617053212191415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44944141569744702141460943 67416212354617053212191415)
  ·
    refine ⟨101124318531925579818287123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67416212354617053212191415 101124318531925579818287123)
    ·
      refine ⟨151686477797888369727430685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101124318531925579818287123 151686477797888369727430685)
      ·
        refine ⟨56882429174208138647786507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151686477797888369727430685 56882429174208138647786507)
        ·
          refine ⟨85323643761312207971679761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56882429174208138647786507 85323643761312207971679761)
          ·
            refine ⟨63992732820984155978759821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85323643761312207971679761 63992732820984155978759821)
            ·
              refine ⟨23997274807869058492034933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63992732820984155978759821 23997274807869058492034933)
              ·
                refine ⟨2249744513237724233628275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23997274807869058492034933 2249744513237724233628275)
                ·
                  refine ⟨3374616769856586350442413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2249744513237724233628275 3374616769856586350442413)
                  ·
                    refine ⟨1265481288696219881415905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3374616769856586350442413 1265481288696219881415905)
                    ·
                      refine ⟨949110966522164911061929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1265481288696219881415905 949110966522164911061929)
                      ·
                        rfl

theorem cell23_1848387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 5, 1, 3, 2].length) (baseStart_1848387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1848387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1848387 prefixEnd_1848387 := by exact prefixLift 1848387
  have htrace : WordTrace (prefixWord ++ tailWord_1848387) baseStart_1848387 baseEnd_1848387 := by
    simpa [prefixWord, tailWord_1848387, baseEnd_1848387] using wordTrace_append hprefix tailTrace_1848387
  have hstable : (prefixWord ++ tailWord_1848387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1848387).length < 2 ^ (prefixWord ++ tailWord_1848387).sum := by decide
  have hdescent : baseEnd_1848387 < baseStart_1848387 := by decide
  rcases family_descends (prefixWord ++ tailWord_1848387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1848393 : List Nat := [1, 2, 1, 1, 2, 2, 2, 4, 2, 6]
def baseStart_1848393 : Nat := 118140960795 + 1848393 * 2 ^ 59
def prefixEnd_1848393 : Nat := 4983230072969 + 3 ^ 40 * 1848393 * 2
def baseEnd_1848393 : Nat := 316371349135363962528967

theorem tailTrace_1848393 : CollatzResearch.WordTrace tailWord_1848393 prefixEnd_1848393 316371349135363962528967 := by
  unfold tailWord_1848393
  simp only [CollatzResearch.WordTrace]
  refine ⟨67416431192595316236909833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44944287461730210824606555 67416431192595316236909833)
  ·
    refine ⟨50562323394446487177682375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67416431192595316236909833 50562323394446487177682375)
    ·
      refine ⟨75843485091669730766523563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50562323394446487177682375 75843485091669730766523563)
      ·
        refine ⟨113765227637504596149785345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75843485091669730766523563 113765227637504596149785345)
        ·
          refine ⟨85323920728128447112339009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113765227637504596149785345 85323920728128447112339009)
          ·
            refine ⟨63992940546096335334254257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85323920728128447112339009 63992940546096335334254257)
            ·
              refine ⟨47994705409572251500690693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63992940546096335334254257 47994705409572251500690693)
              ·
                refine ⟨8999007264294797156379505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47994705409572251500690693 8999007264294797156379505)
                ·
                  refine ⟨6749255448221097867284629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8999007264294797156379505 6749255448221097867284629)
                  ·
                    refine ⟨316371349135363962528967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6749255448221097867284629 316371349135363962528967)
                    ·
                      rfl

theorem cell23_1848393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 4, 2, 6].length) (baseStart_1848393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1848393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1848393 prefixEnd_1848393 := by exact prefixLift 1848393
  have htrace : WordTrace (prefixWord ++ tailWord_1848393) baseStart_1848393 baseEnd_1848393 := by
    simpa [prefixWord, tailWord_1848393, baseEnd_1848393] using wordTrace_append hprefix tailTrace_1848393
  have hstable : (prefixWord ++ tailWord_1848393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1848393).length < 2 ^ (prefixWord ++ tailWord_1848393).sum := by decide
  have hdescent : baseEnd_1848393 < baseStart_1848393 := by decide
  rcases family_descends (prefixWord ++ tailWord_1848393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1848403 : List Nat := [1, 1, 1, 2, 1, 1, 2, 4, 4, 1, 5]
def baseStart_1848403 : Nat := 118140960795 + 1848403 * 2 ^ 59
def prefixEnd_1848403 : Nat := 4983230072969 + 3 ^ 40 * 1848403 * 2
def baseEnd_1848403 : Nat := 949119182212636848461855

theorem tailTrace_1848403 : CollatzResearch.WordTrace tailWord_1848403 prefixEnd_1848403 949119182212636848461855 := by
  unfold tailWord_1848403
  simp only [CollatzResearch.WordTrace]
  refine ⟨67416795922559087944773863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44944530615039391963182575 67416795922559087944773863)
  ·
    refine ⟨101125193883838631917160795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67416795922559087944773863 101125193883838631917160795)
    ·
      refine ⟨151687790825757947875741193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101125193883838631917160795 151687790825757947875741193)
      ·
        refine ⟨113765843119318460906805895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151687790825757947875741193 113765843119318460906805895)
        ·
          refine ⟨170648764678977691360208843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113765843119318460906805895 170648764678977691360208843)
          ·
            refine ⟨255973147018466537040313265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170648764678977691360208843 255973147018466537040313265)
            ·
              refine ⟨191979860263849902780234949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 255973147018466537040313265 191979860263849902780234949)
              ·
                refine ⟨35996223799471856771294053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 191979860263849902780234949 35996223799471856771294053)
                ·
                  refine ⟨6749291962400973144617635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35996223799471856771294053 6749291962400973144617635)
                  ·
                    refine ⟨10123937943601459716926453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6749291962400973144617635 10123937943601459716926453)
                    ·
                      refine ⟨949119182212636848461855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10123937943601459716926453 949119182212636848461855)
                      ·
                        rfl

theorem cell23_1848403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 4, 4, 1, 5].length) (baseStart_1848403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1848403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1848403 prefixEnd_1848403 := by exact prefixLift 1848403
  have htrace : WordTrace (prefixWord ++ tailWord_1848403) baseStart_1848403 baseEnd_1848403 := by
    simpa [prefixWord, tailWord_1848403, baseEnd_1848403] using wordTrace_append hprefix tailTrace_1848403
  have hstable : (prefixWord ++ tailWord_1848403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1848403).length < 2 ^ (prefixWord ++ tailWord_1848403).sum := by decide
  have hdescent : baseEnd_1848403 < baseStart_1848403 := by decide
  rcases family_descends (prefixWord ++ tailWord_1848403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1848433 : List Nat := [1, 2, 2, 2, 1, 1, 2, 2, 1, 2, 7]
def baseStart_1848433 : Nat := 118140960795 + 1848433 * 2 ^ 59
def prefixEnd_1848433 : Nat := 4983230072969 + 3 ^ 40 * 1848433 * 2
def baseEnd_1848433 : Nat := 949134586632271731086717

theorem tailTrace_1848433 : CollatzResearch.WordTrace tailWord_1848433 prefixEnd_1848433 949134586632271731086717 := by
  unfold tailWord_1848433
  simp only [CollatzResearch.WordTrace]
  refine ⟨67417890112450403068365953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44945260074966935378910635 67417890112450403068365953)
  ·
    refine ⟨50563417584337802301274465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67417890112450403068365953 50563417584337802301274465)
    ·
      refine ⟨37922563188253351725955849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50563417584337802301274465 37922563188253351725955849)
      ·
        refine ⟨28441922391190013794466887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37922563188253351725955849 28441922391190013794466887)
        ·
          refine ⟨42662883586785020691700331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28441922391190013794466887 42662883586785020691700331)
          ·
            refine ⟨63994325380177531037550497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42662883586785020691700331 63994325380177531037550497)
            ·
              refine ⟨47995744035133148278162873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63994325380177531037550497 47995744035133148278162873)
              ·
                refine ⟨35996808026349861208622155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47995744035133148278162873 35996808026349861208622155)
                ·
                  refine ⟨53995212039524791812933233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35996808026349861208622155 53995212039524791812933233)
                  ·
                    refine ⟨40496409029643593859699925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 53995212039524791812933233 40496409029643593859699925)
                    ·
                      refine ⟨949134586632271731086717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 40496409029643593859699925 949134586632271731086717)
                      ·
                        rfl

theorem cell23_1848433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 2, 1, 2, 7].length) (baseStart_1848433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1848433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1848433 prefixEnd_1848433 := by exact prefixLift 1848433
  have htrace : WordTrace (prefixWord ++ tailWord_1848433) baseStart_1848433 baseEnd_1848433 := by
    simpa [prefixWord, tailWord_1848433, baseEnd_1848433] using wordTrace_append hprefix tailTrace_1848433
  have hstable : (prefixWord ++ tailWord_1848433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1848433).length < 2 ^ (prefixWord ++ tailWord_1848433).sum := by decide
  have hdescent : baseEnd_1848433 < baseStart_1848433 := by decide
  rcases family_descends (prefixWord ++ tailWord_1848433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1848446 : List Nat := [4, 2, 4, 1, 2, 1, 2, 2, 1, 2, 2]
def baseStart_1848446 : Nat := 118140960795 + 1848446 * 2 ^ 59
def prefixEnd_1848446 : Nat := 4983230072969 + 3 ^ 40 * 1848446 * 2
def baseEnd_1848446 : Nat := 949141261880780180224159

theorem tailTrace_1848446 : CollatzResearch.WordTrace tailWord_1848446 prefixEnd_1848446 949141261880780180224159 := by
  unfold tailWord_1848446
  simp only [CollatzResearch.WordTrace]
  refine ⟨8427295532675413286073649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44945576174268870859059461 8427295532675413286073649)
  ·
    refine ⟨6320471649506559964555237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8427295532675413286073649 6320471649506559964555237)
    ·
      refine ⟨1185088434282479993354107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6320471649506559964555237 1185088434282479993354107)
      ·
        refine ⟨1777632651423719990031161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1185088434282479993354107 1777632651423719990031161)
        ·
          refine ⟨1333224488567789992523371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1777632651423719990031161 1333224488567789992523371)
          ·
            refine ⟨1999836732851684988785057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1333224488567789992523371 1999836732851684988785057)
            ·
              refine ⟨1499877549638763741588793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1999836732851684988785057 1499877549638763741588793)
              ·
                refine ⟨1124908162229072806191595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1499877549638763741588793 1124908162229072806191595)
                ·
                  refine ⟨1687362243343609209287393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1124908162229072806191595 1687362243343609209287393)
                  ·
                    refine ⟨1265521682507706906965545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1687362243343609209287393 1265521682507706906965545)
                    ·
                      refine ⟨949141261880780180224159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1265521682507706906965545 949141261880780180224159)
                      ·
                        rfl

theorem cell23_1848446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 2, 2, 1, 2, 2].length) (baseStart_1848446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1848446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1848446 prefixEnd_1848446 := by exact prefixLift 1848446
  have htrace : WordTrace (prefixWord ++ tailWord_1848446) baseStart_1848446 baseEnd_1848446 := by
    simpa [prefixWord, tailWord_1848446, baseEnd_1848446] using wordTrace_append hprefix tailTrace_1848446
  have hstable : (prefixWord ++ tailWord_1848446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1848446).length < 2 ^ (prefixWord ++ tailWord_1848446).sum := by decide
  have hdescent : baseEnd_1848446 < baseStart_1848446 := by decide
  rcases family_descends (prefixWord ++ tailWord_1848446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1848457 : List Nat := [1, 2, 1, 1, 4, 4, 1, 4, 5]
def baseStart_1848457 : Nat := 118140960795 + 1848457 * 2 ^ 59
def prefixEnd_1848457 : Nat := 4983230072969 + 3 ^ 40 * 1848457 * 2
def baseEnd_1848457 : Nat := 105460767796442181909623

theorem tailTrace_1848457 : CollatzResearch.WordTrace tailWord_1848457 prefixEnd_1848457 105460767796442181909623 := by
  unfold tailWord_1848457
  simp only [CollatzResearch.WordTrace]
  refine ⟨67418765464363455167239625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44945843642908970111493083 67418765464363455167239625)
  ·
    refine ⟨50564074098272591375429719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67418765464363455167239625 50564074098272591375429719)
    ·
      refine ⟨75846111147408887063144579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50564074098272591375429719 75846111147408887063144579)
      ·
        refine ⟨113769166721113330594716869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75846111147408887063144579 113769166721113330594716869)
        ·
          refine ⟨21331718760208749486509413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 113769166721113330594716869 21331718760208749486509413)
          ·
            refine ⟨3999697267539140528720515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21331718760208749486509413 3999697267539140528720515)
            ·
              refine ⟨5999545901308710793080773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3999697267539140528720515 5999545901308710793080773)
              ·
                refine ⟨1124914856495383273702645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5999545901308710793080773 1124914856495383273702645)
                ·
                  refine ⟨105460767796442181909623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1124914856495383273702645 105460767796442181909623)
                  ·
                    rfl

theorem cell23_1848457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 4, 5].length) (baseStart_1848457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1848457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1848457 prefixEnd_1848457 := by exact prefixLift 1848457
  have htrace : WordTrace (prefixWord ++ tailWord_1848457) baseStart_1848457 baseEnd_1848457 := by
    simpa [prefixWord, tailWord_1848457, baseEnd_1848457] using wordTrace_append hprefix tailTrace_1848457
  have hstable : (prefixWord ++ tailWord_1848457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1848457).length < 2 ^ (prefixWord ++ tailWord_1848457).sum := by decide
  have hdescent : baseEnd_1848457 < baseStart_1848457 := by decide
  rcases family_descends (prefixWord ++ tailWord_1848457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1848463 : List Nat := [1, 1, 2, 1, 1, 1, 1, 2, 5, 1, 7]
def baseStart_1848463 : Nat := 118140960795 + 1848463 * 2 ^ 59
def prefixEnd_1848463 : Nat := 4983230072969 + 3 ^ 40 * 1848463 * 2
def baseEnd_1848463 : Nat := 949149991051906613711579

theorem tailTrace_1848463 : CollatzResearch.WordTrace tailWord_1848463 prefixEnd_1848463 949149991051906613711579 := by
  unfold tailWord_1848463
  simp only [CollatzResearch.WordTrace]
  refine ⟨67418984302341718191958043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44945989534894478794638695 67418984302341718191958043)
  ·
    refine ⟨101128476453512577287937065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67418984302341718191958043 101128476453512577287937065)
    ·
      refine ⟨75846357340134432965952799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101128476453512577287937065 75846357340134432965952799)
      ·
        refine ⟨113769536010201649448929199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75846357340134432965952799 113769536010201649448929199)
        ·
          refine ⟨170654304015302474173393799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113769536010201649448929199 170654304015302474173393799)
          ·
            refine ⟨255981456022953711260090699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170654304015302474173393799 255981456022953711260090699)
            ·
              refine ⟨383972184034430566890136049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 255981456022953711260090699 383972184034430566890136049)
              ·
                refine ⟨287979138025822925167602037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 383972184034430566890136049 287979138025822925167602037)
                ·
                  refine ⟨26998044189920899234462691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 287979138025822925167602037 26998044189920899234462691)
                  ·
                    refine ⟨40497066284881348851694037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26998044189920899234462691 40497066284881348851694037)
                    ·
                      refine ⟨949149991051906613711579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 40497066284881348851694037 949149991051906613711579)
                      ·
                        rfl

theorem cell23_1848463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 5, 1, 7].length) (baseStart_1848463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1848463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1848463 prefixEnd_1848463 := by exact prefixLift 1848463
  have htrace : WordTrace (prefixWord ++ tailWord_1848463) baseStart_1848463 baseEnd_1848463 := by
    simpa [prefixWord, tailWord_1848463, baseEnd_1848463] using wordTrace_append hprefix tailTrace_1848463
  have hstable : (prefixWord ++ tailWord_1848463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1848463).length < 2 ^ (prefixWord ++ tailWord_1848463).sum := by decide
  have hdescent : baseEnd_1848463 < baseStart_1848463 := by decide
  rcases family_descends (prefixWord ++ tailWord_1848463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1848477 : List Nat := [1, 4, 2, 1, 1, 2, 1, 2, 2, 5, 2]
def baseStart_1848477 : Nat := 118140960795 + 1848477 * 2 ^ 59
def prefixEnd_1848477 : Nat := 4983230072969 + 3 ^ 40 * 1848477 * 2
def baseEnd_1848477 : Nat := 949157179781069558936515

theorem tailTrace_1848477 : CollatzResearch.WordTrace tailWord_1848477 prefixEnd_1848477 949157179781069558936515 := by
  unfold tailWord_1848477
  simp only [CollatzResearch.WordTrace]
  refine ⟨67419494924290998582967685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44946329949527332388645123 67419494924290998582967685)
  ·
    refine ⟨12641155298304562234306441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67419494924290998582967685 12641155298304562234306441)
    ·
      refine ⟨9480866473728421675729831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12641155298304562234306441 9480866473728421675729831)
      ·
        refine ⟨14221299710592632513594747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9480866473728421675729831 14221299710592632513594747)
        ·
          refine ⟨21331949565888948770392121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14221299710592632513594747 21331949565888948770392121)
          ·
            refine ⟨15998962174416711577794091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21331949565888948770392121 15998962174416711577794091)
            ·
              refine ⟨23998443261625067366691137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15998962174416711577794091 23998443261625067366691137)
              ·
                refine ⟨17998832446218800525018353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23998443261625067366691137 17998832446218800525018353)
                ·
                  refine ⟨13499124334664100393763765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17998832446218800525018353 13499124334664100393763765)
                  ·
                    refine ⟨1265542906374759411915353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13499124334664100393763765 1265542906374759411915353)
                    ·
                      refine ⟨949157179781069558936515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1265542906374759411915353 949157179781069558936515)
                      ·
                        rfl

theorem cell23_1848477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 2, 2, 5, 2].length) (baseStart_1848477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1848477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1848477 prefixEnd_1848477 := by exact prefixLift 1848477
  have htrace : WordTrace (prefixWord ++ tailWord_1848477) baseStart_1848477 baseEnd_1848477 := by
    simpa [prefixWord, tailWord_1848477, baseEnd_1848477] using wordTrace_append hprefix tailTrace_1848477
  have hstable : (prefixWord ++ tailWord_1848477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1848477).length < 2 ^ (prefixWord ++ tailWord_1848477).sum := by decide
  have hdescent : baseEnd_1848477 < baseStart_1848477 := by decide
  rcases family_descends (prefixWord ++ tailWord_1848477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1848487 : List Nat := [1, 1, 6, 2, 1, 2, 1, 1, 1, 7]
def baseStart_1848487 : Nat := 118140960795 + 1848487 * 2 ^ 59
def prefixEnd_1848487 : Nat := 4983230072969 + 3 ^ 40 * 1848487 * 2
def baseEnd_1848487 : Nat := 316387438195871506603823

theorem tailTrace_1848487 : CollatzResearch.WordTrace tailWord_1848487 prefixEnd_1848487 316387438195871506603823 := by
  unfold tailWord_1848487
  simp only [CollatzResearch.WordTrace]
  refine ⟨67419859654254770290831715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44946573102836513527221143 67419859654254770290831715)
  ·
    refine ⟨101129789481382155436247573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67419859654254770290831715 101129789481382155436247573)
    ·
      refine ⟨4740458881939788536074105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 101129789481382155436247573 4740458881939788536074105)
      ·
        refine ⟨3555344161454841402055579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4740458881939788536074105 3555344161454841402055579)
        ·
          refine ⟨5333016242182262103083369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3555344161454841402055579 5333016242182262103083369)
          ·
            refine ⟨3999762181636696577312527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5333016242182262103083369 3999762181636696577312527)
            ·
              refine ⟨5999643272455044865968791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3999762181636696577312527 5999643272455044865968791)
              ·
                refine ⟨8999464908682567298953187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5999643272455044865968791 8999464908682567298953187)
                ·
                  refine ⟨13499197363023850948429781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8999464908682567298953187 13499197363023850948429781)
                  ·
                    refine ⟨316387438195871506603823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13499197363023850948429781 316387438195871506603823)
                    ·
                      rfl

theorem cell23_1848487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 1, 1, 7].length) (baseStart_1848487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1848487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1848487 prefixEnd_1848487 := by exact prefixLift 1848487
  have htrace : WordTrace (prefixWord ++ tailWord_1848487) baseStart_1848487 baseEnd_1848487 := by
    simpa [prefixWord, tailWord_1848487, baseEnd_1848487] using wordTrace_append hprefix tailTrace_1848487
  have hstable : (prefixWord ++ tailWord_1848487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1848487).length < 2 ^ (prefixWord ++ tailWord_1848487).sum := by decide
  have hdescent : baseEnd_1848487 < baseStart_1848487 := by decide
  rcases family_descends (prefixWord ++ tailWord_1848487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1848502 : List Nat := [5, 1, 3, 2, 1, 2, 1, 2, 2, 2, 2]
def baseStart_1848502 : Nat := 118140960795 + 1848502 * 2 ^ 59
def prefixEnd_1848502 : Nat := 4983230072969 + 3 ^ 40 * 1848502 * 2
def baseEnd_1848502 : Nat := 949170016797431961123901

theorem tailTrace_1848502 : CollatzResearch.WordTrace tailWord_1848502 prefixEnd_1848502 949170016797431961123901 := by
  unfold tailWord_1848502
  simp only [CollatzResearch.WordTrace]
  refine ⟨4213775421825026740789235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 44946937832800285235085173 4213775421825026740789235)
  ·
    refine ⟨6320663132737540111183853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4213775421825026740789235 6320663132737540111183853)
    ·
      refine ⟨2370248674776577541693945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6320663132737540111183853 2370248674776577541693945)
      ·
        refine ⟨1777686506082433156270459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2370248674776577541693945 1777686506082433156270459)
        ·
          refine ⟨2666529759123649734405689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1777686506082433156270459 2666529759123649734405689)
          ·
            refine ⟨1999897319342737300804267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2666529759123649734405689 1999897319342737300804267)
            ·
              refine ⟨2999845979014105951206401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1999897319342737300804267 2999845979014105951206401)
              ·
                refine ⟨2249884484260579463404801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2999845979014105951206401 2249884484260579463404801)
                ·
                  refine ⟨1687413363195434597553601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2249884484260579463404801 1687413363195434597553601)
                  ·
                    refine ⟨1265560022396575948165201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1687413363195434597553601 1265560022396575948165201)
                    ·
                      refine ⟨949170016797431961123901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1265560022396575948165201 949170016797431961123901)
                      ·
                        rfl

theorem cell23_1848502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 1, 2, 2, 2, 2].length) (baseStart_1848502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1848502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1848502 prefixEnd_1848502 := by exact prefixLift 1848502
  have htrace : WordTrace (prefixWord ++ tailWord_1848502) baseStart_1848502 baseEnd_1848502 := by
    simpa [prefixWord, tailWord_1848502, baseEnd_1848502] using wordTrace_append hprefix tailTrace_1848502
  have hstable : (prefixWord ++ tailWord_1848502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1848502).length < 2 ^ (prefixWord ++ tailWord_1848502).sum := by decide
  have hdescent : baseEnd_1848502 < baseStart_1848502 := by decide
  rcases family_descends (prefixWord ++ tailWord_1848502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1848560 : List Nat := [2, 1, 1, 1, 3, 1, 1, 1, 7, 5]
def baseStart_1848560 : Nat := 118140960795 + 1848560 * 2 ^ 59
def prefixEnd_1848560 : Nat := 4983230072969 + 3 ^ 40 * 1848560 * 2
def baseEnd_1848560 : Nat := 316399932891797578066211

theorem tailTrace_1848560 : CollatzResearch.WordTrace tailWord_1848560 prefixEnd_1848560 316399932891797578066211 := by
  unfold tailWord_1848560
  simp only [CollatzResearch.WordTrace]
  refine ⟨33711261091495151879119567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44948348121993535838826089 33711261091495151879119567)
  ·
    refine ⟨50566891637242727818679351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33711261091495151879119567 50566891637242727818679351)
    ·
      refine ⟨75850337455864091728019027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50566891637242727818679351 75850337455864091728019027)
      ·
        refine ⟨113775506183796137592028541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75850337455864091728019027 113775506183796137592028541)
        ·
          refine ⟨42665814818923551597010703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113775506183796137592028541 42665814818923551597010703)
          ·
            refine ⟨63998722228385327395516055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42665814818923551597010703 63998722228385327395516055)
            ·
              refine ⟨95998083342577991093274083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63998722228385327395516055 95998083342577991093274083)
              ·
                refine ⟨143997125013866986639911125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95998083342577991093274083 143997125013866986639911125)
                ·
                  refine ⟨3374932617512507499372917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 143997125013866986639911125 3374932617512507499372917)
                  ·
                    refine ⟨316399932891797578066211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3374932617512507499372917 316399932891797578066211)
                    ·
                      rfl

theorem cell23_1848560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 7, 5].length) (baseStart_1848560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1848560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1848560 prefixEnd_1848560 := by exact prefixLift 1848560
  have htrace : WordTrace (prefixWord ++ tailWord_1848560) baseStart_1848560 baseEnd_1848560 := by
    simpa [prefixWord, tailWord_1848560, baseEnd_1848560] using wordTrace_append hprefix tailTrace_1848560
  have hstable : (prefixWord ++ tailWord_1848560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1848560).length < 2 ^ (prefixWord ++ tailWord_1848560).sum := by decide
  have hdescent : baseEnd_1848560 < baseStart_1848560 := by decide
  rcases family_descends (prefixWord ++ tailWord_1848560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1848624 : List Nat := [2, 1, 1, 1, 2, 2, 6, 2, 2, 4]
def baseStart_1848624 : Nat := 118140960795 + 1848624 * 2 ^ 59
def prefixEnd_1848624 : Nat := 4983230072969 + 3 ^ 40 * 1848624 * 2
def baseEnd_1848624 : Nat := 316410887145760161266113

theorem tailTrace_1848624 : CollatzResearch.WordTrace tailWord_1848624 prefixEnd_1848624 316410887145760161266113 := by
  unfold tailWord_1848624
  simp only [CollatzResearch.WordTrace]
  refine ⟨33712428227379221344284463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44949904303172295125712617 33712428227379221344284463)
  ·
    refine ⟨50568642341068832016426695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33712428227379221344284463 50568642341068832016426695)
    ·
      refine ⟨75852963511603248024640043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50568642341068832016426695 75852963511603248024640043)
      ·
        refine ⟨113779445267404872036960065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75852963511603248024640043 113779445267404872036960065)
        ·
          refine ⟨85334583950553654027720049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113779445267404872036960065 85334583950553654027720049)
          ·
            refine ⟨64000937962915240520790037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85334583950553654027720049 64000937962915240520790037)
            ·
              refine ⟨3000043967011651899412033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 64000937962915240520790037 3000043967011651899412033)
              ·
                refine ⟨2250032975258738924559025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3000043967011651899412033 2250032975258738924559025)
                ·
                  refine ⟨1687524731444054193419269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2250032975258738924559025 1687524731444054193419269)
                  ·
                    refine ⟨316410887145760161266113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1687524731444054193419269 316410887145760161266113)
                    ·
                      rfl

theorem cell23_1848624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 6, 2, 2, 4].length) (baseStart_1848624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1848624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1848624 prefixEnd_1848624 := by exact prefixLift 1848624
  have htrace : WordTrace (prefixWord ++ tailWord_1848624) baseStart_1848624 baseEnd_1848624 := by
    simpa [prefixWord, tailWord_1848624, baseEnd_1848624] using wordTrace_append hprefix tailTrace_1848624
  have hstable : (prefixWord ++ tailWord_1848624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1848624).length < 2 ^ (prefixWord ++ tailWord_1848624).sum := by decide
  have hdescent : baseEnd_1848624 < baseStart_1848624 := by decide
  rcases family_descends (prefixWord ++ tailWord_1848624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1848625 : List Nat := [1, 2, 2, 3, 3, 3, 2, 2, 1, 1, 3]
def baseStart_1848625 : Nat := 118140960795 + 1848625 * 2 ^ 59
def prefixEnd_1848625 : Nat := 4983230072969 + 3 ^ 40 * 1848625 * 2
def baseEnd_1848625 : Nat := 949233174917934979885835

theorem tailTrace_1848625 : CollatzResearch.WordTrace tailWord_1848625 prefixEnd_1848625 949233174917934979885835 := by
  unfold tailWord_1848625
  simp only [CollatzResearch.WordTrace]
  refine ⟨67424892927754819859355329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44949928618503213239570219 67424892927754819859355329)
  ·
    refine ⟨50568669695816114894516497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67424892927754819859355329 50568669695816114894516497)
    ·
      refine ⟨37926502271862086170887373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50568669695816114894516497 37926502271862086170887373)
      ·
        refine ⟨14222438351948282314082765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37926502271862086170887373 14222438351948282314082765)
        ·
          refine ⟨5333414381980605867781037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14222438351948282314082765 5333414381980605867781037)
          ·
            refine ⟨2000030393242727200417889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5333414381980605867781037 2000030393242727200417889)
            ·
              refine ⟨1500022794932045400313417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2000030393242727200417889 1500022794932045400313417)
              ·
                refine ⟨1125017096199034050235063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1500022794932045400313417 1125017096199034050235063)
                ·
                  refine ⟨1687525644298551075352595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1125017096199034050235063 1687525644298551075352595)
                  ·
                    refine ⟨2531288466447826613028893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1687525644298551075352595 2531288466447826613028893)
                    ·
                      refine ⟨949233174917934979885835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2531288466447826613028893 949233174917934979885835)
                      ·
                        rfl

theorem cell23_1848625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 2, 2, 1, 1, 3].length) (baseStart_1848625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1848625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1848625 prefixEnd_1848625 := by exact prefixLift 1848625
  have htrace : WordTrace (prefixWord ++ tailWord_1848625) baseStart_1848625 baseEnd_1848625 := by
    simpa [prefixWord, tailWord_1848625, baseEnd_1848625] using wordTrace_append hprefix tailTrace_1848625
  have hstable : (prefixWord ++ tailWord_1848625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1848625).length < 2 ^ (prefixWord ++ tailWord_1848625).sum := by decide
  have hdescent : baseEnd_1848625 < baseStart_1848625 := by decide
  rcases family_descends (prefixWord ++ tailWord_1848625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1848641 : List Nat := [1, 2, 5, 2, 1, 1, 2, 3, 2, 4]
def baseStart_1848641 : Nat := 118140960795 + 1848641 * 2 ^ 59
def prefixEnd_1848641 : Nat := 4983230072969 + 3 ^ 40 * 1848641 * 2
def baseEnd_1848641 : Nat := 316413796869468972428587

theorem tailTrace_1848641 : CollatzResearch.WordTrace tailWord_1848641 prefixEnd_1848641 316413796869468972428587 := by
  unfold tailWord_1848641
  simp only [CollatzResearch.WordTrace]
  refine ⟨67425476495696854591937777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44950317663797903061291851 67425476495696854591937777)
  ·
    refine ⟨50569107371772640943953333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67425476495696854591937777 50569107371772640943953333)
    ·
      refine ⟨4740853816103685088495625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 50569107371772640943953333 4740853816103685088495625)
      ·
        refine ⟨3555640362077763816371719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4740853816103685088495625 3555640362077763816371719)
        ·
          refine ⟨5333460543116645724557579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3555640362077763816371719 5333460543116645724557579)
          ·
            refine ⟨8000190814674968586836369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5333460543116645724557579 8000190814674968586836369)
            ·
              refine ⟨6000143111006226440127277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8000190814674968586836369 6000143111006226440127277)
              ·
                refine ⟨2250053666627334915047729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6000143111006226440127277 2250053666627334915047729)
                ·
                  refine ⟨1687540249970501186285797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2250053666627334915047729 1687540249970501186285797)
                  ·
                    refine ⟨316413796869468972428587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1687540249970501186285797 316413796869468972428587)
                    ·
                      rfl

theorem cell23_1848641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 3, 2, 4].length) (baseStart_1848641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1848641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1848641 prefixEnd_1848641 := by exact prefixLift 1848641
  have htrace : WordTrace (prefixWord ++ tailWord_1848641) baseStart_1848641 baseEnd_1848641 := by
    simpa [prefixWord, tailWord_1848641, baseEnd_1848641] using wordTrace_append hprefix tailTrace_1848641
  have hstable : (prefixWord ++ tailWord_1848641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1848641).length < 2 ^ (prefixWord ++ tailWord_1848641).sum := by decide
  have hdescent : baseEnd_1848641 < baseStart_1848641 := by decide
  rcases family_descends (prefixWord ++ tailWord_1848641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1848664 : List Nat := [2, 1, 2, 2, 1, 1, 4, 2, 4, 1, 3]
def baseStart_1848664 : Nat := 118140960795 + 1848664 * 2 ^ 59
def prefixEnd_1848664 : Nat := 4983230072969 + 3 ^ 40 * 1848664 * 2
def baseEnd_1848664 : Nat := 949253200663460327298155

theorem tailTrace_1848664 : CollatzResearch.WordTrace tailWord_1848664 prefixEnd_1848664 949253200663460327298155 := by
  unfold tailWord_1848664
  simp only [CollatzResearch.WordTrace]
  refine ⟨33713157687306764760012523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44950876916409019680016697 33713157687306764760012523)
  ·
    refine ⟨50569736530960147140018785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33713157687306764760012523 50569736530960147140018785)
    ·
      refine ⟨37927302398220110355014089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50569736530960147140018785 37927302398220110355014089)
      ·
        refine ⟨28445476798665082766260567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37927302398220110355014089 28445476798665082766260567)
        ·
          refine ⟨42668215197997624149390851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28445476798665082766260567 42668215197997624149390851)
          ·
            refine ⟨64002322796996436224086277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42668215197997624149390851 64002322796996436224086277)
            ·
              refine ⟨12000435524436831792016177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64002322796996436224086277 12000435524436831792016177)
              ·
                refine ⟨9000326643327623844012133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12000435524436831792016177 9000326643327623844012133)
                ·
                  refine ⟨1687561245623929470752275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9000326643327623844012133 1687561245623929470752275)
                  ·
                    refine ⟨2531341868435894206128413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1687561245623929470752275 2531341868435894206128413)
                    ·
                      refine ⟨949253200663460327298155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2531341868435894206128413 949253200663460327298155)
                      ·
                        rfl

theorem cell23_1848664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 2, 4, 1, 3].length) (baseStart_1848664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1848664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1848664 prefixEnd_1848664 := by exact prefixLift 1848664
  have htrace : WordTrace (prefixWord ++ tailWord_1848664) baseStart_1848664 baseEnd_1848664 := by
    simpa [prefixWord, tailWord_1848664, baseEnd_1848664] using wordTrace_append hprefix tailTrace_1848664
  have hstable : (prefixWord ++ tailWord_1848664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1848664).length < 2 ^ (prefixWord ++ tailWord_1848664).sum := by decide
  have hdescent : baseEnd_1848664 < baseStart_1848664 := by decide
  rcases family_descends (prefixWord ++ tailWord_1848664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1848697 : List Nat := [1, 2, 1, 3, 2, 1, 4, 1, 2, 6]
def baseStart_1848697 : Nat := 118140960795 + 1848697 * 2 ^ 59
def prefixEnd_1848697 : Nat := 4983230072969 + 3 ^ 40 * 1848697 * 2
def baseEnd_1848697 : Nat := 316423381841686232728501

theorem tailTrace_1848697 : CollatzResearch.WordTrace tailWord_1848697 prefixEnd_1848697 316423381841686232728501 := by
  unfold tailWord_1848697
  simp only [CollatzResearch.WordTrace]
  refine ⟨67427518983493976155976345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44951679322329317437317563 67427518983493976155976345)
  ·
    refine ⟨50570639237620482116982259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67427518983493976155976345 50570639237620482116982259)
    ·
      refine ⟨75855958856430723175473389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50570639237620482116982259 75855958856430723175473389)
      ·
        refine ⟨28445984571161521190802521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75855958856430723175473389 28445984571161521190802521)
        ·
          refine ⟨21334488428371140893101891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28445984571161521190802521 21334488428371140893101891)
          ·
            refine ⟨32001732642556711339652837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21334488428371140893101891 32001732642556711339652837)
            ·
              refine ⟨6000324870479383376184907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32001732642556711339652837 6000324870479383376184907)
              ·
                refine ⟨9000487305719075064277361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6000324870479383376184907 9000487305719075064277361)
                ·
                  refine ⟨6750365479289306298208021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9000487305719075064277361 6750365479289306298208021)
                  ·
                    refine ⟨316423381841686232728501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6750365479289306298208021 316423381841686232728501)
                    ·
                      rfl

theorem cell23_1848697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 1, 2, 6].length) (baseStart_1848697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1848697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1848697 prefixEnd_1848697 := by exact prefixLift 1848697
  have htrace : WordTrace (prefixWord ++ tailWord_1848697) baseStart_1848697 baseEnd_1848697 := by
    simpa [prefixWord, tailWord_1848697, baseEnd_1848697] using wordTrace_append hprefix tailTrace_1848697
  have hstable : (prefixWord ++ tailWord_1848697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1848697).length < 2 ^ (prefixWord ++ tailWord_1848697).sum := by decide
  have hdescent : baseEnd_1848697 < baseStart_1848697 := by decide
  rcases family_descends (prefixWord ++ tailWord_1848697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1848708 : List Nat := [2, 3, 2, 1, 1, 4, 2, 2, 1, 3, 2]
def baseStart_1848708 : Nat := 118140960795 + 1848708 * 2 ^ 59
def prefixEnd_1848708 : Nat := 4983230072969 + 3 ^ 40 * 1848708 * 2
def baseEnd_1848708 : Nat := 949275793812258155147953

theorem tailTrace_1848708 : CollatzResearch.WordTrace tailWord_1848708 prefixEnd_1848708 949275793812258155147953 := by
  unfold tailWord_1848708
  simp only [CollatzResearch.WordTrace]
  refine ⟨33713960093227062517313389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44951946790969416689751185 33713960093227062517313389)
  ·
    refine ⟨12642735034960148443992521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33713960093227062517313389 12642735034960148443992521)
    ·
      refine ⟨9482051276220111332994391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12642735034960148443992521 9482051276220111332994391)
      ·
        refine ⟨14223076914330166999491587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9482051276220111332994391 14223076914330166999491587)
        ·
          refine ⟨21334615371495250499237381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14223076914330166999491587 21334615371495250499237381)
          ·
            refine ⟨4000240382155359468607009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21334615371495250499237381 4000240382155359468607009)
            ·
              refine ⟨3000180286616519601455257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4000240382155359468607009 3000180286616519601455257)
              ·
                refine ⟨2250135214962389701091443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3000180286616519601455257 2250135214962389701091443)
                ·
                  refine ⟨3375202822443584551637165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2250135214962389701091443 3375202822443584551637165)
                  ·
                    refine ⟨1265701058416344206863937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3375202822443584551637165 1265701058416344206863937)
                    ·
                      refine ⟨949275793812258155147953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1265701058416344206863937 949275793812258155147953)
                      ·
                        rfl

theorem cell23_1848708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 2, 2, 1, 3, 2].length) (baseStart_1848708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1848708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1848708 prefixEnd_1848708 := by exact prefixLift 1848708
  have htrace : WordTrace (prefixWord ++ tailWord_1848708) baseStart_1848708 baseEnd_1848708 := by
    simpa [prefixWord, tailWord_1848708, baseEnd_1848708] using wordTrace_append hprefix tailTrace_1848708
  have hstable : (prefixWord ++ tailWord_1848708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1848708).length < 2 ^ (prefixWord ++ tailWord_1848708).sum := by decide
  have hdescent : baseEnd_1848708 < baseStart_1848708 := by decide
  rcases family_descends (prefixWord ++ tailWord_1848708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1848724 : List Nat := [2, 4, 2, 1, 2, 1, 1, 1, 1, 3, 5]
def baseStart_1848724 : Nat := 118140960795 + 1848724 * 2 ^ 59
def prefixEnd_1848724 : Nat := 4983230072969 + 3 ^ 40 * 1848724 * 2
def baseEnd_1848724 : Nat := 949284009502730092547879

theorem tailTrace_1848724 : CollatzResearch.WordTrace tailWord_1848724 prefixEnd_1848724 949284009502730092547879 := by
  unfold tailWord_1848724
  simp only [CollatzResearch.WordTrace]
  refine ⟨33714251877198079883604613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44952335836264106511472817 33714251877198079883604613)
  ·
    refine ⟨6321422226974639978175865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33714251877198079883604613 6321422226974639978175865)
    ·
      refine ⟨4741066670230979983631899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6321422226974639978175865 4741066670230979983631899)
      ·
        refine ⟨7111600005346469975447849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4741066670230979983631899 7111600005346469975447849)
        ·
          refine ⟨5333700004009852481585887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7111600005346469975447849 5333700004009852481585887)
          ·
            refine ⟨8000550006014778722378831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5333700004009852481585887 8000550006014778722378831)
            ·
              refine ⟨12000825009022168083568247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8000550006014778722378831 12000825009022168083568247)
              ·
                refine ⟨18001237513533252125352371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12000825009022168083568247 18001237513533252125352371)
                ·
                  refine ⟨27001856270299878188028557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18001237513533252125352371 27001856270299878188028557)
                  ·
                    refine ⟨10125696101362454320510709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27001856270299878188028557 10125696101362454320510709)
                    ·
                      refine ⟨949284009502730092547879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10125696101362454320510709 949284009502730092547879)
                      ·
                        rfl

theorem cell23_1848724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 1, 1, 3, 5].length) (baseStart_1848724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1848724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1848724 prefixEnd_1848724 := by exact prefixLift 1848724
  have htrace : WordTrace (prefixWord ++ tailWord_1848724) baseStart_1848724 baseEnd_1848724 := by
    simpa [prefixWord, tailWord_1848724, baseEnd_1848724] using wordTrace_append hprefix tailTrace_1848724
  have hstable : (prefixWord ++ tailWord_1848724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1848724).length < 2 ^ (prefixWord ++ tailWord_1848724).sum := by decide
  have hdescent : baseEnd_1848724 < baseStart_1848724 := by decide
  rcases family_descends (prefixWord ++ tailWord_1848724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1848738 : List Nat := [3, 3, 1, 2, 1, 2, 2, 1, 4, 2, 2]
def baseStart_1848738 : Nat := 118140960795 + 1848738 * 2 ^ 59
def prefixEnd_1848738 : Nat := 4983230072969 + 3 ^ 40 * 1848738 * 2
def baseEnd_1848738 : Nat := 949291198231893037772815

theorem tailTrace_1848738 : CollatzResearch.WordTrace tailWord_1848738 prefixEnd_1848738 949291198231893037772815 := by
  unfold tailWord_1848738
  simp only [CollatzResearch.WordTrace]
  refine ⟨16857253594086360039554717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44952676250896960105479245 16857253594086360039554717)
  ·
    refine ⟨6321470097782385014833019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16857253594086360039554717 6321470097782385014833019)
    ·
      refine ⟨9482205146673577522249529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6321470097782385014833019 9482205146673577522249529)
      ·
        refine ⟨7111653860005183141687147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9482205146673577522249529 7111653860005183141687147)
        ·
          refine ⟨10667480790007774712530721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7111653860005183141687147 10667480790007774712530721)
          ·
            refine ⟨8000610592505831034398041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10667480790007774712530721 8000610592505831034398041)
            ·
              refine ⟨6000457944379373275798531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8000610592505831034398041 6000457944379373275798531)
              ·
                refine ⟨9000686916569059913697797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6000457944379373275798531 9000686916569059913697797)
                ·
                  refine ⟨1687628796856698733818337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9000686916569059913697797 1687628796856698733818337)
                  ·
                    refine ⟨1265721597642524050363753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1687628796856698733818337 1265721597642524050363753)
                    ·
                      refine ⟨949291198231893037772815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1265721597642524050363753 949291198231893037772815)
                      ·
                        rfl

theorem cell23_1848738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 1, 4, 2, 2].length) (baseStart_1848738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1848738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1848738 prefixEnd_1848738 := by exact prefixLift 1848738
  have htrace : WordTrace (prefixWord ++ tailWord_1848738) baseStart_1848738 baseEnd_1848738 := by
    simpa [prefixWord, tailWord_1848738, baseEnd_1848738] using wordTrace_append hprefix tailTrace_1848738
  have hstable : (prefixWord ++ tailWord_1848738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1848738).length < 2 ^ (prefixWord ++ tailWord_1848738).sum := by decide
  have hdescent : baseEnd_1848738 < baseStart_1848738 := by decide
  rcases family_descends (prefixWord ++ tailWord_1848738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1848804 : List Nat := [2, 3, 1, 1, 1, 1, 1, 2, 7, 4]
def baseStart_1848804 : Nat := 118140960795 + 1848804 * 2 ^ 59
def prefixEnd_1848804 : Nat := 4983230072969 + 3 ^ 40 * 1848804 * 2
def baseEnd_1848804 : Nat := 316441695985029926515837

theorem tailTrace_1848804 : CollatzResearch.WordTrace tailWord_1848804 prefixEnd_1848804 316441695985029926515837 := by
  unfold tailWord_1848804
  simp only [CollatzResearch.WordTrace]
  refine ⟨33715710797053166715060733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44954281062737555620080977 33715710797053166715060733)
  ·
    refine ⟨12643391548894937518147775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33715710797053166715060733 12643391548894937518147775)
    ·
      refine ⟨18965087323342406277221663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12643391548894937518147775 18965087323342406277221663)
      ·
        refine ⟨28447630985013609415832495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18965087323342406277221663 28447630985013609415832495)
        ·
          refine ⟨42671446477520414123748743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28447630985013609415832495 42671446477520414123748743)
          ·
            refine ⟨64007169716280621185623115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42671446477520414123748743 64007169716280621185623115)
            ·
              refine ⟨96010754574420931778434673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64007169716280621185623115 96010754574420931778434673)
              ·
                refine ⟨72008065930815698833826005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96010754574420931778434673 72008065930815698833826005)
                ·
                  refine ⟨1687689045253492941417797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 72008065930815698833826005 1687689045253492941417797)
                  ·
                    refine ⟨316441695985029926515837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1687689045253492941417797 316441695985029926515837)
                    ·
                      rfl

theorem cell23_1848804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 2, 7, 4].length) (baseStart_1848804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1848804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1848804 prefixEnd_1848804 := by exact prefixLift 1848804
  have htrace : WordTrace (prefixWord ++ tailWord_1848804) baseStart_1848804 baseEnd_1848804 := by
    simpa [prefixWord, tailWord_1848804, baseEnd_1848804] using wordTrace_append hprefix tailTrace_1848804
  have hstable : (prefixWord ++ tailWord_1848804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1848804).length < 2 ^ (prefixWord ++ tailWord_1848804).sum := by decide
  have hdescent : baseEnd_1848804 < baseStart_1848804 := by decide
  rcases family_descends (prefixWord ++ tailWord_1848804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1848847 : List Nat := [1, 1, 2, 1, 1, 1, 2, 2, 1, 11]
def baseStart_1848847 : Nat := 118140960795 + 1848847 * 2 ^ 59
def prefixEnd_1848847 : Nat := 4983230072969 + 3 ^ 40 * 1848847 * 2
def baseEnd_1848847 : Nat := 316449055874411037103271

theorem tailTrace_1848847 : CollatzResearch.WordTrace tailWord_1848847 prefixEnd_1848847 316449055874411037103271 := by
  unfold tailWord_1848847
  simp only [CollatzResearch.WordTrace]
  refine ⟨67432989932950551773936795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44955326621967034515957863 67432989932950551773936795)
  ·
    refine ⟨101149484899425827660905193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67432989932950551773936795 101149484899425827660905193)
    ·
      refine ⟨75862113674569370745678895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101149484899425827660905193 75862113674569370745678895)
      ·
        refine ⟨113793170511854056118518343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75862113674569370745678895 113793170511854056118518343)
        ·
          refine ⟨170689755767781084177777515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113793170511854056118518343 170689755767781084177777515)
          ·
            refine ⟨256034633651671626266666273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170689755767781084177777515 256034633651671626266666273)
            ·
              refine ⟨192025975238753719699999705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 256034633651671626266666273 192025975238753719699999705)
              ·
                refine ⟨144019481429065289774999779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 192025975238753719699999705 144019481429065289774999779)
                ·
                  refine ⟨216029222143597934662499669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 144019481429065289774999779 216029222143597934662499669)
                  ·
                    refine ⟨316449055874411037103271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 216029222143597934662499669 316449055874411037103271)
                    ·
                      rfl

theorem cell23_1848847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 11].length) (baseStart_1848847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1848847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1848847 prefixEnd_1848847 := by exact prefixLift 1848847
  have htrace : WordTrace (prefixWord ++ tailWord_1848847) baseStart_1848847 baseEnd_1848847 := by
    simpa [prefixWord, tailWord_1848847, baseEnd_1848847] using wordTrace_append hprefix tailTrace_1848847
  have hstable : (prefixWord ++ tailWord_1848847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1848847).length < 2 ^ (prefixWord ++ tailWord_1848847).sum := by decide
  have hdescent : baseEnd_1848847 < baseStart_1848847 := by decide
  rcases family_descends (prefixWord ++ tailWord_1848847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1848851 : List Nat := [1, 1, 1, 2, 1, 8, 1, 2, 6]
def baseStart_1848851 : Nat := 118140960795 + 1848851 * 2 ^ 59
def prefixEnd_1848851 : Nat := 4983230072969 + 3 ^ 40 * 1848851 * 2
def baseEnd_1848851 : Nat := 105483246838427899517755

theorem tailTrace_1848851 : CollatzResearch.WordTrace tailWord_1848851 prefixEnd_1848851 105483246838427899517755 := by
  unfold tailWord_1848851
  simp only [CollatzResearch.WordTrace]
  refine ⟨67433135824936060457082407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44955423883290706971388271 67433135824936060457082407)
  ·
    refine ⟨101149703737404090685623611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67433135824936060457082407 101149703737404090685623611)
    ·
      refine ⟨151724555606106136028435417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101149703737404090685623611 151724555606106136028435417)
      ·
        refine ⟨113793416704579602021326563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151724555606106136028435417 113793416704579602021326563)
        ·
          refine ⟨170690125056869403031989845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113793416704579602021326563 170690125056869403031989845)
          ·
            refine ⟨2000274903010188316781131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 170690125056869403031989845 2000274903010188316781131)
            ·
              refine ⟨3000412354515282475171697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2000274903010188316781131 3000412354515282475171697)
              ·
                refine ⟨2250309265886461856378773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3000412354515282475171697 2250309265886461856378773)
                ·
                  refine ⟨105483246838427899517755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2250309265886461856378773 105483246838427899517755)
                  ·
                    rfl

theorem cell23_1848851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 1, 2, 6].length) (baseStart_1848851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1848851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1848851 prefixEnd_1848851 := by exact prefixLift 1848851
  have htrace : WordTrace (prefixWord ++ tailWord_1848851) baseStart_1848851 baseEnd_1848851 := by
    simpa [prefixWord, tailWord_1848851, baseEnd_1848851] using wordTrace_append hprefix tailTrace_1848851
  have hstable : (prefixWord ++ tailWord_1848851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1848851).length < 2 ^ (prefixWord ++ tailWord_1848851).sum := by decide
  have hdescent : baseEnd_1848851 < baseStart_1848851 := by decide
  rcases family_descends (prefixWord ++ tailWord_1848851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1848895 : List Nat := [1, 1, 2, 2, 3, 3, 3, 3, 1, 1, 3]
def baseStart_1848895 : Nat := 118140960795 + 1848895 * 2 ^ 59
def prefixEnd_1848895 : Nat := 4983230072969 + 3 ^ 40 * 1848895 * 2
def baseEnd_1848895 : Nat := 949371814694648923509593

theorem tailTrace_1848895 : CollatzResearch.WordTrace tailWord_1848895 prefixEnd_1848895 949371814694648923509593 := by
  unfold tailWord_1848895
  simp only [CollatzResearch.WordTrace]
  refine ⟨67434740636776655971684139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44956493757851103981122759 67434740636776655971684139)
  ·
    refine ⟨101152110955164983957526209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67434740636776655971684139 101152110955164983957526209)
    ·
      refine ⟨75864083216373737968144657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101152110955164983957526209 75864083216373737968144657)
      ·
        refine ⟨56898062412280303476108493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75864083216373737968144657 56898062412280303476108493)
        ·
          refine ⟨21336773404605113803540685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56898062412280303476108493 21336773404605113803540685)
          ·
            refine ⟨8001290026726917676327757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21336773404605113803540685 8001290026726917676327757)
            ·
              refine ⟨3000483760022594128622909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8001290026726917676327757 3000483760022594128622909)
              ·
                refine ⟨1125181410008472798233591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3000483760022594128622909 1125181410008472798233591)
                ·
                  refine ⟨1687772115012709197350387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1125181410008472798233591 1687772115012709197350387)
                  ·
                    refine ⟨2531658172519063796025581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1687772115012709197350387 2531658172519063796025581)
                    ·
                      refine ⟨949371814694648923509593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2531658172519063796025581 949371814694648923509593)
                      ·
                        rfl

theorem cell23_1848895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 3, 3, 1, 1, 3].length) (baseStart_1848895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1848895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1848895 prefixEnd_1848895 := by exact prefixLift 1848895
  have htrace : WordTrace (prefixWord ++ tailWord_1848895) baseStart_1848895 baseEnd_1848895 := by
    simpa [prefixWord, tailWord_1848895, baseEnd_1848895] using wordTrace_append hprefix tailTrace_1848895
  have hstable : (prefixWord ++ tailWord_1848895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1848895).length < 2 ^ (prefixWord ++ tailWord_1848895).sum := by decide
  have hdescent : baseEnd_1848895 < baseStart_1848895 := by decide
  rcases family_descends (prefixWord ++ tailWord_1848895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1848901 : List Nat := [1, 3, 1, 1, 1, 4, 1, 5, 1, 1, 4]
def baseStart_1848901 : Nat := 118140960795 + 1848901 * 2 ^ 59
def prefixEnd_1848901 : Nat := 4983230072969 + 3 ^ 40 * 1848901 * 2
def baseEnd_1848901 : Nat := 949374895578575900034565

theorem tailTrace_1848901 : CollatzResearch.WordTrace tailWord_1848901 prefixEnd_1848901 949374895578575900034565 := by
  unfold tailWord_1848901
  simp only [CollatzResearch.WordTrace]
  refine ⟨67434959474754918996402557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44956639649836612664268371 67434959474754918996402557)
  ·
    refine ⟨25288109803033094623650959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67434959474754918996402557 25288109803033094623650959)
    ·
      refine ⟨37932164704549641935476439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25288109803033094623650959 37932164704549641935476439)
      ·
        refine ⟨56898247056824462903214659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37932164704549641935476439 56898247056824462903214659)
        ·
          refine ⟨85347370585236694354821989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56898247056824462903214659 85347370585236694354821989)
          ·
            refine ⟨16002631984731880191529123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85347370585236694354821989 16002631984731880191529123)
            ·
              refine ⟨24003947977097820287293685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16002631984731880191529123 24003947977097820287293685)
              ·
                refine ⟨2250370122852920651933783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24003947977097820287293685 2250370122852920651933783)
                ·
                  refine ⟨3375555184279380977900675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2250370122852920651933783 3375555184279380977900675)
                  ·
                    refine ⟨5063332776419071466851013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3375555184279380977900675 5063332776419071466851013)
                    ·
                      refine ⟨949374895578575900034565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5063332776419071466851013 949374895578575900034565)
                      ·
                        rfl

theorem cell23_1848901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 5, 1, 1, 4].length) (baseStart_1848901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1848901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1848901 prefixEnd_1848901 := by exact prefixLift 1848901
  have htrace : WordTrace (prefixWord ++ tailWord_1848901) baseStart_1848901 baseEnd_1848901 := by
    simpa [prefixWord, tailWord_1848901, baseEnd_1848901] using wordTrace_append hprefix tailTrace_1848901
  have hstable : (prefixWord ++ tailWord_1848901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1848901).length < 2 ^ (prefixWord ++ tailWord_1848901).sum := by decide
  have hdescent : baseEnd_1848901 < baseStart_1848901 := by decide
  rcases family_descends (prefixWord ++ tailWord_1848901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1848911 : List Nat := [1, 1, 2, 1, 1, 2, 3, 6, 2, 4]
def baseStart_1848911 : Nat := 118140960795 + 1848911 * 2 ^ 59
def prefixEnd_1848911 : Nat := 4983230072969 + 3 ^ 40 * 1848911 * 2
def baseEnd_1848911 : Nat := 316460010128373620303173

theorem tailTrace_1848911 : CollatzResearch.WordTrace tailWord_1848911 prefixEnd_1848911 316460010128373620303173 := by
  unfold tailWord_1848911
  simp only [CollatzResearch.WordTrace]
  refine ⟨67435324204718690704266587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44956882803145793802844391 67435324204718690704266587)
  ·
    refine ⟨101152986307078036056399881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67435324204718690704266587 101152986307078036056399881)
    ·
      refine ⟨75864739730308527042299911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101152986307078036056399881 75864739730308527042299911)
      ·
        refine ⟨113797109595462790563449867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75864739730308527042299911 113797109595462790563449867)
        ·
          refine ⟨170695664393194185845174801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113797109595462790563449867 170695664393194185845174801)
          ·
            refine ⟨128021748294895639383881101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170695664393194185845174801 128021748294895639383881101)
            ·
              refine ⟨48008155610585864768955413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 128021748294895639383881101 48008155610585864768955413)
              ·
                refine ⟨2250382294246212411044785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 48008155610585864768955413 2250382294246212411044785)
                ·
                  refine ⟨1687786720684659308283589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2250382294246212411044785 1687786720684659308283589)
                  ·
                    refine ⟨316460010128373620303173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1687786720684659308283589 316460010128373620303173)
                    ·
                      rfl

theorem cell23_1848911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 6, 2, 4].length) (baseStart_1848911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1848911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1848911 prefixEnd_1848911 := by exact prefixLift 1848911
  have htrace : WordTrace (prefixWord ++ tailWord_1848911) baseStart_1848911 baseEnd_1848911 := by
    simpa [prefixWord, tailWord_1848911, baseEnd_1848911] using wordTrace_append hprefix tailTrace_1848911
  have hstable : (prefixWord ++ tailWord_1848911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1848911).length < 2 ^ (prefixWord ++ tailWord_1848911).sum := by decide
  have hdescent : baseEnd_1848911 < baseStart_1848911 := by decide
  rcases family_descends (prefixWord ++ tailWord_1848911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1848938 : List Nat := [3, 1, 3, 2, 1, 3, 1, 1, 3, 2, 3]
def baseStart_1848938 : Nat := 118140960795 + 1848938 * 2 ^ 59
def prefixEnd_1848938 : Nat := 4983230072969 + 3 ^ 40 * 1848938 * 2
def baseEnd_1848938 : Nat := 949393894362792255271895

theorem tailTrace_1848938 : CollatzResearch.WordTrace tailWord_1848938 prefixEnd_1848938 949393894362792255271895 := by
  unfold tailWord_1848938
  simp only [CollatzResearch.WordTrace]
  refine ⟨16859077243905218578874867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44957539317080582876999645 16859077243905218578874867)
  ·
    refine ⟨25288615865857827868312301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16859077243905218578874867 25288615865857827868312301)
    ·
      refine ⟨9483230949696685450617113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25288615865857827868312301 9483230949696685450617113)
      ·
        refine ⟨7112423212272514087962835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9483230949696685450617113 7112423212272514087962835)
        ·
          refine ⟨10668634818408771131944253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7112423212272514087962835 10668634818408771131944253)
          ·
            refine ⟨4000738056903289174479095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10668634818408771131944253 4000738056903289174479095)
            ·
              refine ⟨6001107085354933761718643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4000738056903289174479095 6001107085354933761718643)
              ·
                refine ⟨9001660628032400642577965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6001107085354933761718643 9001660628032400642577965)
                ·
                  refine ⟨3375622735512150240966737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9001660628032400642577965 3375622735512150240966737)
                  ·
                    refine ⟨2531717051634112680725053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3375622735512150240966737 2531717051634112680725053)
                    ·
                      refine ⟨949393894362792255271895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2531717051634112680725053 949393894362792255271895)
                      ·
                        rfl

theorem cell23_1848938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 1, 3, 2, 3].length) (baseStart_1848938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1848938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1848938 prefixEnd_1848938 := by exact prefixLift 1848938
  have htrace : WordTrace (prefixWord ++ tailWord_1848938) baseStart_1848938 baseEnd_1848938 := by
    simpa [prefixWord, tailWord_1848938, baseEnd_1848938] using wordTrace_append hprefix tailTrace_1848938
  have hstable : (prefixWord ++ tailWord_1848938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1848938).length < 2 ^ (prefixWord ++ tailWord_1848938).sum := by decide
  have hdescent : baseEnd_1848938 < baseStart_1848938 := by decide
  rcases family_descends (prefixWord ++ tailWord_1848938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1849006 : List Nat := [4, 1, 4, 1, 3, 1, 2, 1, 1, 2, 3]
def baseStart_1849006 : Nat := 118140960795 + 1849006 * 2 ^ 59
def prefixEnd_1849006 : Nat := 4983230072969 + 3 ^ 40 * 1849006 * 2
def baseEnd_1849006 : Nat := 949428811047297989221583

theorem tailTrace_1849006 : CollatzResearch.WordTrace tailWord_1849006 prefixEnd_1849006 949428811047297989221583 := by
  unfold tailWord_1849006
  simp only [CollatzResearch.WordTrace]
  refine ⟨8429848642421815241121859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44959192759583014619316581 8429848642421815241121859)
  ·
    refine ⟨12644772963632722861682789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8429848642421815241121859 12644772963632722861682789)
    ·
      refine ⟨2370894930681135536565523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12644772963632722861682789 2370894930681135536565523)
      ·
        refine ⟨3556342396021703304848285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2370894930681135536565523 3556342396021703304848285)
        ·
          refine ⟨1333628398508138739318107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3556342396021703304848285 1333628398508138739318107)
          ·
            refine ⟨2000442597762208108977161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1333628398508138739318107 2000442597762208108977161)
            ·
              refine ⟨1500331948321656081732871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2000442597762208108977161 1500331948321656081732871)
              ·
                refine ⟨2250497922482484122599307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1500331948321656081732871 2250497922482484122599307)
                ·
                  refine ⟨3375746883723726183898961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2250497922482484122599307 3375746883723726183898961)
                  ·
                    refine ⟨2531810162792794637924221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3375746883723726183898961 2531810162792794637924221)
                    ·
                      refine ⟨949428811047297989221583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2531810162792794637924221 949428811047297989221583)
                      ·
                        rfl

theorem cell23_1849006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 2, 1, 1, 2, 3].length) (baseStart_1849006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1849006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1849006 prefixEnd_1849006 := by exact prefixLift 1849006
  have htrace : WordTrace (prefixWord ++ tailWord_1849006) baseStart_1849006 baseEnd_1849006 := by
    simpa [prefixWord, tailWord_1849006, baseEnd_1849006] using wordTrace_append hprefix tailTrace_1849006
  have hstable : (prefixWord ++ tailWord_1849006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1849006).length < 2 ^ (prefixWord ++ tailWord_1849006).sum := by decide
  have hdescent : baseEnd_1849006 < baseStart_1849006 := by decide
  rcases family_descends (prefixWord ++ tailWord_1849006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1849008 : List Nat := [2, 1, 1, 1, 2, 1, 6, 2, 1, 4, 2]
def baseStart_1849008 : Nat := 118140960795 + 1849008 * 2 ^ 59
def prefixEnd_1849008 : Nat := 4983230072969 + 3 ^ 40 * 1849008 * 2
def baseEnd_1849008 : Nat := 949429838008606981396573

theorem tailTrace_1849008 : CollatzResearch.WordTrace tailWord_1849008 prefixEnd_1849008 949429838008606981396573 := by
  unfold tailWord_1849008
  simp only [CollatzResearch.WordTrace]
  refine ⟨33719431042683638135273839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44959241390244850847031785 33719431042683638135273839)
  ·
    refine ⟨50579146564025457202910759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33719431042683638135273839 50579146564025457202910759)
    ·
      refine ⟨75868719846038185804366139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50579146564025457202910759 75868719846038185804366139)
      ·
        refine ⟨113803079769057278706549209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75868719846038185804366139 113803079769057278706549209)
        ·
          refine ⟨85352309826792959029911907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113803079769057278706549209 85352309826792959029911907)
          ·
            refine ⟨128028464740189438544867861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85352309826792959029911907 128028464740189438544867861)
            ·
              refine ⟨6001334284696379931790681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 128028464740189438544867861 6001334284696379931790681)
              ·
                refine ⟨4501000713522284948843011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6001334284696379931790681 4501000713522284948843011)
                ·
                  refine ⟨6751501070283427423264517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4501000713522284948843011 6751501070283427423264517)
                  ·
                    refine ⟨1265906450678142641862097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6751501070283427423264517 1265906450678142641862097)
                    ·
                      refine ⟨949429838008606981396573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1265906450678142641862097 949429838008606981396573)
                      ·
                        rfl

theorem cell23_1849008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 2, 1, 4, 2].length) (baseStart_1849008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1849008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1849008 prefixEnd_1849008 := by exact prefixLift 1849008
  have htrace : WordTrace (prefixWord ++ tailWord_1849008) baseStart_1849008 baseEnd_1849008 := by
    simpa [prefixWord, tailWord_1849008, baseEnd_1849008] using wordTrace_append hprefix tailTrace_1849008
  have hstable : (prefixWord ++ tailWord_1849008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1849008).length < 2 ^ (prefixWord ++ tailWord_1849008).sum := by decide
  have hdescent : baseEnd_1849008 < baseStart_1849008 := by decide
  rcases family_descends (prefixWord ++ tailWord_1849008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1849021 : List Nat := [1, 4, 1, 2, 1, 2, 1, 1, 4, 2, 4]
def baseStart_1849021 : Nat := 118140960795 + 1849021 * 2 ^ 59
def prefixEnd_1849021 : Nat := 4983230072969 + 3 ^ 40 * 1849021 * 2
def baseEnd_1849021 : Nat := 949436513257115430534013

theorem tailTrace_1849021 : CollatzResearch.WordTrace tailWord_1849021 prefixEnd_1849021 949436513257115430534013 := by
  unfold tailWord_1849021
  simp only [CollatzResearch.WordTrace]
  refine ⟨67439336234320179490770917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44959557489546786327180611 67439336234320179490770917)
  ·
    refine ⟨12644875543935033654519547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67439336234320179490770917 12644875543935033654519547)
    ·
      refine ⟨18967313315902550481779321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12644875543935033654519547 18967313315902550481779321)
      ·
        refine ⟨14225484986926912861334491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18967313315902550481779321 14225484986926912861334491)
        ·
          refine ⟨21338227480390369292001737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14225484986926912861334491 21338227480390369292001737)
          ·
            refine ⟨16003670610292776969001303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21338227480390369292001737 16003670610292776969001303)
            ·
              refine ⟨24005505915439165453501955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16003670610292776969001303 24005505915439165453501955)
              ·
                refine ⟨36008258873158748180252933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24005505915439165453501955 36008258873158748180252933)
                ·
                  refine ⟨6751548538717265283797425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36008258873158748180252933 6751548538717265283797425)
                  ·
                    refine ⟨5063661404037948962848069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6751548538717265283797425 5063661404037948962848069)
                    ·
                      refine ⟨949436513257115430534013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5063661404037948962848069 949436513257115430534013)
                      ·
                        rfl

theorem cell23_1849021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 1, 4, 2, 4].length) (baseStart_1849021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1849021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1849021 prefixEnd_1849021 := by exact prefixLift 1849021
  have htrace : WordTrace (prefixWord ++ tailWord_1849021) baseStart_1849021 baseEnd_1849021 := by
    simpa [prefixWord, tailWord_1849021, baseEnd_1849021] using wordTrace_append hprefix tailTrace_1849021
  have hstable : (prefixWord ++ tailWord_1849021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1849021).length < 2 ^ (prefixWord ++ tailWord_1849021).sum := by decide
  have hdescent : baseEnd_1849021 < baseStart_1849021 := by decide
  rcases family_descends (prefixWord ++ tailWord_1849021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1849031 : List Nat := [1, 1, 4, 1, 1, 1, 6, 1, 7]
def baseStart_1849031 : Nat := 118140960795 + 1849031 * 2 ^ 59
def prefixEnd_1849031 : Nat := 4983230072969 + 3 ^ 40 * 1849031 * 2
def baseEnd_1849031 : Nat := 105493516451517821267663

theorem tailTrace_1849031 : CollatzResearch.WordTrace tailWord_1849031 prefixEnd_1849031 105493516451517821267663 := by
  unfold tailWord_1849031
  simp only [CollatzResearch.WordTrace]
  refine ⟨67439700964283951198634947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44959800642855967465756631 67439700964283951198634947)
  ·
    refine ⟨101159551446425926797952421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67439700964283951198634947 101159551446425926797952421)
    ·
      refine ⟨18967415896204861274616079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101159551446425926797952421 18967415896204861274616079)
      ·
        refine ⟨28451123844307291911924119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18967415896204861274616079 28451123844307291911924119)
        ·
          refine ⟨42676685766460937867886179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28451123844307291911924119 42676685766460937867886179)
          ·
            refine ⟨64015028649691406801829269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42676685766460937867886179 64015028649691406801829269)
            ·
              refine ⟨3000704467954284693835747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 64015028649691406801829269 3000704467954284693835747)
              ·
                refine ⟨4501056701931427040753621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3000704467954284693835747 4501056701931427040753621)
                ·
                  refine ⟨105493516451517821267663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4501056701931427040753621 105493516451517821267663)
                  ·
                    rfl

theorem cell23_1849031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 6, 1, 7].length) (baseStart_1849031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1849031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1849031 prefixEnd_1849031 := by exact prefixLift 1849031
  have htrace : WordTrace (prefixWord ++ tailWord_1849031) baseStart_1849031 baseEnd_1849031 := by
    simpa [prefixWord, tailWord_1849031, baseEnd_1849031] using wordTrace_append hprefix tailTrace_1849031
  have hstable : (prefixWord ++ tailWord_1849031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1849031).length < 2 ^ (prefixWord ++ tailWord_1849031).sum := by decide
  have hdescent : baseEnd_1849031 < baseStart_1849031 := by decide
  rcases family_descends (prefixWord ++ tailWord_1849031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1849042 : List Nat := [3, 2, 2, 2, 2, 3, 1, 1, 1, 4, 2]
def baseStart_1849042 : Nat := 118140960795 + 1849042 * 2 ^ 59
def prefixEnd_1849042 : Nat := 4983230072969 + 3 ^ 40 * 1849042 * 2
def baseEnd_1849042 : Nat := 949447296350859848371417

theorem tailTrace_1849042 : CollatzResearch.WordTrace tailWord_1849042 prefixEnd_1849042 949447296350859848371417 := by
  unfold tailWord_1849042
  simp only [CollatzResearch.WordTrace]
  refine ⟨16860025541811025019321345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44960068111496066718190253 16860025541811025019321345)
  ·
    refine ⟨12645019156358268764491009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16860025541811025019321345 12645019156358268764491009)
    ·
      refine ⟨9483764367268701573368257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12645019156358268764491009 9483764367268701573368257)
      ·
        refine ⟨7112823275451526180026193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9483764367268701573368257 7112823275451526180026193)
        ·
          refine ⟨5334617456588644635019645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7112823275451526180026193 5334617456588644635019645)
          ·
            refine ⟨2000481546220741738132367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5334617456588644635019645 2000481546220741738132367)
            ·
              refine ⟨3000722319331112607198551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2000481546220741738132367 3000722319331112607198551)
              ·
                refine ⟨4501083478996668910797827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3000722319331112607198551 4501083478996668910797827)
                ·
                  refine ⟨6751625218495003366196741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4501083478996668910797827 6751625218495003366196741)
                  ·
                    refine ⟨1265929728467813131161889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6751625218495003366196741 1265929728467813131161889)
                    ·
                      refine ⟨949447296350859848371417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1265929728467813131161889 949447296350859848371417)
                      ·
                        rfl

theorem cell23_1849042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 1, 1, 1, 4, 2].length) (baseStart_1849042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1849042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1849042 prefixEnd_1849042 := by exact prefixLift 1849042
  have htrace : WordTrace (prefixWord ++ tailWord_1849042) baseStart_1849042 baseEnd_1849042 := by
    simpa [prefixWord, tailWord_1849042, baseEnd_1849042] using wordTrace_append hprefix tailTrace_1849042
  have hstable : (prefixWord ++ tailWord_1849042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1849042).length < 2 ^ (prefixWord ++ tailWord_1849042).sum := by decide
  have hdescent : baseEnd_1849042 < baseStart_1849042 := by decide
  rcases family_descends (prefixWord ++ tailWord_1849042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1849046 : List Nat := [5, 2, 1, 3, 1, 1, 2, 2, 1, 3, 2]
def baseStart_1849046 : Nat := 118140960795 + 1849046 * 2 ^ 59
def prefixEnd_1849046 : Nat := 4983230072969 + 3 ^ 40 * 1849046 * 2
def baseEnd_1849046 : Nat := 949449350273477832721399

theorem tailTrace_1849046 : CollatzResearch.WordTrace tailWord_1849046 prefixEnd_1849046 949449350273477832721399 := by
  unfold tailWord_1849046
  simp only [CollatzResearch.WordTrace]
  refine ⟨4215015503701850547526937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 44960165372819739173620661 4215015503701850547526937)
  ·
    refine ⟨3161261627776387910645203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4215015503701850547526937 3161261627776387910645203)
    ·
      refine ⟨4741892441664581865967805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3161261627776387910645203 4741892441664581865967805)
      ·
        refine ⟨1778209665624218199737927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4741892441664581865967805 1778209665624218199737927)
        ·
          refine ⟨2667314498436327299606891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1778209665624218199737927 2667314498436327299606891)
          ·
            refine ⟨4000971747654490949410337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2667314498436327299606891 4000971747654490949410337)
            ·
              refine ⟨3000728810740868212057753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4000971747654490949410337 3000728810740868212057753)
              ·
                refine ⟨2250546608055651159043315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3000728810740868212057753 2250546608055651159043315)
                ·
                  refine ⟨3375819912083476738564973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2250546608055651159043315 3375819912083476738564973)
                  ·
                    refine ⟨1265932467031303776961865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3375819912083476738564973 1265932467031303776961865)
                    ·
                      refine ⟨949449350273477832721399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1265932467031303776961865 949449350273477832721399)
                      ·
                        rfl

theorem cell23_1849046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 2, 2, 1, 3, 2].length) (baseStart_1849046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1849046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1849046 prefixEnd_1849046 := by exact prefixLift 1849046
  have htrace : WordTrace (prefixWord ++ tailWord_1849046) baseStart_1849046 baseEnd_1849046 := by
    simpa [prefixWord, tailWord_1849046, baseEnd_1849046] using wordTrace_append hprefix tailTrace_1849046
  have hstable : (prefixWord ++ tailWord_1849046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1849046).length < 2 ^ (prefixWord ++ tailWord_1849046).sum := by decide
  have hdescent : baseEnd_1849046 < baseStart_1849046 := by decide
  rcases family_descends (prefixWord ++ tailWord_1849046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1849061 : List Nat := [1, 3, 1, 4, 1, 1, 1, 3, 1, 7]
def baseStart_1849061 : Nat := 118140960795 + 1849061 * 2 ^ 59
def prefixEnd_1849061 : Nat := 4983230072969 + 3 ^ 40 * 1849061 * 2
def baseEnd_1849061 : Nat := 316485684161098424677943

theorem tailTrace_1849061 : CollatzResearch.WordTrace tailWord_1849061 prefixEnd_1849061 316485684161098424677943 := by
  unfold tailWord_1849061
  simp only [CollatzResearch.WordTrace]
  refine ⟨67440795154175266322227037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44960530102783510881484691 67440795154175266322227037)
  ·
    refine ⟨25290298182815724870835139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67440795154175266322227037 25290298182815724870835139)
    ·
      refine ⟨37935447274223587306252709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25290298182815724870835139 37935447274223587306252709)
      ·
        refine ⟨7112896363916922619922383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37935447274223587306252709 7112896363916922619922383)
        ·
          refine ⟨10669344545875383929883575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7112896363916922619922383 10669344545875383929883575)
          ·
            refine ⟨16004016818813075894825363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10669344545875383929883575 16004016818813075894825363)
            ·
              refine ⟨24006025228219613842238045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16004016818813075894825363 24006025228219613842238045)
              ·
                refine ⟨9002259460582355190839267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24006025228219613842238045 9002259460582355190839267)
                ·
                  refine ⟨13503389190873532786258901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9002259460582355190839267 13503389190873532786258901)
                  ·
                    refine ⟨316485684161098424677943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13503389190873532786258901 316485684161098424677943)
                    ·
                      rfl

theorem cell23_1849061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 3, 1, 7].length) (baseStart_1849061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1849061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1849061 prefixEnd_1849061 := by exact prefixLift 1849061
  have htrace : WordTrace (prefixWord ++ tailWord_1849061) baseStart_1849061 baseEnd_1849061 := by
    simpa [prefixWord, tailWord_1849061, baseEnd_1849061] using wordTrace_append hprefix tailTrace_1849061
  have hstable : (prefixWord ++ tailWord_1849061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1849061).length < 2 ^ (prefixWord ++ tailWord_1849061).sum := by decide
  have hdescent : baseEnd_1849061 < baseStart_1849061 := by decide
  rcases family_descends (prefixWord ++ tailWord_1849061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1849071 : List Nat := [1, 1, 2, 1, 5, 1, 2, 2, 1, 2, 5]
def baseStart_1849071 : Nat := 118140960795 + 1849071 * 2 ^ 59
def prefixEnd_1849071 : Nat := 4983230072969 + 3 ^ 40 * 1849071 * 2
def baseEnd_1849071 : Nat := 949462187289840234908783

theorem tailTrace_1849071 : CollatzResearch.WordTrace tailWord_1849071 prefixEnd_1849071 949462187289840234908783 := by
  unfold tailWord_1849071
  simp only [CollatzResearch.WordTrace]
  refine ⟨67441159884139038030091067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44960773256092692020060711 67441159884139038030091067)
  ·
    refine ⟨101161739826208557045136601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67441159884139038030091067 101161739826208557045136601)
    ·
      refine ⟨75871304869656417783852451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101161739826208557045136601 75871304869656417783852451)
      ·
        refine ⟨113806957304484626675778677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75871304869656417783852451 113806957304484626675778677)
        ·
          refine ⟨10669402247295433750854251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 113806957304484626675778677 10669402247295433750854251)
          ·
            refine ⟨16004103370943150626281377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10669402247295433750854251 16004103370943150626281377)
            ·
              refine ⟨12003077528207362969711033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16004103370943150626281377 12003077528207362969711033)
              ·
                refine ⟨9002308146155522227283275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12003077528207362969711033 9002308146155522227283275)
                ·
                  refine ⟨13503462219233283340924913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9002308146155522227283275 13503462219233283340924913)
                  ·
                    refine ⟨10127596664424962505693685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13503462219233283340924913 10127596664424962505693685)
                    ·
                      refine ⟨949462187289840234908783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10127596664424962505693685 949462187289840234908783)
                      ·
                        rfl

theorem cell23_1849071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 2, 1, 2, 5].length) (baseStart_1849071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1849071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1849071 prefixEnd_1849071 := by exact prefixLift 1849071
  have htrace : WordTrace (prefixWord ++ tailWord_1849071) baseStart_1849071 baseEnd_1849071 := by
    simpa [prefixWord, tailWord_1849071, baseEnd_1849071] using wordTrace_append hprefix tailTrace_1849071
  have hstable : (prefixWord ++ tailWord_1849071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1849071).length < 2 ^ (prefixWord ++ tailWord_1849071).sum := by decide
  have hdescent : baseEnd_1849071 < baseStart_1849071 := by decide
  rcases family_descends (prefixWord ++ tailWord_1849071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1849078 : List Nat := [5, 1, 1, 1, 1, 3, 1, 1, 4, 5]
def baseStart_1849078 : Nat := 118140960795 + 1849078 * 2 ^ 59
def prefixEnd_1849078 : Nat := 4983230072969 + 3 ^ 40 * 1849078 * 2
def baseEnd_1849078 : Nat := 316488593884807235840417

theorem tailTrace_1849078 : CollatzResearch.WordTrace tailWord_1849078 prefixEnd_1849078 316488593884807235840417 := by
  unfold tailWord_1849078
  simp only [CollatzResearch.WordTrace]
  refine ⟨4215088449694604889099743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 44960943463409118817063925 4215088449694604889099743)
  ·
    refine ⟨6322632674541907333649615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4215088449694604889099743 6322632674541907333649615)
    ·
      refine ⟨9483949011812861000474423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6322632674541907333649615 9483949011812861000474423)
      ·
        refine ⟨14225923517719291500711635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9483949011812861000474423 14225923517719291500711635)
        ·
          refine ⟨21338885276578937251067453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14225923517719291500711635 21338885276578937251067453)
          ·
            refine ⟨8002081978717101469150295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21338885276578937251067453 8002081978717101469150295)
            ·
              refine ⟨12003122968075652203725443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8002081978717101469150295 12003122968075652203725443)
              ·
                refine ⟨18004684452113478305588165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12003122968075652203725443 18004684452113478305588165)
                ·
                  refine ⟨3375878334771277182297781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18004684452113478305588165 3375878334771277182297781)
                  ·
                    refine ⟨316488593884807235840417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3375878334771277182297781 316488593884807235840417)
                    ·
                      rfl

theorem cell23_1849078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 1, 4, 5].length) (baseStart_1849078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1849078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1849078 prefixEnd_1849078 := by exact prefixLift 1849078
  have htrace : WordTrace (prefixWord ++ tailWord_1849078) baseStart_1849078 baseEnd_1849078 := by
    simpa [prefixWord, tailWord_1849078, baseEnd_1849078] using wordTrace_append hprefix tailTrace_1849078
  have hstable : (prefixWord ++ tailWord_1849078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1849078).length < 2 ^ (prefixWord ++ tailWord_1849078).sum := by decide
  have hdescent : baseEnd_1849078 < baseStart_1849078 := by decide
  rcases family_descends (prefixWord ++ tailWord_1849078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1849138 : List Nat := [3, 2, 1, 1, 3, 2, 1, 4, 6]
def baseStart_1849138 : Nat := 118140960795 + 1849138 * 2 ^ 59
def prefixEnd_1849138 : Nat := 4983230072969 + 3 ^ 40 * 1849138 * 2
def baseEnd_1849138 : Nat := 105499621165965719196775

theorem tailTrace_1849138 : CollatzResearch.WordTrace tailWord_1849138 prefixEnd_1849138 105499621165965719196775 := by
  unfold tailWord_1849138
  simp only [CollatzResearch.WordTrace]
  refine ⟨16860900893724077118195017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44962402383264205648520045 16860900893724077118195017)
  ·
    refine ⟨12645675670293057838646263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16860900893724077118195017 12645675670293057838646263)
    ·
      refine ⟨18968513505439586757969395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12645675670293057838646263 18968513505439586757969395)
      ·
        refine ⟨28452770258159380136954093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18968513505439586757969395 28452770258159380136954093)
        ·
          refine ⟨10669788846809767551357785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28452770258159380136954093 10669788846809767551357785)
          ·
            refine ⟨8002341635107325663518339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10669788846809767551357785 8002341635107325663518339)
            ·
              refine ⟨12003512452660988495277509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8002341635107325663518339 12003512452660988495277509)
              ·
                refine ⟨2250658584873935342864533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12003512452660988495277509 2250658584873935342864533)
                ·
                  refine ⟨105499621165965719196775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2250658584873935342864533 105499621165965719196775)
                  ·
                    rfl

theorem cell23_1849138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 4, 6].length) (baseStart_1849138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1849138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1849138 prefixEnd_1849138 := by exact prefixLift 1849138
  have htrace : WordTrace (prefixWord ++ tailWord_1849138) baseStart_1849138 baseEnd_1849138 := by
    simpa [prefixWord, tailWord_1849138, baseEnd_1849138] using wordTrace_append hprefix tailTrace_1849138
  have hstable : (prefixWord ++ tailWord_1849138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1849138).length < 2 ^ (prefixWord ++ tailWord_1849138).sum := by decide
  have hdescent : baseEnd_1849138 < baseStart_1849138 := by decide
  rcases family_descends (prefixWord ++ tailWord_1849138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1849161 : List Nat := [1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 7]
def baseStart_1849161 : Nat := 118140960795 + 1849161 * 2 ^ 59
def prefixEnd_1849161 : Nat := 4983230072969 + 3 ^ 40 * 1849161 * 2
def baseEnd_1849161 : Nat := 949508400548744882783369

theorem tailTrace_1849161 : CollatzResearch.WordTrace tailWord_1849161 prefixEnd_1849161 949508400548744882783369 := by
  unfold tailWord_1849161
  simp only [CollatzResearch.WordTrace]
  refine ⟨67444442453812983400867337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44962961635875322267244891 67444442453812983400867337)
  ·
    refine ⟨50583331840359737550650503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67444442453812983400867337 50583331840359737550650503)
    ·
      refine ⟨75874997760539606325975755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50583331840359737550650503 75874997760539606325975755)
      ·
        refine ⟨113812496640809409488963633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75874997760539606325975755 113812496640809409488963633)
        ·
          refine ⟨85359372480607057116722725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113812496640809409488963633 85359372480607057116722725)
          ·
            refine ⟨16004882340113823209385511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85359372480607057116722725 16004882340113823209385511)
            ·
              refine ⟨24007323510170734814078267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16004882340113823209385511 24007323510170734814078267)
              ·
                refine ⟨36010985265256102221117401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24007323510170734814078267 36010985265256102221117401)
                ·
                  refine ⟨27008238948942076665838051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36010985265256102221117401 27008238948942076665838051)
                  ·
                    refine ⟨40512358423413114998757077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27008238948942076665838051 40512358423413114998757077)
                    ·
                      refine ⟨949508400548744882783369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 40512358423413114998757077 949508400548744882783369)
                      ·
                        rfl

theorem cell23_1849161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 7].length) (baseStart_1849161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1849161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1849161 prefixEnd_1849161 := by exact prefixLift 1849161
  have htrace : WordTrace (prefixWord ++ tailWord_1849161) baseStart_1849161 baseEnd_1849161 := by
    simpa [prefixWord, tailWord_1849161, baseEnd_1849161] using wordTrace_append hprefix tailTrace_1849161
  have hstable : (prefixWord ++ tailWord_1849161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1849161).length < 2 ^ (prefixWord ++ tailWord_1849161).sum := by decide
  have hdescent : baseEnd_1849161 < baseStart_1849161 := by decide
  rcases family_descends (prefixWord ++ tailWord_1849161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1849168 : List Nat := [2, 1, 1, 1, 1, 4, 1, 6, 1, 5]
def baseStart_1849168 : Nat := 118140960795 + 1849168 * 2 ^ 59
def prefixEnd_1849168 : Nat := 4983230072969 + 3 ^ 40 * 1849168 * 2
def baseEnd_1849168 : Nat := 316503998304442118465279

theorem tailTrace_1849168 : CollatzResearch.WordTrace tailWord_1849168 prefixEnd_1849168 316503998304442118465279 := by
  unfold tailWord_1849168
  simp only [CollatzResearch.WordTrace]
  refine ⟨33722348882393811798186079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44963131843191749064248105 33722348882393811798186079)
  ·
    refine ⟨50583523323590717697279119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33722348882393811798186079 50583523323590717697279119)
    ·
      refine ⟨75875284985386076545918679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50583523323590717697279119 75875284985386076545918679)
      ·
        refine ⟨113812927478079114818878019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75875284985386076545918679 113812927478079114818878019)
        ·
          refine ⟨170719391217118672228317029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113812927478079114818878019 170719391217118672228317029)
          ·
            refine ⟨32009885853209751042809443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 170719391217118672228317029 32009885853209751042809443)
            ·
              refine ⟨48014828779814626564214165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32009885853209751042809443 48014828779814626564214165)
              ·
                refine ⟨2250695099053810620197539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 48014828779814626564214165 2250695099053810620197539)
                ·
                  refine ⟨3376042648580715930296309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2250695099053810620197539 3376042648580715930296309)
                  ·
                    refine ⟨316503998304442118465279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3376042648580715930296309 316503998304442118465279)
                    ·
                      rfl

theorem cell23_1849168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 6, 1, 5].length) (baseStart_1849168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1849168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1849168 prefixEnd_1849168 := by exact prefixLift 1849168
  have htrace : WordTrace (prefixWord ++ tailWord_1849168) baseStart_1849168 baseEnd_1849168 := by
    simpa [prefixWord, tailWord_1849168, baseEnd_1849168] using wordTrace_append hprefix tailTrace_1849168
  have hstable : (prefixWord ++ tailWord_1849168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1849168).length < 2 ^ (prefixWord ++ tailWord_1849168).sum := by decide
  have hdescent : baseEnd_1849168 < baseStart_1849168 := by decide
  rcases family_descends (prefixWord ++ tailWord_1849168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1849211 : List Nat := [1, 1, 1, 1, 1, 5, 1, 12]
def baseStart_1849211 : Nat := 118140960795 + 1849211 * 2 ^ 59
def prefixEnd_1849211 : Nat := 4983230072969 + 3 ^ 40 * 1849211 * 2
def baseEnd_1849211 : Nat := 35167928688202581005857

theorem tailTrace_1849211 : CollatzResearch.WordTrace tailWord_1849211 prefixEnd_1849211 35167928688202581005857 := by
  unfold tailWord_1849211
  simp only [CollatzResearch.WordTrace]
  refine ⟨67446266103631841940187487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44964177402421227960124991 67446266103631841940187487)
  ·
    refine ⟨101169399155447762910281231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67446266103631841940187487 101169399155447762910281231)
    ·
      refine ⟨151754098733171644365421847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101169399155447762910281231 151754098733171644365421847)
      ·
        refine ⟨227631148099757466548132771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151754098733171644365421847 227631148099757466548132771)
        ·
          refine ⟨341446722149636199822199157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227631148099757466548132771 341446722149636199822199157)
          ·
            refine ⟨32010630201528393733331171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 341446722149636199822199157 32010630201528393733331171)
            ·
              refine ⟨48015945302292590599996757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32010630201528393733331171 48015945302292590599996757)
              ·
                refine ⟨35167928688202581005857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 48015945302292590599996757 35167928688202581005857)
                ·
                  rfl

theorem cell23_1849211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 12].length) (baseStart_1849211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1849211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1849211 prefixEnd_1849211 := by exact prefixLift 1849211
  have htrace : WordTrace (prefixWord ++ tailWord_1849211) baseStart_1849211 baseEnd_1849211 := by
    simpa [prefixWord, tailWord_1849211, baseEnd_1849211] using wordTrace_append hprefix tailTrace_1849211
  have hstable : (prefixWord ++ tailWord_1849211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1849211).length < 2 ^ (prefixWord ++ tailWord_1849211).sum := by decide
  have hdescent : baseEnd_1849211 < baseStart_1849211 := by decide
  rcases family_descends (prefixWord ++ tailWord_1849211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1849242 : List Nat := [3, 1, 1, 4, 2, 1, 2, 3, 1, 2, 3]
def baseStart_1849242 : Nat := 118140960795 + 1849242 * 2 ^ 59
def prefixEnd_1849242 : Nat := 4983230072969 + 3 ^ 40 * 1849242 * 2
def baseEnd_1849242 : Nat := 949549992481759065870497

theorem tailTrace_1849242 : CollatzResearch.WordTrace tailWord_1849242 prefixEnd_1849242 949549992481759065870497 := by
  unfold tailWord_1849242
  simp only [CollatzResearch.WordTrace]
  refine ⟨16861849191629883558641495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44964931177679689489710653 16861849191629883558641495)
  ·
    refine ⟨25292773787444825337962243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16861849191629883558641495 25292773787444825337962243)
    ·
      refine ⟨37939160681167238006943365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25292773787444825337962243 37939160681167238006943365)
      ·
        refine ⟨7113592627718857126301881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37939160681167238006943365 7113592627718857126301881)
        ·
          refine ⟨5335194470789142844726411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7113592627718857126301881 5335194470789142844726411)
          ·
            refine ⟨8002791706183714267089617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5335194470789142844726411 8002791706183714267089617)
            ·
              refine ⟨6002093779637785700317213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8002791706183714267089617 6002093779637785700317213)
              ·
                refine ⟨2250785167364169637618955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6002093779637785700317213 2250785167364169637618955)
                ·
                  refine ⟨3376177751046254456428433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2250785167364169637618955 3376177751046254456428433)
                  ·
                    refine ⟨2532133313284690842321325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3376177751046254456428433 2532133313284690842321325)
                    ·
                      refine ⟨949549992481759065870497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2532133313284690842321325 949549992481759065870497)
                      ·
                        rfl

theorem cell23_1849242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 3, 1, 2, 3].length) (baseStart_1849242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1849242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1849242 prefixEnd_1849242 := by exact prefixLift 1849242
  have htrace : WordTrace (prefixWord ++ tailWord_1849242) baseStart_1849242 baseEnd_1849242 := by
    simpa [prefixWord, tailWord_1849242, baseEnd_1849242] using wordTrace_append hprefix tailTrace_1849242
  have hstable : (prefixWord ++ tailWord_1849242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1849242).length < 2 ^ (prefixWord ++ tailWord_1849242).sum := by decide
  have hdescent : baseEnd_1849242 < baseStart_1849242 := by decide
  rcases family_descends (prefixWord ++ tailWord_1849242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1849272 : List Nat := [2, 1, 2, 1, 2, 3, 3, 3, 2, 1, 3]
def baseStart_1849272 : Nat := 118140960795 + 1849272 * 2 ^ 59
def prefixEnd_1849272 : Nat := 4983230072969 + 3 ^ 40 * 1849272 * 2
def baseEnd_1849272 : Nat := 949565396901393948495359

theorem tailTrace_1849272 : CollatzResearch.WordTrace tailWord_1849272 prefixEnd_1849272 949565396901393948495359 := by
  unfold tailWord_1849272
  simp only [CollatzResearch.WordTrace]
  refine ⟨33724245478205424679079035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44965660637607232905438713 33724245478205424679079035)
  ·
    refine ⟨50586368217308137018618553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33724245478205424679079035 50586368217308137018618553)
    ·
      refine ⟨37939776162981102763963915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50586368217308137018618553 37939776162981102763963915)
      ·
        refine ⟨56909664244471654145945873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37939776162981102763963915 56909664244471654145945873)
        ·
          refine ⟨42682248183353740609459405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56909664244471654145945873 42682248183353740609459405)
          ·
            refine ⟨16005843068757652728547277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42682248183353740609459405 16005843068757652728547277)
            ·
              refine ⟨6002191150784119773205229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16005843068757652728547277 6002191150784119773205229)
              ·
                refine ⟨2250821681544044914951961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6002191150784119773205229 2250821681544044914951961)
                ·
                  refine ⟨1688116261158033686213971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2250821681544044914951961 1688116261158033686213971)
                  ·
                    refine ⟨2532174391737050529320957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1688116261158033686213971 2532174391737050529320957)
                    ·
                      refine ⟨949565396901393948495359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2532174391737050529320957 949565396901393948495359)
                      ·
                        rfl

theorem cell23_1849272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 3, 2, 1, 3].length) (baseStart_1849272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1849272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1849272 prefixEnd_1849272 := by exact prefixLift 1849272
  have htrace : WordTrace (prefixWord ++ tailWord_1849272) baseStart_1849272 baseEnd_1849272 := by
    simpa [prefixWord, tailWord_1849272, baseEnd_1849272] using wordTrace_append hprefix tailTrace_1849272
  have hstable : (prefixWord ++ tailWord_1849272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1849272).length < 2 ^ (prefixWord ++ tailWord_1849272).sum := by decide
  have hdescent : baseEnd_1849272 < baseStart_1849272 := by decide
  rcases family_descends (prefixWord ++ tailWord_1849272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1849276 : List Nat := [2, 2, 2, 5, 1, 2, 1, 2, 1, 2, 3]
def baseStart_1849276 : Nat := 118140960795 + 1849276 * 2 ^ 59
def prefixEnd_1849276 : Nat := 4983230072969 + 3 ^ 40 * 1849276 * 2
def baseEnd_1849276 : Nat := 949567450824011932845341

theorem tailTrace_1849276 : CollatzResearch.WordTrace tailWord_1849276 prefixEnd_1849276 949567450824011932845341 := by
  unfold tailWord_1849276
  simp only [CollatzResearch.WordTrace]
  refine ⟨33724318424198179020651841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44965757898930905360869121 33724318424198179020651841)
  ·
    refine ⟨25293238818148634265488881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33724318424198179020651841 25293238818148634265488881)
    ·
      refine ⟨18969929113611475699116661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25293238818148634265488881 18969929113611475699116661)
      ·
        refine ⟨1778430854401075846792187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18969929113611475699116661 1778430854401075846792187)
        ·
          refine ⟨2667646281601613770188281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1778430854401075846792187 2667646281601613770188281)
          ·
            refine ⟨2000734711201210327641211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2667646281601613770188281 2000734711201210327641211)
            ·
              refine ⟨3001102066801815491461817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2000734711201210327641211 3001102066801815491461817)
              ·
                refine ⟨2250826550101361618596363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3001102066801815491461817 2250826550101361618596363)
                ·
                  refine ⟨3376239825152042427894545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2250826550101361618596363 3376239825152042427894545)
                  ·
                    refine ⟨2532179868864031820920909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3376239825152042427894545 2532179868864031820920909)
                    ·
                      refine ⟨949567450824011932845341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2532179868864031820920909 949567450824011932845341)
                      ·
                        rfl

theorem cell23_1849276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_1849276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1849276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1849276 prefixEnd_1849276 := by exact prefixLift 1849276
  have htrace : WordTrace (prefixWord ++ tailWord_1849276) baseStart_1849276 baseEnd_1849276 := by
    simpa [prefixWord, tailWord_1849276, baseEnd_1849276] using wordTrace_append hprefix tailTrace_1849276
  have hstable : (prefixWord ++ tailWord_1849276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1849276).length < 2 ^ (prefixWord ++ tailWord_1849276).sum := by decide
  have hdescent : baseEnd_1849276 < baseStart_1849276 := by decide
  rcases family_descends (prefixWord ++ tailWord_1849276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1849312 : List Nat := [2, 1, 1, 3, 1, 1, 1, 5, 4, 2, 2]
def baseStart_1849312 : Nat := 118140960795 + 1849312 * 2 ^ 59
def prefixEnd_1849312 : Nat := 4983230072969 + 3 ^ 40 * 1849312 * 2
def baseEnd_1849312 : Nat := 949585936127573791995175

theorem tailTrace_1849312 : CollatzResearch.WordTrace tailWord_1849312 prefixEnd_1849312 949585936127573791995175 := by
  unfold tailWord_1849312
  simp only [CollatzResearch.WordTrace]
  refine ⟨33724974938132968094807095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44966633250843957459742793 33724974938132968094807095)
  ·
    refine ⟨50587462407199452142210643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33724974938132968094807095 50587462407199452142210643)
    ·
      refine ⟨75881193610799178213315965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50587462407199452142210643 75881193610799178213315965)
      ·
        refine ⟨28455447604049691829993487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75881193610799178213315965 28455447604049691829993487)
        ·
          refine ⟨42683171406074537744990231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28455447604049691829993487 42683171406074537744990231)
          ·
            refine ⟨64024757109111806617485347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42683171406074537744990231 64024757109111806617485347)
            ·
              refine ⟨96037135663667709926228021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64024757109111806617485347 96037135663667709926228021)
              ·
                refine ⟨9003481468468847805583877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 96037135663667709926228021 9003481468468847805583877)
                ·
                  refine ⟨1688152775337908963546977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9003481468468847805583877 1688152775337908963546977)
                  ·
                    refine ⟨1266114581503431722660233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1688152775337908963546977 1266114581503431722660233)
                    ·
                      refine ⟨949585936127573791995175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1266114581503431722660233 949585936127573791995175)
                      ·
                        rfl

theorem cell23_1849312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 5, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 5, 4, 2, 2].length) (baseStart_1849312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1849312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1849312 prefixEnd_1849312 := by exact prefixLift 1849312
  have htrace : WordTrace (prefixWord ++ tailWord_1849312) baseStart_1849312 baseEnd_1849312 := by
    simpa [prefixWord, tailWord_1849312, baseEnd_1849312] using wordTrace_append hprefix tailTrace_1849312
  have hstable : (prefixWord ++ tailWord_1849312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1849312).length < 2 ^ (prefixWord ++ tailWord_1849312).sum := by decide
  have hdescent : baseEnd_1849312 < baseStart_1849312 := by decide
  rcases family_descends (prefixWord ++ tailWord_1849312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1849315 : List Nat := [1, 1, 1, 6, 1, 2, 1, 1, 2, 4, 3]
def baseStart_1849315 : Nat := 118140960795 + 1849315 * 2 ^ 59
def prefixEnd_1849315 : Nat := 4983230072969 + 3 ^ 40 * 1849315 * 2
def baseEnd_1849315 : Nat := 949587476569537280257661

theorem tailTrace_1849315 : CollatzResearch.WordTrace tailWord_1849315 prefixEnd_1849315 949587476569537280257661 := by
  unfold tailWord_1849315
  simp only [CollatzResearch.WordTrace]
  refine ⟨67450059295255067701973399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44966706196836711801315599 67450059295255067701973399)
  ·
    refine ⟨101175088942882601552960099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67450059295255067701973399 101175088942882601552960099)
    ·
      refine ⟨151762633414323902329440149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101175088942882601552960099 151762633414323902329440149)
      ·
        refine ⟨7113873441296432921692507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 151762633414323902329440149 7113873441296432921692507)
        ·
          refine ⟨10670810161944649382538761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7113873441296432921692507 10670810161944649382538761)
          ·
            refine ⟨8003107621458487036904071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10670810161944649382538761 8003107621458487036904071)
            ·
              refine ⟨12004661432187730555356107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8003107621458487036904071 12004661432187730555356107)
              ·
                refine ⟨18006992148281595833034161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12004661432187730555356107 18006992148281595833034161)
                ·
                  refine ⟨13505244111211196874775621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18006992148281595833034161 13505244111211196874775621)
                  ·
                    refine ⟨2532233270852099414020429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13505244111211196874775621 2532233270852099414020429)
                    ·
                      refine ⟨949587476569537280257661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2532233270852099414020429 949587476569537280257661)
                      ·
                        rfl

theorem cell23_1849315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 1, 2, 4, 3].length) (baseStart_1849315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1849315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1849315 prefixEnd_1849315 := by exact prefixLift 1849315
  have htrace : WordTrace (prefixWord ++ tailWord_1849315) baseStart_1849315 baseEnd_1849315 := by
    simpa [prefixWord, tailWord_1849315, baseEnd_1849315] using wordTrace_append hprefix tailTrace_1849315
  have hstable : (prefixWord ++ tailWord_1849315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1849315).length < 2 ^ (prefixWord ++ tailWord_1849315).sum := by decide
  have hdescent : baseEnd_1849315 < baseStart_1849315 := by decide
  rcases family_descends (prefixWord ++ tailWord_1849315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1849329 : List Nat := [1, 2, 2, 2, 5, 1, 2, 1, 1, 4, 2]
def baseStart_1849329 : Nat := 118140960795 + 1849329 * 2 ^ 59
def prefixEnd_1849329 : Nat := 4983230072969 + 3 ^ 40 * 1849329 * 2
def baseEnd_1849329 : Nat := 949594665298700225482597

theorem tailTrace_1849329 : CollatzResearch.WordTrace tailWord_1849329 prefixEnd_1849329 949594665298700225482597 := by
  unfold tailWord_1849329
  simp only [CollatzResearch.WordTrace]
  refine ⟨67450569917204348092983041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44967046611469565395322027 67450569917204348092983041)
  ·
    refine ⟨50587927437903261069737281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67450569917204348092983041 50587927437903261069737281)
    ·
      refine ⟨37940945578427445802302961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50587927437903261069737281 37940945578427445802302961)
      ·
        refine ⟨28455709183820584351727221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37940945578427445802302961 28455709183820584351727221)
        ·
          refine ⟨2667722735983179782974427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 28455709183820584351727221 2667722735983179782974427)
          ·
            refine ⟨4001584103974769674461641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2667722735983179782974427 4001584103974769674461641)
            ·
              refine ⟨3001188077981077255846231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4001584103974769674461641 3001188077981077255846231)
              ·
                refine ⟨4501782116971615883769347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3001188077981077255846231 4501782116971615883769347)
                ·
                  refine ⟨6752673175457423825654021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4501782116971615883769347 6752673175457423825654021)
                  ·
                    refine ⟨1266126220398266967310129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6752673175457423825654021 1266126220398266967310129)
                    ·
                      refine ⟨949594665298700225482597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1266126220398266967310129 949594665298700225482597)
                      ·
                        rfl

theorem cell23_1849329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 2, 1, 1, 4, 2].length) (baseStart_1849329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1849329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1849329 prefixEnd_1849329 := by exact prefixLift 1849329
  have htrace : WordTrace (prefixWord ++ tailWord_1849329) baseStart_1849329 baseEnd_1849329 := by
    simpa [prefixWord, tailWord_1849329, baseEnd_1849329] using wordTrace_append hprefix tailTrace_1849329
  have hstable : (prefixWord ++ tailWord_1849329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1849329).length < 2 ^ (prefixWord ++ tailWord_1849329).sum := by decide
  have hdescent : baseEnd_1849329 < baseStart_1849329 := by decide
  rcases family_descends (prefixWord ++ tailWord_1849329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1849345 : List Nat := [1, 2, 4, 1, 2, 1, 1, 2, 1, 5, 3]
def baseStart_1849345 : Nat := 118140960795 + 1849345 * 2 ^ 59
def prefixEnd_1849345 : Nat := 4983230072969 + 3 ^ 40 * 1849345 * 2
def baseEnd_1849345 : Nat := 949602880989172162882523

theorem tailTrace_1849345 : CollatzResearch.WordTrace tailWord_1849345 prefixEnd_1849345 949602880989172162882523 := by
  unfold tailWord_1849345
  simp only [CollatzResearch.WordTrace]
  refine ⟨67451153485146382825565489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44967435656764255217043659 67451153485146382825565489)
  ·
    refine ⟨50588365113859787119174117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67451153485146382825565489 50588365113859787119174117)
    ·
      refine ⟨9485318458848710084845147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50588365113859787119174117 9485318458848710084845147)
      ·
        refine ⟨14227977688273065127267721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9485318458848710084845147 14227977688273065127267721)
        ·
          refine ⟨10670983266204798845450791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14227977688273065127267721 10670983266204798845450791)
          ·
            refine ⟨16006474899307198268176187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10670983266204798845450791 16006474899307198268176187)
            ·
              refine ⟨24009712348960797402264281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16006474899307198268176187 24009712348960797402264281)
              ·
                refine ⟨18007284261720598051698211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24009712348960797402264281 18007284261720598051698211)
                ·
                  refine ⟨27010926392580897077547317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18007284261720598051698211 27010926392580897077547317)
                  ·
                    refine ⟨2532274349304459101020061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27010926392580897077547317 2532274349304459101020061)
                    ·
                      refine ⟨949602880989172162882523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2532274349304459101020061 949602880989172162882523)
                      ·
                        rfl

theorem cell23_1849345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 2, 1, 5, 3].length) (baseStart_1849345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1849345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1849345 prefixEnd_1849345 := by exact prefixLift 1849345
  have htrace : WordTrace (prefixWord ++ tailWord_1849345) baseStart_1849345 baseEnd_1849345 := by
    simpa [prefixWord, tailWord_1849345, baseEnd_1849345] using wordTrace_append hprefix tailTrace_1849345
  have hstable : (prefixWord ++ tailWord_1849345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1849345).length < 2 ^ (prefixWord ++ tailWord_1849345).sum := by decide
  have hdescent : baseEnd_1849345 < baseStart_1849345 := by decide
  rcases family_descends (prefixWord ++ tailWord_1849345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1849352 : List Nat := [2, 1, 3, 2, 1, 2, 4, 3, 5]
def baseStart_1849352 : Nat := 118140960795 + 1849352 * 2 ^ 59
def prefixEnd_1849352 : Nat := 4983230072969 + 3 ^ 40 * 1849352 * 2
def baseEnd_1849352 : Nat := 105511830594861515054999

theorem tailTrace_1849352 : CollatzResearch.WordTrace tailWord_1849352 prefixEnd_1849352 105511830594861515054999 := by
  unfold tailWord_1849352
  simp only [CollatzResearch.WordTrace]
  refine ⟨33725704398060511510535155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44967605864080682014046873 33725704398060511510535155)
  ·
    refine ⟨50588556597090767265802733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33725704398060511510535155 50588556597090767265802733)
    ·
      refine ⟨18970708723909037724676025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50588556597090767265802733 18970708723909037724676025)
      ·
        refine ⟨14228031542931778293507019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18970708723909037724676025 14228031542931778293507019)
        ·
          refine ⟨21342047314397667440260529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14228031542931778293507019 21342047314397667440260529)
          ·
            refine ⟨16006535485798250580195397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21342047314397667440260529 16006535485798250580195397)
            ·
              refine ⟨3001225403587171983786637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16006535485798250580195397 3001225403587171983786637)
              ·
                refine ⟨1125459526345189493919989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3001225403587171983786637 1125459526345189493919989)
                ·
                  refine ⟨105511830594861515054999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1125459526345189493919989 105511830594861515054999)
                  ·
                    rfl

theorem cell23_1849352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 4, 3, 5].length) (baseStart_1849352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1849352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1849352 prefixEnd_1849352 := by exact prefixLift 1849352
  have htrace : WordTrace (prefixWord ++ tailWord_1849352) baseStart_1849352 baseEnd_1849352 := by
    simpa [prefixWord, tailWord_1849352, baseEnd_1849352] using wordTrace_append hprefix tailTrace_1849352
  have hstable : (prefixWord ++ tailWord_1849352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1849352).length < 2 ^ (prefixWord ++ tailWord_1849352).sum := by decide
  have hdescent : baseEnd_1849352 < baseStart_1849352 := by decide
  rcases family_descends (prefixWord ++ tailWord_1849352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1849357 : List Nat := [1, 7, 1, 2, 2, 1, 1, 2, 2, 1, 3]
def baseStart_1849357 : Nat := 118140960795 + 1849357 * 2 ^ 59
def prefixEnd_1849357 : Nat := 4983230072969 + 3 ^ 40 * 1849357 * 2
def baseEnd_1849357 : Nat := 949609042757026115932469

theorem tailTrace_1849357 : CollatzResearch.WordTrace tailWord_1849357 prefixEnd_1849357 949609042757026115932469 := by
  unfold tailWord_1849357
  simp only [CollatzResearch.WordTrace]
  refine ⟨67451591161102908875002325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44967727440735272583334883 67451591161102908875002325)
  ·
    refine ⟨1580896667838349426757867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 67451591161102908875002325 1580896667838349426757867)
    ·
      refine ⟨2371345001757524140136801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1580896667838349426757867 2371345001757524140136801)
      ·
        refine ⟨1778508751318143105102601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2371345001757524140136801 1778508751318143105102601)
        ·
          refine ⟨1333881563488607328826951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1778508751318143105102601 1333881563488607328826951)
          ·
            refine ⟨2000822345232910993240427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1333881563488607328826951 2000822345232910993240427)
            ·
              refine ⟨3001233517849366489860641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2000822345232910993240427 3001233517849366489860641)
              ·
                refine ⟨2250925138387024867395481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3001233517849366489860641 2250925138387024867395481)
                ·
                  refine ⟨1688193853790268650546611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2250925138387024867395481 1688193853790268650546611)
                  ·
                    refine ⟨2532290780685402975819917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1688193853790268650546611 2532290780685402975819917)
                    ·
                      refine ⟨949609042757026115932469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2532290780685402975819917 949609042757026115932469)
                      ·
                        rfl

theorem cell23_1849357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 1, 2, 2, 1, 3].length) (baseStart_1849357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1849357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1849357 prefixEnd_1849357 := by exact prefixLift 1849357
  have htrace : WordTrace (prefixWord ++ tailWord_1849357) baseStart_1849357 baseEnd_1849357 := by
    simpa [prefixWord, tailWord_1849357, baseEnd_1849357] using wordTrace_append hprefix tailTrace_1849357
  have hstable : (prefixWord ++ tailWord_1849357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1849357).length < 2 ^ (prefixWord ++ tailWord_1849357).sum := by decide
  have hdescent : baseEnd_1849357 < baseStart_1849357 := by decide
  rcases family_descends (prefixWord ++ tailWord_1849357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1849422 : List Nat := [4, 1, 1, 1, 1, 4, 1, 1, 4, 2, 3]
def baseStart_1849422 : Nat := 118140960795 + 1849422 * 2 ^ 59
def prefixEnd_1849422 : Nat := 4983230072969 + 3 ^ 40 * 1849422 * 2
def baseEnd_1849422 : Nat := 949642418999568361619669

theorem tailTrace_1849422 : CollatzResearch.WordTrace tailWord_1849422 prefixEnd_1849422 949642418999568361619669 := by
  unfold tailWord_1849422
  simp only [CollatzResearch.WordTrace]
  refine ⟨8431745238233428122014815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44969307937244949984079013 8431745238233428122014815)
  ·
    refine ⟨12647617857350142183022223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8431745238233428122014815 12647617857350142183022223)
    ·
      refine ⟨18971426786025213274533335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12647617857350142183022223 18971426786025213274533335)
      ·
        refine ⟨28457140179037819911800003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18971426786025213274533335 28457140179037819911800003)
        ·
          refine ⟨42685710268556729867700005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28457140179037819911800003 42685710268556729867700005)
          ·
            refine ⟨8003570675354386850193751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42685710268556729867700005 8003570675354386850193751)
            ·
              refine ⟨12005356013031580275290627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8003570675354386850193751 12005356013031580275290627)
              ·
                refine ⟨18008034019547370412935941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12005356013031580275290627 18008034019547370412935941)
                ·
                  refine ⟨3376506378665131952425489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18008034019547370412935941 3376506378665131952425489)
                  ·
                    refine ⟨2532379783998848964319117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3376506378665131952425489 2532379783998848964319117)
                    ·
                      refine ⟨949642418999568361619669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2532379783998848964319117 949642418999568361619669)
                      ·
                        rfl

theorem cell23_1849422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 1, 4, 2, 3].length) (baseStart_1849422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1849422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1849422 prefixEnd_1849422 := by exact prefixLift 1849422
  have htrace : WordTrace (prefixWord ++ tailWord_1849422) baseStart_1849422 baseEnd_1849422 := by
    simpa [prefixWord, tailWord_1849422, baseEnd_1849422] using wordTrace_append hprefix tailTrace_1849422
  have hstable : (prefixWord ++ tailWord_1849422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1849422).length < 2 ^ (prefixWord ++ tailWord_1849422).sum := by decide
  have hdescent : baseEnd_1849422 < baseStart_1849422 := by decide
  rcases family_descends (prefixWord ++ tailWord_1849422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1849425 : List Nat := [1, 2, 2, 1, 3, 1, 1, 6, 6]
def baseStart_1849425 : Nat := 118140960795 + 1849425 * 2 ^ 59
def prefixEnd_1849425 : Nat := 4983230072969 + 3 ^ 40 * 1849425 * 2
def baseEnd_1849425 : Nat := 105515995493503538875795

theorem tailTrace_1849425 : CollatzResearch.WordTrace tailWord_1849425 prefixEnd_1849425 105515995493503538875795 := by
  unfold tailWord_1849425
  simp only [CollatzResearch.WordTrace]
  refine ⟨67454071324856556488477729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44969380883237704325651819 67454071324856556488477729)
  ·
    refine ⟨50590553493642417366358297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67454071324856556488477729 50590553493642417366358297)
    ·
      refine ⟨37942915120231813024768723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50590553493642417366358297 37942915120231813024768723)
      ·
        refine ⟨56914372680347719537153085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37942915120231813024768723 56914372680347719537153085)
        ·
          refine ⟨21342889755130394826432407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56914372680347719537153085 21342889755130394826432407)
          ·
            refine ⟨32014334632695592239648611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21342889755130394826432407 32014334632695592239648611)
            ·
              refine ⟨48021501949043388359472917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32014334632695592239648611 48021501949043388359472917)
              ·
                refine ⟨2251007903861408829350293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 48021501949043388359472917 2251007903861408829350293)
                ·
                  refine ⟨105515995493503538875795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2251007903861408829350293 105515995493503538875795)
                  ·
                    rfl

theorem cell23_1849425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 6, 6].length) (baseStart_1849425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1849425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1849425 prefixEnd_1849425 := by exact prefixLift 1849425
  have htrace : WordTrace (prefixWord ++ tailWord_1849425) baseStart_1849425 baseEnd_1849425 := by
    simpa [prefixWord, tailWord_1849425, baseEnd_1849425] using wordTrace_append hprefix tailTrace_1849425
  have hstable : (prefixWord ++ tailWord_1849425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1849425).length < 2 ^ (prefixWord ++ tailWord_1849425).sum := by decide
  have hdescent : baseEnd_1849425 < baseStart_1849425 := by decide
  rcases family_descends (prefixWord ++ tailWord_1849425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1849429 : List Nat := [1, 3, 2, 2, 1, 5, 1, 1, 3, 4]
def baseStart_1849429 : Nat := 118140960795 + 1849429 * 2 ^ 59
def prefixEnd_1849429 : Nat := 4983230072969 + 3 ^ 40 * 1849429 * 2
def baseEnd_1849429 : Nat := 316548671121383278077379

theorem tailTrace_1849429 : CollatzResearch.WordTrace tailWord_1849429 prefixEnd_1849429 316548671121383278077379 := by
  unfold tailWord_1849429
  simp only [CollatzResearch.WordTrace]
  refine ⟨67454217216842065171623341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44969478144561376781082227 67454217216842065171623341)
  ·
    refine ⟨25295331456315774439358753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67454217216842065171623341 25295331456315774439358753)
    ·
      refine ⟨18971498592236830829519065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25295331456315774439358753 18971498592236830829519065)
      ·
        refine ⟨14228623944177623122139299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18971498592236830829519065 14228623944177623122139299)
        ·
          refine ⟨21342935916266434683208949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14228623944177623122139299 21342935916266434683208949)
          ·
            refine ⟨2000900242149978251550839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21342935916266434683208949 2000900242149978251550839)
            ·
              refine ⟨3001350363224967377326259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2000900242149978251550839 3001350363224967377326259)
              ·
                refine ⟨4502025544837451065989389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3001350363224967377326259 4502025544837451065989389)
                ·
                  refine ⟨1688259579314044149746021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4502025544837451065989389 1688259579314044149746021)
                  ·
                    refine ⟨316548671121383278077379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1688259579314044149746021 316548671121383278077379)
                    ·
                      rfl

theorem cell23_1849429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 1, 1, 3, 4].length) (baseStart_1849429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1849429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1849429 prefixEnd_1849429 := by exact prefixLift 1849429
  have htrace : WordTrace (prefixWord ++ tailWord_1849429) baseStart_1849429 baseEnd_1849429 := by
    simpa [prefixWord, tailWord_1849429, baseEnd_1849429] using wordTrace_append hprefix tailTrace_1849429
  have hstable : (prefixWord ++ tailWord_1849429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1849429).length < 2 ^ (prefixWord ++ tailWord_1849429).sum := by decide
  have hdescent : baseEnd_1849429 < baseStart_1849429 := by decide
  rcases family_descends (prefixWord ++ tailWord_1849429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1849479 : List Nat := [1, 1, 4, 2, 1, 1, 4, 2, 2, 3, 2]
def baseStart_1849479 : Nat := 118140960795 + 1849479 * 2 ^ 59
def prefixEnd_1849479 : Nat := 4983230072969 + 3 ^ 40 * 1849479 * 2
def baseEnd_1849479 : Nat := 949671687396874638606907

theorem tailTrace_1849479 : CollatzResearch.WordTrace tailWord_1849479 prefixEnd_1849479 949671687396874638606907 := by
  unfold tailWord_1849479
  simp only [CollatzResearch.WordTrace]
  refine ⟨67456040866660923710943491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44970693911107282473962327 67456040866660923710943491)
  ·
    refine ⟨101184061299991385566415237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67456040866660923710943491 101184061299991385566415237)
    ·
      refine ⟨18972011493748384793702857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101184061299991385566415237 18972011493748384793702857)
      ·
        refine ⟨14229008620311288595277143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18972011493748384793702857 14229008620311288595277143)
        ·
          refine ⟨21343512930466932892915715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14229008620311288595277143 21343512930466932892915715)
          ·
            refine ⟨32015269395700399339373573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21343512930466932892915715 32015269395700399339373573)
            ·
              refine ⟨6002863011693824876132545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32015269395700399339373573 6002863011693824876132545)
              ·
                refine ⟨4502147258770368657099409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6002863011693824876132545 4502147258770368657099409)
                ·
                  refine ⟨3376610444077776492824557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4502147258770368657099409 3376610444077776492824557)
                  ·
                    refine ⟨1266228916529166184809209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3376610444077776492824557 1266228916529166184809209)
                    ·
                      refine ⟨949671687396874638606907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1266228916529166184809209 949671687396874638606907)
                      ·
                        rfl

theorem cell23_1849479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 2, 2, 3, 2].length) (baseStart_1849479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1849479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1849479 prefixEnd_1849479 := by exact prefixLift 1849479
  have htrace : WordTrace (prefixWord ++ tailWord_1849479) baseStart_1849479 baseEnd_1849479 := by
    simpa [prefixWord, tailWord_1849479, baseEnd_1849479] using wordTrace_append hprefix tailTrace_1849479
  have hstable : (prefixWord ++ tailWord_1849479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1849479).length < 2 ^ (prefixWord ++ tailWord_1849479).sum := by decide
  have hdescent : baseEnd_1849479 < baseStart_1849479 := by decide
  rcases family_descends (prefixWord ++ tailWord_1849479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1849522 : List Nat := [3, 2, 1, 1, 1, 3, 1, 4, 1, 2, 4]
def baseStart_1849522 : Nat := 118140960795 + 1849522 * 2 ^ 59
def prefixEnd_1849522 : Nat := 4983230072969 + 3 ^ 40 * 1849522 * 2
def baseEnd_1849522 : Nat := 949693767065017970369209

theorem tailTrace_1849522 : CollatzResearch.WordTrace tailWord_1849522 prefixEnd_1849522 949693767065017970369209 := by
  unfold tailWord_1849522
  simp only [CollatzResearch.WordTrace]
  refine ⟨16864402301376285513689705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44971739470336761369839213 16864402301376285513689705)
  ·
    refine ⟨12648301726032214135267279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16864402301376285513689705 12648301726032214135267279)
    ·
      refine ⟨18972452589048321202900919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12648301726032214135267279 18972452589048321202900919)
      ·
        refine ⟨28458678883572481804351379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18972452589048321202900919 28458678883572481804351379)
        ·
          refine ⟨42688018325358722706527069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28458678883572481804351379 42688018325358722706527069)
          ·
            refine ⟨16008006872009521014947651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42688018325358722706527069 16008006872009521014947651)
            ·
              refine ⟨24012010308014281522421477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16008006872009521014947651 24012010308014281522421477)
              ·
                refine ⟨4502251932752677785454027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24012010308014281522421477 4502251932752677785454027)
                ·
                  refine ⟨6753377899129016678181041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4502251932752677785454027 6753377899129016678181041)
                  ·
                    refine ⟨5065033424346762508635781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6753377899129016678181041 5065033424346762508635781)
                    ·
                      refine ⟨949693767065017970369209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5065033424346762508635781 949693767065017970369209)
                      ·
                        rfl

theorem cell23_1849522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 4, 1, 2, 4].length) (baseStart_1849522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1849522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1849522 prefixEnd_1849522 := by exact prefixLift 1849522
  have htrace : WordTrace (prefixWord ++ tailWord_1849522) baseStart_1849522 baseEnd_1849522 := by
    simpa [prefixWord, tailWord_1849522, baseEnd_1849522] using wordTrace_append hprefix tailTrace_1849522
  have hstable : (prefixWord ++ tailWord_1849522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1849522).length < 2 ^ (prefixWord ++ tailWord_1849522).sum := by decide
  have hdescent : baseEnd_1849522 < baseStart_1849522 := by decide
  rcases family_descends (prefixWord ++ tailWord_1849522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1849529 : List Nat := [1, 2, 1, 4, 1, 2, 3, 3, 1, 2, 3]
def baseStart_1849529 : Nat := 118140960795 + 1849529 * 2 ^ 59
def prefixEnd_1849529 : Nat := 4983230072969 + 3 ^ 40 * 1849529 * 2
def baseEnd_1849529 : Nat := 949697361429599442981677

theorem tailTrace_1849529 : CollatzResearch.WordTrace tailWord_1849529 prefixEnd_1849529 949697361429599442981677 := by
  unfold tailWord_1849529
  simp only [CollatzResearch.WordTrace]
  refine ⟨67457864516479782250263641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44971909677653188166842427 67457864516479782250263641)
  ·
    refine ⟨50593398387359836687697731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67457864516479782250263641 50593398387359836687697731)
    ·
      refine ⟨75890097581039755031546597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50593398387359836687697731 75890097581039755031546597)
      ·
        refine ⟨14229393296444954068414987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75890097581039755031546597 14229393296444954068414987)
        ·
          refine ⟨21344089944667431102622481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14229393296444954068414987 21344089944667431102622481)
          ·
            refine ⟨16008067458500573326966861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21344089944667431102622481 16008067458500573326966861)
            ·
              refine ⟨6003025296937714997612573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16008067458500573326966861 6003025296937714997612573)
              ·
                refine ⟨2251134486351643124104715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6003025296937714997612573 2251134486351643124104715)
                ·
                  refine ⟨3376701729527464686157073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2251134486351643124104715 3376701729527464686157073)
                  ·
                    refine ⟨2532526297145598514617805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3376701729527464686157073 2532526297145598514617805)
                    ·
                      refine ⟨949697361429599442981677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2532526297145598514617805 949697361429599442981677)
                      ·
                        rfl

theorem cell23_1849529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 3, 1, 2, 3].length) (baseStart_1849529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1849529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1849529 prefixEnd_1849529 := by exact prefixLift 1849529
  have htrace : WordTrace (prefixWord ++ tailWord_1849529) baseStart_1849529 baseEnd_1849529 := by
    simpa [prefixWord, tailWord_1849529, baseEnd_1849529] using wordTrace_append hprefix tailTrace_1849529
  have hstable : (prefixWord ++ tailWord_1849529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1849529).length < 2 ^ (prefixWord ++ tailWord_1849529).sum := by decide
  have hdescent : baseEnd_1849529 < baseStart_1849529 := by decide
  rcases family_descends (prefixWord ++ tailWord_1849529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1849532 : List Nat := [2, 2, 2, 3, 3, 1, 10]
def baseStart_1849532 : Nat := 118140960795 + 1849532 * 2 ^ 59
def prefixEnd_1849532 : Nat := 4983230072969 + 3 ^ 40 * 1849532 * 2
def baseEnd_1849532 : Nat := 11724677800883492978323

theorem tailTrace_1849532 : CollatzResearch.WordTrace tailWord_1849532 prefixEnd_1849532 11724677800883492978323 := by
  unfold tailWord_1849532
  simp only [CollatzResearch.WordTrace]
  refine ⟨33728986967734456881311425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44971982623645942508415233 33728986967734456881311425)
  ·
    refine ⟨25296740225800842660983569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33728986967734456881311425 25296740225800842660983569)
    ·
      refine ⟨18972555169350631995737677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25296740225800842660983569 18972555169350631995737677)
      ·
        refine ⟨7114708188506486998401629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18972555169350631995737677 7114708188506486998401629)
        ·
          refine ⟨2668015570689932624400611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7114708188506486998401629 2668015570689932624400611)
          ·
            refine ⟨4002023356034898936600917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2668015570689932624400611 4002023356034898936600917)
            ·
              refine ⟨11724677800883492978323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 4002023356034898936600917 11724677800883492978323)
              ·
                rfl

theorem cell23_1849532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 10].length) (baseStart_1849532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1849532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1849532 prefixEnd_1849532 := by exact prefixLift 1849532
  have htrace : WordTrace (prefixWord ++ tailWord_1849532) baseStart_1849532 baseEnd_1849532 := by
    simpa [prefixWord, tailWord_1849532, baseEnd_1849532] using wordTrace_append hprefix tailTrace_1849532
  have hstable : (prefixWord ++ tailWord_1849532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1849532).length < 2 ^ (prefixWord ++ tailWord_1849532).sum := by decide
  have hdescent : baseEnd_1849532 < baseStart_1849532 := by decide
  rcases family_descends (prefixWord ++ tailWord_1849532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1849535 : List Nat := [1, 1, 2, 2, 2, 2, 1, 2, 2, 2, 6]
def baseStart_1849535 : Nat := 118140960795 + 1849535 * 2 ^ 59
def prefixEnd_1849535 : Nat := 4983230072969 + 3 ^ 40 * 1849535 * 2
def baseEnd_1849535 : Nat := 949700442313526419506649

theorem tailTrace_1849535 : CollatzResearch.WordTrace tailWord_1849535 prefixEnd_1849535 949700442313526419506649 := by
  unfold tailWord_1849535
  simp only [CollatzResearch.WordTrace]
  refine ⟨67458083354458045274982059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44972055569638696849988039 67458083354458045274982059)
  ·
    refine ⟨101187125031687067912473089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67458083354458045274982059 101187125031687067912473089)
    ·
      refine ⟨75890343773765300934354817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101187125031687067912473089 75890343773765300934354817)
      ·
        refine ⟨56917757830323975700766113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75890343773765300934354817 56917757830323975700766113)
        ·
          refine ⟨42688318372742981775574585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56917757830323975700766113 42688318372742981775574585)
          ·
            refine ⟨32016238779557236331680939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42688318372742981775574585 32016238779557236331680939)
            ·
              refine ⟨48024358169335854497521409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32016238779557236331680939 48024358169335854497521409)
              ·
                refine ⟨36018268627001890873141057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48024358169335854497521409 36018268627001890873141057)
                ·
                  refine ⟨27013701470251418154855793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36018268627001890873141057 27013701470251418154855793)
                  ·
                    refine ⟨20260276102688563616141845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27013701470251418154855793 20260276102688563616141845)
                    ·
                      refine ⟨949700442313526419506649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 20260276102688563616141845 949700442313526419506649)
                      ·
                        rfl

theorem cell23_1849535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 2, 2, 2, 6].length) (baseStart_1849535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1849535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1849535 prefixEnd_1849535 := by exact prefixLift 1849535
  have htrace : WordTrace (prefixWord ++ tailWord_1849535) baseStart_1849535 baseEnd_1849535 := by
    simpa [prefixWord, tailWord_1849535, baseEnd_1849535] using wordTrace_append hprefix tailTrace_1849535
  have hstable : (prefixWord ++ tailWord_1849535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1849535).length < 2 ^ (prefixWord ++ tailWord_1849535).sum := by decide
  have hdescent : baseEnd_1849535 < baseStart_1849535 := by decide
  rcases family_descends (prefixWord ++ tailWord_1849535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1849536 : List Nat := [2, 1, 1, 2, 5, 3, 1, 2, 2, 4]
def baseStart_1849536 : Nat := 118140960795 + 1849536 * 2 ^ 59
def prefixEnd_1849536 : Nat := 4983230072969 + 3 ^ 40 * 1849536 * 2
def baseEnd_1849536 : Nat := 316566985264726971864715

theorem tailTrace_1849536 : CollatzResearch.WordTrace tailWord_1849536 prefixEnd_1849536 316566985264726971864715 := by
  unfold tailWord_1849536
  simp only [CollatzResearch.WordTrace]
  refine ⟨33729059913727211222884231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44972079884969614963845641 33729059913727211222884231)
  ·
    refine ⟨50593589870590816834326347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33729059913727211222884231 50593589870590816834326347)
    ·
      refine ⟨75890384805886225251489521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50593589870590816834326347 75890384805886225251489521)
      ·
        refine ⟨56917788604414668938617141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75890384805886225251489521 56917788604414668938617141)
        ·
          refine ⟨5336042681663875212995357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 56917788604414668938617141 5336042681663875212995357)
          ·
            refine ⟨2001016005623953204873259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5336042681663875212995357 2001016005623953204873259)
            ·
              refine ⟨3001524008435929807309889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2001016005623953204873259 3001524008435929807309889)
              ·
                refine ⟨2251143006326947355482417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3001524008435929807309889 2251143006326947355482417)
                ·
                  refine ⟨1688357254745210516611813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2251143006326947355482417 1688357254745210516611813)
                  ·
                    refine ⟨316566985264726971864715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1688357254745210516611813 316566985264726971864715)
                    ·
                      rfl

theorem cell23_1849536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 1, 2, 2, 4].length) (baseStart_1849536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1849536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1849536 prefixEnd_1849536 := by exact prefixLift 1849536
  have htrace : WordTrace (prefixWord ++ tailWord_1849536) baseStart_1849536 baseEnd_1849536 := by
    simpa [prefixWord, tailWord_1849536, baseEnd_1849536] using wordTrace_append hprefix tailTrace_1849536
  have hstable : (prefixWord ++ tailWord_1849536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1849536).length < 2 ^ (prefixWord ++ tailWord_1849536).sum := by decide
  have hdescent : baseEnd_1849536 < baseStart_1849536 := by decide
  rcases family_descends (prefixWord ++ tailWord_1849536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1849545 : List Nat := [1, 2, 1, 1, 2, 1, 1, 5, 2, 7]
def baseStart_1849545 : Nat := 118140960795 + 1849545 * 2 ^ 59
def prefixEnd_1849545 : Nat := 4983230072969 + 3 ^ 40 * 1849545 * 2
def baseEnd_1849545 : Nat := 316568525706690460127201

theorem tailTrace_1849545 : CollatzResearch.WordTrace tailWord_1849545 prefixEnd_1849545 316568525706690460127201 := by
  unfold tailWord_1849545
  simp only [CollatzResearch.WordTrace]
  refine ⟨67458448084421816982846089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44972298722947877988564059 67458448084421816982846089)
  ·
    refine ⟨50593836063316362737134567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67458448084421816982846089 50593836063316362737134567)
    ·
      refine ⟨75890754094974544105701851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50593836063316362737134567 75890754094974544105701851)
      ·
        refine ⟨113836131142461816158552777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75890754094974544105701851 113836131142461816158552777)
        ·
          refine ⟨85377098356846362118914583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113836131142461816158552777 85377098356846362118914583)
          ·
            refine ⟨128065647535269543178371875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85377098356846362118914583 128065647535269543178371875)
            ·
              refine ⟨192098471302904314767557813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128065647535269543178371875 192098471302904314767557813)
              ·
                refine ⟨18009231684647279509458545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 192098471302904314767557813 18009231684647279509458545)
                ·
                  refine ⟨13506923763485459632093909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18009231684647279509458545 13506923763485459632093909)
                  ·
                    refine ⟨316568525706690460127201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13506923763485459632093909 316568525706690460127201)
                    ·
                      rfl

theorem cell23_1849545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 5, 2, 7].length) (baseStart_1849545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1849545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1849545 prefixEnd_1849545 := by exact prefixLift 1849545
  have htrace : WordTrace (prefixWord ++ tailWord_1849545) baseStart_1849545 baseEnd_1849545 := by
    simpa [prefixWord, tailWord_1849545, baseEnd_1849545] using wordTrace_append hprefix tailTrace_1849545
  have hstable : (prefixWord ++ tailWord_1849545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1849545).length < 2 ^ (prefixWord ++ tailWord_1849545).sum := by decide
  have hdescent : baseEnd_1849545 < baseStart_1849545 := by decide
  rcases family_descends (prefixWord ++ tailWord_1849545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1849555 : List Nat := [1, 1, 1, 2, 1, 1, 1, 3, 3, 4, 5]
def baseStart_1849555 : Nat := 118140960795 + 1849555 * 2 ^ 59
def prefixEnd_1849555 : Nat := 4983230072969 + 3 ^ 40 * 1849555 * 2
def baseEnd_1849555 : Nat := 949710711926616341256557

theorem tailTrace_1849555 : CollatzResearch.WordTrace tailWord_1849555 prefixEnd_1849555 949710711926616341256557 := by
  unfold tailWord_1849555
  simp only [CollatzResearch.WordTrace]
  refine ⟨67458812814385588690710119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44972541876257059127140079 67458812814385588690710119)
  ·
    refine ⟨101188219221578383036065179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67458812814385588690710119 101188219221578383036065179)
    ·
      refine ⟨151782328832367574554097769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101188219221578383036065179 151782328832367574554097769)
      ·
        refine ⟨113836746624275680915573327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151782328832367574554097769 113836746624275680915573327)
        ·
          refine ⟨170755119936413521373359991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113836746624275680915573327 170755119936413521373359991)
          ·
            refine ⟨256132679904620282060039987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170755119936413521373359991 256132679904620282060039987)
            ·
              refine ⟨384199019856930423090059981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 256132679904620282060039987 384199019856930423090059981)
              ·
                refine ⟨144074632446348908658772493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 384199019856930423090059981 144074632446348908658772493)
                ·
                  refine ⟨54027987167380840747039685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 144074632446348908658772493 54027987167380840747039685)
                  ·
                    refine ⟨10130247593883907640069941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54027987167380840747039685 10130247593883907640069941)
                    ·
                      refine ⟨949710711926616341256557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10130247593883907640069941 949710711926616341256557)
                      ·
                        rfl

theorem cell23_1849555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 3, 4, 5].length) (baseStart_1849555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1849555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1849555 prefixEnd_1849555 := by exact prefixLift 1849555
  have htrace : WordTrace (prefixWord ++ tailWord_1849555) baseStart_1849555 baseEnd_1849555 := by
    simpa [prefixWord, tailWord_1849555, baseEnd_1849555] using wordTrace_append hprefix tailTrace_1849555
  have hstable : (prefixWord ++ tailWord_1849555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1849555).length < 2 ^ (prefixWord ++ tailWord_1849555).sum := by decide
  have hdescent : baseEnd_1849555 < baseStart_1849555 := by decide
  rcases family_descends (prefixWord ++ tailWord_1849555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1849582 : List Nat := [4, 1, 2, 1, 1, 1, 1, 2, 1, 5, 4]
def baseStart_1849582 : Nat := 118140960795 + 1849582 * 2 ^ 59
def prefixEnd_1849582 : Nat := 4983230072969 + 3 ^ 40 * 1849582 * 2
def baseEnd_1849582 : Nat := 949724575904287735618933

theorem tailTrace_1849582 : CollatzResearch.WordTrace tailWord_1849582 prefixEnd_1849582 949724575904287735618933 := by
  unfold tailWord_1849582
  simp only [CollatzResearch.WordTrace]
  refine ⟨8432474698160971537742875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44973198390191848201295333 8432474698160971537742875)
  ·
    refine ⟨12648712047241457306614313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8432474698160971537742875 12648712047241457306614313)
    ·
      refine ⟨9486534035431092979960735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12648712047241457306614313 9486534035431092979960735)
      ·
        refine ⟨14229801053146639469941103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9486534035431092979960735 14229801053146639469941103)
        ·
          refine ⟨21344701579719959204911655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14229801053146639469941103 21344701579719959204911655)
          ·
            refine ⟨32017052369579938807367483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21344701579719959204911655 32017052369579938807367483)
            ·
              refine ⟨48025578554369908211051225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32017052369579938807367483 48025578554369908211051225)
              ·
                refine ⟨36019183915777431158288419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48025578554369908211051225 36019183915777431158288419)
                ·
                  refine ⟨54028775873666146737432629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36019183915777431158288419 54028775873666146737432629)
                  ·
                    refine ⟨5065197738156201256634309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54028775873666146737432629 5065197738156201256634309)
                    ·
                      refine ⟨949724575904287735618933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5065197738156201256634309 949724575904287735618933)
                      ·
                        rfl

theorem cell23_1849582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 2, 1, 5, 4].length) (baseStart_1849582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1849582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1849582 prefixEnd_1849582 := by exact prefixLift 1849582
  have htrace : WordTrace (prefixWord ++ tailWord_1849582) baseStart_1849582 baseEnd_1849582 := by
    simpa [prefixWord, tailWord_1849582, baseEnd_1849582] using wordTrace_append hprefix tailTrace_1849582
  have hstable : (prefixWord ++ tailWord_1849582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1849582).length < 2 ^ (prefixWord ++ tailWord_1849582).sum := by decide
  have hdescent : baseEnd_1849582 < baseStart_1849582 := by decide
  rcases family_descends (prefixWord ++ tailWord_1849582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1849612 : List Nat := [2, 2, 1, 2, 2, 2, 2, 1, 1, 4, 4]
def baseStart_1849612 : Nat := 118140960795 + 1849612 * 2 ^ 59
def prefixEnd_1849612 : Nat := 4983230072969 + 3 ^ 40 * 1849612 * 2
def baseEnd_1849612 : Nat := 949739980323922618243795

theorem tailTrace_1849612 : CollatzResearch.WordTrace tailWord_1849612 prefixEnd_1849612 949739980323922618243795 := by
  unfold tailWord_1849612
  simp only [CollatzResearch.WordTrace]
  refine ⟨33730445887589543712767545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44973927850119391617023393 33730445887589543712767545)
  ·
    refine ⟨25297834415692157784575659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33730445887589543712767545 25297834415692157784575659)
    ·
      refine ⟨37946751623538236676863489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25297834415692157784575659 37946751623538236676863489)
      ·
        refine ⟨28460063717653677507647617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37946751623538236676863489 28460063717653677507647617)
        ·
          refine ⟨21345047788240258130735713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28460063717653677507647617 21345047788240258130735713)
          ·
            refine ⟨16008785841180193598051785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21345047788240258130735713 16008785841180193598051785)
            ·
              refine ⟨12006589380885145198538839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16008785841180193598051785 12006589380885145198538839)
              ·
                refine ⟨18009884071327717797808259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12006589380885145198538839 18009884071327717797808259)
                ·
                  refine ⟨27014826106991576696712389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18009884071327717797808259 27014826106991576696712389)
                  ·
                    refine ⟨5065279895060920630633573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27014826106991576696712389 5065279895060920630633573)
                    ·
                      refine ⟨949739980323922618243795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5065279895060920630633573 949739980323922618243795)
                      ·
                        rfl

theorem cell23_1849612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 1, 1, 4, 4].length) (baseStart_1849612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1849612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1849612 prefixEnd_1849612 := by exact prefixLift 1849612
  have htrace : WordTrace (prefixWord ++ tailWord_1849612) baseStart_1849612 baseEnd_1849612 := by
    simpa [prefixWord, tailWord_1849612, baseEnd_1849612] using wordTrace_append hprefix tailTrace_1849612
  have hstable : (prefixWord ++ tailWord_1849612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1849612).length < 2 ^ (prefixWord ++ tailWord_1849612).sum := by decide
  have hdescent : baseEnd_1849612 < baseStart_1849612 := by decide
  rcases family_descends (prefixWord ++ tailWord_1849612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1849650 : List Nat := [3, 2, 1, 1, 5, 1, 2, 2, 2, 2, 2]
def baseStart_1849650 : Nat := 118140960795 + 1849650 * 2 ^ 59
def prefixEnd_1849650 : Nat := 4983230072969 + 3 ^ 40 * 1849650 * 2
def baseEnd_1849650 : Nat := 949759492588793469568621

theorem tailTrace_1849650 : CollatzResearch.WordTrace tailWord_1849650 prefixEnd_1849650 949759492588793469568621 := by
  unfold tailWord_1849650
  simp only [CollatzResearch.WordTrace]
  refine ⟨16865569437260354978854601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44974851832694279943612269 16865569437260354978854601)
  ·
    refine ⟨12649177077945266234140951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16865569437260354978854601 12649177077945266234140951)
    ·
      refine ⟨18973765616917899351211427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12649177077945266234140951 18973765616917899351211427)
      ·
        refine ⟨28460648425376849026817141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18973765616917899351211427 28460648425376849026817141)
        ·
          refine ⟨2668185789879079596264107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 28460648425376849026817141 2668185789879079596264107)
          ·
            refine ⟨4002278684818619394396161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2668185789879079596264107 4002278684818619394396161)
            ·
              refine ⟨3001709013613964545797121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4002278684818619394396161 3001709013613964545797121)
              ·
                refine ⟨2251281760210473409347841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3001709013613964545797121 2251281760210473409347841)
                ·
                  refine ⟨1688461320157855057010881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2251281760210473409347841 1688461320157855057010881)
                  ·
                    refine ⟨1266345990118391292758161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1688461320157855057010881 1266345990118391292758161)
                    ·
                      refine ⟨949759492588793469568621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1266345990118391292758161 949759492588793469568621)
                      ·
                        rfl

theorem cell23_1849650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 2, 2, 2, 2, 2].length) (baseStart_1849650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1849650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1849650 prefixEnd_1849650 := by exact prefixLift 1849650
  have htrace : WordTrace (prefixWord ++ tailWord_1849650) baseStart_1849650 baseEnd_1849650 := by
    simpa [prefixWord, tailWord_1849650, baseEnd_1849650] using wordTrace_append hprefix tailTrace_1849650
  have hstable : (prefixWord ++ tailWord_1849650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1849650).length < 2 ^ (prefixWord ++ tailWord_1849650).sum := by decide
  have hdescent : baseEnd_1849650 < baseStart_1849650 := by decide
  rcases family_descends (prefixWord ++ tailWord_1849650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1849656 : List Nat := [2, 1, 2, 1, 3, 1, 6, 2, 5]
def baseStart_1849656 : Nat := 118140960795 + 1849656 * 2 ^ 59
def prefixEnd_1849656 : Nat := 4983230072969 + 3 ^ 40 * 1849656 * 2
def baseEnd_1849656 : Nat := 105529174830302271788177

theorem tailTrace_1849656 : CollatzResearch.WordTrace tailWord_1849656 prefixEnd_1849656 105529174830302271788177 := by
  unfold tailWord_1849656
  simp only [CollatzResearch.WordTrace]
  refine ⟨33731248293509841470068411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44974997724679788626757881 33731248293509841470068411)
  ·
    refine ⟨50596872440264762205102617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33731248293509841470068411 50596872440264762205102617)
    ·
      refine ⟨37947654330198571653826963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50596872440264762205102617 37947654330198571653826963)
      ·
        refine ⟨56921481495297857480740445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37947654330198571653826963 56921481495297857480740445)
        ·
          refine ⟨21345555560736696555277667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56921481495297857480740445 21345555560736696555277667)
          ·
            refine ⟨32018333341105044832916501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21345555560736696555277667 32018333341105044832916501)
            ·
              refine ⟨1500859375364298976542961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 32018333341105044832916501 1500859375364298976542961)
              ·
                refine ⟨1125644531523224232407221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1500859375364298976542961 1125644531523224232407221)
                ·
                  refine ⟨105529174830302271788177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1125644531523224232407221 105529174830302271788177)
                  ·
                    rfl

theorem cell23_1849656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 6, 2, 5].length) (baseStart_1849656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1849656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1849656 prefixEnd_1849656 := by exact prefixLift 1849656
  have htrace : WordTrace (prefixWord ++ tailWord_1849656) baseStart_1849656 baseEnd_1849656 := by
    simpa [prefixWord, tailWord_1849656, baseEnd_1849656] using wordTrace_append hprefix tailTrace_1849656
  have hstable : (prefixWord ++ tailWord_1849656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1849656).length < 2 ^ (prefixWord ++ tailWord_1849656).sum := by decide
  have hdescent : baseEnd_1849656 < baseStart_1849656 := by decide
  rcases family_descends (prefixWord ++ tailWord_1849656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1849689 : List Nat := [1, 2, 1, 2, 2, 2, 1, 1, 3, 6, 2]
def baseStart_1849689 : Nat := 118140960795 + 1849689 * 2 ^ 59
def prefixEnd_1849689 : Nat := 4983230072969 + 3 ^ 40 * 1849689 * 2
def baseEnd_1849689 : Nat := 949779518334318816980941

theorem tailTrace_1849689 : CollatzResearch.WordTrace tailWord_1849689 prefixEnd_1849689 949779518334318816980941 := by
  unfold tailWord_1849689
  simp only [CollatzResearch.WordTrace]
  refine ⟨67463700195900129576088121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44975800130600086384058747 67463700195900129576088121)
  ·
    refine ⟨50597775146925097182066091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67463700195900129576088121 50597775146925097182066091)
    ·
      refine ⟨75896662720387645773099137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50597775146925097182066091 75896662720387645773099137)
      ·
        refine ⟨56922497040290734329824353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75896662720387645773099137 56922497040290734329824353)
        ·
          refine ⟨42691872780218050747368265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56922497040290734329824353 42691872780218050747368265)
          ·
            refine ⟨32018904585163538060526199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42691872780218050747368265 32018904585163538060526199)
            ·
              refine ⟨48028356877745307090789299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32018904585163538060526199 48028356877745307090789299)
              ·
                refine ⟨72042535316617960636183949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48028356877745307090789299 72042535316617960636183949)
                ·
                  refine ⟨27015950743731735238568981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72042535316617960636183949 27015950743731735238568981)
                  ·
                    refine ⟨1266372691112425089307921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27015950743731735238568981 1266372691112425089307921)
                    ·
                      refine ⟨949779518334318816980941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1266372691112425089307921 949779518334318816980941)
                      ·
                        rfl

theorem cell23_1849689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 3, 6, 2].length) (baseStart_1849689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1849689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1849689 prefixEnd_1849689 := by exact prefixLift 1849689
  have htrace : WordTrace (prefixWord ++ tailWord_1849689) baseStart_1849689 baseEnd_1849689 := by
    simpa [prefixWord, tailWord_1849689, baseEnd_1849689] using wordTrace_append hprefix tailTrace_1849689
  have hstable : (prefixWord ++ tailWord_1849689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1849689).length < 2 ^ (prefixWord ++ tailWord_1849689).sum := by decide
  have hdescent : baseEnd_1849689 < baseStart_1849689 := by decide
  rcases family_descends (prefixWord ++ tailWord_1849689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1849699 : List Nat := [1, 1, 1, 5, 2, 1, 1, 2, 5, 4]
def baseStart_1849699 : Nat := 118140960795 + 1849699 * 2 ^ 59
def prefixEnd_1849699 : Nat := 4983230072969 + 3 ^ 40 * 1849699 * 2
def baseEnd_1849699 : Nat := 316594884380287925951965

theorem tailTrace_1849699 : CollatzResearch.WordTrace tailWord_1849699 prefixEnd_1849699 316594884380287925951965 := by
  unfold tailWord_1849699
  simp only [CollatzResearch.WordTrace]
  refine ⟨67464064925863901283952151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44976043283909267522634767 67464064925863901283952151)
  ·
    refine ⟨101196097388795851925928227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67464064925863901283952151 101196097388795851925928227)
    ·
      refine ⟨151794146083193777888892341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101196097388795851925928227 151794146083193777888892341)
      ·
        refine ⟨14230701195299416677083657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 151794146083193777888892341 14230701195299416677083657)
        ·
          refine ⟨10673025896474562507812743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14230701195299416677083657 10673025896474562507812743)
          ·
            refine ⟨16009538844711843761719115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10673025896474562507812743 16009538844711843761719115)
            ·
              refine ⟨24014308267067765642578673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16009538844711843761719115 24014308267067765642578673)
              ·
                refine ⟨18010731200300824231934005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24014308267067765642578673 18010731200300824231934005)
                ·
                  refine ⟨1688506050028202271743813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18010731200300824231934005 1688506050028202271743813)
                  ·
                    refine ⟨316594884380287925951965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1688506050028202271743813 316594884380287925951965)
                    ·
                      rfl

theorem cell23_1849699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 2, 5, 4].length) (baseStart_1849699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1849699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1849699 prefixEnd_1849699 := by exact prefixLift 1849699
  have htrace : WordTrace (prefixWord ++ tailWord_1849699) baseStart_1849699 baseEnd_1849699 := by
    simpa [prefixWord, tailWord_1849699, baseEnd_1849699] using wordTrace_append hprefix tailTrace_1849699
  have hstable : (prefixWord ++ tailWord_1849699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1849699).length < 2 ^ (prefixWord ++ tailWord_1849699).sum := by decide
  have hdescent : baseEnd_1849699 < baseStart_1849699 := by decide
  rcases family_descends (prefixWord ++ tailWord_1849699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1849780 : List Nat := [2, 5, 2, 2, 1, 1, 1, 3, 6]
def baseStart_1849780 : Nat := 118140960795 + 1849780 * 2 ^ 59
def prefixEnd_1849780 : Nat := 4983230072969 + 3 ^ 40 * 1849780 * 2
def baseEnd_1849780 : Nat := 105536249452653106771447

theorem tailTrace_1849780 : CollatzResearch.WordTrace tailWord_1849780 prefixEnd_1849780 105536249452653106771447 := by
  unfold tailWord_1849780
  simp only [CollatzResearch.WordTrace]
  refine ⟨33733509619285226058825397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44978012825713634745100529 33733509619285226058825397)
  ·
    refine ⟨3162516526807989943014881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 33733509619285226058825397 3162516526807989943014881)
    ·
      refine ⟨2371887395105992457261161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3162516526807989943014881 2371887395105992457261161)
      ·
        refine ⟨1778915546329494342945871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2371887395105992457261161 1778915546329494342945871)
        ·
          refine ⟨2668373319494241514418807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1778915546329494342945871 2668373319494241514418807)
          ·
            refine ⟨4002559979241362271628211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2668373319494241514418807 4002559979241362271628211)
            ·
              refine ⟨6003839968862043407442317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4002559979241362271628211 6003839968862043407442317)
              ·
                refine ⟨2251439988323266277790869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6003839968862043407442317 2251439988323266277790869)
                ·
                  refine ⟨105536249452653106771447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2251439988323266277790869 105536249452653106771447)
                  ·
                    rfl

theorem cell23_1849780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 3, 6].length) (baseStart_1849780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1849780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1849780 prefixEnd_1849780 := by exact prefixLift 1849780
  have htrace : WordTrace (prefixWord ++ tailWord_1849780) baseStart_1849780 baseEnd_1849780 := by
    simpa [prefixWord, tailWord_1849780, baseEnd_1849780] using wordTrace_append hprefix tailTrace_1849780
  have hstable : (prefixWord ++ tailWord_1849780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1849780).length < 2 ^ (prefixWord ++ tailWord_1849780).sum := by decide
  have hdescent : baseEnd_1849780 < baseStart_1849780 := by decide
  rcases family_descends (prefixWord ++ tailWord_1849780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1849823 : List Nat := [1, 1, 2, 3, 3, 3, 2, 2, 2, 4]
def baseStart_1849823 : Nat := 118140960795 + 1849823 * 2 ^ 59
def prefixEnd_1849823 : Nat := 4983230072969 + 3 ^ 40 * 1849823 * 2
def baseEnd_1849823 : Nat := 316616108247340430901775

theorem tailTrace_1849823 : CollatzResearch.WordTrace tailWord_1849823 prefixEnd_1849823 316616108247340430901775 := by
  unfold tailWord_1849823
  simp only [CollatzResearch.WordTrace]
  refine ⟨67468587577414670461466123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44979058384943113640977415 67468587577414670461466123)
  ·
    refine ⟨101202881366122005692199185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67468587577414670461466123 101202881366122005692199185)
    ·
      refine ⟨75902161024591504269149389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101202881366122005692199185 75902161024591504269149389)
      ·
        refine ⟨28463310384221814100931021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75902161024591504269149389 28463310384221814100931021)
        ·
          refine ⟨10673741394083180287849133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28463310384221814100931021 10673741394083180287849133)
          ·
            refine ⟨4002653022781192607943425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10673741394083180287849133 4002653022781192607943425)
            ·
              refine ⟨3001989767085894455957569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4002653022781192607943425 3001989767085894455957569)
              ·
                refine ⟨2251492325314420841968177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3001989767085894455957569 2251492325314420841968177)
                ·
                  refine ⟨1688619243985815631476133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2251492325314420841968177 1688619243985815631476133)
                  ·
                    refine ⟨316616108247340430901775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1688619243985815631476133 316616108247340430901775)
                    ·
                      rfl

theorem cell23_1849823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 2, 2, 2, 4].length) (baseStart_1849823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1849823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1849823 prefixEnd_1849823 := by exact prefixLift 1849823
  have htrace : WordTrace (prefixWord ++ tailWord_1849823) baseStart_1849823 baseEnd_1849823 := by
    simpa [prefixWord, tailWord_1849823, baseEnd_1849823] using wordTrace_append hprefix tailTrace_1849823
  have hstable : (prefixWord ++ tailWord_1849823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1849823).length < 2 ^ (prefixWord ++ tailWord_1849823).sum := by decide
  have hdescent : baseEnd_1849823 < baseStart_1849823 := by decide
  rcases family_descends (prefixWord ++ tailWord_1849823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1849859 : List Nat := [1, 1, 1, 3, 2, 1, 4, 1, 2, 2, 5]
def baseStart_1849859 : Nat := 118140960795 + 1849859 * 2 ^ 59
def prefixEnd_1849859 : Nat := 4983230072969 + 3 ^ 40 * 1849859 * 2
def baseEnd_1849859 : Nat := 949866810045583151855159

theorem tailTrace_1849859 : CollatzResearch.WordTrace tailWord_1849859 prefixEnd_1849859 949866810045583151855159 := by
  unfold tailWord_1849859
  simp only [CollatzResearch.WordTrace]
  refine ⟨67469900605284248609776631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44979933736856165739851087 67469900605284248609776631)
  ·
    refine ⟨101204850907926372914664947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67469900605284248609776631 101204850907926372914664947)
    ·
      refine ⟨151807276361889559371997421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101204850907926372914664947 151807276361889559371997421)
      ·
        refine ⟨56927728635708584764499033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151807276361889559371997421 56927728635708584764499033)
        ·
          refine ⟨42695796476781438573374275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56927728635708584764499033 42695796476781438573374275)
          ·
            refine ⟨64043694715172157860061413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42695796476781438573374275 64043694715172157860061413)
            ·
              refine ⟨12008192759094779598761515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64043694715172157860061413 12008192759094779598761515)
              ·
                refine ⟨18012289138642169398142273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12008192759094779598761515 18012289138642169398142273)
                ·
                  refine ⟨13509216853981627048606705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18012289138642169398142273 13509216853981627048606705)
                  ·
                    refine ⟨10131912640486220286455029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13509216853981627048606705 10131912640486220286455029)
                    ·
                      refine ⟨949866810045583151855159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10131912640486220286455029 949866810045583151855159)
                      ·
                        rfl

theorem cell23_1849859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 1, 2, 2, 5].length) (baseStart_1849859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1849859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1849859 prefixEnd_1849859 := by exact prefixLift 1849859
  have htrace : WordTrace (prefixWord ++ tailWord_1849859) baseStart_1849859 baseEnd_1849859 := by
    simpa [prefixWord, tailWord_1849859, baseEnd_1849859] using wordTrace_append hprefix tailTrace_1849859
  have hstable : (prefixWord ++ tailWord_1849859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1849859).length < 2 ^ (prefixWord ++ tailWord_1849859).sum := by decide
  have hdescent : baseEnd_1849859 < baseStart_1849859 := by decide
  rcases family_descends (prefixWord ++ tailWord_1849859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1849880 : List Nat := [2, 1, 2, 3, 3, 1, 3, 2, 2, 1, 3]
def baseStart_1849880 : Nat := 118140960795 + 1849880 * 2 ^ 59
def prefixEnd_1849880 : Nat := 4983230072969 + 3 ^ 40 * 1849880 * 2
def baseEnd_1849880 : Nat := 949877593139327569692563

theorem tailTrace_1849880 : CollatzResearch.WordTrace tailWord_1849880 prefixEnd_1849880 949877593139327569692563 := by
  unfold tailWord_1849880
  simp only [CollatzResearch.WordTrace]
  refine ⟨33735333269104084598145547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44980444358805446130860729 33735333269104084598145547)
  ·
    refine ⟨50602999903656126897218321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33735333269104084598145547 50602999903656126897218321)
    ·
      refine ⟨37952249927742095172913741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50602999903656126897218321 37952249927742095172913741)
      ·
        refine ⟨14232093722903285689842653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37952249927742095172913741 14232093722903285689842653)
        ·
          refine ⟨5337035146088732133690995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14232093722903285689842653 5337035146088732133690995)
          ·
            refine ⟨8005552719133098200536493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5337035146088732133690995 8005552719133098200536493)
            ·
              refine ⟨3002082269674911825201185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8005552719133098200536493 3002082269674911825201185)
              ·
                refine ⟨2251561702256183868900889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3002082269674911825201185 2251561702256183868900889)
                ·
                  refine ⟨1688671276692137901675667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2251561702256183868900889 1688671276692137901675667)
                  ·
                    refine ⟨2533006915038206852513501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1688671276692137901675667 2533006915038206852513501)
                    ·
                      refine ⟨949877593139327569692563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2533006915038206852513501 949877593139327569692563)
                      ·
                        rfl

theorem cell23_1849880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 3, 2, 2, 1, 3].length) (baseStart_1849880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1849880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1849880 prefixEnd_1849880 := by exact prefixLift 1849880
  have htrace : WordTrace (prefixWord ++ tailWord_1849880) baseStart_1849880 baseEnd_1849880 := by
    simpa [prefixWord, tailWord_1849880, baseEnd_1849880] using wordTrace_append hprefix tailTrace_1849880
  have hstable : (prefixWord ++ tailWord_1849880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1849880).length < 2 ^ (prefixWord ++ tailWord_1849880).sum := by decide
  have hdescent : baseEnd_1849880 < baseStart_1849880 := by decide
  rcases family_descends (prefixWord ++ tailWord_1849880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1849906 : List Nat := [3, 2, 1, 1, 2, 1, 2, 2, 2, 4, 3]
def baseStart_1849906 : Nat := 118140960795 + 1849906 * 2 ^ 59
def prefixEnd_1849906 : Nat := 4983230072969 + 3 ^ 40 * 1849906 * 2
def baseEnd_1849906 : Nat := 949890943636344467967443

theorem tailTrace_1849906 : CollatzResearch.WordTrace tailWord_1849906 prefixEnd_1849906 949890943636344467967443 := by
  unfold tailWord_1849906
  simp only [CollatzResearch.WordTrace]
  refine ⟨16867903709028493909184393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44981076557409317091158381 16867903709028493909184393)
  ·
    refine ⟨12650927781771370431888295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16867903709028493909184393 12650927781771370431888295)
    ·
      refine ⟨18976391672657055647832443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12650927781771370431888295 18976391672657055647832443)
      ·
        refine ⟨28464587508985583471748665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18976391672657055647832443 28464587508985583471748665)
        ·
          refine ⟨21348440631739187603811499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28464587508985583471748665 21348440631739187603811499)
          ·
            refine ⟨32022660947608781405717249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21348440631739187603811499 32022660947608781405717249)
            ·
              refine ⟨24016995710706586054287937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32022660947608781405717249 24016995710706586054287937)
              ·
                refine ⟨18012746783029939540715953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24016995710706586054287937 18012746783029939540715953)
                ·
                  refine ⟨13509560087272454655536965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18012746783029939540715953 13509560087272454655536965)
                  ·
                    refine ⟨2533042516363585247913181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13509560087272454655536965 2533042516363585247913181)
                    ·
                      refine ⟨949890943636344467967443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2533042516363585247913181 949890943636344467967443)
                      ·
                        rfl

theorem cell23_1849906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 2, 2, 4, 3].length) (baseStart_1849906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1849906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1849906 prefixEnd_1849906 := by exact prefixLift 1849906
  have htrace : WordTrace (prefixWord ++ tailWord_1849906) baseStart_1849906 baseEnd_1849906 := by
    simpa [prefixWord, tailWord_1849906, baseEnd_1849906] using wordTrace_append hprefix tailTrace_1849906
  have hstable : (prefixWord ++ tailWord_1849906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1849906).length < 2 ^ (prefixWord ++ tailWord_1849906).sum := by decide
  have hdescent : baseEnd_1849906 < baseStart_1849906 := by decide
  rcases family_descends (prefixWord ++ tailWord_1849906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1849929 : List Nat := [1, 2, 1, 1, 2, 2, 1, 1, 2, 4, 6]
def baseStart_1849929 : Nat := 118140960795 + 1849929 * 2 ^ 59
def prefixEnd_1849929 : Nat := 4983230072969 + 3 ^ 40 * 1849929 * 2
def baseEnd_1849929 : Nat := 949902753691397877979837

theorem tailTrace_1849929 : CollatzResearch.WordTrace tailWord_1849929 prefixEnd_1849929 949902753691397877979837 := by
  unfold tailWord_1849929
  simp only [CollatzResearch.WordTrace]
  refine ⟨67472453715030650564824841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44981635810020433709883227 67472453715030650564824841)
  ·
    refine ⟨50604340286272987923618631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67472453715030650564824841 50604340286272987923618631)
    ·
      refine ⟨75906510429409481885427947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50604340286272987923618631 75906510429409481885427947)
      ·
        refine ⟨113859765644114222828141921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75906510429409481885427947 113859765644114222828141921)
        ·
          refine ⟨85394824233085667121106441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113859765644114222828141921 85394824233085667121106441)
          ·
            refine ⟨64046118174814250340829831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85394824233085667121106441 64046118174814250340829831)
            ·
              refine ⟨96069177262221375511244747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64046118174814250340829831 96069177262221375511244747)
              ·
                refine ⟨144103765893332063266867121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96069177262221375511244747 144103765893332063266867121)
                ·
                  refine ⟨108077824419999047450150341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 144103765893332063266867121 108077824419999047450150341)
                  ·
                    refine ⟨20264592078749821396903189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 108077824419999047450150341 20264592078749821396903189)
                    ·
                      refine ⟨949902753691397877979837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 20264592078749821396903189 949902753691397877979837)
                      ·
                        rfl

theorem cell23_1849929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 4, 6].length) (baseStart_1849929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1849929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1849929 prefixEnd_1849929 := by exact prefixLift 1849929
  have htrace : WordTrace (prefixWord ++ tailWord_1849929) baseStart_1849929 baseEnd_1849929 := by
    simpa [prefixWord, tailWord_1849929, baseEnd_1849929] using wordTrace_append hprefix tailTrace_1849929
  have hstable : (prefixWord ++ tailWord_1849929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1849929).length < 2 ^ (prefixWord ++ tailWord_1849929).sum := by decide
  have hdescent : baseEnd_1849929 < baseStart_1849929 := by decide
  rcases family_descends (prefixWord ++ tailWord_1849929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1849936 : List Nat := [2, 1, 1, 1, 1, 3, 2, 4, 2, 3, 3]
def baseStart_1849936 : Nat := 118140960795 + 1849936 * 2 ^ 59
def prefixEnd_1849936 : Nat := 4983230072969 + 3 ^ 40 * 1849936 * 2
def baseEnd_1849936 : Nat := 949906348055979350592305

theorem tailTrace_1849936 : CollatzResearch.WordTrace tailWord_1849936 prefixEnd_1849936 949906348055979350592305 := by
  unfold tailWord_1849936
  simp only [CollatzResearch.WordTrace]
  refine ⟨33736354513002645380164831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44981806017336860506886441 33736354513002645380164831)
  ·
    refine ⟨50604531769503968070247247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33736354513002645380164831 50604531769503968070247247)
    ·
      refine ⟨75906797654255952105370871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50604531769503968070247247 75906797654255952105370871)
      ·
        refine ⟨113860196481383928158056307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75906797654255952105370871 113860196481383928158056307)
        ·
          refine ⟨170790294722075892237084461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113860196481383928158056307 170790294722075892237084461)
          ·
            refine ⟨64046360520778459588906673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 170790294722075892237084461 64046360520778459588906673)
            ·
              refine ⟨48034770390583844691680005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64046360520778459588906673 48034770390583844691680005)
              ·
                refine ⟨9006519448234470879690001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48034770390583844691680005 9006519448234470879690001)
                ·
                  refine ⟨6754889586175853159767501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9006519448234470879690001 6754889586175853159767501)
                  ·
                    refine ⟨2533083594815944934912813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6754889586175853159767501 2533083594815944934912813)
                    ·
                      refine ⟨949906348055979350592305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2533083594815944934912813 949906348055979350592305)
                      ·
                        rfl

theorem cell23_1849936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 4, 2, 3, 3].length) (baseStart_1849936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1849936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1849936 prefixEnd_1849936 := by exact prefixLift 1849936
  have htrace : WordTrace (prefixWord ++ tailWord_1849936) baseStart_1849936 baseEnd_1849936 := by
    simpa [prefixWord, tailWord_1849936, baseEnd_1849936] using wordTrace_append hprefix tailTrace_1849936
  have hstable : (prefixWord ++ tailWord_1849936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1849936).length < 2 ^ (prefixWord ++ tailWord_1849936).sum := by decide
  have hdescent : baseEnd_1849936 < baseStart_1849936 := by decide
  rcases family_descends (prefixWord ++ tailWord_1849936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1849956 : List Nat := [2, 3, 1, 1, 2, 2, 1, 2, 4, 5]
def baseStart_1849956 : Nat := 118140960795 + 1849956 * 2 ^ 59
def prefixEnd_1849956 : Nat := 4983230072969 + 3 ^ 40 * 1849956 * 2
def baseEnd_1849956 : Nat := 316638872556356424114071

theorem tailTrace_1849956 : CollatzResearch.WordTrace tailWord_1849956 prefixEnd_1849956 316638872556356424114071 := by
  unfold tailWord_1849956
  simp only [CollatzResearch.WordTrace]
  refine ⟨33736719242966417088028861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44982292323955222784038481 33736719242966417088028861)
  ·
    refine ⟨12651269716112406408010823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33736719242966417088028861 12651269716112406408010823)
    ·
      refine ⟨18976904574168609612016235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12651269716112406408010823 18976904574168609612016235)
      ·
        refine ⟨28465356861252914418024353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18976904574168609612016235 28465356861252914418024353)
        ·
          refine ⟨21349017645939685813518265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28465356861252914418024353 21349017645939685813518265)
          ·
            refine ⟨16011763234454764360138699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21349017645939685813518265 16011763234454764360138699)
            ·
              refine ⟨24017644851682146540208049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16011763234454764360138699 24017644851682146540208049)
              ·
                refine ⟨18013233638761609905156037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24017644851682146540208049 18013233638761609905156037)
                ·
                  refine ⟨3377481307267801857216757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18013233638761609905156037 3377481307267801857216757)
                  ·
                    refine ⟨316638872556356424114071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3377481307267801857216757 316638872556356424114071)
                    ·
                      rfl

theorem cell23_1849956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 2, 4, 5].length) (baseStart_1849956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1849956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1849956 prefixEnd_1849956 := by exact prefixLift 1849956
  have htrace : WordTrace (prefixWord ++ tailWord_1849956) baseStart_1849956 baseEnd_1849956 := by
    simpa [prefixWord, tailWord_1849956, baseEnd_1849956] using wordTrace_append hprefix tailTrace_1849956
  have hstable : (prefixWord ++ tailWord_1849956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1849956).length < 2 ^ (prefixWord ++ tailWord_1849956).sum := by decide
  have hdescent : baseEnd_1849956 < baseStart_1849956 := by decide
  rcases family_descends (prefixWord ++ tailWord_1849956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1849976 : List Nat := [2, 1, 2, 1, 1, 1, 2, 2, 6, 1, 4]
def baseStart_1849976 : Nat := 118140960795 + 1849976 * 2 ^ 59
def prefixEnd_1849976 : Nat := 4983230072969 + 3 ^ 40 * 1849976 * 2
def baseEnd_1849976 : Nat := 949926887282159194092121

theorem tailTrace_1849976 : CollatzResearch.WordTrace tailWord_1849976 prefixEnd_1849976 949926887282159194092121 := by
  unfold tailWord_1849976
  simp only [CollatzResearch.WordTrace]
  refine ⟨33737083972930188795892891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44982778630573585061190521 33737083972930188795892891)
  ·
    refine ⟨50605625959395283193839337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33737083972930188795892891 50605625959395283193839337)
    ·
      refine ⟨37954219469546462395379503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50605625959395283193839337 37954219469546462395379503)
      ·
        refine ⟨56931329204319693593069255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37954219469546462395379503 56931329204319693593069255)
        ·
          refine ⟨85396993806479540389603883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56931329204319693593069255 85396993806479540389603883)
          ·
            refine ⟨128095490709719310584405825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85396993806479540389603883 128095490709719310584405825)
            ·
              refine ⟨96071618032289482938304369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128095490709719310584405825 96071618032289482938304369)
              ·
                refine ⟨72053713524217112203728277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96071618032289482938304369 72053713524217112203728277)
                ·
                  refine ⟨3377517821447677134549763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 72053713524217112203728277 3377517821447677134549763)
                  ·
                    refine ⟨5066276732171515701824645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3377517821447677134549763 5066276732171515701824645)
                    ·
                      refine ⟨949926887282159194092121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5066276732171515701824645 949926887282159194092121)
                      ·
                        rfl

theorem cell23_1849976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 6, 1, 4].length) (baseStart_1849976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1849976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1849976 prefixEnd_1849976 := by exact prefixLift 1849976
  have htrace : WordTrace (prefixWord ++ tailWord_1849976) baseStart_1849976 baseEnd_1849976 := by
    simpa [prefixWord, tailWord_1849976, baseEnd_1849976] using wordTrace_append hprefix tailTrace_1849976
  have hstable : (prefixWord ++ tailWord_1849976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1849976).length < 2 ^ (prefixWord ++ tailWord_1849976).sum := by decide
  have hdescent : baseEnd_1849976 < baseStart_1849976 := by decide
  rcases family_descends (prefixWord ++ tailWord_1849976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1849993 : List Nat := [1, 2, 1, 1, 4, 1, 1, 4, 2, 4, 2]
def baseStart_1849993 : Nat := 118140960795 + 1849993 * 2 ^ 59
def prefixEnd_1849993 : Nat := 4983230072969 + 3 ^ 40 * 1849993 * 2
def baseEnd_1849993 : Nat := 949935616453285627579543

theorem tailTrace_1849993 : CollatzResearch.WordTrace tailWord_1849993 prefixEnd_1849993 949935616453285627579543 := by
  unfold tailWord_1849993
  simp only [CollatzResearch.WordTrace]
  refine ⟨67474787986798789495154633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44983191991199192996769755 67474787986798789495154633)
  ·
    refine ⟨50606090990099092121365975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67474787986798789495154633 50606090990099092121365975)
    ·
      refine ⟨75909136485148638182048963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50606090990099092121365975 75909136485148638182048963)
      ·
        refine ⟨113863704727722957273073445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75909136485148638182048963 113863704727722957273073445)
        ·
          refine ⟨21349444636448054488701271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 113863704727722957273073445 21349444636448054488701271)
          ·
            refine ⟨32024166954672081733051907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21349444636448054488701271 32024166954672081733051907)
            ·
              refine ⟨48036250432008122599577861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32024166954672081733051907 48036250432008122599577861)
              ·
                refine ⟨9006796956001522987420849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48036250432008122599577861 9006796956001522987420849)
                ·
                  refine ⟨6755097717001142240565637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9006796956001522987420849 6755097717001142240565637)
                  ·
                    refine ⟨1266580821937714170106057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6755097717001142240565637 1266580821937714170106057)
                    ·
                      refine ⟨949935616453285627579543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1266580821937714170106057 949935616453285627579543)
                      ·
                        rfl

theorem cell23_1849993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 4, 2, 4, 2].length) (baseStart_1849993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1849993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1849993 prefixEnd_1849993 := by exact prefixLift 1849993
  have htrace : WordTrace (prefixWord ++ tailWord_1849993) baseStart_1849993 baseEnd_1849993 := by
    simpa [prefixWord, tailWord_1849993, baseEnd_1849993] using wordTrace_append hprefix tailTrace_1849993
  have hstable : (prefixWord ++ tailWord_1849993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1849993).length < 2 ^ (prefixWord ++ tailWord_1849993).sum := by decide
  have hdescent : baseEnd_1849993 < baseStart_1849993 := by decide
  rcases family_descends (prefixWord ++ tailWord_1849993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1849994 : List Nat := [3, 1, 2, 3, 4, 1, 2, 2, 5]
def baseStart_1849994 : Nat := 118140960795 + 1849994 * 2 ^ 59
def prefixEnd_1849994 : Nat := 4983230072969 + 3 ^ 40 * 1849994 * 2
def baseEnd_1849994 : Nat := 105548458881548902629671

theorem tailTrace_1849994 : CollatzResearch.WordTrace tailWord_1849994 prefixEnd_1849994 105548458881548902629671 := by
  unfold tailWord_1849994
  simp only [CollatzResearch.WordTrace]
  refine ⟨16868706114948791666485259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44983216306530111110627357 16868706114948791666485259)
  ·
    refine ⟨25303059172423187499727889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16868706114948791666485259 25303059172423187499727889)
    ·
      refine ⟨18977294379317390624795917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25303059172423187499727889 18977294379317390624795917)
      ·
        refine ⟨7116485392244021484298469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18977294379317390624795917 7116485392244021484298469)
        ·
          refine ⟨1334341011045754028305963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7116485392244021484298469 1334341011045754028305963)
          ·
            refine ⟨2001511516568631042458945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1334341011045754028305963 2001511516568631042458945)
            ·
              refine ⟨1501133637426473281844209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2001511516568631042458945 1501133637426473281844209)
              ·
                refine ⟨1125850228069854961383157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1501133637426473281844209 1125850228069854961383157)
                ·
                  refine ⟨105548458881548902629671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1125850228069854961383157 105548458881548902629671)
                  ·
                    rfl

theorem cell23_1849994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 2, 2, 5].length) (baseStart_1849994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1849994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1849994 prefixEnd_1849994 := by exact prefixLift 1849994
  have htrace : WordTrace (prefixWord ++ tailWord_1849994) baseStart_1849994 baseEnd_1849994 := by
    simpa [prefixWord, tailWord_1849994, baseEnd_1849994] using wordTrace_append hprefix tailTrace_1849994
  have hstable : (prefixWord ++ tailWord_1849994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1849994).length < 2 ^ (prefixWord ++ tailWord_1849994).sum := by decide
  have hdescent : baseEnd_1849994 < baseStart_1849994 := by decide
  rcases family_descends (prefixWord ++ tailWord_1849994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1850013 : List Nat := [1, 4, 2, 1, 1, 1, 2, 2, 4, 2, 3]
def baseStart_1850013 : Nat := 118140960795 + 1850013 * 2 ^ 59
def prefixEnd_1850013 : Nat := 4983230072969 + 3 ^ 40 * 1850013 * 2
def baseEnd_1850013 : Nat := 949945886066375549329451

theorem tailTrace_1850013 : CollatzResearch.WordTrace tailWord_1850013 prefixEnd_1850013 949945886066375549329451 := by
  unfold tailWord_1850013
  simp only [CollatzResearch.WordTrace]
  refine ⟨67475517446726332910882693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44983678297817555273921795 67475517446726332910882693)
  ·
    refine ⟨12651659521261187420790505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67475517446726332910882693 12651659521261187420790505)
    ·
      refine ⟨9488744640945890565592879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12651659521261187420790505 9488744640945890565592879)
      ·
        refine ⟨14233116961418835848389319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9488744640945890565592879 14233116961418835848389319)
        ·
          refine ⟨21349675442128253772583979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14233116961418835848389319 21349675442128253772583979)
          ·
            refine ⟨32024513163192380658875969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21349675442128253772583979 32024513163192380658875969)
            ·
              refine ⟨24018384872394285494156977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32024513163192380658875969 24018384872394285494156977)
              ·
                refine ⟨18013788654295714120617733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24018384872394285494156977 18013788654295714120617733)
                ·
                  refine ⟨3377585372680446397615825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18013788654295714120617733 3377585372680446397615825)
                  ·
                    refine ⟨2533189029510334798211869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3377585372680446397615825 2533189029510334798211869)
                    ·
                      refine ⟨949945886066375549329451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2533189029510334798211869 949945886066375549329451)
                      ·
                        rfl

theorem cell23_1850013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 2, 4, 2, 3].length) (baseStart_1850013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1850013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1850013 prefixEnd_1850013 := by exact prefixLift 1850013
  have htrace : WordTrace (prefixWord ++ tailWord_1850013) baseStart_1850013 baseEnd_1850013 := by
    simpa [prefixWord, tailWord_1850013, baseEnd_1850013] using wordTrace_append hprefix tailTrace_1850013
  have hstable : (prefixWord ++ tailWord_1850013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1850013).length < 2 ^ (prefixWord ++ tailWord_1850013).sum := by decide
  have hdescent : baseEnd_1850013 < baseStart_1850013 := by decide
  rcases family_descends (prefixWord ++ tailWord_1850013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1850037 : List Nat := [1, 3, 3, 3, 1, 1, 1, 5, 1, 4]
def baseStart_1850037 : Nat := 118140960795 + 1850037 * 2 ^ 59
def prefixEnd_1850037 : Nat := 4983230072969 + 3 ^ 40 * 1850037 * 2
def baseEnd_1850037 : Nat := 316652736534027818476447

theorem tailTrace_1850037 : CollatzResearch.WordTrace tailWord_1850037 prefixEnd_1850037 316652736534027818476447 := by
  unfold tailWord_1850037
  simp only [CollatzResearch.WordTrace]
  refine ⟨67476392798639385009756365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44984261865759590006504243 67476392798639385009756365)
  ·
    refine ⟨25303647299489769378658637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67476392798639385009756365 25303647299489769378658637)
    ·
      refine ⟨9488867737308663516996989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25303647299489769378658637 9488867737308663516996989)
      ·
        refine ⟨3558325401490748818873871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9488867737308663516996989 3558325401490748818873871)
        ·
          refine ⟨5337488102236123228310807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3558325401490748818873871 5337488102236123228310807)
          ·
            refine ⟨8006232153354184842466211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5337488102236123228310807 8006232153354184842466211)
            ·
              refine ⟨12009348230031277263699317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8006232153354184842466211 12009348230031277263699317)
              ·
                refine ⟨1125876396565432243471811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12009348230031277263699317 1125876396565432243471811)
                ·
                  refine ⟨1688814594848148365207717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1125876396565432243471811 1688814594848148365207717)
                  ·
                    refine ⟨316652736534027818476447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1688814594848148365207717 316652736534027818476447)
                    ·
                      rfl

theorem cell23_1850037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 5, 1, 4].length) (baseStart_1850037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1850037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1850037 prefixEnd_1850037 := by exact prefixLift 1850037
  have htrace : WordTrace (prefixWord ++ tailWord_1850037) baseStart_1850037 baseEnd_1850037 := by
    simpa [prefixWord, tailWord_1850037, baseEnd_1850037] using wordTrace_append hprefix tailTrace_1850037
  have hstable : (prefixWord ++ tailWord_1850037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1850037).length < 2 ^ (prefixWord ++ tailWord_1850037).sum := by decide
  have hdescent : baseEnd_1850037 < baseStart_1850037 := by decide
  rcases family_descends (prefixWord ++ tailWord_1850037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1850053 : List Nat := [1, 3, 1, 1, 1, 1, 2, 1, 5, 5, 2]
def baseStart_1850053 : Nat := 118140960795 + 1850053 * 2 ^ 59
def prefixEnd_1850053 : Nat := 4983230072969 + 3 ^ 40 * 1850053 * 2
def baseEnd_1850053 : Nat := 949966425292555392829267

theorem tailTrace_1850053 : CollatzResearch.WordTrace tailWord_1850053 prefixEnd_1850053 949966425292555392829267 := by
  unfold tailWord_1850053
  simp only [CollatzResearch.WordTrace]
  refine ⟨67476976366581419742338813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44984650911054279828225875 67476976366581419742338813)
  ·
    refine ⟨25303866137468032403377055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67476976366581419742338813 25303866137468032403377055)
    ·
      refine ⟨37955799206202048605065583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25303866137468032403377055 37955799206202048605065583)
      ·
        refine ⟨56933698809303072907598375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37955799206202048605065583 56933698809303072907598375)
        ·
          refine ⟨85400548213954609361397563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56933698809303072907598375 85400548213954609361397563)
          ·
            refine ⟨128100822320931914042096345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85400548213954609361397563 128100822320931914042096345)
            ·
              refine ⟨96075616740698935531572259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128100822320931914042096345 96075616740698935531572259)
              ·
                refine ⟨144113425111048403297358389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96075616740698935531572259 144113425111048403297358389)
                ·
                  refine ⟨13510633604160787809127349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 144113425111048403297358389 13510633604160787809127349)
                  ·
                    refine ⟨1266621900390073857105689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13510633604160787809127349 1266621900390073857105689)
                    ·
                      refine ⟨949966425292555392829267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1266621900390073857105689 949966425292555392829267)
                      ·
                        rfl

theorem cell23_1850053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 5, 5, 2].length) (baseStart_1850053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1850053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1850053 prefixEnd_1850053 := by exact prefixLift 1850053
  have htrace : WordTrace (prefixWord ++ tailWord_1850053) baseStart_1850053 baseEnd_1850053 := by
    simpa [prefixWord, tailWord_1850053, baseEnd_1850053] using wordTrace_append hprefix tailTrace_1850053
  have hstable : (prefixWord ++ tailWord_1850053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1850053).length < 2 ^ (prefixWord ++ tailWord_1850053).sum := by decide
  have hdescent : baseEnd_1850053 < baseStart_1850053 := by decide
  rcases family_descends (prefixWord ++ tailWord_1850053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1850093 : List Nat := [1, 5, 1, 2, 1, 1, 2, 1, 3, 6]
def baseStart_1850093 : Nat := 118140960795 + 1850093 * 2 ^ 59
def prefixEnd_1850093 : Nat := 4983230072969 + 3 ^ 40 * 1850093 * 2
def baseEnd_1850093 : Nat := 316662321506245078776361

theorem tailTrace_1850093 : CollatzResearch.WordTrace tailWord_1850093 prefixEnd_1850093 316662321506245078776361 := by
  unfold tailWord_1850093
  simp only [CollatzResearch.WordTrace]
  refine ⟨67478435286436506573794933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44985623524291004382529955 67478435286436506573794933)
  ·
    refine ⟨6326103308103422491293275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 67478435286436506573794933 6326103308103422491293275)
    ·
      refine ⟨9489154962155133736939913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6326103308103422491293275 9489154962155133736939913)
      ·
        refine ⟨7116866221616350302704935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9489154962155133736939913 7116866221616350302704935)
        ·
          refine ⟨10675299332424525454057403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7116866221616350302704935 10675299332424525454057403)
          ·
            refine ⟨16012948998636788181086105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10675299332424525454057403 16012948998636788181086105)
            ·
              refine ⟨12009711748977591135814579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16012948998636788181086105 12009711748977591135814579)
              ·
                refine ⟨18014567623466386703721869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12009711748977591135814579 18014567623466386703721869)
                ·
                  refine ⟨6755462858799895013895701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18014567623466386703721869 6755462858799895013895701)
                  ·
                    refine ⟨316662321506245078776361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6755462858799895013895701 316662321506245078776361)
                    ·
                      rfl

theorem cell23_1850093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 1, 3, 6].length) (baseStart_1850093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1850093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1850093 prefixEnd_1850093 := by exact prefixLift 1850093
  have htrace : WordTrace (prefixWord ++ tailWord_1850093) baseStart_1850093 baseEnd_1850093 := by
    simpa [prefixWord, tailWord_1850093, baseEnd_1850093] using wordTrace_append hprefix tailTrace_1850093
  have hstable : (prefixWord ++ tailWord_1850093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1850093).length < 2 ^ (prefixWord ++ tailWord_1850093).sum := by decide
  have hdescent : baseEnd_1850093 < baseStart_1850093 := by decide
  rcases family_descends (prefixWord ++ tailWord_1850093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1850094 : List Nat := [4, 1, 2, 1, 1, 3, 3, 3, 1, 1, 3]
def baseStart_1850094 : Nat := 118140960795 + 1850094 * 2 ^ 59
def prefixEnd_1850094 : Nat := 4983230072969 + 3 ^ 40 * 1850094 * 2
def baseEnd_1850094 : Nat := 949987477999389732416579

theorem tailTrace_1850094 : CollatzResearch.WordTrace tailWord_1850094 prefixEnd_1850094 949987477999389732416579 := by
  unfold tailWord_1850094
  simp only [CollatzResearch.WordTrace]
  refine ⟨8434808969929110468072667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44985647839621922496387557 8434808969929110468072667)
  ·
    refine ⟨12652213454893665702109001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8434808969929110468072667 12652213454893665702109001)
    ·
      refine ⟨9489160091170249276581751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12652213454893665702109001 9489160091170249276581751)
      ·
        refine ⟨14233740136755373914872627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9489160091170249276581751 14233740136755373914872627)
        ·
          refine ⟨21350610205133060872308941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14233740136755373914872627 21350610205133060872308941)
          ·
            refine ⟨8006478826924897827115853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21350610205133060872308941 8006478826924897827115853)
            ·
              refine ⟨3002429560096836685168445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8006478826924897827115853 3002429560096836685168445)
              ·
                refine ⟨1125911085036313756938167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3002429560096836685168445 1125911085036313756938167)
                ·
                  refine ⟨1688866627554470635407251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1125911085036313756938167 1688866627554470635407251)
                  ·
                    refine ⟨2533299941331705953110877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1688866627554470635407251 2533299941331705953110877)
                    ·
                      refine ⟨949987477999389732416579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2533299941331705953110877 949987477999389732416579)
                      ·
                        rfl

theorem cell23_1850094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 3, 3, 1, 1, 3].length) (baseStart_1850094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1850094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1850094 prefixEnd_1850094 := by exact prefixLift 1850094
  have htrace : WordTrace (prefixWord ++ tailWord_1850094) baseStart_1850094 baseEnd_1850094 := by
    simpa [prefixWord, tailWord_1850094, baseEnd_1850094] using wordTrace_append hprefix tailTrace_1850094
  have hstable : (prefixWord ++ tailWord_1850094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1850094).length < 2 ^ (prefixWord ++ tailWord_1850094).sum := by decide
  have hdescent : baseEnd_1850094 < baseStart_1850094 := by decide
  rcases family_descends (prefixWord ++ tailWord_1850094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1850103 : List Nat := [1, 1, 3, 1, 1, 1, 3, 2, 5, 2, 3]
def baseStart_1850103 : Nat := 118140960795 + 1850103 * 2 ^ 59
def prefixEnd_1850103 : Nat := 4983230072969 + 3 ^ 40 * 1850103 * 2
def baseEnd_1850103 : Nat := 949992099325280197204037

theorem tailTrace_1850103 : CollatzResearch.WordTrace tailWord_1850103 prefixEnd_1850103 949992099325280197204037 := by
  unfold tailWord_1850103
  simp only [CollatzResearch.WordTrace]
  refine ⟨67478800016400278281658963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44985866677600185521105975 67478800016400278281658963)
  ·
    refine ⟨101218200024600417422488445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67478800016400278281658963 101218200024600417422488445)
    ·
      refine ⟨37956825009225156533433167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101218200024600417422488445 37956825009225156533433167)
      ·
        refine ⟨56935237513837734800149751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37956825009225156533433167 56935237513837734800149751)
        ·
          refine ⟨85402856270756602200224627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56935237513837734800149751 85402856270756602200224627)
          ·
            refine ⟨128104284406134903300336941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85402856270756602200224627 128104284406134903300336941)
            ·
              refine ⟨48039106652300588737626353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 128104284406134903300336941 48039106652300588737626353)
              ·
                refine ⟨36029329989225441553219765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48039106652300588737626353 36029329989225441553219765)
                ·
                  refine ⟨3377749686489885145614353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36029329989225441553219765 3377749686489885145614353)
                  ·
                    refine ⟨2533312264867413859210765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3377749686489885145614353 2533312264867413859210765)
                    ·
                      refine ⟨949992099325280197204037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2533312264867413859210765 949992099325280197204037)
                      ·
                        rfl

theorem cell23_1850103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 2, 5, 2, 3].length) (baseStart_1850103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1850103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1850103 prefixEnd_1850103 := by exact prefixLift 1850103
  have htrace : WordTrace (prefixWord ++ tailWord_1850103) baseStart_1850103 baseEnd_1850103 := by
    simpa [prefixWord, tailWord_1850103, baseEnd_1850103] using wordTrace_append hprefix tailTrace_1850103
  have hstable : (prefixWord ++ tailWord_1850103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1850103).length < 2 ^ (prefixWord ++ tailWord_1850103).sum := by decide
  have hdescent : baseEnd_1850103 < baseStart_1850103 := by decide
  rcases family_descends (prefixWord ++ tailWord_1850103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1850106 : List Nat := [3, 1, 1, 1, 1, 3, 13]
def baseStart_1850106 : Nat := 118140960795 + 1850106 * 2 ^ 59
def prefixEnd_1850106 : Nat := 4983230072969 + 3 ^ 40 * 1850106 * 2
def baseEnd_1850106 : Nat := 11728316540336341795883

theorem tailTrace_1850106 : CollatzResearch.WordTrace tailWord_1850106 prefixEnd_1850106 11728316540336341795883 := by
  unfold tailWord_1850106
  simp only [CollatzResearch.WordTrace]
  refine ⟨16869727358847352448504543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44985939623592939862678781 16869727358847352448504543)
  ·
    refine ⟨25304591038271028672756815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16869727358847352448504543 25304591038271028672756815)
    ·
      refine ⟨37956886557406543009135223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25304591038271028672756815 37956886557406543009135223)
      ·
        refine ⟨56935329836109814513702835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37956886557406543009135223 56935329836109814513702835)
        ·
          refine ⟨85402994754164721770554253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56935329836109814513702835 85402994754164721770554253)
          ·
            refine ⟨32026123032811770663957845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85402994754164721770554253 32026123032811770663957845)
            ·
              refine ⟨11728316540336341795883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 32026123032811770663957845 11728316540336341795883)
              ·
                rfl

theorem cell23_1850106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 13].length) (baseStart_1850106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1850106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1850106 prefixEnd_1850106 := by exact prefixLift 1850106
  have htrace : WordTrace (prefixWord ++ tailWord_1850106) baseStart_1850106 baseEnd_1850106 := by
    simpa [prefixWord, tailWord_1850106, baseEnd_1850106] using wordTrace_append hprefix tailTrace_1850106
  have hstable : (prefixWord ++ tailWord_1850106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1850106).length < 2 ^ (prefixWord ++ tailWord_1850106).sum := by decide
  have hdescent : baseEnd_1850106 < baseStart_1850106 := by decide
  rcases family_descends (prefixWord ++ tailWord_1850106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1850154 : List Nat := [3, 1, 4, 3, 1, 2, 1, 1, 1, 1, 5]
def baseStart_1850154 : Nat := 118140960795 + 1850154 * 2 ^ 59
def prefixEnd_1850154 : Nat := 4983230072969 + 3 ^ 40 * 1850154 * 2
def baseEnd_1850154 : Nat := 950018286838659497666303

theorem tailTrace_1850154 : CollatzResearch.WordTrace tailWord_1850154 prefixEnd_1850154 950018286838659497666303 := by
  unfold tailWord_1850154
  simp only [CollatzResearch.WordTrace]
  refine ⟨16870165034803878497941379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44987106759477009327843677 16870165034803878497941379)
  ·
    refine ⟨25305247552205817746912069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16870165034803878497941379 25305247552205817746912069)
    ·
      refine ⟨4744733916038590827546013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25305247552205817746912069 4744733916038590827546013)
      ·
        refine ⟨1779275218514471560329755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4744733916038590827546013 1779275218514471560329755)
        ·
          refine ⟨2668912827771707340494633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1779275218514471560329755 2668912827771707340494633)
          ·
            refine ⟨2001684620828780505370975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2668912827771707340494633 2001684620828780505370975)
            ·
              refine ⟨3002526931243170758056463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2001684620828780505370975 3002526931243170758056463)
              ·
                refine ⟨4503790396864756137084695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3002526931243170758056463 4503790396864756137084695)
                ·
                  refine ⟨6755685595297134205627043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4503790396864756137084695 6755685595297134205627043)
                  ·
                    refine ⟨10133528392945701308440565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6755685595297134205627043 10133528392945701308440565)
                    ·
                      refine ⟨950018286838659497666303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10133528392945701308440565 950018286838659497666303)
                      ·
                        rfl

theorem cell23_1850154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_1850154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1850154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1850154 prefixEnd_1850154 := by exact prefixLift 1850154
  have htrace : WordTrace (prefixWord ++ tailWord_1850154) baseStart_1850154 baseEnd_1850154 := by
    simpa [prefixWord, tailWord_1850154, baseEnd_1850154] using wordTrace_append hprefix tailTrace_1850154
  have hstable : (prefixWord ++ tailWord_1850154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1850154).length < 2 ^ (prefixWord ++ tailWord_1850154).sum := by decide
  have hdescent : baseEnd_1850154 < baseStart_1850154 := by decide
  rcases family_descends (prefixWord ++ tailWord_1850154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1850157 : List Nat := [1, 5, 3, 2, 2, 10]
def baseStart_1850157 : Nat := 118140960795 + 1850157 * 2 ^ 59
def prefixEnd_1850157 : Nat := 4983230072969 + 3 ^ 40 * 1850157 * 2
def baseEnd_1850157 : Nat := 3909546614323551382423

theorem tailTrace_1850157 : CollatzResearch.WordTrace tailWord_1850157 prefixEnd_1850157 3909546614323551382423 := by
  unfold tailWord_1850157
  simp only [CollatzResearch.WordTrace]
  refine ⟨67480769558204645504124725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44987179705469763669416483 67480769558204645504124725)
  ·
    refine ⟨6326322146081685516011693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 67480769558204645504124725 6326322146081685516011693)
    ·
      refine ⟨2372370804780632068504385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6326322146081685516011693 2372370804780632068504385)
      ·
        refine ⟨1779278103585474051378289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2372370804780632068504385 1779278103585474051378289)
        ·
          refine ⟨1334458577689105538533717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1779278103585474051378289 1334458577689105538533717)
          ·
            refine ⟨3909546614323551382423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1334458577689105538533717 3909546614323551382423)
            ·
              rfl

theorem cell23_1850157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 10].length) (baseStart_1850157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1850157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1850157 prefixEnd_1850157 := by exact prefixLift 1850157
  have htrace : WordTrace (prefixWord ++ tailWord_1850157) baseStart_1850157 baseEnd_1850157 := by
    simpa [prefixWord, tailWord_1850157, baseEnd_1850157] using wordTrace_append hprefix tailTrace_1850157
  have hstable : (prefixWord ++ tailWord_1850157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1850157).length < 2 ^ (prefixWord ++ tailWord_1850157).sum := by decide
  have hdescent : baseEnd_1850157 < baseStart_1850157 := by decide
  rcases family_descends (prefixWord ++ tailWord_1850157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1850167 : List Nat := [1, 1, 3, 1, 2, 1, 6, 2, 2, 1, 3]
def baseStart_1850167 : Nat := 118140960795 + 1850167 * 2 ^ 59
def prefixEnd_1850167 : Nat := 4983230072969 + 3 ^ 40 * 1850167 * 2
def baseEnd_1850167 : Nat := 950024962087167946803743

theorem tailTrace_1850167 : CollatzResearch.WordTrace tailWord_1850167 prefixEnd_1850167 950024962087167946803743 := by
  unfold tailWord_1850167
  simp only [CollatzResearch.WordTrace]
  refine ⟨67481134288168417211988755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44987422858778944807992503 67481134288168417211988755)
  ·
    refine ⟨101221701432252625817983133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67481134288168417211988755 101221701432252625817983133)
    ·
      refine ⟨37958138037094734681743675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101221701432252625817983133 37958138037094734681743675)
      ·
        refine ⟨56937207055642102022615513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37958138037094734681743675 56937207055642102022615513)
        ·
          refine ⟨42702905291731576516961635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56937207055642102022615513 42702905291731576516961635)
          ·
            refine ⟨64054357937597364775442453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42702905291731576516961635 64054357937597364775442453)
            ·
              refine ⟨3002548028324876473848865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 64054357937597364775442453 3002548028324876473848865)
              ·
                refine ⟨2251911021243657355386649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3002548028324876473848865 2251911021243657355386649)
                ·
                  refine ⟨1688933265932743016539987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2251911021243657355386649 1688933265932743016539987)
                  ·
                    refine ⟨2533399898899114524809981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1688933265932743016539987 2533399898899114524809981)
                    ·
                      refine ⟨950024962087167946803743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2533399898899114524809981 950024962087167946803743)
                      ·
                        rfl

theorem cell23_1850167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 6, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 6, 2, 2, 1, 3].length) (baseStart_1850167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1850167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1850167 prefixEnd_1850167 := by exact prefixLift 1850167
  have htrace : WordTrace (prefixWord ++ tailWord_1850167) baseStart_1850167 baseEnd_1850167 := by
    simpa [prefixWord, tailWord_1850167, baseEnd_1850167] using wordTrace_append hprefix tailTrace_1850167
  have hstable : (prefixWord ++ tailWord_1850167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1850167).length < 2 ^ (prefixWord ++ tailWord_1850167).sum := by decide
  have hdescent : baseEnd_1850167 < baseStart_1850167 := by decide
  rcases family_descends (prefixWord ++ tailWord_1850167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1850207 : List Nat := [1, 1, 2, 3, 1, 3, 2, 2, 4, 2, 2]
def baseStart_1850207 : Nat := 118140960795 + 1850207 * 2 ^ 59
def prefixEnd_1850207 : Nat := 4983230072969 + 3 ^ 40 * 1850207 * 2
def baseEnd_1850207 : Nat := 950045501313347790303559

theorem tailTrace_1850207 : CollatzResearch.WordTrace tailWord_1850207 prefixEnd_1850207 950045501313347790303559 := by
  unfold tailWord_1850207
  simp only [CollatzResearch.WordTrace]
  refine ⟨67482593208023504043444875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44988395472015669362296583 67482593208023504043444875)
  ·
    refine ⟨101223889812035256065167313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67482593208023504043444875 101223889812035256065167313)
    ·
      refine ⟨75917917359026442048875485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101223889812035256065167313 75917917359026442048875485)
      ·
        refine ⟨28469219009634915768328307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75917917359026442048875485 28469219009634915768328307)
        ·
          refine ⟨42703828514452373652492461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28469219009634915768328307 42703828514452373652492461)
          ·
            refine ⟨16013935692919640119684673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42703828514452373652492461 16013935692919640119684673)
            ·
              refine ⟨12010451769689730089763505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16013935692919640119684673 12010451769689730089763505)
              ·
                refine ⟨9007838827267297567322629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12010451769689730089763505 9007838827267297567322629)
                ·
                  refine ⟨1688969780112618293872993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9007838827267297567322629 1688969780112618293872993)
                  ·
                    refine ⟨1266727335084463720404745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1688969780112618293872993 1266727335084463720404745)
                    ·
                      refine ⟨950045501313347790303559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1266727335084463720404745 950045501313347790303559)
                      ·
                        rfl

theorem cell23_1850207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 2, 4, 2, 2].length) (baseStart_1850207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1850207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1850207 prefixEnd_1850207 := by exact prefixLift 1850207
  have htrace : WordTrace (prefixWord ++ tailWord_1850207) baseStart_1850207 baseEnd_1850207 := by
    simpa [prefixWord, tailWord_1850207, baseEnd_1850207] using wordTrace_append hprefix tailTrace_1850207
  have hstable : (prefixWord ++ tailWord_1850207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1850207).length < 2 ^ (prefixWord ++ tailWord_1850207).sum := by decide
  have hdescent : baseEnd_1850207 < baseStart_1850207 := by decide
  rcases family_descends (prefixWord ++ tailWord_1850207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1850211 : List Nat := [1, 1, 1, 5, 3, 3, 2, 1, 1, 3, 2]
def baseStart_1850211 : Nat := 118140960795 + 1850211 * 2 ^ 59
def prefixEnd_1850211 : Nat := 4983230072969 + 3 ^ 40 * 1850211 * 2
def baseEnd_1850211 : Nat := 950047555235965774653541

theorem tailTrace_1850211 : CollatzResearch.WordTrace tailWord_1850211 prefixEnd_1850211 950047555235965774653541 := by
  unfold tailWord_1850211
  simp only [CollatzResearch.WordTrace]
  refine ⟨67482739100009012726590487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44988492733339341817726991 67482739100009012726590487)
  ·
    refine ⟨101224108650013519089885731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67482739100009012726590487 101224108650013519089885731)
    ·
      refine ⟨151836162975020278634828597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101224108650013519089885731 151836162975020278634828597)
      ·
        refine ⟨14234640278908151122015181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 151836162975020278634828597 14234640278908151122015181)
        ·
          refine ⟨5337990104590556670755693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14234640278908151122015181 5337990104590556670755693)
          ·
            refine ⟨2001746289221458751533385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5337990104590556670755693 2001746289221458751533385)
            ·
              refine ⟨1501309716916094063650039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2001746289221458751533385 1501309716916094063650039)
              ·
                refine ⟨2251964575374141095475059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1501309716916094063650039 2251964575374141095475059)
                ·
                  refine ⟨3377946863061211643212589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2251964575374141095475059 3377946863061211643212589)
                  ·
                    refine ⟨1266730073647954366204721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3377946863061211643212589 1266730073647954366204721)
                    ·
                      refine ⟨950047555235965774653541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1266730073647954366204721 950047555235965774653541)
                      ·
                        rfl

theorem cell23_1850211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 2, 1, 1, 3, 2].length) (baseStart_1850211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1850211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1850211 prefixEnd_1850211 := by exact prefixLift 1850211
  have htrace : WordTrace (prefixWord ++ tailWord_1850211) baseStart_1850211 baseEnd_1850211 := by
    simpa [prefixWord, tailWord_1850211, baseEnd_1850211] using wordTrace_append hprefix tailTrace_1850211
  have hstable : (prefixWord ++ tailWord_1850211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1850211).length < 2 ^ (prefixWord ++ tailWord_1850211).sum := by decide
  have hdescent : baseEnd_1850211 < baseStart_1850211 := by decide
  rcases family_descends (prefixWord ++ tailWord_1850211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1850224 : List Nat := [2, 1, 1, 1, 4, 1, 5, 2, 2, 2, 2]
def baseStart_1850224 : Nat := 118140960795 + 1850224 * 2 ^ 59
def prefixEnd_1850224 : Nat := 4983230072969 + 3 ^ 40 * 1850224 * 2
def baseEnd_1850224 : Nat := 950054230484474223790981

theorem tailTrace_1850224 : CollatzResearch.WordTrace tailWord_1850224 prefixEnd_1850224 950054230484474223790981 := by
  unfold tailWord_1850224
  simp only [CollatzResearch.WordTrace]
  refine ⟨33741606624480957973406863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44988808832641277297875817 33741606624480957973406863)
  ·
    refine ⟨50612409936721436960110295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33741606624480957973406863 50612409936721436960110295)
    ·
      refine ⟨75918614905082155440165443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50612409936721436960110295 75918614905082155440165443)
      ·
        refine ⟨113877922357623233160248165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75918614905082155440165443 113877922357623233160248165)
        ·
          refine ⟨21352110442054356217546531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 113877922357623233160248165 21352110442054356217546531)
          ·
            refine ⟨32028165663081534326319797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21352110442054356217546531 32028165663081534326319797)
            ·
              refine ⟨3002640530913893843092481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32028165663081534326319797 3002640530913893843092481)
              ·
                refine ⟨2251980398185420382319361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3002640530913893843092481 2251980398185420382319361)
                ·
                  refine ⟨1688985298639065286739521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2251980398185420382319361 1688985298639065286739521)
                  ·
                    refine ⟨1266738973979298965054641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1688985298639065286739521 1266738973979298965054641)
                    ·
                      refine ⟨950054230484474223790981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1266738973979298965054641 950054230484474223790981)
                      ·
                        rfl

theorem cell23_1850224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 5, 2, 2, 2, 2].length) (baseStart_1850224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1850224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1850224 prefixEnd_1850224 := by exact prefixLift 1850224
  have htrace : WordTrace (prefixWord ++ tailWord_1850224) baseStart_1850224 baseEnd_1850224 := by
    simpa [prefixWord, tailWord_1850224, baseEnd_1850224] using wordTrace_append hprefix tailTrace_1850224
  have hstable : (prefixWord ++ tailWord_1850224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1850224).length < 2 ^ (prefixWord ++ tailWord_1850224).sum := by decide
  have hdescent : baseEnd_1850224 < baseStart_1850224 := by decide
  rcases family_descends (prefixWord ++ tailWord_1850224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1850243 : List Nat := [1, 1, 1, 3, 4, 1, 1, 1, 3, 7]
def baseStart_1850243 : Nat := 118140960795 + 1850243 * 2 ^ 59
def prefixEnd_1850243 : Nat := 4983230072969 + 3 ^ 40 * 1850243 * 2
def baseEnd_1850243 : Nat := 316687995538969883151131

theorem tailTrace_1850243 : CollatzResearch.WordTrace tailWord_1850243 prefixEnd_1850243 316687995538969883151131 := by
  unfold tailWord_1850243
  simp only [CollatzResearch.WordTrace]
  refine ⟨67483906235893082191755383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44989270823928721461170255 67483906235893082191755383)
  ·
    refine ⟨101225859353839623287633075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67483906235893082191755383 101225859353839623287633075)
    ·
      refine ⟨151838789030759434931449613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101225859353839623287633075 151838789030759434931449613)
      ·
        refine ⟨56939545886534788099293605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151838789030759434931449613 56939545886534788099293605)
        ·
          refine ⟨10676164853725272768617551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56939545886534788099293605 10676164853725272768617551)
          ·
            refine ⟨16014247280587909152926327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10676164853725272768617551 16014247280587909152926327)
            ·
              refine ⟨24021370920881863729389491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16014247280587909152926327 24021370920881863729389491)
              ·
                refine ⟨36032056381322795594084237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24021370920881863729389491 36032056381322795594084237)
                ·
                  refine ⟨13512021142996048347781589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36032056381322795594084237 13512021142996048347781589)
                  ·
                    refine ⟨316687995538969883151131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13512021142996048347781589 316687995538969883151131)
                    ·
                      rfl

theorem cell23_1850243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 1, 3, 7].length) (baseStart_1850243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1850243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1850243 prefixEnd_1850243 := by exact prefixLift 1850243
  have htrace : WordTrace (prefixWord ++ tailWord_1850243) baseStart_1850243 baseEnd_1850243 := by
    simpa [prefixWord, tailWord_1850243, baseEnd_1850243] using wordTrace_append hprefix tailTrace_1850243
  have hstable : (prefixWord ++ tailWord_1850243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1850243).length < 2 ^ (prefixWord ++ tailWord_1850243).sum := by decide
  have hdescent : baseEnd_1850243 < baseStart_1850243 := by decide
  rcases family_descends (prefixWord ++ tailWord_1850243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1850260 : List Nat := [2, 4, 2, 1, 1, 1, 1, 3, 1, 7]
def baseStart_1850260 : Nat := 118140960795 + 1850260 * 2 ^ 59
def prefixEnd_1850260 : Nat := 4983230072969 + 3 ^ 40 * 1850260 * 2
def baseEnd_1850260 : Nat := 316690905262678694313605

theorem tailTrace_1850260 : CollatzResearch.WordTrace tailWord_1850260 prefixEnd_1850260 316690905262678694313605 := by
  unfold tailWord_1850260
  simp only [CollatzResearch.WordTrace]
  refine ⟨33742263138415747047562117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44989684184554329396749489 33742263138415747047562117)
  ·
    refine ⟨6326674338452952571417897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33742263138415747047562117 6326674338452952571417897)
    ·
      refine ⟨4745005753839714428563423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6326674338452952571417897 4745005753839714428563423)
      ·
        refine ⟨7117508630759571642845135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4745005753839714428563423 7117508630759571642845135)
        ·
          refine ⟨10676262946139357464267703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7117508630759571642845135 10676262946139357464267703)
          ·
            refine ⟨16014394419209036196401555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10676262946139357464267703 16014394419209036196401555)
            ·
              refine ⟨24021591628813554294602333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16014394419209036196401555 24021591628813554294602333)
              ·
                refine ⟨9008096860805082860475875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24021591628813554294602333 9008096860805082860475875)
                ·
                  refine ⟨13512145291207624290713813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9008096860805082860475875 13512145291207624290713813)
                  ·
                    refine ⟨316690905262678694313605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13512145291207624290713813 316690905262678694313605)
                    ·
                      rfl

theorem cell23_1850260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 3, 1, 7].length) (baseStart_1850260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1850260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1850260 prefixEnd_1850260 := by exact prefixLift 1850260
  have htrace : WordTrace (prefixWord ++ tailWord_1850260) baseStart_1850260 baseEnd_1850260 := by
    simpa [prefixWord, tailWord_1850260, baseEnd_1850260] using wordTrace_append hprefix tailTrace_1850260
  have hstable : (prefixWord ++ tailWord_1850260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1850260).length < 2 ^ (prefixWord ++ tailWord_1850260).sum := by decide
  have hdescent : baseEnd_1850260 < baseStart_1850260 := by decide
  rcases family_descends (prefixWord ++ tailWord_1850260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1850283 : List Nat := [1, 1, 1, 1, 2, 1, 1, 5, 2, 3, 5]
def baseStart_1850283 : Nat := 118140960795 + 1850283 * 2 ^ 59
def prefixEnd_1850283 : Nat := 4983230072969 + 3 ^ 40 * 1850283 * 2
def baseEnd_1850283 : Nat := 950084525843089492953209

theorem tailTrace_1850283 : CollatzResearch.WordTrace tailWord_1850283 prefixEnd_1850283 950084525843089492953209 := by
  unfold tailWord_1850283
  simp only [CollatzResearch.WordTrace]
  refine ⟨67485365155748169023211503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44990243437165446015474335 67485365155748169023211503)
  ·
    refine ⟨101228047733622253534817255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67485365155748169023211503 101228047733622253534817255)
    ·
      refine ⟨151842071600433380302225883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101228047733622253534817255 151842071600433380302225883)
      ·
        refine ⟨227763107400650070453338825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151842071600433380302225883 227763107400650070453338825)
        ·
          refine ⟨170822330550487552840004119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 227763107400650070453338825 170822330550487552840004119)
          ·
            refine ⟨256233495825731329260006179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170822330550487552840004119 256233495825731329260006179)
            ·
              refine ⟨384350243738596993890009269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 256233495825731329260006179 384350243738596993890009269)
              ·
                refine ⟨36032835350493468177188369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 384350243738596993890009269 36032835350493468177188369)
                ·
                  refine ⟨27024626512870101132891277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36032835350493468177188369 27024626512870101132891277)
                  ·
                    refine ⟨10134234942326287924834229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27024626512870101132891277 10134234942326287924834229)
                    ·
                      refine ⟨950084525843089492953209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10134234942326287924834229 950084525843089492953209)
                      ·
                        rfl

theorem cell23_1850283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 5, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 5, 2, 3, 5].length) (baseStart_1850283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1850283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1850283 prefixEnd_1850283 := by exact prefixLift 1850283
  have htrace : WordTrace (prefixWord ++ tailWord_1850283) baseStart_1850283 baseEnd_1850283 := by
    simpa [prefixWord, tailWord_1850283, baseEnd_1850283] using wordTrace_append hprefix tailTrace_1850283
  have hstable : (prefixWord ++ tailWord_1850283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1850283).length < 2 ^ (prefixWord ++ tailWord_1850283).sum := by decide
  have hdescent : baseEnd_1850283 < baseStart_1850283 := by decide
  rcases family_descends (prefixWord ++ tailWord_1850283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1850303 : List Nat := [1, 1, 2, 2, 2, 1, 2, 2, 10]
def baseStart_1850303 : Nat := 118140960795 + 1850303 * 2 ^ 59
def prefixEnd_1850303 : Nat := 4983230072969 + 3 ^ 40 * 1850303 * 2
def baseEnd_1850303 : Nat := 105566088384019934967013

theorem tailTrace_1850303 : CollatzResearch.WordTrace tailWord_1850303 prefixEnd_1850303 105566088384019934967013 := by
  unfold tailWord_1850303
  simp only [CollatzResearch.WordTrace]
  refine ⟨67486094615675712438939563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44990729743783808292626375 67486094615675712438939563)
  ·
    refine ⟨101229141923513568658409345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67486094615675712438939563 101229141923513568658409345)
    ·
      refine ⟨75921856442635176493807009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101229141923513568658409345 75921856442635176493807009)
      ·
        refine ⟨56941392331976382370355257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75921856442635176493807009 56941392331976382370355257)
        ·
          refine ⟨42706044248982286777766443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56941392331976382370355257 42706044248982286777766443)
          ·
            refine ⟨64059066373473430166649665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42706044248982286777766443 64059066373473430166649665)
            ·
              refine ⟨48044299780105072624987249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64059066373473430166649665 48044299780105072624987249)
              ·
                refine ⟨36033224835078804468740437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48044299780105072624987249 36033224835078804468740437)
                ·
                  refine ⟨105566088384019934967013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 36033224835078804468740437 105566088384019934967013)
                  ·
                    rfl

theorem cell23_1850303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 2, 10].length) (baseStart_1850303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1850303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1850303 prefixEnd_1850303 := by exact prefixLift 1850303
  have htrace : WordTrace (prefixWord ++ tailWord_1850303) baseStart_1850303 baseEnd_1850303 := by
    simpa [prefixWord, tailWord_1850303, baseEnd_1850303] using wordTrace_append hprefix tailTrace_1850303
  have hstable : (prefixWord ++ tailWord_1850303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1850303).length < 2 ^ (prefixWord ++ tailWord_1850303).sum := by decide
  have hdescent : baseEnd_1850303 < baseStart_1850303 := by decide
  rcases family_descends (prefixWord ++ tailWord_1850303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1850313 : List Nat := [1, 2, 1, 1, 2, 1, 2, 1, 2, 1, 9]
def baseStart_1850313 : Nat := 118140960795 + 1850313 * 2 ^ 59
def prefixEnd_1850313 : Nat := 4983230072969 + 3 ^ 40 * 1850313 * 2
def baseEnd_1850313 : Nat := 950099930262724375578071

theorem tailTrace_1850313 : CollatzResearch.WordTrace tailWord_1850313 prefixEnd_1850313 950099930262724375578071 := by
  unfold tailWord_1850313
  simp only [CollatzResearch.WordTrace]
  refine ⟨67486459345639484146803593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44990972897092989431202395 67486459345639484146803593)
  ·
    refine ⟨50614844509229613110102695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67486459345639484146803593 50614844509229613110102695)
    ·
      refine ⟨75922266763844419665154043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50614844509229613110102695 75922266763844419665154043)
      ·
        refine ⟨113883400145766629497731065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75922266763844419665154043 113883400145766629497731065)
        ·
          refine ⟨85412550109324972123298299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113883400145766629497731065 85412550109324972123298299)
          ·
            refine ⟨128118825163987458184947449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85412550109324972123298299 128118825163987458184947449)
            ·
              refine ⟨96089118872990593638710587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128118825163987458184947449 96089118872990593638710587)
              ·
                refine ⟨144133678309485890458065881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96089118872990593638710587 144133678309485890458065881)
                ·
                  refine ⟨108100258732114417843549411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 144133678309485890458065881 108100258732114417843549411)
                  ·
                    refine ⟨162150388098171626765324117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 108100258732114417843549411 162150388098171626765324117)
                    ·
                      refine ⟨950099930262724375578071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 162150388098171626765324117 950099930262724375578071)
                      ·
                        rfl

theorem cell23_1850313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 1, 9].length) (baseStart_1850313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1850313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1850313 prefixEnd_1850313 := by exact prefixLift 1850313
  have htrace : WordTrace (prefixWord ++ tailWord_1850313) baseStart_1850313 baseEnd_1850313 := by
    simpa [prefixWord, tailWord_1850313, baseEnd_1850313] using wordTrace_append hprefix tailTrace_1850313
  have hstable : (prefixWord ++ tailWord_1850313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1850313).length < 2 ^ (prefixWord ++ tailWord_1850313).sum := by decide
  have hdescent : baseEnd_1850313 < baseStart_1850313 := by decide
  rcases family_descends (prefixWord ++ tailWord_1850313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1850364 : List Nat := [2, 2, 2, 1, 2, 4, 1, 2, 3, 1, 3]
def baseStart_1850364 : Nat := 118140960795 + 1850364 * 2 ^ 59
def prefixEnd_1850364 : Nat := 4983230072969 + 3 ^ 40 * 1850364 * 2
def baseEnd_1850364 : Nat := 950126117776103676040337

theorem tailTrace_1850364 : CollatzResearch.WordTrace tailWord_1850364 prefixEnd_1850364 950126117776103676040337 := by
  unfold tailWord_1850364
  simp only [CollatzResearch.WordTrace]
  refine ⟨33744159734227359928455073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44992212978969813237940097 33744159734227359928455073)
  ·
    refine ⟨25308119800670519946341305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33744159734227359928455073 25308119800670519946341305)
    ·
      refine ⟨18981089850502889959755979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25308119800670519946341305 18981089850502889959755979)
      ·
        refine ⟨28471634775754334939633969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18981089850502889959755979 28471634775754334939633969)
        ·
          refine ⟨21353726081815751204725477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28471634775754334939633969 21353726081815751204725477)
          ·
            refine ⟨4003823640340453350886027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21353726081815751204725477 4003823640340453350886027)
            ·
              refine ⟨6005735460510680026329041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4003823640340453350886027 6005735460510680026329041)
              ·
                refine ⟨4504301595383010019746781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6005735460510680026329041 4504301595383010019746781)
                ·
                  refine ⟨1689113098268628757405043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4504301595383010019746781 1689113098268628757405043)
                  ·
                    refine ⟨2533669647402943136107565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1689113098268628757405043 2533669647402943136107565)
                    ·
                      refine ⟨950126117776103676040337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2533669647402943136107565 950126117776103676040337)
                      ·
                        rfl

theorem cell23_1850364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 2, 3, 1, 3].length) (baseStart_1850364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1850364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1850364 prefixEnd_1850364 := by exact prefixLift 1850364
  have htrace : WordTrace (prefixWord ++ tailWord_1850364) baseStart_1850364 baseEnd_1850364 := by
    simpa [prefixWord, tailWord_1850364, baseEnd_1850364] using wordTrace_append hprefix tailTrace_1850364
  have hstable : (prefixWord ++ tailWord_1850364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1850364).length < 2 ^ (prefixWord ++ tailWord_1850364).sum := by decide
  have hdescent : baseEnd_1850364 < baseStart_1850364 := by decide
  rcases family_descends (prefixWord ++ tailWord_1850364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1850424 : List Nat := [2, 1, 2, 1, 5, 1, 1, 4, 1, 2, 3]
def baseStart_1850424 : Nat := 118140960795 + 1850424 * 2 ^ 59
def prefixEnd_1850424 : Nat := 4983230072969 + 3 ^ 40 * 1850424 * 2
def baseEnd_1850424 : Nat := 950156926615373441290061

theorem tailTrace_1850424 : CollatzResearch.WordTrace tailWord_1850424 prefixEnd_1850424 950156926615373441290061 := by
  unfold tailWord_1850424
  simp only [CollatzResearch.WordTrace]
  refine ⟨33745253924118675052047163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44993671898824900069396217 33745253924118675052047163)
  ·
    refine ⟨50617880886178012578070745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33745253924118675052047163 50617880886178012578070745)
    ·
      refine ⟨37963410664633509433553059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50617880886178012578070745 37963410664633509433553059)
      ·
        refine ⟨56945115996950264150329589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37963410664633509433553059 56945115996950264150329589)
        ·
          refine ⟨5338604624714087264093399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 56945115996950264150329589 5338604624714087264093399)
          ·
            refine ⟨8007906937071130896140099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5338604624714087264093399 8007906937071130896140099)
            ·
              refine ⟨12011860405606696344210149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8007906937071130896140099 12011860405606696344210149)
              ·
                refine ⟨2252223826051255564539403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12011860405606696344210149 2252223826051255564539403)
                ·
                  refine ⟨3378335739076883346809105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2252223826051255564539403 3378335739076883346809105)
                  ·
                    refine ⟨2533751804307662510106829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3378335739076883346809105 2533751804307662510106829)
                    ·
                      refine ⟨950156926615373441290061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2533751804307662510106829 950156926615373441290061)
                      ·
                        rfl

theorem cell23_1850424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 4, 1, 2, 3].length) (baseStart_1850424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1850424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1850424 prefixEnd_1850424 := by exact prefixLift 1850424
  have htrace : WordTrace (prefixWord ++ tailWord_1850424) baseStart_1850424 baseEnd_1850424 := by
    simpa [prefixWord, tailWord_1850424, baseEnd_1850424] using wordTrace_append hprefix tailTrace_1850424
  have hstable : (prefixWord ++ tailWord_1850424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1850424).length < 2 ^ (prefixWord ++ tailWord_1850424).sum := by decide
  have hdescent : baseEnd_1850424 < baseStart_1850424 := by decide
  rcases family_descends (prefixWord ++ tailWord_1850424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1850437 : List Nat := [1, 3, 1, 1, 1, 3, 2, 4, 1, 3, 3]
def baseStart_1850437 : Nat := 118140960795 + 1850437 * 2 ^ 59
def prefixEnd_1850437 : Nat := 4983230072969 + 3 ^ 40 * 1850437 * 2
def baseEnd_1850437 : Nat := 950163601863881890427501

theorem tailTrace_1850437 : CollatzResearch.WordTrace tailWord_1850437 prefixEnd_1850437 950163601863881890427501 := by
  unfold tailWord_1850437
  simp only [CollatzResearch.WordTrace]
  refine ⟨67490981997190253324317565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44993987998126835549545043 67490981997190253324317565)
  ·
    refine ⟨25309118248946344996619087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67490981997190253324317565 25309118248946344996619087)
    ·
      refine ⟨37963677373419517494928631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25309118248946344996619087 37963677373419517494928631)
      ·
        refine ⟨56945516060129276242392947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37963677373419517494928631 56945516060129276242392947)
        ·
          refine ⟨85418274090193914363589421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56945516060129276242392947 85418274090193914363589421)
          ·
            refine ⟨32031852783822717886346033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85418274090193914363589421 32031852783822717886346033)
            ·
              refine ⟨24023889587867038414759525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32031852783822717886346033 24023889587867038414759525)
              ·
                refine ⟨4504479297725069702767411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24023889587867038414759525 4504479297725069702767411)
                ·
                  refine ⟨6756718946587604554151117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4504479297725069702767411 6756718946587604554151117)
                  ·
                    refine ⟨2533769604970351707806669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6756718946587604554151117 2533769604970351707806669)
                    ·
                      refine ⟨950163601863881890427501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2533769604970351707806669 950163601863881890427501)
                      ·
                        rfl

theorem cell23_1850437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 4, 1, 3, 3].length) (baseStart_1850437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1850437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1850437 prefixEnd_1850437 := by exact prefixLift 1850437
  have htrace : WordTrace (prefixWord ++ tailWord_1850437) baseStart_1850437 baseEnd_1850437 := by
    simpa [prefixWord, tailWord_1850437, baseEnd_1850437] using wordTrace_append hprefix tailTrace_1850437
  have hstable : (prefixWord ++ tailWord_1850437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1850437).length < 2 ^ (prefixWord ++ tailWord_1850437).sum := by decide
  have hdescent : baseEnd_1850437 < baseStart_1850437 := by decide
  rcases family_descends (prefixWord ++ tailWord_1850437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1850464 : List Nat := [2, 1, 1, 3, 2, 2, 2, 2, 3, 3, 2]
def baseStart_1850464 : Nat := 118140960795 + 1850464 * 2 ^ 59
def prefixEnd_1850464 : Nat := 4983230072969 + 3 ^ 40 * 1850464 * 2
def baseEnd_1850464 : Nat := 950177465841553284789877

theorem tailTrace_1850464 : CollatzResearch.WordTrace tailWord_1850464 prefixEnd_1850464 950177465841553284789877 := by
  unfold tailWord_1850464
  simp only [CollatzResearch.WordTrace]
  refine ⟨33745983384046218467775223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44994644512061624623700297 33745983384046218467775223)
  ·
    refine ⟨50618975076069327701662835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33745983384046218467775223 50618975076069327701662835)
    ·
      refine ⟨75928462614103991552494253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50618975076069327701662835 75928462614103991552494253)
      ·
        refine ⟨28473173480288996832185345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75928462614103991552494253 28473173480288996832185345)
        ·
          refine ⟨21354880110216747624139009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28473173480288996832185345 21354880110216747624139009)
          ·
            refine ⟨16016160082662560718104257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21354880110216747624139009 16016160082662560718104257)
            ·
              refine ⟨12012120061996920538578193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16016160082662560718104257 12012120061996920538578193)
              ·
                refine ⟨9009090046497690403933645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12012120061996920538578193 9009090046497690403933645)
                ·
                  refine ⟨3378408767436633901475117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9009090046497690403933645 3378408767436633901475117)
                  ·
                    refine ⟨1266903287788737713053169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3378408767436633901475117 1266903287788737713053169)
                    ·
                      refine ⟨950177465841553284789877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1266903287788737713053169 950177465841553284789877)
                      ·
                        rfl

theorem cell23_1850464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 2, 3, 3, 2].length) (baseStart_1850464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1850464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1850464 prefixEnd_1850464 := by exact prefixLift 1850464
  have htrace : WordTrace (prefixWord ++ tailWord_1850464) baseStart_1850464 baseEnd_1850464 := by
    simpa [prefixWord, tailWord_1850464, baseEnd_1850464] using wordTrace_append hprefix tailTrace_1850464
  have hstable : (prefixWord ++ tailWord_1850464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1850464).length < 2 ^ (prefixWord ++ tailWord_1850464).sum := by decide
  have hdescent : baseEnd_1850464 < baseStart_1850464 := by decide
  rcases family_descends (prefixWord ++ tailWord_1850464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1850471 : List Nat := [1, 1, 5, 1, 1, 4, 1, 3, 2, 1, 3]
def baseStart_1850471 : Nat := 118140960795 + 1850471 * 2 ^ 59
def prefixEnd_1850471 : Nat := 4983230072969 + 3 ^ 40 * 1850471 * 2
def baseEnd_1850471 : Nat := 950181060206134757402345

theorem tailTrace_1850471 : CollatzResearch.WordTrace tailWord_1850471 prefixEnd_1850471 950181060206134757402345 := by
  unfold tailWord_1850471
  simp only [CollatzResearch.WordTrace]
  refine ⟨67492222079067077131055267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44994814719378051420703511 67492222079067077131055267)
  ·
    refine ⟨101238333118600615696582901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67492222079067077131055267 101238333118600615696582901)
    ·
      refine ⟨9491093729868807721554647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 101238333118600615696582901 9491093729868807721554647)
      ·
        refine ⟨14236640594803211582331971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9491093729868807721554647 14236640594803211582331971)
        ·
          refine ⟨21354960892204817373497957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14236640594803211582331971 21354960892204817373497957)
          ·
            refine ⟨4004055167288403257530867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21354960892204817373497957 4004055167288403257530867)
            ·
              refine ⟨6006082750932604886296301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4004055167288403257530867 6006082750932604886296301)
              ·
                refine ⟨2252281031599726832361113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6006082750932604886296301 2252281031599726832361113)
                ·
                  refine ⟨1689210773699795124270835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2252281031599726832361113 1689210773699795124270835)
                  ·
                    refine ⟨2533816160549692686406253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1689210773699795124270835 2533816160549692686406253)
                    ·
                      refine ⟨950181060206134757402345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2533816160549692686406253 950181060206134757402345)
                      ·
                        rfl

theorem cell23_1850471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 3, 2, 1, 3].length) (baseStart_1850471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1850471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1850471 prefixEnd_1850471 := by exact prefixLift 1850471
  have htrace : WordTrace (prefixWord ++ tailWord_1850471) baseStart_1850471 baseEnd_1850471 := by
    simpa [prefixWord, tailWord_1850471, baseEnd_1850471] using wordTrace_append hprefix tailTrace_1850471
  have hstable : (prefixWord ++ tailWord_1850471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1850471).length < 2 ^ (prefixWord ++ tailWord_1850471).sum := by decide
  have hdescent : baseEnd_1850471 < baseStart_1850471 := by decide
  rcases family_descends (prefixWord ++ tailWord_1850471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1850514 : List Nat := [3, 2, 3, 1, 1, 2, 1, 1, 2, 4, 3]
def baseStart_1850514 : Nat := 118140960795 + 1850514 * 2 ^ 59
def prefixEnd_1850514 : Nat := 4983230072969 + 3 ^ 40 * 1850514 * 2
def baseEnd_1850514 : Nat := 950203139874278089164647

theorem tailTrace_1850514 : CollatzResearch.WordTrace tailWord_1850514 prefixEnd_1850514 950203139874278089164647 := by
  unfold tailWord_1850514
  simp only [CollatzResearch.WordTrace]
  refine ⟨16873447604477823868717649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44995860278607530316580397 16873447604477823868717649)
  ·
    refine ⟨12655085703358367901538237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16873447604477823868717649 12655085703358367901538237)
    ·
      refine ⟨4745657138759387963076839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12655085703358367901538237 4745657138759387963076839)
      ·
        refine ⟨7118485708139081944615259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4745657138759387963076839 7118485708139081944615259)
        ·
          refine ⟨10677728562208622916922889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7118485708139081944615259 10677728562208622916922889)
          ·
            refine ⟨8008296421656467187692167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10677728562208622916922889 8008296421656467187692167)
            ·
              refine ⟨12012444632484700781538251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8008296421656467187692167 12012444632484700781538251)
              ·
                refine ⟨18018666948727051172307377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12012444632484700781538251 18018666948727051172307377)
                ·
                  refine ⟨13514000211545288379230533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18018666948727051172307377 13514000211545288379230533)
                  ·
                    refine ⟨2533875039664741571105725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13514000211545288379230533 2533875039664741571105725)
                    ·
                      refine ⟨950203139874278089164647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2533875039664741571105725 950203139874278089164647)
                      ·
                        rfl

theorem cell23_1850514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 1, 2, 4, 3].length) (baseStart_1850514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1850514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1850514 prefixEnd_1850514 := by exact prefixLift 1850514
  have htrace : WordTrace (prefixWord ++ tailWord_1850514) baseStart_1850514 baseEnd_1850514 := by
    simpa [prefixWord, tailWord_1850514, baseEnd_1850514] using wordTrace_append hprefix tailTrace_1850514
  have hstable : (prefixWord ++ tailWord_1850514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1850514).length < 2 ^ (prefixWord ++ tailWord_1850514).sum := by decide
  have hdescent : baseEnd_1850514 < baseStart_1850514 := by decide
  rcases family_descends (prefixWord ++ tailWord_1850514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1850524 : List Nat := [2, 2, 3, 2, 1, 3, 1, 1, 2, 2, 4]
def baseStart_1850524 : Nat := 118140960795 + 1850524 * 2 ^ 59
def prefixEnd_1850524 : Nat := 4983230072969 + 3 ^ 40 * 1850524 * 2
def baseEnd_1850524 : Nat := 950208274680823050039601

theorem tailTrace_1850524 : CollatzResearch.WordTrace tailWord_1850524 prefixEnd_1850524 950208274680823050039601 := by
  unfold tailWord_1850524
  simp only [CollatzResearch.WordTrace]
  refine ⟨33747077573937533591367313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44996103431916711455156417 33747077573937533591367313)
  ·
    refine ⟨25310308180453150193525485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33747077573937533591367313 25310308180453150193525485)
    ·
      refine ⟨9491365567669931322572057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25310308180453150193525485 9491365567669931322572057)
      ·
        refine ⟨7118524175752448491929043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9491365567669931322572057 7118524175752448491929043)
        ·
          refine ⟨10677786263628672737893565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7118524175752448491929043 10677786263628672737893565)
          ·
            refine ⟨4004169848860752276710087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10677786263628672737893565 4004169848860752276710087)
            ·
              refine ⟨6006254773291128415065131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4004169848860752276710087 6006254773291128415065131)
              ·
                refine ⟨9009382159936692622597697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6006254773291128415065131 9009382159936692622597697)
                ·
                  refine ⟨6757036619952519466948273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9009382159936692622597697 6757036619952519466948273)
                  ·
                    refine ⟨5067777464964389600211205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6757036619952519466948273 5067777464964389600211205)
                    ·
                      refine ⟨950208274680823050039601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5067777464964389600211205 950208274680823050039601)
                      ·
                        rfl

theorem cell23_1850524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 1, 2, 2, 4].length) (baseStart_1850524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1850524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1850524 prefixEnd_1850524 := by exact prefixLift 1850524
  have htrace : WordTrace (prefixWord ++ tailWord_1850524) baseStart_1850524 baseEnd_1850524 := by
    simpa [prefixWord, tailWord_1850524, baseEnd_1850524] using wordTrace_append hprefix tailTrace_1850524
  have hstable : (prefixWord ++ tailWord_1850524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1850524).length < 2 ^ (prefixWord ++ tailWord_1850524).sum := by decide
  have hdescent : baseEnd_1850524 < baseStart_1850524 := by decide
  rcases family_descends (prefixWord ++ tailWord_1850524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1850557 : List Nat := [1, 4, 1, 2, 1, 1, 2, 1, 3, 2, 5]
def baseStart_1850557 : Nat := 118140960795 + 1850557 * 2 ^ 59
def prefixEnd_1850557 : Nat := 4983230072969 + 3 ^ 40 * 1850557 * 2
def baseEnd_1850557 : Nat := 950225219542421420926949

theorem tailTrace_1850557 : CollatzResearch.WordTrace tailWord_1850557 prefixEnd_1850557 950225219542421420926949 := by
  unfold tailWord_1850557
  simp only [CollatzResearch.WordTrace]
  refine ⟨67495358756755513818685925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44996905837837009212457283 67495358756755513818685925)
  ·
    refine ⟨12655379766891658841003611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67495358756755513818685925 12655379766891658841003611)
    ·
      refine ⟨18983069650337488261505417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12655379766891658841003611 18983069650337488261505417)
      ·
        refine ⟨14237302237753116196129063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18983069650337488261505417 14237302237753116196129063)
        ·
          refine ⟨21355953356629674294193595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14237302237753116196129063 21355953356629674294193595)
          ·
            refine ⟨32033930034944511441290393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21355953356629674294193595 32033930034944511441290393)
            ·
              refine ⟨24025447526208383580967795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32033930034944511441290393 24025447526208383580967795)
              ·
                refine ⟨36038171289312575371451693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24025447526208383580967795 36038171289312575371451693)
                ·
                  refine ⟨13514314233492215764294385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36038171289312575371451693 13514314233492215764294385)
                  ·
                    refine ⟨10135735675119161823220789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13514314233492215764294385 10135735675119161823220789)
                    ·
                      refine ⟨950225219542421420926949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10135735675119161823220789 950225219542421420926949)
                      ·
                        rfl

theorem cell23_1850557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 1, 3, 2, 5].length) (baseStart_1850557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1850557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1850557 prefixEnd_1850557 := by exact prefixLift 1850557
  have htrace : WordTrace (prefixWord ++ tailWord_1850557) baseStart_1850557 baseEnd_1850557 := by
    simpa [prefixWord, tailWord_1850557, baseEnd_1850557] using wordTrace_append hprefix tailTrace_1850557
  have hstable : (prefixWord ++ tailWord_1850557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1850557).length < 2 ^ (prefixWord ++ tailWord_1850557).sum := by decide
  have hdescent : baseEnd_1850557 < baseStart_1850557 := by decide
  rcases family_descends (prefixWord ++ tailWord_1850557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1850561 : List Nat := [1, 2, 6, 1, 1, 1, 1, 2, 2, 3, 3]
def baseStart_1850561 : Nat := 118140960795 + 1850561 * 2 ^ 59
def prefixEnd_1850561 : Nat := 4983230072969 + 3 ^ 40 * 1850561 * 2
def baseEnd_1850561 : Nat := 950227273465039405276931

theorem tailTrace_1850561 : CollatzResearch.WordTrace tailWord_1850561 prefixEnd_1850561 950227273465039405276931 := by
  unfold tailWord_1850561
  simp only [CollatzResearch.WordTrace]
  refine ⟨67495504648741022501831537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44997003099160681667887691 67495504648741022501831537)
  ·
    refine ⟨50621628486555766876373653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67495504648741022501831537 50621628486555766876373653)
    ·
      refine ⟨2372888835307301572330015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 50621628486555766876373653 2372888835307301572330015)
      ·
        refine ⟨3559333252960952358495023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2372888835307301572330015 3559333252960952358495023)
        ·
          refine ⟨5338999879441428537742535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3559333252960952358495023 5338999879441428537742535)
          ·
            refine ⟨8008499819162142806613803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5338999879441428537742535 8008499819162142806613803)
            ·
              refine ⟨12012749728743214209920705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8008499819162142806613803 12012749728743214209920705)
              ·
                refine ⟨9009562296557410657440529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12012749728743214209920705 9009562296557410657440529)
                ·
                  refine ⟨6757171722418057993080397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9009562296557410657440529 6757171722418057993080397)
                  ·
                    refine ⟨2533939395906771747405149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6757171722418057993080397 2533939395906771747405149)
                    ·
                      refine ⟨950227273465039405276931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2533939395906771747405149 950227273465039405276931)
                      ·
                        rfl

theorem cell23_1850561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 2, 2, 3, 3].length) (baseStart_1850561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1850561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1850561 prefixEnd_1850561 := by exact prefixLift 1850561
  have htrace : WordTrace (prefixWord ++ tailWord_1850561) baseStart_1850561 baseEnd_1850561 := by
    simpa [prefixWord, tailWord_1850561, baseEnd_1850561] using wordTrace_append hprefix tailTrace_1850561
  have hstable : (prefixWord ++ tailWord_1850561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1850561).length < 2 ^ (prefixWord ++ tailWord_1850561).sum := by decide
  have hdescent : baseEnd_1850561 < baseStart_1850561 := by decide
  rcases family_descends (prefixWord ++ tailWord_1850561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1850562 : List Nat := [3, 5, 1, 1, 2, 1, 1, 1, 4, 2, 2]
def baseStart_1850562 : Nat := 118140960795 + 1850562 * 2 ^ 59
def prefixEnd_1850562 : Nat := 4983230072969 + 3 ^ 40 * 1850562 * 2
def baseEnd_1850562 : Nat := 950227786945693901364427

theorem tailTrace_1850562 : CollatzResearch.WordTrace tailWord_1850562 prefixEnd_1850562 950227786945693901364427 := by
  unfold tailWord_1850562
  simp only [CollatzResearch.WordTrace]
  refine ⟨16873885280434349918154485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44997027414491599781745293 16873885280434349918154485)
  ·
    refine ⟨1581926745040720304826983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16873885280434349918154485 1581926745040720304826983)
    ·
      refine ⟨2372890117561080457240475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1581926745040720304826983 2372890117561080457240475)
      ·
        refine ⟨3559335176341620685860713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2372890117561080457240475 3559335176341620685860713)
        ·
          refine ⟨2669501382256215514395535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3559335176341620685860713 2669501382256215514395535)
          ·
            refine ⟨4004252073384323271593303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2669501382256215514395535 4004252073384323271593303)
            ·
              refine ⟨6006378110076484907389955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4004252073384323271593303 6006378110076484907389955)
              ·
                refine ⟨9009567165114727361084933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6006378110076484907389955 9009567165114727361084933)
                ·
                  refine ⟨1689293843459011380203425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9009567165114727361084933 1689293843459011380203425)
                  ·
                    refine ⟨1266970382594258535152569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1689293843459011380203425 1266970382594258535152569)
                    ·
                      refine ⟨950227786945693901364427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1266970382594258535152569 950227786945693901364427)
                      ·
                        rfl

theorem cell23_1850562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 1, 4, 2, 2].length) (baseStart_1850562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1850562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1850562 prefixEnd_1850562 := by exact prefixLift 1850562
  have htrace : WordTrace (prefixWord ++ tailWord_1850562) baseStart_1850562 baseEnd_1850562 := by
    simpa [prefixWord, tailWord_1850562, baseEnd_1850562] using wordTrace_append hprefix tailTrace_1850562
  have hstable : (prefixWord ++ tailWord_1850562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1850562).length < 2 ^ (prefixWord ++ tailWord_1850562).sum := by decide
  have hdescent : baseEnd_1850562 < baseStart_1850562 := by decide
  rcases family_descends (prefixWord ++ tailWord_1850562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1850604 : List Nat := [2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 3]
def baseStart_1850604 : Nat := 118140960795 + 1850604 * 2 ^ 59
def prefixEnd_1850604 : Nat := 4983230072969 + 3 ^ 40 * 1850604 * 2
def baseEnd_1850604 : Nat := 950249353133182737039233

theorem tailTrace_1850604 : CollatzResearch.WordTrace tailWord_1850604 prefixEnd_1850604 950249353133182737039233 := by
  unfold tailWord_1850604
  simp only [CollatzResearch.WordTrace]
  refine ⟨33748536493792620422823433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44998048658390160563764577 33748536493792620422823433)
  ·
    refine ⟨25311402370344465317117575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33748536493792620422823433 25311402370344465317117575)
    ·
      refine ⟨37967103555516697975676363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25311402370344465317117575 37967103555516697975676363)
      ·
        refine ⟨56950655333275046963514545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37967103555516697975676363 56950655333275046963514545)
        ·
          refine ⟨42712991499956285222635909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56950655333275046963514545 42712991499956285222635909)
          ·
            refine ⟨8008685906241803479244233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42712991499956285222635909 8008685906241803479244233)
            ·
              refine ⟨6006514429681352609433175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8008685906241803479244233 6006514429681352609433175)
              ·
                refine ⟨9009771644522028914149763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6006514429681352609433175 9009771644522028914149763)
                ·
                  refine ⟨13514657466783043371224645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9009771644522028914149763 13514657466783043371224645)
                  ·
                    refine ⟨2533998275021820632104621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13514657466783043371224645 2533998275021820632104621)
                    ·
                      refine ⟨950249353133182737039233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2533998275021820632104621 950249353133182737039233)
                      ·
                        rfl

theorem cell23_1850604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 3].length) (baseStart_1850604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1850604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1850604 prefixEnd_1850604 := by exact prefixLift 1850604
  have htrace : WordTrace (prefixWord ++ tailWord_1850604) baseStart_1850604 baseEnd_1850604 := by
    simpa [prefixWord, tailWord_1850604, baseEnd_1850604] using wordTrace_append hprefix tailTrace_1850604
  have hstable : (prefixWord ++ tailWord_1850604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1850604).length < 2 ^ (prefixWord ++ tailWord_1850604).sum := by decide
  have hdescent : baseEnd_1850604 < baseStart_1850604 := by decide
  rcases family_descends (prefixWord ++ tailWord_1850604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1850628 : List Nat := [2, 3, 2, 2, 2, 3, 1, 1, 3, 4]
def baseStart_1850628 : Nat := 118140960795 + 1850628 * 2 ^ 59
def prefixEnd_1850628 : Nat := 4983230072969 + 3 ^ 40 * 1850628 * 2
def baseEnd_1850628 : Nat := 316753892222963547713041

theorem tailTrace_1850628 : CollatzResearch.WordTrace tailWord_1850628 prefixEnd_1850628 316753892222963547713041 := by
  unfold tailWord_1850628
  simp only [CollatzResearch.WordTrace]
  refine ⟨33748974169749146472260269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44998632226332195296347025 33748974169749146472260269)
  ·
    refine ⟨12655865313655929927097601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33748974169749146472260269 12655865313655929927097601)
    ·
      refine ⟨9491898985241947445323201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12655865313655929927097601 9491898985241947445323201)
      ·
        refine ⟨7118924238931460583992401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9491898985241947445323201 7118924238931460583992401)
        ·
          refine ⟨5339193179198595437994301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7118924238931460583992401 5339193179198595437994301)
          ·
            refine ⟨2002197442199473289247863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5339193179198595437994301 2002197442199473289247863)
            ·
              refine ⟨3003296163299209933871795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2002197442199473289247863 3003296163299209933871795)
              ·
                refine ⟨4504944244948814900807693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3003296163299209933871795 4504944244948814900807693)
                ·
                  refine ⟨1689354091855805587802885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4504944244948814900807693 1689354091855805587802885)
                  ·
                    refine ⟨316753892222963547713041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1689354091855805587802885 316753892222963547713041)
                    ·
                      rfl

theorem cell23_1850628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 1, 1, 3, 4].length) (baseStart_1850628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1850628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1850628 prefixEnd_1850628 := by exact prefixLift 1850628
  have htrace : WordTrace (prefixWord ++ tailWord_1850628) baseStart_1850628 baseEnd_1850628 := by
    simpa [prefixWord, tailWord_1850628, baseEnd_1850628] using wordTrace_append hprefix tailTrace_1850628
  have hstable : (prefixWord ++ tailWord_1850628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1850628).length < 2 ^ (prefixWord ++ tailWord_1850628).sum := by decide
  have hdescent : baseEnd_1850628 < baseStart_1850628 := by decide
  rcases family_descends (prefixWord ++ tailWord_1850628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1850668 : List Nat := [2, 2, 1, 1, 1, 3, 1, 7, 1, 1, 3]
def baseStart_1850668 : Nat := 118140960795 + 1850668 * 2 ^ 59
def prefixEnd_1850668 : Nat := 4983230072969 + 3 ^ 40 * 1850668 * 2
def baseEnd_1850668 : Nat := 950282215895070486638939

theorem tailTrace_1850668 : CollatzResearch.WordTrace tailWord_1850668 prefixEnd_1850668 950282215895070486638939 := by
  unfold tailWord_1850668
  simp only [CollatzResearch.WordTrace]
  refine ⟨33749703629676689887988329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44999604839568919850651105 33749703629676689887988329)
  ·
    refine ⟨25312277722257517415991247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33749703629676689887988329 25312277722257517415991247)
    ·
      refine ⟨37968416583386276123986871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25312277722257517415991247 37968416583386276123986871)
      ·
        refine ⟨56952624875079414185980307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37968416583386276123986871 56952624875079414185980307)
        ·
          refine ⟨85428937312619121278970461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56952624875079414185980307 85428937312619121278970461)
          ·
            refine ⟨32035851492232170479613923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85428937312619121278970461 32035851492232170479613923)
            ·
              refine ⟨48053777238348255719420885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32035851492232170479613923 48053777238348255719420885)
              ·
                refine ⟨1126260404023787243423927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 48053777238348255719420885 1126260404023787243423927)
                ·
                  refine ⟨1689390606035680865135891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1126260404023787243423927 1689390606035680865135891)
                  ·
                    refine ⟨2534085909053521297703837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1689390606035680865135891 2534085909053521297703837)
                    ·
                      refine ⟨950282215895070486638939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2534085909053521297703837 950282215895070486638939)
                      ·
                        rfl

theorem cell23_1850668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 7, 1, 1, 3].length) (baseStart_1850668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1850668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1850668 prefixEnd_1850668 := by exact prefixLift 1850668
  have htrace : WordTrace (prefixWord ++ tailWord_1850668) baseStart_1850668 baseEnd_1850668 := by
    simpa [prefixWord, tailWord_1850668, baseEnd_1850668] using wordTrace_append hprefix tailTrace_1850668
  have hstable : (prefixWord ++ tailWord_1850668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1850668).length < 2 ^ (prefixWord ++ tailWord_1850668).sum := by decide
  have hdescent : baseEnd_1850668 < baseStart_1850668 := by decide
  rcases family_descends (prefixWord ++ tailWord_1850668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1850711 : List Nat := [1, 1, 3, 2, 3, 2, 2, 1, 3, 2, 3]
def baseStart_1850711 : Nat := 118140960795 + 1850711 * 2 ^ 59
def prefixEnd_1850711 : Nat := 4983230072969 + 3 ^ 40 * 1850711 * 2
def baseEnd_1850711 : Nat := 950304295563213818401241

theorem tailTrace_1850711 : CollatzResearch.WordTrace tailWord_1850711 prefixEnd_1850711 950304295563213818401241 := by
  unfold tailWord_1850711
  simp only [CollatzResearch.WordTrace]
  refine ⟨67500975598197598119791987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45000650398798398746527991 67500975598197598119791987)
  ·
    refine ⟨101251463397296397179687981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67500975598197598119791987 101251463397296397179687981)
    ·
      refine ⟨37969298773986148942382993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101251463397296397179687981 37969298773986148942382993)
      ·
        refine ⟨28476974080489611706787245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37969298773986148942382993 28476974080489611706787245)
        ·
          refine ⟨10678865280183604390045217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28476974080489611706787245 10678865280183604390045217)
          ·
            refine ⟨8009148960137703292533913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10678865280183604390045217 8009148960137703292533913)
            ·
              refine ⟨6006861720103277469400435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8009148960137703292533913 6006861720103277469400435)
              ·
                refine ⟨9010292580154916204100653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6006861720103277469400435 9010292580154916204100653)
                ·
                  refine ⟨3378859717558093576537745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9010292580154916204100653 3378859717558093576537745)
                  ·
                    refine ⟨2534144788168570182403309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3378859717558093576537745 2534144788168570182403309)
                    ·
                      refine ⟨950304295563213818401241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2534144788168570182403309 950304295563213818401241)
                      ·
                        rfl

theorem cell23_1850711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 1, 3, 2, 3].length) (baseStart_1850711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1850711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1850711 prefixEnd_1850711 := by exact prefixLift 1850711
  have htrace : WordTrace (prefixWord ++ tailWord_1850711) baseStart_1850711 baseEnd_1850711 := by
    simpa [prefixWord, tailWord_1850711, baseEnd_1850711] using wordTrace_append hprefix tailTrace_1850711
  have hstable : (prefixWord ++ tailWord_1850711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1850711).length < 2 ^ (prefixWord ++ tailWord_1850711).sum := by decide
  have hdescent : baseEnd_1850711 < baseStart_1850711 := by decide
  rcases family_descends (prefixWord ++ tailWord_1850711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1850776 : List Nat := [2, 1, 2, 5, 3, 1, 1, 3, 1, 2, 2]
def baseStart_1850776 : Nat := 118140960795 + 1850776 * 2 ^ 59
def prefixEnd_1850776 : Nat := 4983230072969 + 3 ^ 40 * 1850776 * 2
def baseEnd_1850776 : Nat := 950337671805756064088443

theorem tailTrace_1850776 : CollatzResearch.WordTrace tailWord_1850776 prefixEnd_1850776 950337671805756064088443 := by
  unfold tailWord_1850776
  simp only [CollatzResearch.WordTrace]
  refine ⟨33751673171481057110454091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45002230895308076147272121 33751673171481057110454091)
  ·
    refine ⟨50627509757221585665681137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33751673171481057110454091 50627509757221585665681137)
    ·
      refine ⟨37970632317916189249260853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50627509757221585665681137 37970632317916189249260853)
      ·
        refine ⟨3559746779804642742118205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 37970632317916189249260853 3559746779804642742118205)
        ·
          refine ⟨1334905042426741028294327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3559746779804642742118205 1334905042426741028294327)
          ·
            refine ⟨2002357563640111542441491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1334905042426741028294327 2002357563640111542441491)
            ·
              refine ⟨3003536345460167313662237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2002357563640111542441491 3003536345460167313662237)
              ·
                refine ⟨1126326129547562742623339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3003536345460167313662237 1126326129547562742623339)
                ·
                  refine ⟨1689489194321344113935009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1126326129547562742623339 1689489194321344113935009)
                  ·
                    refine ⟨1267116895741008085451257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1689489194321344113935009 1267116895741008085451257)
                    ·
                      refine ⟨950337671805756064088443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1267116895741008085451257 950337671805756064088443)
                      ·
                        rfl

theorem cell23_1850776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 1, 3, 1, 2, 2].length) (baseStart_1850776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1850776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1850776 prefixEnd_1850776 := by exact prefixLift 1850776
  have htrace : WordTrace (prefixWord ++ tailWord_1850776) baseStart_1850776 baseEnd_1850776 := by
    simpa [prefixWord, tailWord_1850776, baseEnd_1850776] using wordTrace_append hprefix tailTrace_1850776
  have hstable : (prefixWord ++ tailWord_1850776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1850776).length < 2 ^ (prefixWord ++ tailWord_1850776).sum := by decide
  have hdescent : baseEnd_1850776 < baseStart_1850776 := by decide
  rcases family_descends (prefixWord ++ tailWord_1850776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1850801 : List Nat := [1, 2, 2, 4, 1, 1, 2, 1, 2, 4, 3]
def baseStart_1850801 : Nat := 118140960795 + 1850801 * 2 ^ 59
def prefixEnd_1850801 : Nat := 4983230072969 + 3 ^ 40 * 1850801 * 2
def baseEnd_1850801 : Nat := 950350508822118466275827

theorem tailTrace_1850801 : CollatzResearch.WordTrace tailWord_1850801 prefixEnd_1850801 950350508822118466275827 := by
  unfold tailWord_1850801
  simp only [CollatzResearch.WordTrace]
  refine ⟨67504258167871543490568257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45002838778581028993712171 67504258167871543490568257)
  ·
    refine ⟨50628193625903657617926193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67504258167871543490568257 50628193625903657617926193)
    ·
      refine ⟨37971145219427743213444645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50628193625903657617926193 37971145219427743213444645)
      ·
        refine ⟨7119589728642701852520871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37971145219427743213444645 7119589728642701852520871)
        ·
          refine ⟨10679384592964052778781307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7119589728642701852520871 10679384592964052778781307)
          ·
            refine ⟨16019076889446079168171961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10679384592964052778781307 16019076889446079168171961)
            ·
              refine ⟨12014307667084559376128971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16019076889446079168171961 12014307667084559376128971)
              ·
                refine ⟨18021461500626839064193457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12014307667084559376128971 18021461500626839064193457)
                ·
                  refine ⟨13516096125470129298145093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18021461500626839064193457 13516096125470129298145093)
                  ·
                    refine ⟨2534268023525649243402205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13516096125470129298145093 2534268023525649243402205)
                    ·
                      refine ⟨950350508822118466275827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2534268023525649243402205 950350508822118466275827)
                      ·
                        rfl

theorem cell23_1850801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 1, 2, 4, 3].length) (baseStart_1850801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1850801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1850801 prefixEnd_1850801 := by exact prefixLift 1850801
  have htrace : WordTrace (prefixWord ++ tailWord_1850801) baseStart_1850801 baseEnd_1850801 := by
    simpa [prefixWord, tailWord_1850801, baseEnd_1850801] using wordTrace_append hprefix tailTrace_1850801
  have hstable : (prefixWord ++ tailWord_1850801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1850801).length < 2 ^ (prefixWord ++ tailWord_1850801).sum := by decide
  have hdescent : baseEnd_1850801 < baseStart_1850801 := by decide
  rcases family_descends (prefixWord ++ tailWord_1850801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1850809 : List Nat := [1, 2, 1, 4, 5, 1, 2, 1, 2, 1, 3]
def baseStart_1850809 : Nat := 118140960795 + 1850809 * 2 ^ 59
def prefixEnd_1850809 : Nat := 4983230072969 + 3 ^ 40 * 1850809 * 2
def baseEnd_1850809 : Nat := 950354616667354434975791

theorem tailTrace_1850809 : CollatzResearch.WordTrace tailWord_1850809 prefixEnd_1850809 950354616667354434975791 := by
  unfold tailWord_1850809
  simp only [CollatzResearch.WordTrace]
  refine ⟨67504549951842560856859481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45003033301228373904572987 67504549951842560856859481)
  ·
    refine ⟨50628412463881920642644611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67504549951842560856859481 50628412463881920642644611)
    ·
      refine ⟨75942618695822880963966917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50628412463881920642644611 75942618695822880963966917)
      ·
        refine ⟨14239241005466790180743797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75942618695822880963966917 14239241005466790180743797)
        ·
          refine ⟨1334928844262511579444731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14239241005466790180743797 1334928844262511579444731)
          ·
            refine ⟨2002393266393767369167097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1334928844262511579444731 2002393266393767369167097)
            ·
              refine ⟨1501794949795325526875323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2002393266393767369167097 1501794949795325526875323)
              ·
                refine ⟨2252692424692988290312985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1501794949795325526875323 2252692424692988290312985)
                ·
                  refine ⟨1689519318519741217734739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2252692424692988290312985 1689519318519741217734739)
                  ·
                    refine ⟨2534278977779611826602109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1689519318519741217734739 2534278977779611826602109)
                    ·
                      refine ⟨950354616667354434975791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2534278977779611826602109 950354616667354434975791)
                      ·
                        rfl

theorem cell23_1850809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 2, 1, 2, 1, 3].length) (baseStart_1850809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1850809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1850809 prefixEnd_1850809 := by exact prefixLift 1850809
  have htrace : WordTrace (prefixWord ++ tailWord_1850809) baseStart_1850809 baseEnd_1850809 := by
    simpa [prefixWord, tailWord_1850809, baseEnd_1850809] using wordTrace_append hprefix tailTrace_1850809
  have hstable : (prefixWord ++ tailWord_1850809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1850809).length < 2 ^ (prefixWord ++ tailWord_1850809).sum := by decide
  have hdescent : baseEnd_1850809 < baseStart_1850809 := by decide
  rcases family_descends (prefixWord ++ tailWord_1850809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1850855 : List Nat := [1, 1, 5, 2, 1, 2, 4, 2, 5]
def baseStart_1850855 : Nat := 118140960795 + 1850855 * 2 ^ 59
def prefixEnd_1850855 : Nat := 4983230072969 + 3 ^ 40 * 1850855 * 2
def baseEnd_1850855 : Nat := 105597581864162361666731

theorem tailTrace_1850855 : CollatzResearch.WordTrace tailWord_1850855 prefixEnd_1850855 105597581864162361666731 := by
  unfold tailWord_1850855
  simp only [CollatzResearch.WordTrace]
  refine ⟨67506227709675910713034019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45004151806450607142022679 67506227709675910713034019)
  ·
    refine ⟨101259341564513866069551029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67506227709675910713034019 101259341564513866069551029)
    ·
      refine ⟨9493063271673174944020409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 101259341564513866069551029 9493063271673174944020409)
      ·
        refine ⟨7119797453754881208015307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9493063271673174944020409 7119797453754881208015307)
        ·
          refine ⟨10679696180632321812022961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7119797453754881208015307 10679696180632321812022961)
          ·
            refine ⟨8009772135474241359017221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10679696180632321812022961 8009772135474241359017221)
            ·
              refine ⟨1501832275401420254815729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8009772135474241359017221 1501832275401420254815729)
              ·
                refine ⟨1126374206551065191111797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1501832275401420254815729 1126374206551065191111797)
                ·
                  refine ⟨105597581864162361666731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1126374206551065191111797 105597581864162361666731)
                  ·
                    rfl

theorem cell23_1850855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 4, 2, 5].length) (baseStart_1850855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1850855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1850855 prefixEnd_1850855 := by exact prefixLift 1850855
  have htrace : WordTrace (prefixWord ++ tailWord_1850855) baseStart_1850855 baseEnd_1850855 := by
    simpa [prefixWord, tailWord_1850855, baseEnd_1850855] using wordTrace_append hprefix tailTrace_1850855
  have hstable : (prefixWord ++ tailWord_1850855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1850855).length < 2 ^ (prefixWord ++ tailWord_1850855).sum := by decide
  have hdescent : baseEnd_1850855 < baseStart_1850855 := by decide
  rcases family_descends (prefixWord ++ tailWord_1850855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1850888 : List Nat := [2, 1, 3, 2, 1, 1, 5, 1, 2, 1, 4]
def baseStart_1850888 : Nat := 118140960795 + 1850888 * 2 ^ 59
def prefixEnd_1850888 : Nat := 4983230072969 + 3 ^ 40 * 1850888 * 2
def baseEnd_1850888 : Nat := 950395181639059625887927

theorem tailTrace_1850888 : CollatzResearch.WordTrace tailWord_1850888 prefixEnd_1850888 950395181639059625887927 := by
  unfold tailWord_1850888
  simp only [CollatzResearch.WordTrace]
  refine ⟨33753715659278178674492659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45004954212370904899323545 33753715659278178674492659)
  ·
    refine ⟨50630573488917268011738989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33753715659278178674492659 50630573488917268011738989)
    ·
      refine ⟨18986465058343975504402121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50630573488917268011738989 18986465058343975504402121)
      ·
        refine ⟨14239848793757981628301591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18986465058343975504402121 14239848793757981628301591)
        ·
          refine ⟨21359773190636972442452387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14239848793757981628301591 21359773190636972442452387)
          ·
            refine ⟨32039659785955458663678581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21359773190636972442452387 32039659785955458663678581)
            ·
              refine ⟨3003718104933324249719867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32039659785955458663678581 3003718104933324249719867)
              ·
                refine ⟨4505577157399986374579801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3003718104933324249719867 4505577157399986374579801)
                ·
                  refine ⟨3379182868049989780934851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4505577157399986374579801 3379182868049989780934851)
                  ·
                    refine ⟨5068774302074984671402277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3379182868049989780934851 5068774302074984671402277)
                    ·
                      refine ⟨950395181639059625887927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5068774302074984671402277 950395181639059625887927)
                      ·
                        rfl

theorem cell23_1850888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 5, 1, 2, 1, 4].length) (baseStart_1850888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1850888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1850888 prefixEnd_1850888 := by exact prefixLift 1850888
  have htrace : WordTrace (prefixWord ++ tailWord_1850888) baseStart_1850888 baseEnd_1850888 := by
    simpa [prefixWord, tailWord_1850888, baseEnd_1850888] using wordTrace_append hprefix tailTrace_1850888
  have hstable : (prefixWord ++ tailWord_1850888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1850888).length < 2 ^ (prefixWord ++ tailWord_1850888).sum := by decide
  have hdescent : baseEnd_1850888 < baseStart_1850888 := by decide
  rcases family_descends (prefixWord ++ tailWord_1850888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1850901 : List Nat := [1, 3, 2, 1, 3, 2, 1, 1, 2, 1, 6]
def baseStart_1850901 : Nat := 118140960795 + 1850901 * 2 ^ 59
def prefixEnd_1850901 : Nat := 4983230072969 + 3 ^ 40 * 1850901 * 2
def baseEnd_1850901 : Nat := 950401856887568075025367

theorem tailTrace_1850901 : CollatzResearch.WordTrace tailWord_1850901 prefixEnd_1850901 950401856887568075025367 := by
  unfold tailWord_1850901
  simp only [CollatzResearch.WordTrace]
  refine ⟨67507905467509260569208557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45005270311672840379472371 67507905467509260569208557)
  ·
    refine ⟨25315464550315972713453209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67507905467509260569208557 25315464550315972713453209)
    ·
      refine ⟨18986598412736979535089907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25315464550315972713453209 18986598412736979535089907)
      ·
        refine ⟨28479897619105469302634861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18986598412736979535089907 28479897619105469302634861)
        ·
          refine ⟨10679961607164550988488073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28479897619105469302634861 10679961607164550988488073)
          ·
            refine ⟨8009971205373413241366055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10679961607164550988488073 8009971205373413241366055)
            ·
              refine ⟨12014956808060119862049083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8009971205373413241366055 12014956808060119862049083)
              ·
                refine ⟨18022435212090179793073625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12014956808060119862049083 18022435212090179793073625)
                ·
                  refine ⟨13516826409067634844805219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18022435212090179793073625 13516826409067634844805219)
                  ·
                    refine ⟨20275239613601452267207829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13516826409067634844805219 20275239613601452267207829)
                    ·
                      refine ⟨950401856887568075025367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 20275239613601452267207829 950401856887568075025367)
                      ·
                        rfl

theorem cell23_1850901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 1, 2, 1, 6].length) (baseStart_1850901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1850901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1850901 prefixEnd_1850901 := by exact prefixLift 1850901
  have htrace : WordTrace (prefixWord ++ tailWord_1850901) baseStart_1850901 baseEnd_1850901 := by
    simpa [prefixWord, tailWord_1850901, baseEnd_1850901] using wordTrace_append hprefix tailTrace_1850901
  have hstable : (prefixWord ++ tailWord_1850901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1850901).length < 2 ^ (prefixWord ++ tailWord_1850901).sum := by decide
  have hdescent : baseEnd_1850901 < baseStart_1850901 := by decide
  rcases family_descends (prefixWord ++ tailWord_1850901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1850908 : List Nat := [2, 2, 3, 1, 2, 1, 2, 1, 4, 2, 3]
def baseStart_1850908 : Nat := 118140960795 + 1850908 * 2 ^ 59
def prefixEnd_1850908 : Nat := 4983230072969 + 3 ^ 40 * 1850908 * 2
def baseEnd_1850908 : Nat := 950405451252149547637835

theorem tailTrace_1850908 : CollatzResearch.WordTrace tailWord_1850908 prefixEnd_1850908 950405451252149547637835 := by
  unfold tailWord_1850908
  simp only [CollatzResearch.WordTrace]
  refine ⟨33754080389241950382356689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45005440518989267176475585 33754080389241950382356689)
  ·
    refine ⟨25315560291931462786767517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33754080389241950382356689 25315560291931462786767517)
    ·
      refine ⟨9493335109474298545037819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25315560291931462786767517 9493335109474298545037819)
      ·
        refine ⟨14240002664211447817556729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9493335109474298545037819 14240002664211447817556729)
        ·
          refine ⟨10680001998158585863167547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14240002664211447817556729 10680001998158585863167547)
          ·
            refine ⟨16020002997237878794751321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10680001998158585863167547 16020002997237878794751321)
            ·
              refine ⟨12015002247928409096063491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16020002997237878794751321 12015002247928409096063491)
              ·
                refine ⟨18022503371892613644095237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12015002247928409096063491 18022503371892613644095237)
                ·
                  refine ⟨3379219382229865058267857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18022503371892613644095237 3379219382229865058267857)
                  ·
                    refine ⟨2534414536672398793700893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3379219382229865058267857 2534414536672398793700893)
                    ·
                      refine ⟨950405451252149547637835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2534414536672398793700893 950405451252149547637835)
                      ·
                        rfl

theorem cell23_1850908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 1, 4, 2, 3].length) (baseStart_1850908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1850908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1850908 prefixEnd_1850908 := by exact prefixLift 1850908
  have htrace : WordTrace (prefixWord ++ tailWord_1850908) baseStart_1850908 baseEnd_1850908 := by
    simpa [prefixWord, tailWord_1850908, baseEnd_1850908] using wordTrace_append hprefix tailTrace_1850908
  have hstable : (prefixWord ++ tailWord_1850908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1850908).length < 2 ^ (prefixWord ++ tailWord_1850908).sum := by decide
  have hdescent : baseEnd_1850908 < baseStart_1850908 := by decide
  rcases family_descends (prefixWord ++ tailWord_1850908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1850915 : List Nat := [1, 1, 1, 4, 5, 1, 2, 1, 3, 4]
def baseStart_1850915 : Nat := 118140960795 + 1850915 * 2 ^ 59
def prefixEnd_1850915 : Nat := 4983230072969 + 3 ^ 40 * 1850915 * 2
def baseEnd_1850915 : Nat := 316803015205577006750101

theorem tailTrace_1850915 : CollatzResearch.WordTrace tailWord_1850915 prefixEnd_1850915 316803015205577006750101 := by
  unfold tailWord_1850915
  simp only [CollatzResearch.WordTrace]
  refine ⟨67508416089458540960218199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45005610726305693973478799 67508416089458540960218199)
  ·
    refine ⟨101262624134187811440327299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67508416089458540960218199 101262624134187811440327299)
    ·
      refine ⟨151893936201281717160490949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101262624134187811440327299 151893936201281717160490949)
      ·
        refine ⟨28480113037740321967592053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 151893936201281717160490949 28480113037740321967592053)
        ·
          refine ⟨2670010597288155184461755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 28480113037740321967592053 2670010597288155184461755)
          ·
            refine ⟨4005015895932232776692633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2670010597288155184461755 4005015895932232776692633)
            ·
              refine ⟨3003761921949174582519475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4005015895932232776692633 3003761921949174582519475)
              ·
                refine ⟨4505642882923761873779213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3003761921949174582519475 4505642882923761873779213)
                ·
                  refine ⟨1689616081096410702667205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4505642882923761873779213 1689616081096410702667205)
                  ·
                    refine ⟨316803015205577006750101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1689616081096410702667205 316803015205577006750101)
                    ·
                      rfl

theorem cell23_1850915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 2, 1, 3, 4].length) (baseStart_1850915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1850915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1850915 prefixEnd_1850915 := by exact prefixLift 1850915
  have htrace : WordTrace (prefixWord ++ tailWord_1850915) baseStart_1850915 baseEnd_1850915 := by
    simpa [prefixWord, tailWord_1850915, baseEnd_1850915] using wordTrace_append hprefix tailTrace_1850915
  have hstable : (prefixWord ++ tailWord_1850915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1850915).length < 2 ^ (prefixWord ++ tailWord_1850915).sum := by decide
  have hdescent : baseEnd_1850915 < baseStart_1850915 := by decide
  rcases family_descends (prefixWord ++ tailWord_1850915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1850966 : List Nat := [5, 2, 2, 2, 1, 2, 1, 1, 3, 4]
def baseStart_1850966 : Nat := 118140960795 + 1850966 * 2 ^ 59
def prefixEnd_1850966 : Nat := 4983230072969 + 3 ^ 40 * 1850966 * 2
def baseEnd_1850966 : Nat := 316811744376703440237523

theorem tailTrace_1850966 : CollatzResearch.WordTrace tailWord_1850966 prefixEnd_1850966 316811744376703440237523 := by
  unfold tailWord_1850966
  simp only [CollatzResearch.WordTrace]
  refine ⟨4219392263267111041895297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 45006850808182517780216501 4219392263267111041895297)
  ·
    refine ⟨3164544197450333281421473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4219392263267111041895297 3164544197450333281421473)
    ·
      refine ⟨2373408148087749961066105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3164544197450333281421473 2373408148087749961066105)
      ·
        refine ⟨1780056111065812470799579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2373408148087749961066105 1780056111065812470799579)
        ·
          refine ⟨2670084166598718706199369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1780056111065812470799579 2670084166598718706199369)
          ·
            refine ⟨2002563124949039029649527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2670084166598718706199369 2002563124949039029649527)
            ·
              refine ⟨3003844687423558544474291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2002563124949039029649527 3003844687423558544474291)
              ·
                refine ⟨4505767031135337816711437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3003844687423558544474291 4505767031135337816711437)
                ·
                  refine ⟨1689662636675751681266789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4505767031135337816711437 1689662636675751681266789)
                  ·
                    refine ⟨316811744376703440237523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1689662636675751681266789 316811744376703440237523)
                    ·
                      rfl

theorem cell23_1850966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 1, 1, 3, 4].length) (baseStart_1850966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1850966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1850966 prefixEnd_1850966 := by exact prefixLift 1850966
  have htrace : WordTrace (prefixWord ++ tailWord_1850966) baseStart_1850966 baseEnd_1850966 := by
    simpa [prefixWord, tailWord_1850966, baseEnd_1850966] using wordTrace_append hprefix tailTrace_1850966
  have hstable : (prefixWord ++ tailWord_1850966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1850966).length < 2 ^ (prefixWord ++ tailWord_1850966).sum := by decide
  have hdescent : baseEnd_1850966 < baseStart_1850966 := by decide
  rcases family_descends (prefixWord ++ tailWord_1850966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1850972 : List Nat := [2, 2, 4, 1, 2, 1, 3, 1, 3, 1, 3]
def baseStart_1850972 : Nat := 118140960795 + 1850972 * 2 ^ 59
def prefixEnd_1850972 : Nat := 4983230072969 + 3 ^ 40 * 1850972 * 2
def baseEnd_1850972 : Nat := 950438314014037297237541

theorem tailTrace_1850972 : CollatzResearch.WordTrace tailWord_1850972 prefixEnd_1850972 950438314014037297237541 := by
  unfold tailWord_1850972
  simp only [CollatzResearch.WordTrace]
  refine ⟨33755247525126019847521585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45006996700168026463362113 33755247525126019847521585)
  ·
    refine ⟨25316435643844514885641189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33755247525126019847521585 25316435643844514885641189)
    ·
      refine ⟨4746831683220846541057723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25316435643844514885641189 4746831683220846541057723)
      ·
        refine ⟨7120247524831269811586585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4746831683220846541057723 7120247524831269811586585)
        ·
          refine ⟨5340185643623452358689939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7120247524831269811586585 5340185643623452358689939)
          ·
            refine ⟨8010278465435178538034909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5340185643623452358689939 8010278465435178538034909)
            ·
              refine ⟨3003854424538191951763091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8010278465435178538034909 3003854424538191951763091)
              ·
                refine ⟨4505781636807287927644637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3003854424538191951763091 4505781636807287927644637)
                ·
                  refine ⟨1689668113802732972866739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4505781636807287927644637 1689668113802732972866739)
                  ·
                    refine ⟨2534502170704099459300109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1689668113802732972866739 2534502170704099459300109)
                    ·
                      refine ⟨950438314014037297237541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2534502170704099459300109 950438314014037297237541)
                      ·
                        rfl

theorem cell23_1850972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 3, 1, 3, 1, 3].length) (baseStart_1850972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1850972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1850972 prefixEnd_1850972 := by exact prefixLift 1850972
  have htrace : WordTrace (prefixWord ++ tailWord_1850972) baseStart_1850972 baseEnd_1850972 := by
    simpa [prefixWord, tailWord_1850972, baseEnd_1850972] using wordTrace_append hprefix tailTrace_1850972
  have hstable : (prefixWord ++ tailWord_1850972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1850972).length < 2 ^ (prefixWord ++ tailWord_1850972).sum := by decide
  have hdescent : baseEnd_1850972 < baseStart_1850972 := by decide
  rcases family_descends (prefixWord ++ tailWord_1850972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1851001 : List Nat := [1, 2, 1, 3, 3, 1, 1, 11]
def baseStart_1851001 : Nat := 118140960795 + 1851001 * 2 ^ 59
def prefixEnd_1851001 : Nat := 4983230072969 + 3 ^ 40 * 1851001 * 2
def baseEnd_1851001 : Nat := 35201970553815469769441

theorem tailTrace_1851001 : CollatzResearch.WordTrace tailWord_1851001 prefixEnd_1851001 35201970553815469769441 := by
  unfold tailWord_1851001
  simp only [CollatzResearch.WordTrace]
  refine ⟨67511552767146977647848857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45007701844764651765232571 67511552767146977647848857)
  ·
    refine ⟨50633664575360233235886643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67511552767146977647848857 50633664575360233235886643)
    ·
      refine ⟨75950496863040349853829965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50633664575360233235886643 75950496863040349853829965)
      ·
        refine ⟨28481436323640131195186237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75950496863040349853829965 28481436323640131195186237)
        ·
          refine ⟨10680538621365049198194839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28481436323640131195186237 10680538621365049198194839)
          ·
            refine ⟨16020807932047573797292259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10680538621365049198194839 16020807932047573797292259)
            ·
              refine ⟨24031211898071360695938389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16020807932047573797292259 24031211898071360695938389)
              ·
                refine ⟨35201970553815469769441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 24031211898071360695938389 35201970553815469769441)
                ·
                  rfl

theorem cell23_1851001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 11].length) (baseStart_1851001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1851001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1851001 prefixEnd_1851001 := by exact prefixLift 1851001
  have htrace : WordTrace (prefixWord ++ tailWord_1851001) baseStart_1851001 baseEnd_1851001 := by
    simpa [prefixWord, tailWord_1851001, baseEnd_1851001] using wordTrace_append hprefix tailTrace_1851001
  have hstable : (prefixWord ++ tailWord_1851001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1851001).length < 2 ^ (prefixWord ++ tailWord_1851001).sum := by decide
  have hdescent : baseEnd_1851001 < baseStart_1851001 := by decide
  rcases family_descends (prefixWord ++ tailWord_1851001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1851008 : List Nat := [2, 1, 1, 2, 1, 4, 3, 2, 1, 2, 4]
def baseStart_1851008 : Nat := 118140960795 + 1851008 * 2 ^ 59
def prefixEnd_1851008 : Nat := 4983230072969 + 3 ^ 40 * 1851008 * 2
def baseEnd_1851008 : Nat := 950456799317599156387375

theorem tailTrace_1851008 : CollatzResearch.WordTrace tailWord_1851008 prefixEnd_1851008 950456799317599156387375 := by
  unfold tailWord_1851008
  simp only [CollatzResearch.WordTrace]
  refine ⟨33755904039060808921676839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45007872052081078562235785 33755904039060808921676839)
  ·
    refine ⟨50633856058591213382515259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33755904039060808921676839 50633856058591213382515259)
    ·
      refine ⟨75950784087886820073772889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50633856058591213382515259 75950784087886820073772889)
      ·
        refine ⟨56963088065915115055329667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75950784087886820073772889 56963088065915115055329667)
        ·
          refine ⟨85444632098872672582994501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56963088065915115055329667 85444632098872672582994501)
          ·
            refine ⟨16020868518538626109311469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85444632098872672582994501 16020868518538626109311469)
            ·
              refine ⟨6007825694451984790991801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16020868518538626109311469 6007825694451984790991801)
              ·
                refine ⟨4505869270838988593243851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6007825694451984790991801 4505869270838988593243851)
                ·
                  refine ⟨6758803906258482889865777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4505869270838988593243851 6758803906258482889865777)
                  ·
                    refine ⟨5069102929693862167399333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6758803906258482889865777 5069102929693862167399333)
                    ·
                      refine ⟨950456799317599156387375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5069102929693862167399333 950456799317599156387375)
                      ·
                        rfl

theorem cell23_1851008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 2, 1, 2, 4].length) (baseStart_1851008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1851008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1851008 prefixEnd_1851008 := by exact prefixLift 1851008
  have htrace : WordTrace (prefixWord ++ tailWord_1851008) baseStart_1851008 baseEnd_1851008 := by
    simpa [prefixWord, tailWord_1851008, baseEnd_1851008] using wordTrace_append hprefix tailTrace_1851008
  have hstable : (prefixWord ++ tailWord_1851008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1851008).length < 2 ^ (prefixWord ++ tailWord_1851008).sum := by decide
  have hdescent : baseEnd_1851008 < baseStart_1851008 := by decide
  rcases family_descends (prefixWord ++ tailWord_1851008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1851015 : List Nat := [1, 1, 4, 2, 1, 5, 1, 1, 1, 1, 5]
def baseStart_1851015 : Nat := 118140960795 + 1851015 * 2 ^ 59
def prefixEnd_1851015 : Nat := 4983230072969 + 3 ^ 40 * 1851015 * 2
def baseEnd_1851015 : Nat := 950460393682180628999843

theorem tailTrace_1851015 : CollatzResearch.WordTrace tailWord_1851015 prefixEnd_1851015 950460393682180628999843 := by
  unfold tailWord_1851015
  simp only [CollatzResearch.WordTrace]
  refine ⟨67512063389096258038858499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45008042259397505359238999 67512063389096258038858499)
  ·
    refine ⟨101268095083644387058287749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67512063389096258038858499 101268095083644387058287749)
    ·
      refine ⟨18987767828183322573428953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101268095083644387058287749 18987767828183322573428953)
      ·
        refine ⟨14240825871137491930071715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18987767828183322573428953 14240825871137491930071715)
        ·
          refine ⟨21361238806706237895107573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14240825871137491930071715 21361238806706237895107573)
          ·
            refine ⟨2002616138128709802666335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21361238806706237895107573 2002616138128709802666335)
            ·
              refine ⟨3003924207193064703999503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2002616138128709802666335 3003924207193064703999503)
              ·
                refine ⟨4505886310789597055999255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3003924207193064703999503 4505886310789597055999255)
                ·
                  refine ⟨6758829466184395583998883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4505886310789597055999255 6758829466184395583998883)
                  ·
                    refine ⟨10138244199276593375998325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6758829466184395583998883 10138244199276593375998325)
                    ·
                      refine ⟨950460393682180628999843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10138244199276593375998325 950460393682180628999843)
                      ·
                        rfl

theorem cell23_1851015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 1, 1, 1, 1, 5].length) (baseStart_1851015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1851015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1851015 prefixEnd_1851015 := by exact prefixLift 1851015
  have htrace : WordTrace (prefixWord ++ tailWord_1851015) baseStart_1851015 baseEnd_1851015 := by
    simpa [prefixWord, tailWord_1851015, baseEnd_1851015] using wordTrace_append hprefix tailTrace_1851015
  have hstable : (prefixWord ++ tailWord_1851015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1851015).length < 2 ^ (prefixWord ++ tailWord_1851015).sum := by decide
  have hdescent : baseEnd_1851015 < baseStart_1851015 := by decide
  rcases family_descends (prefixWord ++ tailWord_1851015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1851022 : List Nat := [4, 1, 1, 3, 1, 3, 2, 2, 2, 4]
def baseStart_1851022 : Nat := 118140960795 + 1851022 * 2 ^ 59
def prefixEnd_1851022 : Nat := 4983230072969 + 3 ^ 40 * 1851022 * 2
def baseEnd_1851022 : Nat := 316821329348920700537437

theorem tailTrace_1851022 : CollatzResearch.WordTrace tailWord_1851022 prefixEnd_1851022 316821329348920700537437 := by
  unfold tailWord_1851022
  simp only [CollatzResearch.WordTrace]
  refine ⟨8439039837508862279295415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45008212466713932156242213 8439039837508862279295415)
  ·
    refine ⟨12658559756263293418943123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8439039837508862279295415 12658559756263293418943123)
    ·
      refine ⟨18987839634394940128414685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12658559756263293418943123 18987839634394940128414685)
      ·
        refine ⟨7120439862898102548155507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18987839634394940128414685 7120439862898102548155507)
        ·
          refine ⟨10680659794347153822233261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7120439862898102548155507 10680659794347153822233261)
          ·
            refine ⟨4005247422880182683337473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10680659794347153822233261 4005247422880182683337473)
            ·
              refine ⟨3003935567160137012503105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4005247422880182683337473 3003935567160137012503105)
              ·
                refine ⟨2252951675370102759377329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3003935567160137012503105 2252951675370102759377329)
                ·
                  refine ⟨1689713756527577069532997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2252951675370102759377329 1689713756527577069532997)
                  ·
                    refine ⟨316821329348920700537437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1689713756527577069532997 316821329348920700537437)
                    ·
                      rfl

theorem cell23_1851022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 2, 2, 2, 4].length) (baseStart_1851022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1851022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1851022 prefixEnd_1851022 := by exact prefixLift 1851022
  have htrace : WordTrace (prefixWord ++ tailWord_1851022) baseStart_1851022 baseEnd_1851022 := by
    simpa [prefixWord, tailWord_1851022, baseEnd_1851022] using wordTrace_append hprefix tailTrace_1851022
  have hstable : (prefixWord ++ tailWord_1851022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1851022).length < 2 ^ (prefixWord ++ tailWord_1851022).sum := by decide
  have hdescent : baseEnd_1851022 < baseStart_1851022 := by decide
  rcases family_descends (prefixWord ++ tailWord_1851022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1851055 : List Nat := [1, 1, 2, 1, 2, 4, 1, 3, 3, 3, 2]
def baseStart_1851055 : Nat := 118140960795 + 1851055 * 2 ^ 59
def prefixEnd_1851055 : Nat := 4983230072969 + 3 ^ 40 * 1851055 * 2
def baseEnd_1851055 : Nat := 950480932908360472499659

theorem tailTrace_1851055 : CollatzResearch.WordTrace tailWord_1851055 prefixEnd_1851055 950480932908360472499659 := by
  unfold tailWord_1851055
  simp only [CollatzResearch.WordTrace]
  refine ⟨67513522308951344870314619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45009014872634229913543079 67513522308951344870314619)
  ·
    refine ⟨101270283463427017305471929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67513522308951344870314619 101270283463427017305471929)
    ·
      refine ⟨75952712597570262979103947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101270283463427017305471929 75952712597570262979103947)
      ·
        refine ⟨113929068896355394468655921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75952712597570262979103947 113929068896355394468655921)
        ·
          refine ⟨85446801672266545851491941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113929068896355394468655921 85446801672266545851491941)
          ·
            refine ⟨16021275313549977347154739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85446801672266545851491941 16021275313549977347154739)
            ·
              refine ⟨24031912970324966020732109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16021275313549977347154739 24031912970324966020732109)
              ·
                refine ⟨9011967363871862257774541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24031912970324966020732109 9011967363871862257774541)
                ·
                  refine ⟨3379487761451948346665453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9011967363871862257774541 3379487761451948346665453)
                  ·
                    refine ⟨1267307910544480629999545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3379487761451948346665453 1267307910544480629999545)
                    ·
                      refine ⟨950480932908360472499659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1267307910544480629999545 950480932908360472499659)
                      ·
                        rfl

theorem cell23_1851055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 3, 3, 3, 2].length) (baseStart_1851055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1851055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1851055 prefixEnd_1851055 := by exact prefixLift 1851055
  have htrace : WordTrace (prefixWord ++ tailWord_1851055) baseStart_1851055 baseEnd_1851055 := by
    simpa [prefixWord, tailWord_1851055, baseEnd_1851055] using wordTrace_append hprefix tailTrace_1851055
  have hstable : (prefixWord ++ tailWord_1851055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1851055).length < 2 ^ (prefixWord ++ tailWord_1851055).sum := by decide
  have hdescent : baseEnd_1851055 < baseStart_1851055 := by decide
  rcases family_descends (prefixWord ++ tailWord_1851055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1851072 : List Nat := [2, 1, 1, 2, 4, 1, 3, 3, 1, 3, 2]
def baseStart_1851072 : Nat := 118140960795 + 1851072 * 2 ^ 59
def prefixEnd_1851072 : Nat := 4983230072969 + 3 ^ 40 * 1851072 * 2
def baseEnd_1851072 : Nat := 950489662079486905987081

theorem tailTrace_1851072 : CollatzResearch.WordTrace tailWord_1851072 prefixEnd_1851072 950489662079486905987081 := by
  unfold tailWord_1851072
  simp only [CollatzResearch.WordTrace]
  refine ⟨33757071174944878386841735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45009428233259837849122313 33757071174944878386841735)
  ·
    refine ⟨50635606762417317580262603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33757071174944878386841735 50635606762417317580262603)
    ·
      refine ⟨75953410143625976370393905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50635606762417317580262603 75953410143625976370393905)
      ·
        refine ⟨56965057607719482277795429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75953410143625976370393905 56965057607719482277795429)
        ·
          refine ⟨10680948301447402927086643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56965057607719482277795429 10680948301447402927086643)
          ·
            refine ⟨16021422452171104390629965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10680948301447402927086643 16021422452171104390629965)
            ·
              refine ⟨6008033419564164146486237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16021422452171104390629965 6008033419564164146486237)
              ·
                refine ⟨2253012532336561554932339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6008033419564164146486237 2253012532336561554932339)
                ·
                  refine ⟨3379518798504842332398509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2253012532336561554932339 3379518798504842332398509)
                  ·
                    refine ⟨1267319549439315874649441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3379518798504842332398509 1267319549439315874649441)
                    ·
                      refine ⟨950489662079486905987081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1267319549439315874649441 950489662079486905987081)
                      ·
                        rfl

theorem cell23_1851072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 3, 1, 3, 2].length) (baseStart_1851072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1851072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1851072 prefixEnd_1851072 := by exact prefixLift 1851072
  have htrace : WordTrace (prefixWord ++ tailWord_1851072) baseStart_1851072 baseEnd_1851072 := by
    simpa [prefixWord, tailWord_1851072, baseEnd_1851072] using wordTrace_append hprefix tailTrace_1851072
  have hstable : (prefixWord ++ tailWord_1851072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1851072).length < 2 ^ (prefixWord ++ tailWord_1851072).sum := by decide
  have hdescent : baseEnd_1851072 < baseStart_1851072 := by decide
  rcases family_descends (prefixWord ++ tailWord_1851072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1851088 : List Nat := [2, 1, 1, 1, 1, 2, 1, 5, 2, 4, 3]
def baseStart_1851088 : Nat := 118140960795 + 1851088 * 2 ^ 59
def prefixEnd_1851088 : Nat := 4983230072969 + 3 ^ 40 * 1851088 * 2
def baseEnd_1851088 : Nat := 950497877769958843387007

theorem tailTrace_1851088 : CollatzResearch.WordTrace tailWord_1851088 prefixEnd_1851088 950497877769958843387007 := by
  unfold tailWord_1851088
  simp only [CollatzResearch.WordTrace]
  refine ⟨33757362958915895753132959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45009817278554527670843945 33757362958915895753132959)
  ·
    refine ⟨50636044438373843629699439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33757362958915895753132959 50636044438373843629699439)
    ·
      refine ⟨75954066657560765444549159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50636044438373843629699439 75954066657560765444549159)
      ·
        refine ⟨113931099986341148166823739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75954066657560765444549159 113931099986341148166823739)
        ·
          refine ⟨170896649979511722250235609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113931099986341148166823739 170896649979511722250235609)
          ·
            refine ⟨128172487484633791687676707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170896649979511722250235609 128172487484633791687676707)
            ·
              refine ⟨192258731226950687531515061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128172487484633791687676707 192258731226950687531515061)
              ·
                refine ⟨18024256052526626956079537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 192258731226950687531515061 18024256052526626956079537)
                ·
                  refine ⟨13518192039394970217059653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18024256052526626956079537 13518192039394970217059653)
                  ·
                    refine ⟨2534661007386556915698685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13518192039394970217059653 2534661007386556915698685)
                    ·
                      refine ⟨950497877769958843387007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2534661007386556915698685 950497877769958843387007)
                      ·
                        rfl

theorem cell23_1851088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 5, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 5, 2, 4, 3].length) (baseStart_1851088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1851088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1851088 prefixEnd_1851088 := by exact prefixLift 1851088
  have htrace : WordTrace (prefixWord ++ tailWord_1851088) baseStart_1851088 baseEnd_1851088 := by
    simpa [prefixWord, tailWord_1851088, baseEnd_1851088] using wordTrace_append hprefix tailTrace_1851088
  have hstable : (prefixWord ++ tailWord_1851088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1851088).length < 2 ^ (prefixWord ++ tailWord_1851088).sum := by decide
  have hdescent : baseEnd_1851088 < baseStart_1851088 := by decide
  rcases family_descends (prefixWord ++ tailWord_1851088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1851108 : List Nat := [2, 3, 1, 1, 1, 3, 1, 4, 7]
def baseStart_1851108 : Nat := 118140960795 + 1851108 * 2 ^ 59
def prefixEnd_1851108 : Nat := 4983230072969 + 3 ^ 40 * 1851108 * 2
def baseEnd_1851108 : Nat := 105612016375894307237435

theorem tailTrace_1851108 : CollatzResearch.WordTrace tailWord_1851108 prefixEnd_1851108 105612016375894307237435 := by
  unfold tailWord_1851108
  simp only [CollatzResearch.WordTrace]
  refine ⟨33757727688879667460996989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45010303585172889947995985 33757727688879667460996989)
  ·
    refine ⟨12659147883329875297873871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33757727688879667460996989 12659147883329875297873871)
    ·
      refine ⟨18988721824994812946810807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12659147883329875297873871 18988721824994812946810807)
      ·
        refine ⟨28483082737492219420216211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18988721824994812946810807 28483082737492219420216211)
        ·
          refine ⟨42724624106238329130324317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28483082737492219420216211 42724624106238329130324317)
          ·
            refine ⟨16021734039839373423871619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42724624106238329130324317 16021734039839373423871619)
            ·
              refine ⟨24032601059759060135807429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16021734039839373423871619 24032601059759060135807429)
              ·
                refine ⟨4506112698704823775463893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24032601059759060135807429 4506112698704823775463893)
                ·
                  refine ⟨105612016375894307237435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4506112698704823775463893 105612016375894307237435)
                  ·
                    rfl

theorem cell23_1851108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 4, 7].length) (baseStart_1851108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1851108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1851108 prefixEnd_1851108 := by exact prefixLift 1851108
  have htrace : WordTrace (prefixWord ++ tailWord_1851108) baseStart_1851108 baseEnd_1851108 := by
    simpa [prefixWord, tailWord_1851108, baseEnd_1851108] using wordTrace_append hprefix tailTrace_1851108
  have hstable : (prefixWord ++ tailWord_1851108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1851108).length < 2 ^ (prefixWord ++ tailWord_1851108).sum := by decide
  have hdescent : baseEnd_1851108 < baseStart_1851108 := by decide
  rcases family_descends (prefixWord ++ tailWord_1851108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1851145 : List Nat := [1, 2, 1, 1, 3, 2, 1, 3, 2, 5, 2]
def baseStart_1851145 : Nat := 118140960795 + 1851145 * 2 ^ 59
def prefixEnd_1851145 : Nat := 4983230072969 + 3 ^ 40 * 1851145 * 2
def baseEnd_1851145 : Nat := 950527146167265120374245

theorem tailTrace_1851145 : CollatzResearch.WordTrace tailWord_1851145 prefixEnd_1851145 950527146167265120374245 := by
  unfold tailWord_1851145
  simp only [CollatzResearch.WordTrace]
  refine ⟨67516804878625290241090889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45011203252416860160727259 67516804878625290241090889)
  ·
    refine ⟨50637603658968967680818167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67516804878625290241090889 50637603658968967680818167)
    ·
      refine ⟨75956405488453451521227251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50637603658968967680818167 75956405488453451521227251)
      ·
        refine ⟨113934608232680177281840877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75956405488453451521227251 113934608232680177281840877)
        ·
          refine ⟨42725478087255066480690329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113934608232680177281840877 42725478087255066480690329)
          ·
            refine ⟨32044108565441299860517747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42725478087255066480690329 32044108565441299860517747)
            ·
              refine ⟨48066162848161949790776621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32044108565441299860517747 48066162848161949790776621)
              ·
                refine ⟨18024811068060731171541233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48066162848161949790776621 18024811068060731171541233)
                ·
                  refine ⟨13518608301045548378655925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18024811068060731171541233 13518608301045548378655925)
                  ·
                    refine ⟨1267369528223020160498993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13518608301045548378655925 1267369528223020160498993)
                    ·
                      refine ⟨950527146167265120374245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1267369528223020160498993 950527146167265120374245)
                      ·
                        rfl

theorem cell23_1851145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 3, 2, 5, 2].length) (baseStart_1851145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1851145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1851145 prefixEnd_1851145 := by exact prefixLift 1851145
  have htrace : WordTrace (prefixWord ++ tailWord_1851145) baseStart_1851145 baseEnd_1851145 := by
    simpa [prefixWord, tailWord_1851145, baseEnd_1851145] using wordTrace_append hprefix tailTrace_1851145
  have hstable : (prefixWord ++ tailWord_1851145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1851145).length < 2 ^ (prefixWord ++ tailWord_1851145).sum := by decide
  have hdescent : baseEnd_1851145 < baseStart_1851145 := by decide
  rcases family_descends (prefixWord ++ tailWord_1851145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1851148 : List Nat := [2, 2, 1, 2, 2, 1, 3, 1, 1, 1, 7]
def baseStart_1851148 : Nat := 118140960795 + 1851148 * 2 ^ 59
def prefixEnd_1851148 : Nat := 4983230072969 + 3 ^ 40 * 1851148 * 2
def baseEnd_1851148 : Nat := 950528686609228608636731

theorem tailTrace_1851148 : CollatzResearch.WordTrace tailWord_1851148 prefixEnd_1851148 950528686609228608636731 := by
  unfold tailWord_1851148
  simp only [CollatzResearch.WordTrace]
  refine ⟨33758457148807210876725049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45011276198409614502300065 33758457148807210876725049)
  ·
    refine ⟨25318842861605408157543787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33758457148807210876725049 25318842861605408157543787)
    ·
      refine ⟨37978264292408112236315681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25318842861605408157543787 37978264292408112236315681)
      ·
        refine ⟨28483698219306084177236761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37978264292408112236315681 28483698219306084177236761)
        ·
          refine ⟨21362773664479563132927571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28483698219306084177236761 21362773664479563132927571)
          ·
            refine ⟨32044160496719344699391357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21362773664479563132927571 32044160496719344699391357)
            ·
              refine ⟨12016560186269754262271759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32044160496719344699391357 12016560186269754262271759)
              ·
                refine ⟨18024840279404631393407639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12016560186269754262271759 18024840279404631393407639)
                ·
                  refine ⟨27037260419106947090111459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18024840279404631393407639 27037260419106947090111459)
                  ·
                    refine ⟨40555890628660420635167189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27037260419106947090111459 40555890628660420635167189)
                    ·
                      refine ⟨950528686609228608636731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 40555890628660420635167189 950528686609228608636731)
                      ·
                        rfl

theorem cell23_1851148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 1, 1, 1, 7].length) (baseStart_1851148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1851148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1851148 prefixEnd_1851148 := by exact prefixLift 1851148
  have htrace : WordTrace (prefixWord ++ tailWord_1851148) baseStart_1851148 baseEnd_1851148 := by
    simpa [prefixWord, tailWord_1851148, baseEnd_1851148] using wordTrace_append hprefix tailTrace_1851148
  have hstable : (prefixWord ++ tailWord_1851148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1851148).length < 2 ^ (prefixWord ++ tailWord_1851148).sum := by decide
  have hdescent : baseEnd_1851148 < baseStart_1851148 := by decide
  rcases family_descends (prefixWord ++ tailWord_1851148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1851172 : List Nat := [2, 3, 1, 3, 2, 2, 2, 1, 2, 5]
def baseStart_1851172 : Nat := 118140960795 + 1851172 * 2 ^ 59
def prefixEnd_1851172 : Nat := 4983230072969 + 3 ^ 40 * 1851172 * 2
def baseEnd_1851172 : Nat := 316847003381645504912207

theorem tailTrace_1851172 : CollatzResearch.WordTrace tailWord_1851172 prefixEnd_1851172 316847003381645504912207 := by
  unfold tailWord_1851172
  simp only [CollatzResearch.WordTrace]
  refine ⟨33758894824763736926161885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45011859766351649234882513 33758894824763736926161885)
  ·
    refine ⟨12659585559286401347310707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33758894824763736926161885 12659585559286401347310707)
    ·
      refine ⟨18989378338929602020966061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12659585559286401347310707 18989378338929602020966061)
      ·
        refine ⟨7121016877098600757862273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18989378338929602020966061 7121016877098600757862273)
        ·
          refine ⟨5340762657823950568396705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7121016877098600757862273 5340762657823950568396705)
          ·
            refine ⟨4005571993367962926297529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5340762657823950568396705 4005571993367962926297529)
            ·
              refine ⟨3004178995025972194723147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4005571993367962926297529 3004178995025972194723147)
              ·
                refine ⟨4506268492538958292084721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3004178995025972194723147 4506268492538958292084721)
                ·
                  refine ⟨3379701369404218719063541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4506268492538958292084721 3379701369404218719063541)
                  ·
                    refine ⟨316847003381645504912207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3379701369404218719063541 316847003381645504912207)
                    ·
                      rfl

theorem cell23_1851172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 2, 1, 2, 5].length) (baseStart_1851172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1851172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1851172 prefixEnd_1851172 := by exact prefixLift 1851172
  have htrace : WordTrace (prefixWord ++ tailWord_1851172) baseStart_1851172 baseEnd_1851172 := by
    simpa [prefixWord, tailWord_1851172, baseEnd_1851172] using wordTrace_append hprefix tailTrace_1851172
  have hstable : (prefixWord ++ tailWord_1851172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1851172).length < 2 ^ (prefixWord ++ tailWord_1851172).sum := by decide
  have hdescent : baseEnd_1851172 < baseStart_1851172 := by decide
  rcases family_descends (prefixWord ++ tailWord_1851172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1851193 : List Nat := [1, 2, 1, 7, 2, 1, 2, 2, 5]
def baseStart_1851193 : Nat := 118140960795 + 1851193 * 2 ^ 59
def prefixEnd_1851193 : Nat := 4983230072969 + 3 ^ 40 * 1851193 * 2
def baseEnd_1851193 : Nat := 105616865915408992508225

theorem tailTrace_1851193 : CollatzResearch.WordTrace tailWord_1851193 prefixEnd_1851193 105616865915408992508225 := by
  unfold tailWord_1851193
  simp only [CollatzResearch.WordTrace]
  refine ⟨67518555582451394438838233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45012370388300929625892155 67518555582451394438838233)
  ·
    refine ⟨50638916686838545829128675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67518555582451394438838233 50638916686838545829128675)
    ·
      refine ⟨75958375030257818743693013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50638916686838545829128675 75958375030257818743693013)
      ·
        refine ⟨1780274414771667626805305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 75958375030257818743693013 1780274414771667626805305)
        ·
          refine ⟨1335205811078750720103979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1780274414771667626805305 1335205811078750720103979)
          ·
            refine ⟨2002808716618126080155969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1335205811078750720103979 2002808716618126080155969)
            ·
              refine ⟨1502106537463594560116977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2002808716618126080155969 1502106537463594560116977)
              ·
                refine ⟨1126579903097695920087733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1502106537463594560116977 1126579903097695920087733)
                ·
                  refine ⟨105616865915408992508225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1126579903097695920087733 105616865915408992508225)
                  ·
                    rfl

theorem cell23_1851193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 2, 2, 5].length) (baseStart_1851193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1851193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1851193 prefixEnd_1851193 := by exact prefixLift 1851193
  have htrace : WordTrace (prefixWord ++ tailWord_1851193) baseStart_1851193 baseEnd_1851193 := by
    simpa [prefixWord, tailWord_1851193, baseEnd_1851193] using wordTrace_append hprefix tailTrace_1851193
  have hstable : (prefixWord ++ tailWord_1851193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1851193).length < 2 ^ (prefixWord ++ tailWord_1851193).sum := by decide
  have hdescent : baseEnd_1851193 < baseStart_1851193 := by decide
  rcases family_descends (prefixWord ++ tailWord_1851193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1851236 : List Nat := [2, 3, 1, 1, 5, 1, 2, 3, 1, 4]
def baseStart_1851236 : Nat := 118140960795 + 1851236 * 2 ^ 59
def prefixEnd_1851236 : Nat := 4983230072969 + 3 ^ 40 * 1851236 * 2
def baseEnd_1851236 : Nat := 316857957635608088112109

theorem tailTrace_1851236 : CollatzResearch.WordTrace tailWord_1851236 prefixEnd_1851236 316857957635608088112109 := by
  unfold tailWord_1851236
  simp only [CollatzResearch.WordTrace]
  refine ⟨33760061960647806391326781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45013415947530408521769041 33760061960647806391326781)
  ·
    refine ⟨12660023235242927396747543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33760061960647806391326781 12660023235242927396747543)
    ·
      refine ⟨18990034852864391095121315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12660023235242927396747543 18990034852864391095121315)
      ·
        refine ⟨28485052279296586642681973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18990034852864391095121315 28485052279296586642681973)
        ·
          refine ⟨2670473651184054997751435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 28485052279296586642681973 2670473651184054997751435)
          ·
            refine ⟨4005710476776082496627153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2670473651184054997751435 4005710476776082496627153)
            ·
              refine ⟨3004282857582061872470365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4005710476776082496627153 3004282857582061872470365)
              ·
                refine ⟨1126606071593273202176387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3004282857582061872470365 1126606071593273202176387)
                ·
                  refine ⟨1689909107389909803264581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1126606071593273202176387 1689909107389909803264581)
                  ·
                    refine ⟨316857957635608088112109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1689909107389909803264581 316857957635608088112109)
                    ·
                      rfl

theorem cell23_1851236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 2, 3, 1, 4].length) (baseStart_1851236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1851236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1851236 prefixEnd_1851236 := by exact prefixLift 1851236
  have htrace : WordTrace (prefixWord ++ tailWord_1851236) baseStart_1851236 baseEnd_1851236 := by
    simpa [prefixWord, tailWord_1851236, baseEnd_1851236] using wordTrace_append hprefix tailTrace_1851236
  have hstable : (prefixWord ++ tailWord_1851236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1851236).length < 2 ^ (prefixWord ++ tailWord_1851236).sum := by decide
  have hdescent : baseEnd_1851236 < baseStart_1851236 := by decide
  rcases family_descends (prefixWord ++ tailWord_1851236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1851285 : List Nat := [1, 3, 2, 1, 1, 3, 1, 2, 3, 1, 5]
def baseStart_1851285 : Nat := 118140960795 + 1851285 * 2 ^ 59
def prefixEnd_1851285 : Nat := 4983230072969 + 3 ^ 40 * 1851285 * 2
def baseEnd_1851285 : Nat := 950599033458894572623601

theorem tailTrace_1851285 : CollatzResearch.WordTrace tailWord_1851285 prefixEnd_1851285 950599033458894572623601 := by
  unfold tailWord_1851285
  simp only [CollatzResearch.WordTrace]
  refine ⟨67521911098118094151187309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45014607398745396100791539 67521911098118094151187309)
  ·
    refine ⟨25320716661794285306695241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67521911098118094151187309 25320716661794285306695241)
    ·
      refine ⟨18990537496345713980021431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25320716661794285306695241 18990537496345713980021431)
      ·
        refine ⟨28485806244518570970032147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18990537496345713980021431 28485806244518570970032147)
        ·
          refine ⟨42728709366777856455048221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28485806244518570970032147 42728709366777856455048221)
          ·
            refine ⟨16023266012541696170643083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42728709366777856455048221 16023266012541696170643083)
            ·
              refine ⟨24034899018812544255964625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16023266012541696170643083 24034899018812544255964625)
              ·
                refine ⟨18026174264109408191973469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24034899018812544255964625 18026174264109408191973469)
                ·
                  refine ⟨6759815349041028071990051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18026174264109408191973469 6759815349041028071990051)
                  ·
                    refine ⟨10139723023561542107985077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6759815349041028071990051 10139723023561542107985077)
                    ·
                      refine ⟨950599033458894572623601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10139723023561542107985077 950599033458894572623601)
                      ·
                        rfl

theorem cell23_1851285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 2, 3, 1, 5].length) (baseStart_1851285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1851285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1851285 prefixEnd_1851285 := by exact prefixLift 1851285
  have htrace : WordTrace (prefixWord ++ tailWord_1851285) baseStart_1851285 baseEnd_1851285 := by
    simpa [prefixWord, tailWord_1851285, baseEnd_1851285] using wordTrace_append hprefix tailTrace_1851285
  have hstable : (prefixWord ++ tailWord_1851285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1851285).length < 2 ^ (prefixWord ++ tailWord_1851285).sum := by decide
  have hdescent : baseEnd_1851285 < baseStart_1851285 := by decide
  rcases family_descends (prefixWord ++ tailWord_1851285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1851293 : List Nat := [1, 4, 2, 1, 2, 4, 1, 3, 1, 1, 3]
def baseStart_1851293 : Nat := 118140960795 + 1851293 * 2 ^ 59
def prefixEnd_1851293 : Nat := 4983230072969 + 3 ^ 40 * 1851293 * 2
def baseEnd_1851293 : Nat := 950603141304130541323565

theorem tailTrace_1851293 : CollatzResearch.WordTrace tailWord_1851293 prefixEnd_1851293 950603141304130541323565 := by
  unfold tailWord_1851293
  simp only [CollatzResearch.WordTrace]
  refine ⟨67522202882089111517478533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45014801921392741011652355 67522202882089111517478533)
  ·
    refine ⟨12660413040391708409527225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67522202882089111517478533 12660413040391708409527225)
    ·
      refine ⟨9495309780293781307145419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12660413040391708409527225 9495309780293781307145419)
      ·
        refine ⟨14242964670440671960718129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9495309780293781307145419 14242964670440671960718129)
        ·
          refine ⟨10682223502830503970538597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14242964670440671960718129 10682223502830503970538597)
          ·
            refine ⟨2002916906780719494475987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10682223502830503970538597 2002916906780719494475987)
            ·
              refine ⟨3004375360171079241713981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2002916906780719494475987 3004375360171079241713981)
              ·
                refine ⟨1126640760064154715642743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3004375360171079241713981 1126640760064154715642743)
                ·
                  refine ⟨1689961140096232073464115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1126640760064154715642743 1689961140096232073464115)
                  ·
                    refine ⟨2534941710144348110196173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1689961140096232073464115 2534941710144348110196173)
                    ·
                      refine ⟨950603141304130541323565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2534941710144348110196173 950603141304130541323565)
                      ·
                        rfl

theorem cell23_1851293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 1, 3, 1, 1, 3].length) (baseStart_1851293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1851293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1851293 prefixEnd_1851293 := by exact prefixLift 1851293
  have htrace : WordTrace (prefixWord ++ tailWord_1851293) baseStart_1851293 baseEnd_1851293 := by
    simpa [prefixWord, tailWord_1851293, baseEnd_1851293] using wordTrace_append hprefix tailTrace_1851293
  have hstable : (prefixWord ++ tailWord_1851293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1851293).length < 2 ^ (prefixWord ++ tailWord_1851293).sum := by decide
  have hdescent : baseEnd_1851293 < baseStart_1851293 := by decide
  rcases family_descends (prefixWord ++ tailWord_1851293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1851326 : List Nat := [4, 2, 1, 1, 1, 3, 4, 1, 2, 4]
def baseStart_1851326 : Nat := 118140960795 + 1851326 * 2 ^ 59
def prefixEnd_1851326 : Nat := 4983230072969 + 3 ^ 40 * 1851326 * 2
def baseEnd_1851326 : Nat := 316873362055242970736971

theorem tailTrace_1851326 : CollatzResearch.WordTrace tailWord_1851326 prefixEnd_1851326 316873362055242970736971 := by
  unfold tailWord_1851326
  simp only [CollatzResearch.WordTrace]
  refine ⟨8440425811371194769178729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45015604327313038768953221 8440425811371194769178729)
  ·
    refine ⟨6330319358528396076884047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8440425811371194769178729 6330319358528396076884047)
    ·
      refine ⟨9495479037792594115326071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6330319358528396076884047 9495479037792594115326071)
      ·
        refine ⟨14243218556688891172989107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9495479037792594115326071 14243218556688891172989107)
        ·
          refine ⟨21364827835033336759483661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14243218556688891172989107 21364827835033336759483661)
          ·
            refine ⟨8011810438137501284806373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21364827835033336759483661 8011810438137501284806373)
            ·
              refine ⟨1502214457150781490901195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8011810438137501284806373 1502214457150781490901195)
              ·
                refine ⟨2253321685726172236351793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1502214457150781490901195 2253321685726172236351793)
                ·
                  refine ⟨1689991264294629177263845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2253321685726172236351793 1689991264294629177263845)
                  ·
                    refine ⟨316873362055242970736971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1689991264294629177263845 316873362055242970736971)
                    ·
                      rfl

theorem cell23_1851326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 4, 1, 2, 4].length) (baseStart_1851326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1851326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1851326 prefixEnd_1851326 := by exact prefixLift 1851326
  have htrace : WordTrace (prefixWord ++ tailWord_1851326) baseStart_1851326 baseEnd_1851326 := by
    simpa [prefixWord, tailWord_1851326, baseEnd_1851326] using wordTrace_append hprefix tailTrace_1851326
  have hstable : (prefixWord ++ tailWord_1851326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1851326).length < 2 ^ (prefixWord ++ tailWord_1851326).sum := by decide
  have hdescent : baseEnd_1851326 < baseStart_1851326 := by decide
  rcases family_descends (prefixWord ++ tailWord_1851326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1851336 : List Nat := [2, 1, 3, 1, 4, 3, 1, 2, 1, 2, 3]
def baseStart_1851336 : Nat := 118140960795 + 1851336 * 2 ^ 59
def prefixEnd_1851336 : Nat := 4983230072969 + 3 ^ 40 * 1851336 * 2
def baseEnd_1851336 : Nat := 950625220972273873085867

theorem tailTrace_1851336 : CollatzResearch.WordTrace tailWord_1851336 prefixEnd_1851336 950625220972273873085867 := by
  unfold tailWord_1851336
  simp only [CollatzResearch.WordTrace]
  refine ⟨33761885610466664930646931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45015847480622219907529241 33761885610466664930646931)
  ·
    refine ⟨50642828415699997395970397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33761885610466664930646931 50642828415699997395970397)
    ·
      refine ⟨18991060655887499023488899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50642828415699997395970397 18991060655887499023488899)
      ·
        refine ⟨28486590983831248535233349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18991060655887499023488899 28486590983831248535233349)
        ·
          refine ⟨5341235809468359100356253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28486590983831248535233349 5341235809468359100356253)
          ·
            refine ⟨2002963428550634662633595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5341235809468359100356253 2002963428550634662633595)
            ·
              refine ⟨3004445142825951993950393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2002963428550634662633595 3004445142825951993950393)
              ·
                refine ⟨2253333857119463995462795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3004445142825951993950393 2253333857119463995462795)
                ·
                  refine ⟨3380000785679195993194193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2253333857119463995462795 3380000785679195993194193)
                  ·
                    refine ⟨2535000589259396994895645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3380000785679195993194193 2535000589259396994895645)
                    ·
                      refine ⟨950625220972273873085867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2535000589259396994895645 950625220972273873085867)
                      ·
                        rfl

theorem cell23_1851336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 1, 2, 1, 2, 3].length) (baseStart_1851336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1851336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1851336 prefixEnd_1851336 := by exact prefixLift 1851336
  have htrace : WordTrace (prefixWord ++ tailWord_1851336) baseStart_1851336 baseEnd_1851336 := by
    simpa [prefixWord, tailWord_1851336, baseEnd_1851336] using wordTrace_append hprefix tailTrace_1851336
  have hstable : (prefixWord ++ tailWord_1851336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1851336).length < 2 ^ (prefixWord ++ tailWord_1851336).sum := by decide
  have hdescent : baseEnd_1851336 < baseStart_1851336 := by decide
  rcases family_descends (prefixWord ++ tailWord_1851336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1851345 : List Nat := [1, 2, 2, 1, 2, 1, 2, 3, 2, 2, 5]
def baseStart_1851345 : Nat := 118140960795 + 1851345 * 2 ^ 59
def prefixEnd_1851345 : Nat := 4983230072969 + 3 ^ 40 * 1851345 * 2
def baseEnd_1851345 : Nat := 950629842298164337873325

theorem tailTrace_1851345 : CollatzResearch.WordTrace tailWord_1851345 prefixEnd_1851345 950629842298164337873325 := by
  unfold tailWord_1851345
  simp only [CollatzResearch.WordTrace]
  refine ⟨67524099477900724398371489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45016066318600482932247659 67524099477900724398371489)
  ·
    refine ⟨50643074608425543298778617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67524099477900724398371489 50643074608425543298778617)
    ·
      refine ⟨37982305956319157474083963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50643074608425543298778617 37982305956319157474083963)
      ·
        refine ⟨56973458934478736211125945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37982305956319157474083963 56973458934478736211125945)
        ·
          refine ⟨42730094200859052158344459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56973458934478736211125945 42730094200859052158344459)
          ·
            refine ⟨64095141301288578237516689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42730094200859052158344459 64095141301288578237516689)
            ·
              refine ⟨48071355975966433678137517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64095141301288578237516689 48071355975966433678137517)
              ·
                refine ⟨18026758490987412629301569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48071355975966433678137517 18026758490987412629301569)
                ·
                  refine ⟨13520068868240559471976177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18026758490987412629301569 13520068868240559471976177)
                  ·
                    refine ⟨10140051651180419603982133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13520068868240559471976177 10140051651180419603982133)
                    ·
                      refine ⟨950629842298164337873325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10140051651180419603982133 950629842298164337873325)
                      ·
                        rfl

theorem cell23_1851345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 3, 2, 2, 5].length) (baseStart_1851345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1851345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1851345 prefixEnd_1851345 := by exact prefixLift 1851345
  have htrace : WordTrace (prefixWord ++ tailWord_1851345) baseStart_1851345 baseEnd_1851345 := by
    simpa [prefixWord, tailWord_1851345, baseEnd_1851345] using wordTrace_append hprefix tailTrace_1851345
  have hstable : (prefixWord ++ tailWord_1851345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1851345).length < 2 ^ (prefixWord ++ tailWord_1851345).sum := by decide
  have hdescent : baseEnd_1851345 < baseStart_1851345 := by decide
  rcases family_descends (prefixWord ++ tailWord_1851345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1851349 : List Nat := [1, 3, 2, 3, 2, 2, 1, 2, 1, 3, 3]
def baseStart_1851349 : Nat := 118140960795 + 1851349 * 2 ^ 59
def prefixEnd_1851349 : Nat := 4983230072969 + 3 ^ 40 * 1851349 * 2
def baseEnd_1851349 : Nat := 950631896220782322223307

theorem tailTrace_1851349 : CollatzResearch.WordTrace tailWord_1851349 prefixEnd_1851349 950631896220782322223307 := by
  unfold tailWord_1851349
  simp only [CollatzResearch.WordTrace]
  refine ⟨67524245369886233081517101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45016163579924155387678067 67524245369886233081517101)
  ·
    refine ⟨25321592013707337405568913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67524245369886233081517101 25321592013707337405568913)
    ·
      refine ⟨18991194010280503054176685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25321592013707337405568913 18991194010280503054176685)
      ·
        refine ⟨7121697753855188645316257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18991194010280503054176685 7121697753855188645316257)
        ·
          refine ⟨5341273315391391483987193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7121697753855188645316257 5341273315391391483987193)
          ·
            refine ⟨4005954986543543612990395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5341273315391391483987193 4005954986543543612990395)
            ·
              refine ⟨6008932479815315419485593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4005954986543543612990395 6008932479815315419485593)
              ·
                refine ⟨4506699359861486564614195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6008932479815315419485593 4506699359861486564614195)
                ·
                  refine ⟨6760049039792229846921293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4506699359861486564614195 6760049039792229846921293)
                  ·
                    refine ⟨2535018389922086192595485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6760049039792229846921293 2535018389922086192595485)
                    ·
                      refine ⟨950631896220782322223307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2535018389922086192595485 950631896220782322223307)
                      ·
                        rfl

theorem cell23_1851349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 2, 1, 3, 3].length) (baseStart_1851349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1851349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1851349 prefixEnd_1851349 := by exact prefixLift 1851349
  have htrace : WordTrace (prefixWord ++ tailWord_1851349) baseStart_1851349 baseEnd_1851349 := by
    simpa [prefixWord, tailWord_1851349, baseEnd_1851349] using wordTrace_append hprefix tailTrace_1851349
  have hstable : (prefixWord ++ tailWord_1851349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1851349).length < 2 ^ (prefixWord ++ tailWord_1851349).sum := by decide
  have hdescent : baseEnd_1851349 < baseStart_1851349 := by decide
  rcases family_descends (prefixWord ++ tailWord_1851349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1851356 : List Nat := [2, 2, 6, 1, 2, 10]
def baseStart_1851356 : Nat := 118140960795 + 1851356 * 2 ^ 59
def prefixEnd_1851356 : Nat := 4983230072969 + 3 ^ 40 * 1851356 * 2
def baseEnd_1851356 : Nat := 3912080208170221377925

theorem tailTrace_1851356 : CollatzResearch.WordTrace tailWord_1851356 prefixEnd_1851356 3912080208170221377925 := by
  unfold tailWord_1851356
  simp only [CollatzResearch.WordTrace]
  refine ⟨33762250340430436638510961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45016333787240582184681281 33762250340430436638510961)
  ·
    refine ⟨25321687755322827478883221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33762250340430436638510961 25321687755322827478883221)
    ·
      refine ⟨1186954113530757538072651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 25321687755322827478883221 1186954113530757538072651)
      ·
        refine ⟨1780431170296136307108977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1186954113530757538072651 1780431170296136307108977)
        ·
          refine ⟨1335323377722102230331733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1780431170296136307108977 1335323377722102230331733)
          ·
            refine ⟨3912080208170221377925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1335323377722102230331733 3912080208170221377925)
            ·
              rfl

theorem cell23_1851356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 10].length) (baseStart_1851356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1851356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1851356 prefixEnd_1851356 := by exact prefixLift 1851356
  have htrace : WordTrace (prefixWord ++ tailWord_1851356) baseStart_1851356 baseEnd_1851356 := by
    simpa [prefixWord, tailWord_1851356, baseEnd_1851356] using wordTrace_append hprefix tailTrace_1851356
  have hstable : (prefixWord ++ tailWord_1851356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1851356).length < 2 ^ (prefixWord ++ tailWord_1851356).sum := by decide
  have hdescent : baseEnd_1851356 < baseStart_1851356 := by decide
  rcases family_descends (prefixWord ++ tailWord_1851356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1851367 : List Nat := [1, 1, 5, 2, 3, 2, 2, 2, 1, 2, 2]
def baseStart_1851367 : Nat := 118140960795 + 1851367 * 2 ^ 59
def prefixEnd_1851367 : Nat := 4983230072969 + 3 ^ 40 * 1851367 * 2
def baseEnd_1851367 : Nat := 950641138872563251798225

theorem tailTrace_1851367 : CollatzResearch.WordTrace tailWord_1851367 prefixEnd_1851367 950641138872563251798225 := by
  unfold tailWord_1851367
  simp only [CollatzResearch.WordTrace]
  refine ⟨67524901883821022155672355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45016601255880681437114903 67524901883821022155672355)
  ·
    refine ⟨101287352825731533233508533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67524901883821022155672355 101287352825731533233508533)
    ·
      refine ⟨9495689327412331240641425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 101287352825731533233508533 9495689327412331240641425)
      ·
        refine ⟨7121766995559248430481069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9495689327412331240641425 7121766995559248430481069)
        ·
          refine ⟨2670662623334718161430401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7121766995559248430481069 2670662623334718161430401)
          ·
            refine ⟨2002996967501038621072801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2670662623334718161430401 2002996967501038621072801)
            ·
              refine ⟨1502247725625778965804601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2002996967501038621072801 1502247725625778965804601)
              ·
                refine ⟨1126685794219334224353451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1502247725625778965804601 1126685794219334224353451)
                ·
                  refine ⟨1690028691329001336530177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1126685794219334224353451 1690028691329001336530177)
                  ·
                    refine ⟨1267521518496751002397633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1690028691329001336530177 1267521518496751002397633)
                    ·
                      refine ⟨950641138872563251798225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1267521518496751002397633 950641138872563251798225)
                      ·
                        rfl

theorem cell23_1851367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 2, 2, 1, 2, 2].length) (baseStart_1851367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1851367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1851367 prefixEnd_1851367 := by exact prefixLift 1851367
  have htrace : WordTrace (prefixWord ++ tailWord_1851367) baseStart_1851367 baseEnd_1851367 := by
    simpa [prefixWord, tailWord_1851367, baseEnd_1851367] using wordTrace_append hprefix tailTrace_1851367
  have hstable : (prefixWord ++ tailWord_1851367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1851367).length < 2 ^ (prefixWord ++ tailWord_1851367).sum := by decide
  have hdescent : baseEnd_1851367 < baseStart_1851367 := by decide
  rcases family_descends (prefixWord ++ tailWord_1851367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1851389 : List Nat := [1, 4, 1, 1, 1, 2, 3, 3, 1, 4, 2]
def baseStart_1851389 : Nat := 118140960795 + 1851389 * 2 ^ 59
def prefixEnd_1851389 : Nat := 4983230072969 + 3 ^ 40 * 1851389 * 2
def baseEnd_1851389 : Nat := 950652435446962165723123

theorem tailTrace_1851389 : CollatzResearch.WordTrace tailWord_1851389 prefixEnd_1851389 950652435446962165723123 := by
  unfold tailWord_1851389
  simp only [CollatzResearch.WordTrace]
  refine ⟨67525704289741319912973221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45017136193160879941982147 67525704289741319912973221)
  ·
    refine ⟨12661069554326497483682479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67525704289741319912973221 12661069554326497483682479)
    ·
      refine ⟨18991604331489746225523719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12661069554326497483682479 18991604331489746225523719)
      ·
        refine ⟨28487406497234619338285579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18991604331489746225523719 28487406497234619338285579)
        ·
          refine ⟨42731109745851929007428369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28487406497234619338285579 42731109745851929007428369)
          ·
            refine ⟨32048332309388946755571277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42731109745851929007428369 32048332309388946755571277)
            ·
              refine ⟨12018124616020855033339229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32048332309388946755571277 12018124616020855033339229)
              ·
                refine ⟨4506796731007820637502211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12018124616020855033339229 4506796731007820637502211)
                ·
                  refine ⟨6760195096511730956253317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4506796731007820637502211 6760195096511730956253317)
                  ·
                    refine ⟨1267536580595949554297497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6760195096511730956253317 1267536580595949554297497)
                    ·
                      refine ⟨950652435446962165723123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1267536580595949554297497 950652435446962165723123)
                      ·
                        rfl

theorem cell23_1851389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 3, 1, 4, 2].length) (baseStart_1851389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1851389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1851389 prefixEnd_1851389 := by exact prefixLift 1851389
  have htrace : WordTrace (prefixWord ++ tailWord_1851389) baseStart_1851389 baseEnd_1851389 := by
    simpa [prefixWord, tailWord_1851389, baseEnd_1851389] using wordTrace_append hprefix tailTrace_1851389
  have hstable : (prefixWord ++ tailWord_1851389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1851389).length < 2 ^ (prefixWord ++ tailWord_1851389).sum := by decide
  have hdescent : baseEnd_1851389 < baseStart_1851389 := by decide
  rcases family_descends (prefixWord ++ tailWord_1851389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1851406 : List Nat := [4, 1, 1, 2, 2, 1, 2, 2, 4, 2, 2]
def baseStart_1851406 : Nat := 118140960795 + 1851406 * 2 ^ 59
def prefixEnd_1851406 : Nat := 4983230072969 + 3 ^ 40 * 1851406 * 2
def baseEnd_1851406 : Nat := 950661164618088599210545

theorem tailTrace_1851406 : CollatzResearch.WordTrace tailWord_1851406 prefixEnd_1851406 950661164618088599210545 := by
  unfold tailWord_1851406
  simp only [CollatzResearch.WordTrace]
  refine ⟨8440790541334966477042759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45017549553786487877561381 8440790541334966477042759)
  ·
    refine ⟨12661185812002449715564139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8440790541334966477042759 12661185812002449715564139)
    ·
      refine ⟨18991778718003674573346209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12661185812002449715564139 18991778718003674573346209)
      ·
        refine ⟨14243834038502755930009657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18991778718003674573346209 14243834038502755930009657)
        ·
          refine ⟨10682875528877066947507243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14243834038502755930009657 10682875528877066947507243)
          ·
            refine ⟨16024313293315600421260865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10682875528877066947507243 16024313293315600421260865)
            ·
              refine ⟨12018234969986700315945649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16024313293315600421260865 12018234969986700315945649)
              ·
                refine ⟨9013676227490025236959237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12018234969986700315945649 9013676227490025236959237)
                ·
                  refine ⟨1690064292654379731929857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9013676227490025236959237 1690064292654379731929857)
                  ·
                    refine ⟨1267548219490784798947393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1690064292654379731929857 1267548219490784798947393)
                    ·
                      refine ⟨950661164618088599210545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1267548219490784798947393 950661164618088599210545)
                      ·
                        rfl

theorem cell23_1851406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 2, 4, 2, 2].length) (baseStart_1851406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1851406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1851406 prefixEnd_1851406 := by exact prefixLift 1851406
  have htrace : WordTrace (prefixWord ++ tailWord_1851406) baseStart_1851406 baseEnd_1851406 := by
    simpa [prefixWord, tailWord_1851406, baseEnd_1851406] using wordTrace_append hprefix tailTrace_1851406
  have hstable : (prefixWord ++ tailWord_1851406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1851406).length < 2 ^ (prefixWord ++ tailWord_1851406).sum := by decide
  have hdescent : baseEnd_1851406 < baseStart_1851406 := by decide
  rcases family_descends (prefixWord ++ tailWord_1851406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1851429 : List Nat := [1, 3, 1, 2, 2, 3, 2, 4, 5]
def baseStart_1851429 : Nat := 118140960795 + 1851429 * 2 ^ 59
def prefixEnd_1851429 : Nat := 4983230072969 + 3 ^ 40 * 1851429 * 2
def baseEnd_1851429 : Nat := 105630330519238001024771

theorem tailTrace_1851429 : CollatzResearch.WordTrace tailWord_1851429 prefixEnd_1851429 105630330519238001024771 := by
  unfold tailWord_1851429
  simp only [CollatzResearch.WordTrace]
  refine ⟨67527163209596406744429341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45018108806397604496286227 67527163209596406744429341)
  ·
    refine ⟨25322686203598652529161003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67527163209596406744429341 25322686203598652529161003)
    ·
      refine ⟨37984029305397978793741505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25322686203598652529161003 37984029305397978793741505)
      ·
        refine ⟨28488021979048484095306129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37984029305397978793741505 28488021979048484095306129)
        ·
          refine ⟨21366016484286363071479597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28488021979048484095306129 21366016484286363071479597)
          ·
            refine ⟨8012256181607386151804849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21366016484286363071479597 8012256181607386151804849)
            ·
              refine ⟨6009192136205539613853637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8012256181607386151804849 6009192136205539613853637)
              ·
                refine ⟨1126723525538538677597557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6009192136205539613853637 1126723525538538677597557)
                ·
                  refine ⟨105630330519238001024771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1126723525538538677597557 105630330519238001024771)
                  ·
                    rfl

theorem cell23_1851429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 4, 5].length) (baseStart_1851429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1851429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1851429 prefixEnd_1851429 := by exact prefixLift 1851429
  have htrace : WordTrace (prefixWord ++ tailWord_1851429) baseStart_1851429 baseEnd_1851429 := by
    simpa [prefixWord, tailWord_1851429, baseEnd_1851429] using wordTrace_append hprefix tailTrace_1851429
  have hstable : (prefixWord ++ tailWord_1851429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1851429).length < 2 ^ (prefixWord ++ tailWord_1851429).sum := by decide
  have hdescent : baseEnd_1851429 < baseStart_1851429 := by decide
  rcases family_descends (prefixWord ++ tailWord_1851429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1851442 : List Nat := [3, 2, 1, 1, 2, 3, 1, 2, 1, 7]
def baseStart_1851442 : Nat := 118140960795 + 1851442 * 2 ^ 59
def prefixEnd_1851442 : Nat := 4983230072969 + 3 ^ 40 * 1851442 * 2
def baseEnd_1851442 : Nat := 316893216640550152786793

theorem tailTrace_1851442 : CollatzResearch.WordTrace tailWord_1851442 prefixEnd_1851442 316893216640550152786793 := by
  unfold tailWord_1851442
  simp only [CollatzResearch.WordTrace]
  refine ⟨16881909339637327491163145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45018424905699539976435053 16881909339637327491163145)
  ·
    refine ⟨12661432004727995618372359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16881909339637327491163145 12661432004727995618372359)
    ·
      refine ⟨18992148007091993427558539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12661432004727995618372359 18992148007091993427558539)
      ·
        refine ⟨28488222010637990141337809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18992148007091993427558539 28488222010637990141337809)
        ·
          refine ⟨21366166507978492606003357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28488222010637990141337809 21366166507978492606003357)
          ·
            refine ⟨8012312440491934727251259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21366166507978492606003357 8012312440491934727251259)
            ·
              refine ⟨12018468660737902090876889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8012312440491934727251259 12018468660737902090876889)
              ·
                refine ⟨9013851495553426568157667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12018468660737902090876889 9013851495553426568157667)
                ·
                  refine ⟨13520777243330139852236501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9013851495553426568157667 13520777243330139852236501)
                  ·
                    refine ⟨316893216640550152786793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13520777243330139852236501 316893216640550152786793)
                    ·
                      rfl

theorem cell23_1851442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 2, 1, 7].length) (baseStart_1851442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1851442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1851442 prefixEnd_1851442 := by exact prefixLift 1851442
  have htrace : WordTrace (prefixWord ++ tailWord_1851442) baseStart_1851442 baseEnd_1851442 := by
    simpa [prefixWord, tailWord_1851442, baseEnd_1851442] using wordTrace_append hprefix tailTrace_1851442
  have hstable : (prefixWord ++ tailWord_1851442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1851442).length < 2 ^ (prefixWord ++ tailWord_1851442).sum := by decide
  have hdescent : baseEnd_1851442 < baseStart_1851442 := by decide
  rcases family_descends (prefixWord ++ tailWord_1851442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1851469 : List Nat := [1, 6, 1, 1, 1, 1, 2, 2, 1, 2, 5]
def baseStart_1851469 : Nat := 118140960795 + 1851469 * 2 ^ 59
def prefixEnd_1851469 : Nat := 4983230072969 + 3 ^ 40 * 1851469 * 2
def baseEnd_1851469 : Nat := 950693513899321852722755

theorem tailTrace_1851469 : CollatzResearch.WordTrace tailWord_1851469 prefixEnd_1851469 950693513899321852722755 := by
  unfold tailWord_1851469
  simp only [CollatzResearch.WordTrace]
  refine ⟨67528622129451493575885461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45019081419634329050590307 67528622129451493575885461)
  ·
    refine ⟨3165404162318038761369631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 67528622129451493575885461 3165404162318038761369631)
    ·
      refine ⟨4748106243477058142054447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3165404162318038761369631 4748106243477058142054447)
      ·
        refine ⟨7122159365215587213081671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4748106243477058142054447 7122159365215587213081671)
        ·
          refine ⟨10683239047823380819622507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7122159365215587213081671 10683239047823380819622507)
          ·
            refine ⟨16024858571735071229433761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10683239047823380819622507 16024858571735071229433761)
            ·
              refine ⟨12018643928801303422075321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16024858571735071229433761 12018643928801303422075321)
              ·
                refine ⟨9013982946600977566556491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12018643928801303422075321 9013982946600977566556491)
                ·
                  refine ⟨13520974419901466349834737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9013982946600977566556491 13520974419901466349834737)
                  ·
                    refine ⟨10140730814926099762376053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13520974419901466349834737 10140730814926099762376053)
                    ·
                      refine ⟨950693513899321852722755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10140730814926099762376053 950693513899321852722755)
                      ·
                        rfl

theorem cell23_1851469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 2, 1, 2, 5].length) (baseStart_1851469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1851469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1851469 prefixEnd_1851469 := by exact prefixLift 1851469
  have htrace : WordTrace (prefixWord ++ tailWord_1851469) baseStart_1851469 baseEnd_1851469 := by
    simpa [prefixWord, tailWord_1851469, baseEnd_1851469] using wordTrace_append hprefix tailTrace_1851469
  have hstable : (prefixWord ++ tailWord_1851469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1851469).length < 2 ^ (prefixWord ++ tailWord_1851469).sum := by decide
  have hdescent : baseEnd_1851469 < baseStart_1851469 := by decide
  rcases family_descends (prefixWord ++ tailWord_1851469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1851479 : List Nat := [1, 1, 3, 2, 2, 1, 2, 1, 4, 4, 2]
def baseStart_1851479 : Nat := 118140960795 + 1851479 * 2 ^ 59
def prefixEnd_1851479 : Nat := 4983230072969 + 3 ^ 40 * 1851479 * 2
def baseEnd_1851479 : Nat := 950698648705866813597709

theorem tailTrace_1851479 : CollatzResearch.WordTrace tailWord_1851479 prefixEnd_1851479 950698648705866813597709 := by
  unfold tailWord_1851479
  simp only [CollatzResearch.WordTrace]
  refine ⟨67528986859415265283749491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45019324572943510189166327 67528986859415265283749491)
  ·
    refine ⟨101293480289122897925624237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67528986859415265283749491 101293480289122897925624237)
    ·
      refine ⟨37985055108421086722109089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101293480289122897925624237 37985055108421086722109089)
      ·
        refine ⟨28488791331315815041581817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37985055108421086722109089 28488791331315815041581817)
        ·
          refine ⟨21366593498486861281186363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28488791331315815041581817 21366593498486861281186363)
          ·
            refine ⟨32049890247730291921779545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21366593498486861281186363 32049890247730291921779545)
            ·
              refine ⟨24037417685797718941334659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32049890247730291921779545 24037417685797718941334659)
              ·
                refine ⟨36056126528696578412001989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24037417685797718941334659 36056126528696578412001989)
                ·
                  refine ⟨6760523724130608452250373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36056126528696578412001989 6760523724130608452250373)
                  ·
                    refine ⟨1267598198274489084796945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6760523724130608452250373 1267598198274489084796945)
                    ·
                      refine ⟨950698648705866813597709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1267598198274489084796945 950698648705866813597709)
                      ·
                        rfl

theorem cell23_1851479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 1, 4, 4, 2].length) (baseStart_1851479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1851479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1851479 prefixEnd_1851479 := by exact prefixLift 1851479
  have htrace : WordTrace (prefixWord ++ tailWord_1851479) baseStart_1851479 baseEnd_1851479 := by
    simpa [prefixWord, tailWord_1851479, baseEnd_1851479] using wordTrace_append hprefix tailTrace_1851479
  have hstable : (prefixWord ++ tailWord_1851479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1851479).length < 2 ^ (prefixWord ++ tailWord_1851479).sum := by decide
  have hdescent : baseEnd_1851479 < baseStart_1851479 := by decide
  rcases family_descends (prefixWord ++ tailWord_1851479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1851492 : List Nat := [2, 3, 1, 1, 2, 1, 2, 2, 2, 1, 6]
def baseStart_1851492 : Nat := 118140960795 + 1851492 * 2 ^ 59
def prefixEnd_1851492 : Nat := 4983230072969 + 3 ^ 40 * 1851492 * 2
def baseEnd_1851492 : Nat := 950705323954375262735149

theorem tailTrace_1851492 : CollatzResearch.WordTrace tailWord_1851492 prefixEnd_1851492 950705323954375262735149 := by
  unfold tailWord_1851492
  simp only [CollatzResearch.WordTrace]
  refine ⟨33764730504184084251986365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45019640672245445669315153 33764730504184084251986365)
  ·
    refine ⟨12661773939069031594494887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33764730504184084251986365 12661773939069031594494887)
    ·
      refine ⟨18992660908603547391742331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12661773939069031594494887 18992660908603547391742331)
      ·
        refine ⟨28488991362905321087613497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18992660908603547391742331 28488991362905321087613497)
        ·
          refine ⟨21366743522178990815710123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28488991362905321087613497 21366743522178990815710123)
          ·
            refine ⟨32050115283268486223565185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21366743522178990815710123 32050115283268486223565185)
            ·
              refine ⟨24037586462451364667673889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32050115283268486223565185 24037586462451364667673889)
              ·
                refine ⟨18028189846838523500755417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24037586462451364667673889 18028189846838523500755417)
                ·
                  refine ⟨13521142385128892625566563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18028189846838523500755417 13521142385128892625566563)
                  ·
                    refine ⟨20281713577693338938349845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13521142385128892625566563 20281713577693338938349845)
                    ·
                      refine ⟨950705323954375262735149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 20281713577693338938349845 950705323954375262735149)
                      ·
                        rfl

theorem cell23_1851492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 2, 2, 1, 6].length) (baseStart_1851492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1851492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1851492 prefixEnd_1851492 := by exact prefixLift 1851492
  have htrace : WordTrace (prefixWord ++ tailWord_1851492) baseStart_1851492 baseEnd_1851492 := by
    simpa [prefixWord, tailWord_1851492, baseEnd_1851492] using wordTrace_append hprefix tailTrace_1851492
  have hstable : (prefixWord ++ tailWord_1851492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1851492).length < 2 ^ (prefixWord ++ tailWord_1851492).sum := by decide
  have hdescent : baseEnd_1851492 < baseStart_1851492 := by decide
  rcases family_descends (prefixWord ++ tailWord_1851492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1851516 : List Nat := [2, 2, 2, 1, 1, 5, 2, 1, 2, 2, 3]
def baseStart_1851516 : Nat := 118140960795 + 1851516 * 2 ^ 59
def prefixEnd_1851516 : Nat := 4983230072969 + 3 ^ 40 * 1851516 * 2
def baseEnd_1851516 : Nat := 950717647490083168835039

theorem tailTrace_1851516 : CollatzResearch.WordTrace tailWord_1851516 prefixEnd_1851516 950717647490083168835039 := by
  unfold tailWord_1851516
  simp only [CollatzResearch.WordTrace]
  refine ⟨33765168180140610301423201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45020224240187480401897601 33765168180140610301423201)
  ·
    refine ⟨25323876135105457726067401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33765168180140610301423201 25323876135105457726067401)
    ·
      refine ⟨18992907101329093294550551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25323876135105457726067401 18992907101329093294550551)
      ·
        refine ⟨28489360651993639941825827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18992907101329093294550551 28489360651993639941825827)
        ·
          refine ⟨42734040977990459912738741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28489360651993639941825827 42734040977990459912738741)
          ·
            refine ⟨4006316341686605616819257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42734040977990459912738741 4006316341686605616819257)
            ·
              refine ⟨3004737256264954212614443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4006316341686605616819257 3004737256264954212614443)
              ·
                refine ⟨4507105884397431318921665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3004737256264954212614443 4507105884397431318921665)
                ·
                  refine ⟨3380329413298073489191249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4507105884397431318921665 3380329413298073489191249)
                  ·
                    refine ⟨2535247059973555116893437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3380329413298073489191249 2535247059973555116893437)
                    ·
                      refine ⟨950717647490083168835039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2535247059973555116893437 950717647490083168835039)
                      ·
                        rfl

theorem cell23_1851516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 2, 1, 2, 2, 3].length) (baseStart_1851516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1851516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1851516 prefixEnd_1851516 := by exact prefixLift 1851516
  have htrace : WordTrace (prefixWord ++ tailWord_1851516) baseStart_1851516 baseEnd_1851516 := by
    simpa [prefixWord, tailWord_1851516, baseEnd_1851516] using wordTrace_append hprefix tailTrace_1851516
  have hstable : (prefixWord ++ tailWord_1851516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1851516).length < 2 ^ (prefixWord ++ tailWord_1851516).sum := by decide
  have hdescent : baseEnd_1851516 < baseStart_1851516 := by decide
  rcases family_descends (prefixWord ++ tailWord_1851516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1851539 : List Nat := [1, 1, 1, 2, 1, 2, 3, 2, 3, 5, 2]
def baseStart_1851539 : Nat := 118140960795 + 1851539 * 2 ^ 59
def prefixEnd_1851539 : Nat := 4983230072969 + 3 ^ 40 * 1851539 * 2
def baseEnd_1851539 : Nat := 950729457545136578847433

theorem tailTrace_1851539 : CollatzResearch.WordTrace tailWord_1851539 prefixEnd_1851539 950729457545136578847433 := by
  unfold tailWord_1851539
  simp only [CollatzResearch.WordTrace]
  refine ⟨67531175239197895530933671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45020783492798597020622447 67531175239197895530933671)
  ·
    refine ⟨101296762858796843296400507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67531175239197895530933671 101296762858796843296400507)
    ·
      refine ⟨151945144288195264944600761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101296762858796843296400507 151945144288195264944600761)
      ·
        refine ⟨113958858216146448708450571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151945144288195264944600761 113958858216146448708450571)
        ·
          refine ⟨170938287324219673062675857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113958858216146448708450571 170938287324219673062675857)
          ·
            refine ⟨128203715493164754797006893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170938287324219673062675857 128203715493164754797006893)
            ·
              refine ⟨48076393309936783048877585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 128203715493164754797006893 48076393309936783048877585)
              ·
                refine ⟨36057294982452587286658189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48076393309936783048877585 36057294982452587286658189)
                ·
                  refine ⟨13521485618419720232496821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36057294982452587286658189 13521485618419720232496821)
                  ·
                    refine ⟨1267639276726848771796577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13521485618419720232496821 1267639276726848771796577)
                    ·
                      refine ⟨950729457545136578847433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1267639276726848771796577 950729457545136578847433)
                      ·
                        rfl

theorem cell23_1851539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 2, 3, 5, 2].length) (baseStart_1851539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1851539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1851539 prefixEnd_1851539 := by exact prefixLift 1851539
  have htrace : WordTrace (prefixWord ++ tailWord_1851539) baseStart_1851539 baseEnd_1851539 := by
    simpa [prefixWord, tailWord_1851539, baseEnd_1851539] using wordTrace_append hprefix tailTrace_1851539
  have hstable : (prefixWord ++ tailWord_1851539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1851539).length < 2 ^ (prefixWord ++ tailWord_1851539).sum := by decide
  have hdescent : baseEnd_1851539 < baseStart_1851539 := by decide
  rcases family_descends (prefixWord ++ tailWord_1851539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1851549 : List Nat := [1, 4, 2, 1, 1, 3, 1, 2, 3, 5]
def baseStart_1851549 : Nat := 118140960795 + 1851549 * 2 ^ 59
def prefixEnd_1851549 : Nat := 4983230072969 + 3 ^ 40 * 1851549 * 2
def baseEnd_1851549 : Nat := 316911530783893846574129

theorem tailTrace_1851549 : CollatzResearch.WordTrace tailWord_1851549 prefixEnd_1851549 316911530783893846574129 := by
  unfold tailWord_1851549
  simp only [CollatzResearch.WordTrace]
  refine ⟨67531539969161667238797701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45021026646107778159198467 67531539969161667238797701)
  ·
    refine ⟨12662163744217812607274569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67531539969161667238797701 12662163744217812607274569)
    ·
      refine ⟨9496622808163359455455927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12662163744217812607274569 9496622808163359455455927)
      ·
        refine ⟨14244934212245039183183891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9496622808163359455455927 14244934212245039183183891)
        ·
          refine ⟨21367401318367558774775837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14244934212245039183183891 21367401318367558774775837)
          ·
            refine ⟨8012775494387834540540939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21367401318367558774775837 8012775494387834540540939)
            ·
              refine ⟨12019163241581751810811409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8012775494387834540540939 12019163241581751810811409)
              ·
                refine ⟨9014372431186313858108557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12019163241581751810811409 9014372431186313858108557)
                ·
                  refine ⟨3380389661694867696790709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9014372431186313858108557 3380389661694867696790709)
                  ·
                    refine ⟨316911530783893846574129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3380389661694867696790709 316911530783893846574129)
                    ·
                      rfl

theorem cell23_1851549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 2, 3, 5].length) (baseStart_1851549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1851549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1851549 prefixEnd_1851549 := by exact prefixLift 1851549
  have htrace : WordTrace (prefixWord ++ tailWord_1851549) baseStart_1851549 baseEnd_1851549 := by
    simpa [prefixWord, tailWord_1851549, baseEnd_1851549] using wordTrace_append hprefix tailTrace_1851549
  have hstable : (prefixWord ++ tailWord_1851549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1851549).length < 2 ^ (prefixWord ++ tailWord_1851549).sum := by decide
  have hdescent : baseEnd_1851549 < baseStart_1851549 := by decide
  rcases family_descends (prefixWord ++ tailWord_1851549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1851579 : List Nat := [1, 1, 1, 1, 1, 2, 6, 2, 4, 4]
def baseStart_1851579 : Nat := 118140960795 + 1851579 * 2 ^ 59
def prefixEnd_1851579 : Nat := 4983230072969 + 3 ^ 40 * 1851579 * 2
def baseEnd_1851579 : Nat := 316916665590438807449083

theorem tailTrace_1851579 : CollatzResearch.WordTrace tailWord_1851579 prefixEnd_1851579 316916665590438807449083 := by
  unfold tailWord_1851579
  simp only [CollatzResearch.WordTrace]
  refine ⟨67532634159052982362389791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45021756106035321574926527 67532634159052982362389791)
  ·
    refine ⟨101298951238579473543584687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67532634159052982362389791 101298951238579473543584687)
    ·
      refine ⟨151948426857869210315377031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101298951238579473543584687 151948426857869210315377031)
      ·
        refine ⟨227922640286803815473065547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151948426857869210315377031 227922640286803815473065547)
        ·
          refine ⟨341883960430205723209598321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227922640286803815473065547 341883960430205723209598321)
          ·
            refine ⟨256412970322654292407198741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 341883960430205723209598321 256412970322654292407198741)
            ·
              refine ⟨12019357983874419956587441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 256412970322654292407198741 12019357983874419956587441)
              ·
                refine ⟨9014518487905814967440581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12019357983874419956587441 9014518487905814967440581)
                ·
                  refine ⟨1690222216482340306395109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9014518487905814967440581 1690222216482340306395109)
                  ·
                    refine ⟨316916665590438807449083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1690222216482340306395109 316916665590438807449083)
                    ·
                      rfl

theorem cell23_1851579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 2, 4, 4].length) (baseStart_1851579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1851579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1851579 prefixEnd_1851579 := by exact prefixLift 1851579
  have htrace : WordTrace (prefixWord ++ tailWord_1851579) baseStart_1851579 baseEnd_1851579 := by
    simpa [prefixWord, tailWord_1851579, baseEnd_1851579] using wordTrace_append hprefix tailTrace_1851579
  have hstable : (prefixWord ++ tailWord_1851579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1851579).length < 2 ^ (prefixWord ++ tailWord_1851579).sum := by decide
  have hdescent : baseEnd_1851579 < baseStart_1851579 := by decide
  rcases family_descends (prefixWord ++ tailWord_1851579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1851613 : List Nat := [1, 4, 3, 2, 1, 3, 1, 1, 1, 6]
def baseStart_1851613 : Nat := 118140960795 + 1851613 * 2 ^ 59
def prefixEnd_1851613 : Nat := 4983230072969 + 3 ^ 40 * 1851613 * 2
def baseEnd_1851613 : Nat := 316922485037856429774031

theorem tailTrace_1851613 : CollatzResearch.WordTrace tailWord_1851613 prefixEnd_1851613 316922485037856429774031 := by
  unfold tailWord_1851613
  simp only [CollatzResearch.WordTrace]
  refine ⟨67533874240929806169127493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45022582827286537446084995 67533874240929806169127493)
  ·
    refine ⟨12662601420174338656711405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67533874240929806169127493 12662601420174338656711405)
    ·
      refine ⟨4748475532565376996266777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12662601420174338656711405 4748475532565376996266777)
      ·
        refine ⟨3561356649424032747200083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4748475532565376996266777 3561356649424032747200083)
        ·
          refine ⟨5342034974136049120800125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3561356649424032747200083 5342034974136049120800125)
          ·
            refine ⟨2003263115301018420300047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5342034974136049120800125 2003263115301018420300047)
            ·
              refine ⟨3004894672951527630450071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2003263115301018420300047 3004894672951527630450071)
              ·
                refine ⟨4507342009427291445675107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3004894672951527630450071 4507342009427291445675107)
                ·
                  refine ⟨6761013014140937168512661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4507342009427291445675107 6761013014140937168512661)
                  ·
                    refine ⟨316922485037856429774031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6761013014140937168512661 316922485037856429774031)
                    ·
                      rfl

theorem cell23_1851613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 1, 1, 1, 6].length) (baseStart_1851613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1851613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1851613 prefixEnd_1851613 := by exact prefixLift 1851613
  have htrace : WordTrace (prefixWord ++ tailWord_1851613) baseStart_1851613 baseEnd_1851613 := by
    simpa [prefixWord, tailWord_1851613, baseEnd_1851613] using wordTrace_append hprefix tailTrace_1851613
  have hstable : (prefixWord ++ tailWord_1851613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1851613).length < 2 ^ (prefixWord ++ tailWord_1851613).sum := by decide
  have hdescent : baseEnd_1851613 < baseStart_1851613 := by decide
  rcases family_descends (prefixWord ++ tailWord_1851613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1851623 : List Nat := [1, 1, 5, 3, 1, 1, 1, 4, 1, 2, 3]
def baseStart_1851623 : Nat := 118140960795 + 1851623 * 2 ^ 59
def prefixEnd_1851623 : Nat := 4983230072969 + 3 ^ 40 * 1851623 * 2
def baseEnd_1851623 : Nat := 950772589920114250197047

theorem tailTrace_1851623 : CollatzResearch.WordTrace tailWord_1851623 prefixEnd_1851623 950772589920114250197047 := by
  unfold tailWord_1851623
  simp only [CollatzResearch.WordTrace]
  refine ⟨67534238970893577876991523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45022825980595718584661015 67534238970893577876991523)
  ·
    refine ⟨101301358456340366815487285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67534238970893577876991523 101301358456340366815487285)
    ·
      refine ⟨9497002355281909388951933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 101301358456340366815487285 9497002355281909388951933)
      ·
        refine ⟨3561375883230716020856975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9497002355281909388951933 3561375883230716020856975)
        ·
          refine ⟨5342063824846074031285463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3561375883230716020856975 5342063824846074031285463)
          ·
            refine ⟨8013095737269111046928195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5342063824846074031285463 8013095737269111046928195)
            ·
              refine ⟨12019643605903666570392293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8013095737269111046928195 12019643605903666570392293)
              ·
                refine ⟨2253683176106937481948555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12019643605903666570392293 2253683176106937481948555)
                ·
                  refine ⟨3380524764160406222922833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2253683176106937481948555 3380524764160406222922833)
                  ·
                    refine ⟨2535393573120304667192125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3380524764160406222922833 2535393573120304667192125)
                    ·
                      refine ⟨950772589920114250197047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2535393573120304667192125 950772589920114250197047)
                      ·
                        rfl

theorem cell23_1851623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 4, 1, 2, 3].length) (baseStart_1851623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1851623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1851623 prefixEnd_1851623 := by exact prefixLift 1851623
  have htrace : WordTrace (prefixWord ++ tailWord_1851623) baseStart_1851623 baseEnd_1851623 := by
    simpa [prefixWord, tailWord_1851623, baseEnd_1851623] using wordTrace_append hprefix tailTrace_1851623
  have hstable : (prefixWord ++ tailWord_1851623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1851623).length < 2 ^ (prefixWord ++ tailWord_1851623).sum := by decide
  have hdescent : baseEnd_1851623 < baseStart_1851623 := by decide
  rcases family_descends (prefixWord ++ tailWord_1851623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1851649 : List Nat := [1, 2, 4, 1, 1, 2, 1, 2, 2, 2, 5]
def baseStart_1851649 : Nat := 118140960795 + 1851649 * 2 ^ 59
def prefixEnd_1851649 : Nat := 4983230072969 + 3 ^ 40 * 1851649 * 2
def baseEnd_1851649 : Nat := 950785940417131148471927

theorem tailTrace_1851649 : CollatzResearch.WordTrace tailWord_1851649 prefixEnd_1851649 950785940417131148471927 := by
  unfold tailWord_1851649
  simp only [CollatzResearch.WordTrace]
  refine ⟨67535187268799384317438001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45023458179199589544958667 67535187268799384317438001)
  ·
    refine ⟨50651390451599538238078501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67535187268799384317438001 50651390451599538238078501)
    ·
      refine ⟨9497135709674913419639719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50651390451599538238078501 9497135709674913419639719)
      ·
        refine ⟨14245703564512370129459579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9497135709674913419639719 14245703564512370129459579)
        ·
          refine ⟨21368555346768555194189369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14245703564512370129459579 21368555346768555194189369)
          ·
            refine ⟨16026416510076416395642027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21368555346768555194189369 16026416510076416395642027)
            ·
              refine ⟨24039624765114624593463041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16026416510076416395642027 24039624765114624593463041)
              ·
                refine ⟨18029718573835968445097281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24039624765114624593463041 18029718573835968445097281)
                ·
                  refine ⟨13522288930376976333822961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18029718573835968445097281 13522288930376976333822961)
                  ·
                    refine ⟨10141716697782732250367221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13522288930376976333822961 10141716697782732250367221)
                    ·
                      refine ⟨950785940417131148471927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10141716697782732250367221 950785940417131148471927)
                      ·
                        rfl

theorem cell23_1851649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 2, 2, 2, 5].length) (baseStart_1851649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1851649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1851649 prefixEnd_1851649 := by exact prefixLift 1851649
  have htrace : WordTrace (prefixWord ++ tailWord_1851649) baseStart_1851649 baseEnd_1851649 := by
    simpa [prefixWord, tailWord_1851649, baseEnd_1851649] using wordTrace_append hprefix tailTrace_1851649
  have hstable : (prefixWord ++ tailWord_1851649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1851649).length < 2 ^ (prefixWord ++ tailWord_1851649).sum := by decide
  have hdescent : baseEnd_1851649 < baseStart_1851649 := by decide
  rcases family_descends (prefixWord ++ tailWord_1851649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1851659 : List Nat := [1, 1, 1, 1, 5, 2, 2, 1, 2, 3, 4]
def baseStart_1851659 : Nat := 118140960795 + 1851659 * 2 ^ 59
def prefixEnd_1851659 : Nat := 4983230072969 + 3 ^ 40 * 1851659 * 2
def baseEnd_1851659 : Nat := 950791075223676109346881

theorem tailTrace_1851659 : CollatzResearch.WordTrace tailWord_1851659 prefixEnd_1851659 950791075223676109346881 := by
  unfold tailWord_1851659
  simp only [CollatzResearch.WordTrace]
  refine ⟨67535551998763156025302031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45023701332508770683534687 67535551998763156025302031)
  ·
    refine ⟨101303327998144734037953047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67535551998763156025302031 101303327998144734037953047)
    ·
      refine ⟨151954991997217101056929571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101303327998144734037953047 151954991997217101056929571)
      ·
        refine ⟨227932487995825651585394357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151954991997217101056929571 227932487995825651585394357)
        ·
          refine ⟨21368670749608654836130721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 227932487995825651585394357 21368670749608654836130721)
          ·
            refine ⟨16026503062206491127098041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21368670749608654836130721 16026503062206491127098041)
            ·
              refine ⟨12019877296654868345323531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16026503062206491127098041 12019877296654868345323531)
              ·
                refine ⟨18029815944982302517985297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12019877296654868345323531 18029815944982302517985297)
                ·
                  refine ⟨13522361958736726888488973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18029815944982302517985297 13522361958736726888488973)
                  ·
                    refine ⟨5070885734526272583183365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13522361958736726888488973 5070885734526272583183365)
                    ·
                      refine ⟨950791075223676109346881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5070885734526272583183365 950791075223676109346881)
                      ·
                        rfl

theorem cell23_1851659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 1, 2, 3, 4].length) (baseStart_1851659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1851659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1851659 prefixEnd_1851659 := by exact prefixLift 1851659
  have htrace : WordTrace (prefixWord ++ tailWord_1851659) baseStart_1851659 baseEnd_1851659 := by
    simpa [prefixWord, tailWord_1851659, baseEnd_1851659] using wordTrace_append hprefix tailTrace_1851659
  have hstable : (prefixWord ++ tailWord_1851659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1851659).length < 2 ^ (prefixWord ++ tailWord_1851659).sum := by decide
  have hdescent : baseEnd_1851659 < baseStart_1851659 := by decide
  rcases family_descends (prefixWord ++ tailWord_1851659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
