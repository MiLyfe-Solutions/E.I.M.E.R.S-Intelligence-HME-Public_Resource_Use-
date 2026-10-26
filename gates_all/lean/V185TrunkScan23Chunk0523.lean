import V185TrunkScan23Chunk0522

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3092026 : List Nat := [3, 1, 1, 1, 3, 2, 2, 2, 1, 1, 6]
def baseStart_3092026 : Nat := 118140960795 + 3092026 * 2 ^ 59
def prefixEnd_3092026 : Nat := 4983230072969 + 3 ^ 40 * 3092026 * 2
def baseEnd_3092026 : Nat := 1587695534199024667755037

theorem tailTrace_3092026 : CollatzResearch.WordTrace tailWord_3092026 prefixEnd_3092026 1587695534199024667755037 := by
  unfold tailWord_3092026
  simp only [CollatzResearch.WordTrace]
  refine ⟨28193863274031338210907983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75183635397416901895754621 28193863274031338210907983)
  ·
    refine ⟨42290794911047007316361975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28193863274031338210907983 42290794911047007316361975)
    ·
      refine ⟨63436192366570510974542963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42290794911047007316361975 63436192366570510974542963)
      ·
        refine ⟨95154288549855766461814445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63436192366570510974542963 95154288549855766461814445)
        ·
          refine ⟨35682858206195912423180417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95154288549855766461814445 35682858206195912423180417)
          ·
            refine ⟨26762143654646934317385313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35682858206195912423180417 26762143654646934317385313)
            ·
              refine ⟨20071607740985200738038985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26762143654646934317385313 20071607740985200738038985)
              ·
                refine ⟨15053705805738900553529239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20071607740985200738038985 15053705805738900553529239)
                ·
                  refine ⟨22580558708608350830293859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15053705805738900553529239 22580558708608350830293859)
                  ·
                    refine ⟨33870838062912526245440789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22580558708608350830293859 33870838062912526245440789)
                    ·
                      refine ⟨1587695534199024667755037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33870838062912526245440789 1587695534199024667755037)
                      ·
                        rfl

theorem cell23_3092026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 2, 1, 1, 6].length) (baseStart_3092026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3092026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3092026 prefixEnd_3092026 := by exact prefixLift 3092026
  have htrace : WordTrace (prefixWord ++ tailWord_3092026) baseStart_3092026 baseEnd_3092026 := by
    simpa [prefixWord, tailWord_3092026, baseEnd_3092026] using wordTrace_append hprefix tailTrace_3092026
  have hstable : (prefixWord ++ tailWord_3092026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3092026).length < 2 ^ (prefixWord ++ tailWord_3092026).sum := by decide
  have hdescent : baseEnd_3092026 < baseStart_3092026 := by decide
  rcases family_descends (prefixWord ++ tailWord_3092026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3092033 : List Nat := [1, 2, 5, 1, 1, 1, 3, 2, 1, 1, 5]
def baseStart_3092033 : Nat := 118140960795 + 3092033 * 2 ^ 59
def prefixEnd_3092033 : Nat := 4983230072969 + 3 ^ 40 * 3092033 * 2
def baseEnd_3092033 : Nat := 1587699128563606140367505

theorem tailTrace_3092033 : CollatzResearch.WordTrace tailWord_3092033 prefixEnd_3092033 1587699128563606140367505 := by
  unfold tailWord_3092033
  simp only [CollatzResearch.WordTrace]
  refine ⟨112775708407099993039136753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75183805604733328692757835 112775708407099993039136753)
  ·
    refine ⟨84581781305324994779352565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112775708407099993039136753 84581781305324994779352565)
    ·
      refine ⟨7929541997374218260564303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 84581781305324994779352565 7929541997374218260564303)
      ·
        refine ⟨11894312996061327390846455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7929541997374218260564303 11894312996061327390846455)
        ·
          refine ⟨17841469494091991086269683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11894312996061327390846455 17841469494091991086269683)
          ·
            refine ⟨26762204241137986629404525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17841469494091991086269683 26762204241137986629404525)
            ·
              refine ⟨10035826590426744986026697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26762204241137986629404525 10035826590426744986026697)
              ·
                refine ⟨7526869942820058739520023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10035826590426744986026697 7526869942820058739520023)
                ·
                  refine ⟨11290304914230088109280035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7526869942820058739520023 11290304914230088109280035)
                  ·
                    refine ⟨16935457371345132163920053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11290304914230088109280035 16935457371345132163920053)
                    ·
                      refine ⟨1587699128563606140367505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16935457371345132163920053 1587699128563606140367505)
                      ·
                        rfl

theorem cell23_3092033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 2, 1, 1, 5].length) (baseStart_3092033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3092033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3092033 prefixEnd_3092033 := by exact prefixLift 3092033
  have htrace : WordTrace (prefixWord ++ tailWord_3092033) baseStart_3092033 baseEnd_3092033 := by
    simpa [prefixWord, tailWord_3092033, baseEnd_3092033] using wordTrace_append hprefix tailTrace_3092033
  have hstable : (prefixWord ++ tailWord_3092033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3092033).length < 2 ^ (prefixWord ++ tailWord_3092033).sum := by decide
  have hdescent : baseEnd_3092033 < baseStart_3092033 := by decide
  rcases family_descends (prefixWord ++ tailWord_3092033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3092050 : List Nat := [3, 2, 2, 1, 2, 2, 1, 4, 1, 2, 3]
def baseStart_3092050 : Nat := 118140960795 + 3092050 * 2 ^ 59
def prefixEnd_3092050 : Nat := 4983230072969 + 3 ^ 40 * 3092050 * 2
def baseEnd_3092050 : Nat := 1587707857734732573854927

theorem tailTrace_3092050 : CollatzResearch.WordTrace tailWord_3092050 prefixEnd_3092050 1587707857734732573854927 := by
  unfold tailWord_3092050
  simp only [CollatzResearch.WordTrace]
  refine ⟨28194082112009601235626401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75184218965358936628337069 28194082112009601235626401)
  ·
    refine ⟨21145561584007200926719801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28194082112009601235626401 21145561584007200926719801)
    ·
      refine ⟨15859171188005400695039851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21145561584007200926719801 15859171188005400695039851)
      ·
        refine ⟨23788756782008101042559777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15859171188005400695039851 23788756782008101042559777)
        ·
          refine ⟨17841567586506075781919833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23788756782008101042559777 17841567586506075781919833)
          ·
            refine ⟨13381175689879556836439875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17841567586506075781919833 13381175689879556836439875)
            ·
              refine ⟨20071763534819335254659813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13381175689879556836439875 20071763534819335254659813)
              ·
                refine ⟨3763455662778625360248715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20071763534819335254659813 3763455662778625360248715)
                ·
                  refine ⟨5645183494167938040373073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3763455662778625360248715 5645183494167938040373073)
                  ·
                    refine ⟨4233887620625953530279805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5645183494167938040373073 4233887620625953530279805)
                    ·
                      refine ⟨1587707857734732573854927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4233887620625953530279805 1587707857734732573854927)
                      ·
                        rfl

theorem cell23_3092050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 4, 1, 2, 3].length) (baseStart_3092050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3092050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3092050 prefixEnd_3092050 := by exact prefixLift 3092050
  have htrace : WordTrace (prefixWord ++ tailWord_3092050) baseStart_3092050 baseEnd_3092050 := by
    simpa [prefixWord, tailWord_3092050, baseEnd_3092050] using wordTrace_append hprefix tailTrace_3092050
  have hstable : (prefixWord ++ tailWord_3092050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3092050).length < 2 ^ (prefixWord ++ tailWord_3092050).sum := by decide
  have hdescent : baseEnd_3092050 < baseStart_3092050 := by decide
  rcases family_descends (prefixWord ++ tailWord_3092050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3092076 : List Nat := [2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 5]
def baseStart_3092076 : Nat := 118140960795 + 3092076 * 2 ^ 59
def prefixEnd_3092076 : Nat := 4983230072969 + 3 ^ 40 * 3092076 * 2
def baseEnd_3092076 : Nat := 1587721208231749472129807

theorem tailTrace_3092076 : CollatzResearch.WordTrace tailWord_3092076 prefixEnd_3092076 1587721208231749472129807 := by
  unfold tailWord_3092076
  simp only [CollatzResearch.WordTrace]
  refine ⟨56388638372972105691476041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75184851163962807588634721 56388638372972105691476041)
  ·
    refine ⟨42291478779729079268607031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56388638372972105691476041 42291478779729079268607031)
    ·
      refine ⟨63437218169593618902910547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42291478779729079268607031 63437218169593618902910547)
      ·
        refine ⟨95155827254390428354365821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63437218169593618902910547 95155827254390428354365821)
        ·
          refine ⟨35683435220396410632887183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95155827254390428354365821 35683435220396410632887183)
          ·
            refine ⟨53525152830594615949330775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35683435220396410632887183 53525152830594615949330775)
            ·
              refine ⟨80287729245891923923996163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53525152830594615949330775 80287729245891923923996163)
              ·
                refine ⟨120431593868837885885994245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80287729245891923923996163 120431593868837885885994245)
                ·
                  refine ⟨22580923850407103603623921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 120431593868837885885994245 22580923850407103603623921)
                  ·
                    refine ⟨16935692887805327702717941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22580923850407103603623921 16935692887805327702717941)
                    ·
                      refine ⟨1587721208231749472129807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16935692887805327702717941 1587721208231749472129807)
                      ·
                        rfl

theorem cell23_3092076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 5].length) (baseStart_3092076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3092076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3092076 prefixEnd_3092076 := by exact prefixLift 3092076
  have htrace : WordTrace (prefixWord ++ tailWord_3092076) baseStart_3092076 baseEnd_3092076 := by
    simpa [prefixWord, tailWord_3092076, baseEnd_3092076] using wordTrace_append hprefix tailTrace_3092076
  have hstable : (prefixWord ++ tailWord_3092076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3092076).length < 2 ^ (prefixWord ++ tailWord_3092076).sum := by decide
  have hdescent : baseEnd_3092076 < baseStart_3092076 := by decide
  rcases family_descends (prefixWord ++ tailWord_3092076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3092080 : List Nat := [2, 1, 1, 1, 6, 1, 2, 1, 4, 1, 3]
def baseStart_3092080 : Nat := 118140960795 + 3092080 * 2 ^ 59
def prefixEnd_3092080 : Nat := 4983230072969 + 3 ^ 40 * 3092080 * 2
def baseEnd_3092080 : Nat := 1587723262154367456479789

theorem tailTrace_3092080 : CollatzResearch.WordTrace tailWord_3092080 prefixEnd_3092080 1587723262154367456479789 := by
  unfold tailWord_3092080
  simp only [CollatzResearch.WordTrace]
  refine ⟨56388711318964860033048847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75184948425286480044065129 56388711318964860033048847)
  ·
    refine ⟨84583066978447290049573271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56388711318964860033048847 84583066978447290049573271)
    ·
      refine ⟨126874600467670935074359907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84583066978447290049573271 126874600467670935074359907)
      ·
        refine ⟨190311900701506402611539861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126874600467670935074359907 190311900701506402611539861)
        ·
          refine ⟨8920870345383112622415931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 190311900701506402611539861 8920870345383112622415931)
          ·
            refine ⟨13381305518074668933623897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8920870345383112622415931 13381305518074668933623897)
            ·
              refine ⟨10035979138556001700217923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13381305518074668933623897 10035979138556001700217923)
              ·
                refine ⟨15053968707834002550326885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10035979138556001700217923 15053968707834002550326885)
                ·
                  refine ⟨2822619132718875478186291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15053968707834002550326885 2822619132718875478186291)
                  ·
                    refine ⟨4233928699078313217279437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2822619132718875478186291 4233928699078313217279437)
                    ·
                      refine ⟨1587723262154367456479789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4233928699078313217279437 1587723262154367456479789)
                      ·
                        rfl

theorem cell23_3092080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 1, 4, 1, 3].length) (baseStart_3092080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3092080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3092080 prefixEnd_3092080 := by exact prefixLift 3092080
  have htrace : WordTrace (prefixWord ++ tailWord_3092080) baseStart_3092080 baseEnd_3092080 := by
    simpa [prefixWord, tailWord_3092080, baseEnd_3092080] using wordTrace_append hprefix tailTrace_3092080
  have hstable : (prefixWord ++ tailWord_3092080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3092080).length < 2 ^ (prefixWord ++ tailWord_3092080).sum := by decide
  have hdescent : baseEnd_3092080 < baseStart_3092080 := by decide
  rcases family_descends (prefixWord ++ tailWord_3092080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3092096 : List Nat := [2, 1, 1, 2, 1, 4, 2, 1, 1, 8]
def baseStart_3092096 : Nat := 118140960795 + 3092096 * 2 ^ 59
def prefixEnd_3092096 : Nat := 4983230072969 + 3 ^ 40 * 3092096 * 2
def baseEnd_3092096 : Nat := 529243825948279797959905

theorem tailTrace_3092096 : CollatzResearch.WordTrace tailWord_3092096 prefixEnd_3092096 529243825948279797959905 := by
  unfold tailWord_3092096
  simp only [CollatzResearch.WordTrace]
  refine ⟨56389003102935877399340071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75185337470581169865786761 56389003102935877399340071)
  ·
    refine ⟨84583504654403816099010107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56389003102935877399340071 84583504654403816099010107)
    ·
      refine ⟨126875256981605724148515161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84583504654403816099010107 126875256981605724148515161)
      ·
        refine ⟨95156442736204293111386371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126875256981605724148515161 95156442736204293111386371)
        ·
          refine ⟨142734664104306439667079557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95156442736204293111386371 142734664104306439667079557)
          ·
            refine ⟨26762749519557457437577417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 142734664104306439667079557 26762749519557457437577417)
            ·
              refine ⟨20072062139668093078183063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26762749519557457437577417 20072062139668093078183063)
              ·
                refine ⟨30108093209502139617274595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20072062139668093078183063 30108093209502139617274595)
                ·
                  refine ⟨45162139814253209425911893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30108093209502139617274595 45162139814253209425911893)
                  ·
                    refine ⟨529243825948279797959905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 45162139814253209425911893 529243825948279797959905)
                    ·
                      rfl

theorem cell23_3092096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 1, 1, 8].length) (baseStart_3092096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3092096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3092096 prefixEnd_3092096 := by exact prefixLift 3092096
  have htrace : WordTrace (prefixWord ++ tailWord_3092096) baseStart_3092096 baseEnd_3092096 := by
    simpa [prefixWord, tailWord_3092096, baseEnd_3092096] using wordTrace_append hprefix tailTrace_3092096
  have hstable : (prefixWord ++ tailWord_3092096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3092096).length < 2 ^ (prefixWord ++ tailWord_3092096).sum := by decide
  have hdescent : baseEnd_3092096 < baseStart_3092096 := by decide
  rcases family_descends (prefixWord ++ tailWord_3092096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3092097 : List Nat := [1, 2, 4, 2, 1, 3, 1, 3, 2, 1, 3]
def baseStart_3092097 : Nat := 118140960795 + 3092097 * 2 ^ 59
def prefixEnd_3092097 : Nat := 4983230072969 + 3 ^ 40 * 3092097 * 2
def baseEnd_3092097 : Nat := 1587731991325493889967211

theorem tailTrace_3092097 : CollatzResearch.WordTrace tailWord_3092097 prefixEnd_3092097 1587731991325493889967211 := by
  unfold tailWord_3092097
  simp only [CollatzResearch.WordTrace]
  refine ⟨112778042678868131969466545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75185361785912087979644363 112778042678868131969466545)
  ·
    refine ⟨84583532009151098977099909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112778042678868131969466545 84583532009151098977099909)
    ·
      refine ⟨15859412251715831058206233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 84583532009151098977099909 15859412251715831058206233)
      ·
        refine ⟨11894559188786873293654675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15859412251715831058206233 11894559188786873293654675)
        ·
          refine ⟨17841838783180309940482013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11894559188786873293654675 17841838783180309940482013)
          ·
            refine ⟨6690689543692616227680755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17841838783180309940482013 6690689543692616227680755)
            ·
              refine ⟨10036034315538924341521133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6690689543692616227680755 10036034315538924341521133)
              ·
                refine ⟨3763512868327096628070425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10036034315538924341521133 3763512868327096628070425)
                ·
                  refine ⟨2822634651245322471052819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3763512868327096628070425 2822634651245322471052819)
                  ·
                    refine ⟨4233951976867983706579229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2822634651245322471052819 4233951976867983706579229)
                    ·
                      refine ⟨1587731991325493889967211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4233951976867983706579229 1587731991325493889967211)
                      ·
                        rfl

theorem cell23_3092097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 3, 2, 1, 3].length) (baseStart_3092097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3092097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3092097 prefixEnd_3092097 := by exact prefixLift 3092097
  have htrace : WordTrace (prefixWord ++ tailWord_3092097) baseStart_3092097 baseEnd_3092097 := by
    simpa [prefixWord, tailWord_3092097, baseEnd_3092097] using wordTrace_append hprefix tailTrace_3092097
  have hstable : (prefixWord ++ tailWord_3092097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3092097).length < 2 ^ (prefixWord ++ tailWord_3092097).sum := by decide
  have hdescent : baseEnd_3092097 < baseStart_3092097 := by decide
  rcases family_descends (prefixWord ++ tailWord_3092097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3092120 : List Nat := [2, 1, 2, 4, 1, 2, 1, 1, 3, 4, 2]
def baseStart_3092120 : Nat := 118140960795 + 3092120 * 2 ^ 59
def prefixEnd_3092120 : Nat := 4983230072969 + 3 ^ 40 * 3092120 * 2
def baseEnd_3092120 : Nat := 1587743801380547299979605

theorem tailTrace_3092120 : CollatzResearch.WordTrace tailWord_3092120 prefixEnd_3092120 1587743801380547299979605 := by
  unfold tailWord_3092120
  simp only [CollatzResearch.WordTrace]
  refine ⟨56389440778892403448776907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75185921038523204598369209 56389440778892403448776907)
  ·
    refine ⟨84584161168338605173165361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56389440778892403448776907 84584161168338605173165361)
    ·
      refine ⟨63438120876253953879874021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84584161168338605173165361 63438120876253953879874021)
      ·
        refine ⟨11894647664297616352476379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63438120876253953879874021 11894647664297616352476379)
        ·
          refine ⟨17841971496446424528714569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11894647664297616352476379 17841971496446424528714569)
          ·
            refine ⟨13381478622334818396535927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17841971496446424528714569 13381478622334818396535927)
            ·
              refine ⟨20072217933502227594803891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13381478622334818396535927 20072217933502227594803891)
              ·
                refine ⟨30108326900253341392205837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20072217933502227594803891 30108326900253341392205837)
                ·
                  refine ⟨11290622587595003022077189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30108326900253341392205837 11290622587595003022077189)
                  ·
                    refine ⟨2116991735174063066639473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11290622587595003022077189 2116991735174063066639473)
                    ·
                      refine ⟨1587743801380547299979605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2116991735174063066639473 1587743801380547299979605)
                      ·
                        rfl

theorem cell23_3092120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 1, 3, 4, 2].length) (baseStart_3092120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3092120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3092120 prefixEnd_3092120 := by exact prefixLift 3092120
  have htrace : WordTrace (prefixWord ++ tailWord_3092120) baseStart_3092120 baseEnd_3092120 := by
    simpa [prefixWord, tailWord_3092120, baseEnd_3092120] using wordTrace_append hprefix tailTrace_3092120
  have hstable : (prefixWord ++ tailWord_3092120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3092120).length < 2 ^ (prefixWord ++ tailWord_3092120).sum := by decide
  have hdescent : baseEnd_3092120 < baseStart_3092120 := by decide
  rcases family_descends (prefixWord ++ tailWord_3092120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3092153 : List Nat := [1, 2, 1, 4, 1, 1, 3, 1, 1, 5, 3]
def baseStart_3092153 : Nat := 118140960795 + 3092153 * 2 ^ 59
def prefixEnd_3092153 : Nat := 4983230072969 + 3 ^ 40 * 3092153 * 2
def baseEnd_3092153 : Nat := 1587760746242145670866953

theorem tailTrace_3092153 : CollatzResearch.WordTrace tailWord_3092153 prefixEnd_3092153 1587760746242145670866953 := by
  unfold tailWord_3092153
  simp only [CollatzResearch.WordTrace]
  refine ⟨112780085166665253533505113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75186723444443502355670075 112780085166665253533505113)
  ·
    refine ⟨84585063874998940150128835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112780085166665253533505113 84585063874998940150128835)
    ·
      refine ⟨126877595812498410225193253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84585063874998940150128835 126877595812498410225193253)
      ·
        refine ⟨23789549214843451917223735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 126877595812498410225193253 23789549214843451917223735)
        ·
          refine ⟨35684323822265177875835603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23789549214843451917223735 35684323822265177875835603)
          ·
            refine ⟨53526485733397766813753405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35684323822265177875835603 53526485733397766813753405)
            ·
              refine ⟨20072432150024162555157527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53526485733397766813753405 20072432150024162555157527)
              ·
                refine ⟨30108648225036243832736291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20072432150024162555157527 30108648225036243832736291)
                ·
                  refine ⟨45162972337554365749104437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30108648225036243832736291 45162972337554365749104437)
                  ·
                    refine ⟨4234028656645721788978541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 45162972337554365749104437 4234028656645721788978541)
                    ·
                      refine ⟨1587760746242145670866953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4234028656645721788978541 1587760746242145670866953)
                      ·
                        rfl

theorem cell23_3092153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 1, 1, 5, 3].length) (baseStart_3092153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3092153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3092153 prefixEnd_3092153 := by exact prefixLift 3092153
  have htrace : WordTrace (prefixWord ++ tailWord_3092153) baseStart_3092153 baseEnd_3092153 := by
    simpa [prefixWord, tailWord_3092153, baseEnd_3092153] using wordTrace_append hprefix tailTrace_3092153
  have hstable : (prefixWord ++ tailWord_3092153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3092153).length < 2 ^ (prefixWord ++ tailWord_3092153).sum := by decide
  have hdescent : baseEnd_3092153 < baseStart_3092153 := by decide
  rcases family_descends (prefixWord ++ tailWord_3092153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3092188 : List Nat := [2, 2, 5, 1, 2, 2, 1, 2, 2, 2, 2]
def baseStart_3092188 : Nat := 118140960795 + 3092188 * 2 ^ 59
def prefixEnd_3092188 : Nat := 4983230072969 + 3 ^ 40 * 3092188 * 2
def baseEnd_3092188 : Nat := 1587778718065053033929293

theorem tailTrace_3092188 : CollatzResearch.WordTrace tailWord_3092188 prefixEnd_3092188 1587778718065053033929293 := by
  unfold tailWord_3092188
  simp only [CollatzResearch.WordTrace]
  refine ⟨56390680860769227255514609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75187574481025636340686145 56390680860769227255514609)
  ·
    refine ⟨42293010645576920441635957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56390680860769227255514609 42293010645576920441635957)
    ·
      refine ⟨3964969748022836291403371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 42293010645576920441635957 3964969748022836291403371)
      ·
        refine ⟨5947454622034254437105057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3964969748022836291403371 5947454622034254437105057)
        ·
          refine ⟨4460590966525690827828793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5947454622034254437105057 4460590966525690827828793)
          ·
            refine ⟨3345443224894268120871595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4460590966525690827828793 3345443224894268120871595)
            ·
              refine ⟨5018164837341402181307393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3345443224894268120871595 5018164837341402181307393)
              ·
                refine ⟨3763623628006051635980545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5018164837341402181307393 3763623628006051635980545)
                ·
                  refine ⟨2822717721004538726985409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3763623628006051635980545 2822717721004538726985409)
                  ·
                    refine ⟨2117038290753404045239057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2822717721004538726985409 2117038290753404045239057)
                    ·
                      refine ⟨1587778718065053033929293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2117038290753404045239057 1587778718065053033929293)
                      ·
                        rfl

theorem cell23_3092188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 1, 2, 2, 2, 2].length) (baseStart_3092188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3092188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3092188 prefixEnd_3092188 := by exact prefixLift 3092188
  have htrace : WordTrace (prefixWord ++ tailWord_3092188) baseStart_3092188 baseEnd_3092188 := by
    simpa [prefixWord, tailWord_3092188, baseEnd_3092188] using wordTrace_append hprefix tailTrace_3092188
  have hstable : (prefixWord ++ tailWord_3092188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3092188).length < 2 ^ (prefixWord ++ tailWord_3092188).sum := by decide
  have hdescent : baseEnd_3092188 < baseStart_3092188 := by decide
  rcases family_descends (prefixWord ++ tailWord_3092188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3092220 : List Nat := [2, 2, 2, 1, 3, 1, 1, 4, 3, 4]
def baseStart_3092220 : Nat := 118140960795 + 3092220 * 2 ^ 59
def prefixEnd_3092220 : Nat := 4983230072969 + 3 ^ 40 * 3092220 * 2
def baseEnd_3092220 : Nat := 529265049815332302909715

theorem tailTrace_3092220 : CollatzResearch.WordTrace tailWord_3092220 prefixEnd_3092220 529265049815332302909715 := by
  unfold tailWord_3092220
  simp only [CollatzResearch.WordTrace]
  refine ⟨56391264428711261988097057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75188352571615015984129409 56391264428711261988097057)
  ·
    refine ⟨42293448321533446491072793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56391264428711261988097057 42293448321533446491072793)
    ·
      refine ⟨31720086241150084868304595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42293448321533446491072793 31720086241150084868304595)
      ·
        refine ⟨47580129361725127302456893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31720086241150084868304595 47580129361725127302456893)
        ·
          refine ⟨17842548510646922738421335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47580129361725127302456893 17842548510646922738421335)
          ·
            refine ⟨26763822765970384107632003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17842548510646922738421335 26763822765970384107632003)
            ·
              refine ⟨40145734148955576161448005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26763822765970384107632003 40145734148955576161448005)
              ·
                refine ⟨7527325152929170530271501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40145734148955576161448005 7527325152929170530271501)
                ·
                  refine ⟨2822746932348438948851813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7527325152929170530271501 2822746932348438948851813)
                  ·
                    refine ⟨529265049815332302909715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2822746932348438948851813 529265049815332302909715)
                    ·
                      rfl

theorem cell23_3092220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 4, 3, 4].length) (baseStart_3092220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3092220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3092220 prefixEnd_3092220 := by exact prefixLift 3092220
  have htrace : WordTrace (prefixWord ++ tailWord_3092220) baseStart_3092220 baseEnd_3092220 := by
    simpa [prefixWord, tailWord_3092220, baseEnd_3092220] using wordTrace_append hprefix tailTrace_3092220
  have hstable : (prefixWord ++ tailWord_3092220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3092220).length < 2 ^ (prefixWord ++ tailWord_3092220).sum := by decide
  have hdescent : baseEnd_3092220 < baseStart_3092220 := by decide
  rcases family_descends (prefixWord ++ tailWord_3092220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3092247 : List Nat := [1, 1, 3, 4, 2, 2, 1, 2, 2, 2, 3]
def baseStart_3092247 : Nat := 118140960795 + 3092247 * 2 ^ 59
def prefixEnd_3092247 : Nat := 4983230072969 + 3 ^ 40 * 3092247 * 2
def baseEnd_3092247 : Nat := 1587809013423668303091521

theorem tailTrace_3092247 : CollatzResearch.WordTrace tailWord_3092247 prefixEnd_3092247 1587809013423668303091521 := by
  unfold tailWord_3092247
  simp only [CollatzResearch.WordTrace]
  refine ⟨112783513628324707587426995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75189009085549805058284663 112783513628324707587426995)
  ·
    refine ⟨169175270442487061381140493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112783513628324707587426995 169175270442487061381140493)
    ·
      refine ⟨63440726415932648017927685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 169175270442487061381140493 63440726415932648017927685)
      ·
        refine ⟨11895136202987371503361441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63440726415932648017927685 11895136202987371503361441)
        ·
          refine ⟨8921352152240528627521081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11895136202987371503361441 8921352152240528627521081)
          ·
            refine ⟨6691014114180396470640811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8921352152240528627521081 6691014114180396470640811)
            ·
              refine ⟨10036521171270594705961217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6691014114180396470640811 10036521171270594705961217)
              ·
                refine ⟨7527390878452946029470913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10036521171270594705961217 7527390878452946029470913)
                ·
                  refine ⟨5645543158839709522103185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7527390878452946029470913 5645543158839709522103185)
                  ·
                    refine ⟨4234157369129782141577389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5645543158839709522103185 4234157369129782141577389)
                    ·
                      refine ⟨1587809013423668303091521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4234157369129782141577389 1587809013423668303091521)
                      ·
                        rfl

theorem cell23_3092247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 2, 2, 2, 3].length) (baseStart_3092247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3092247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3092247 prefixEnd_3092247 := by exact prefixLift 3092247
  have htrace : WordTrace (prefixWord ++ tailWord_3092247) baseStart_3092247 baseEnd_3092247 := by
    simpa [prefixWord, tailWord_3092247, baseEnd_3092247] using wordTrace_append hprefix tailTrace_3092247
  have hstable : (prefixWord ++ tailWord_3092247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3092247).length < 2 ^ (prefixWord ++ tailWord_3092247).sum := by decide
  have hdescent : baseEnd_3092247 < baseStart_3092247 := by decide
  rcases family_descends (prefixWord ++ tailWord_3092247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3092280 : List Nat := [2, 1, 2, 1, 3, 4, 1, 1, 3, 5]
def baseStart_3092280 : Nat := 118140960795 + 3092280 * 2 ^ 59
def prefixEnd_3092280 : Nat := 4983230072969 + 3 ^ 40 * 3092280 * 2
def baseEnd_3092280 : Nat := 529275319428422224659623

theorem tailTrace_3092280 : CollatzResearch.WordTrace tailWord_3092280 prefixEnd_3092280 529275319428422224659623 := by
  unfold tailWord_3092280
  simp only [CollatzResearch.WordTrace]
  refine ⟨56392358618602577111689147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75189811491470102815585529 56392358618602577111689147)
  ·
    refine ⟨84588537927903865667533721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56392358618602577111689147 84588537927903865667533721)
    ·
      refine ⟨63441403445927899250650291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84588537927903865667533721 63441403445927899250650291)
      ·
        refine ⟨95162105168891848875975437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63441403445927899250650291 95162105168891848875975437)
        ·
          refine ⟨35685789438334443328490789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95162105168891848875975437 35685789438334443328490789)
          ·
            refine ⟨6691085519687708124092023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35685789438334443328490789 6691085519687708124092023)
            ·
              refine ⟨10036628279531562186138035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6691085519687708124092023 10036628279531562186138035)
              ·
                refine ⟨15054942419297343279207053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10036628279531562186138035 15054942419297343279207053)
                ·
                  refine ⟨5645603407236503729702645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15054942419297343279207053 5645603407236503729702645)
                  ·
                    refine ⟨529275319428422224659623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5645603407236503729702645 529275319428422224659623)
                    ·
                      rfl

theorem cell23_3092280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 1, 3, 5].length) (baseStart_3092280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3092280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3092280 prefixEnd_3092280 := by exact prefixLift 3092280
  have htrace : WordTrace (prefixWord ++ tailWord_3092280) baseStart_3092280 baseEnd_3092280 := by
    simpa [prefixWord, tailWord_3092280, baseEnd_3092280] using wordTrace_append hprefix tailTrace_3092280
  have hstable : (prefixWord ++ tailWord_3092280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3092280).length < 2 ^ (prefixWord ++ tailWord_3092280).sum := by decide
  have hdescent : baseEnd_3092280 < baseStart_3092280 := by decide
  rcases family_descends (prefixWord ++ tailWord_3092280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3092297 : List Nat := [1, 2, 1, 1, 2, 4, 5, 1, 1, 5]
def baseStart_3092297 : Nat := 118140960795 + 3092297 * 2 ^ 59
def prefixEnd_3092297 : Nat := 4983230072969 + 3 ^ 40 * 3092297 * 2
def baseEnd_3092297 : Nat := 529278229152131035822097

theorem tailTrace_3092297 : CollatzResearch.WordTrace tailWord_3092297 prefixEnd_3092297 529278229152131035822097 := by
  unfold tailWord_3092297
  simp only [CollatzResearch.WordTrace]
  refine ⟨112785337278143566126747145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75190224852095710751164763 112785337278143566126747145)
  ·
    refine ⟨84589002958607674595060359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112785337278143566126747145 84589002958607674595060359)
    ·
      refine ⟨126883504437911511892590539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84589002958607674595060359 126883504437911511892590539)
      ·
        refine ⟨190325256656867267838885809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126883504437911511892590539 190325256656867267838885809)
        ·
          refine ⟨142743942492650450879164357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 190325256656867267838885809 142743942492650450879164357)
          ·
            refine ⟨26764489217371959539843317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 142743942492650450879164357 26764489217371959539843317)
            ·
              refine ⟨2509170864128621206860311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26764489217371959539843317 2509170864128621206860311)
              ·
                refine ⟨3763756296192931810290467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2509170864128621206860311 3763756296192931810290467)
                ·
                  refine ⟨5645634444289397715435701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3763756296192931810290467 5645634444289397715435701)
                  ·
                    refine ⟨529278229152131035822097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5645634444289397715435701 529278229152131035822097)
                    ·
                      rfl

theorem cell23_3092297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 5, 1, 1, 5].length) (baseStart_3092297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3092297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3092297 prefixEnd_3092297 := by exact prefixLift 3092297
  have htrace : WordTrace (prefixWord ++ tailWord_3092297) baseStart_3092297 baseEnd_3092297 := by
    simpa [prefixWord, tailWord_3092297, baseEnd_3092297] using wordTrace_append hprefix tailTrace_3092297
  have hstable : (prefixWord ++ tailWord_3092297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3092297).length < 2 ^ (prefixWord ++ tailWord_3092297).sum := by decide
  have hdescent : baseEnd_3092297 < baseStart_3092297 := by decide
  rcases family_descends (prefixWord ++ tailWord_3092297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3092311 : List Nat := [1, 1, 3, 2, 5, 1, 1, 4, 1, 1, 3]
def baseStart_3092311 : Nat := 118140960795 + 3092311 * 2 ^ 59
def prefixEnd_3092311 : Nat := 4983230072969 + 3 ^ 40 * 3092311 * 2
def baseEnd_3092311 : Nat := 1587841876185556052691227

theorem tailTrace_3092311 : CollatzResearch.WordTrace tailWord_3092311 prefixEnd_3092311 1587841876185556052691227 := by
  unfold tailWord_3092311
  simp only [CollatzResearch.WordTrace]
  refine ⟨112785847900092846517756787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75190565266728564345171191 112785847900092846517756787)
  ·
    refine ⟨169178771850139269776635181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112785847900092846517756787 169178771850139269776635181)
    ·
      refine ⟨63442039443802226166238193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 169178771850139269776635181 63442039443802226166238193)
      ·
        refine ⟨47581529582851669624678645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63442039443802226166238193 47581529582851669624678645)
        ·
          refine ⟨4460768398392344027313623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 47581529582851669624678645 4460768398392344027313623)
          ·
            refine ⟨6691152597588516040970435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4460768398392344027313623 6691152597588516040970435)
            ·
              refine ⟨10036728896382774061455653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6691152597588516040970435 10036728896382774061455653)
              ·
                refine ⟨1881886668071770136522935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10036728896382774061455653 1881886668071770136522935)
                ·
                  refine ⟨2822830002107655204784403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1881886668071770136522935 2822830002107655204784403)
                  ·
                    refine ⟨4234245003161482807176605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2822830002107655204784403 4234245003161482807176605)
                    ·
                      refine ⟨1587841876185556052691227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4234245003161482807176605 1587841876185556052691227)
                      ·
                        rfl

theorem cell23_3092311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 4, 1, 1, 3].length) (baseStart_3092311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3092311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3092311 prefixEnd_3092311 := by exact prefixLift 3092311
  have htrace : WordTrace (prefixWord ++ tailWord_3092311) baseStart_3092311 baseEnd_3092311 := by
    simpa [prefixWord, tailWord_3092311, baseEnd_3092311] using wordTrace_append hprefix tailTrace_3092311
  have hstable : (prefixWord ++ tailWord_3092311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3092311).length < 2 ^ (prefixWord ++ tailWord_3092311).sum := by decide
  have hdescent : baseEnd_3092311 < baseStart_3092311 := by decide
  rcases family_descends (prefixWord ++ tailWord_3092311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3092327 : List Nat := [1, 1, 5, 1, 2, 1, 1, 5, 2, 4]
def baseStart_3092327 : Nat := 118140960795 + 3092327 * 2 ^ 59
def prefixEnd_3092327 : Nat := 4983230072969 + 3 ^ 40 * 3092327 * 2
def baseEnd_3092327 : Nat := 529283363958675996697051

theorem tailTrace_3092327 : CollatzResearch.WordTrace tailWord_3092327 prefixEnd_3092327 529283363958675996697051 := by
  unfold tailWord_3092327
  simp only [CollatzResearch.WordTrace]
  refine ⟨112786431468034881250339235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75190954312023254166892823 112786431468034881250339235)
  ·
    refine ⟨169179647202052321875508853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112786431468034881250339235 169179647202052321875508853)
    ·
      refine ⟨15860591925192405175828955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 169179647202052321875508853 15860591925192405175828955)
      ·
        refine ⟨23790887887788607763743433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15860591925192405175828955 23790887887788607763743433)
        ·
          refine ⟨17843165915841455822807575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23790887887788607763743433 17843165915841455822807575)
          ·
            refine ⟨26764748873762183734211363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17843165915841455822807575 26764748873762183734211363)
            ·
              refine ⟨40147123310643275601317045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26764748873762183734211363 40147123310643275601317045)
              ·
                refine ⟨3763792810372807087623473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40147123310643275601317045 3763792810372807087623473)
                ·
                  refine ⟨2822844607779605315717605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3763792810372807087623473 2822844607779605315717605)
                  ·
                    refine ⟨529283363958675996697051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2822844607779605315717605 529283363958675996697051)
                    ·
                      rfl

theorem cell23_3092327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 5, 2, 4].length) (baseStart_3092327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3092327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3092327 prefixEnd_3092327 := by exact prefixLift 3092327
  have htrace : WordTrace (prefixWord ++ tailWord_3092327) baseStart_3092327 baseEnd_3092327 := by
    simpa [prefixWord, tailWord_3092327, baseEnd_3092327] using wordTrace_append hprefix tailTrace_3092327
  have hstable : (prefixWord ++ tailWord_3092327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3092327).length < 2 ^ (prefixWord ++ tailWord_3092327).sum := by decide
  have hdescent : baseEnd_3092327 < baseStart_3092327 := by decide
  rcases family_descends (prefixWord ++ tailWord_3092327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3092337 : List Nat := [1, 2, 2, 2, 1, 3, 2, 4, 1, 2, 3]
def baseStart_3092337 : Nat := 118140960795 + 3092337 * 2 ^ 59
def prefixEnd_3092337 : Nat := 4983230072969 + 3 ^ 40 * 3092337 * 2
def baseEnd_3092337 : Nat := 1587855226682572950966107

theorem tailTrace_3092337 : CollatzResearch.WordTrace tailWord_3092337 prefixEnd_3092337 1587855226682572950966107 := by
  unfold tailWord_3092337
  simp only [CollatzResearch.WordTrace]
  refine ⟨112786796197998652958203265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75191197465332435305468843 112786796197998652958203265)
  ·
    refine ⟨84590097148498989718652449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112786796197998652958203265 84590097148498989718652449)
    ·
      refine ⟨63442572861374242288989337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84590097148498989718652449 63442572861374242288989337)
      ·
        refine ⟨47581929646030681716742003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63442572861374242288989337 47581929646030681716742003)
        ·
          refine ⟨71372894469046022575113005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47581929646030681716742003 71372894469046022575113005)
          ·
            refine ⟨26764835425892258465667377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71372894469046022575113005 26764835425892258465667377)
            ·
              refine ⟨20073626569419193849250533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26764835425892258465667377 20073626569419193849250533)
              ·
                refine ⟨3763804981766098846734475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20073626569419193849250533 3763804981766098846734475)
                ·
                  refine ⟨5645707472649148270101713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3763804981766098846734475 5645707472649148270101713)
                  ·
                    refine ⟨4234280604486861202576285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5645707472649148270101713 4234280604486861202576285)
                    ·
                      refine ⟨1587855226682572950966107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4234280604486861202576285 1587855226682572950966107)
                      ·
                        rfl

theorem cell23_3092337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 4, 1, 2, 3].length) (baseStart_3092337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3092337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3092337 prefixEnd_3092337 := by exact prefixLift 3092337
  have htrace : WordTrace (prefixWord ++ tailWord_3092337) baseStart_3092337 baseEnd_3092337 := by
    simpa [prefixWord, tailWord_3092337, baseEnd_3092337] using wordTrace_append hprefix tailTrace_3092337
  have hstable : (prefixWord ++ tailWord_3092337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3092337).length < 2 ^ (prefixWord ++ tailWord_3092337).sum := by decide
  have hdescent : baseEnd_3092337 < baseStart_3092337 := by decide
  rcases family_descends (prefixWord ++ tailWord_3092337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3092377 : List Nat := [1, 2, 1, 2, 1, 3, 2, 1, 5, 3, 2]
def baseStart_3092377 : Nat := 118140960795 + 3092377 * 2 ^ 59
def prefixEnd_3092377 : Nat := 4983230072969 + 3 ^ 40 * 3092377 * 2
def baseEnd_3092377 : Nat := 1587875765908752794465923

theorem tailTrace_3092377 : CollatzResearch.WordTrace tailWord_3092377 prefixEnd_3092377 1587875765908752794465923 := by
  unfold tailWord_3092377
  simp only [CollatzResearch.WordTrace]
  refine ⟨112788255117853739789659385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75192170078569159859772923 112788255117853739789659385)
  ·
    refine ⟨84591191338390304842244539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112788255117853739789659385 84591191338390304842244539)
    ·
      refine ⟨126886787007585457263366809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84591191338390304842244539 126886787007585457263366809)
      ·
        refine ⟨95165090255689092947525107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126886787007585457263366809 95165090255689092947525107)
        ·
          refine ⟨142747635383533639421287661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95165090255689092947525107 142747635383533639421287661)
          ·
            refine ⟨53530363268825114782982873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 142747635383533639421287661 53530363268825114782982873)
            ·
              refine ⟨40147772451618836087237155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53530363268825114782982873 40147772451618836087237155)
              ·
                refine ⟨60221658677428254130855733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40147772451618836087237155 60221658677428254130855733)
                ·
                  refine ⟨5645780501008898824767725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 60221658677428254130855733 5645780501008898824767725)
                  ·
                    refine ⟨2117167687878337059287897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5645780501008898824767725 2117167687878337059287897)
                    ·
                      refine ⟨1587875765908752794465923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2117167687878337059287897 1587875765908752794465923)
                      ·
                        rfl

theorem cell23_3092377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 1, 5, 3, 2].length) (baseStart_3092377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3092377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3092377 prefixEnd_3092377 := by exact prefixLift 3092377
  have htrace : WordTrace (prefixWord ++ tailWord_3092377) baseStart_3092377 baseEnd_3092377 := by
    simpa [prefixWord, tailWord_3092377, baseEnd_3092377] using wordTrace_append hprefix tailTrace_3092377
  have hstable : (prefixWord ++ tailWord_3092377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3092377).length < 2 ^ (prefixWord ++ tailWord_3092377).sum := by decide
  have hdescent : baseEnd_3092377 < baseStart_3092377 := by decide
  rcases family_descends (prefixWord ++ tailWord_3092377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3092407 : List Nat := [1, 1, 3, 1, 3, 1, 1, 3, 3, 4, 2]
def baseStart_3092407 : Nat := 118140960795 + 3092407 * 2 ^ 59
def prefixEnd_3092407 : Nat := 4983230072969 + 3 ^ 40 * 3092407 * 2
def baseEnd_3092407 : Nat := 1587891170328387677090785

theorem tailTrace_3092407 : CollatzResearch.WordTrace tailWord_3092407 prefixEnd_3092407 1587891170328387677090785 := by
  unfold tailWord_3092407
  simp only [CollatzResearch.WordTrace]
  refine ⟨112789349307745054913251475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75192899538496703275500983 112789349307745054913251475)
  ·
    refine ⟨169184023961617582369877213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112789349307745054913251475 169184023961617582369877213)
    ·
      refine ⟨63444008985606593388703955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 169184023961617582369877213 63444008985606593388703955)
      ·
        refine ⟨95166013478409890083055933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63444008985606593388703955 95166013478409890083055933)
        ·
          refine ⟨35687255054403708781145975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95166013478409890083055933 35687255054403708781145975)
          ·
            refine ⟨53530882581605563171718963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35687255054403708781145975 53530882581605563171718963)
            ·
              refine ⟨80296323872408344757578445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53530882581605563171718963 80296323872408344757578445)
              ·
                refine ⟨30111121452153129284091917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80296323872408344757578445 30111121452153129284091917)
                ·
                  refine ⟨11291670544557423481534469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30111121452153129284091917 11291670544557423481534469)
                  ·
                    refine ⟨2117188227104516902787713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11291670544557423481534469 2117188227104516902787713)
                    ·
                      refine ⟨1587891170328387677090785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2117188227104516902787713 1587891170328387677090785)
                      ·
                        rfl

theorem cell23_3092407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 3, 3, 4, 2].length) (baseStart_3092407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3092407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3092407 prefixEnd_3092407 := by exact prefixLift 3092407
  have htrace : WordTrace (prefixWord ++ tailWord_3092407) baseStart_3092407 baseEnd_3092407 := by
    simpa [prefixWord, tailWord_3092407, baseEnd_3092407] using wordTrace_append hprefix tailTrace_3092407
  have hstable : (prefixWord ++ tailWord_3092407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3092407).length < 2 ^ (prefixWord ++ tailWord_3092407).sum := by decide
  have hdescent : baseEnd_3092407 < baseStart_3092407 := by decide
  rcases family_descends (prefixWord ++ tailWord_3092407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3092445 : List Nat := [1, 4, 3, 1, 4, 1, 1, 2, 1, 3, 2]
def baseStart_3092445 : Nat := 118140960795 + 3092445 * 2 ^ 59
def prefixEnd_3092445 : Nat := 4983230072969 + 3 ^ 40 * 3092445 * 2
def baseEnd_3092445 : Nat := 1587910682593258528415611

theorem tailTrace_3092445 : CollatzResearch.WordTrace tailWord_3092445 prefixEnd_3092445 1587910682593258528415611 := by
  unfold tailWord_3092445
  simp only [CollatzResearch.WordTrace]
  refine ⟨112790735281607387403134789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75193823521071591602089859 112790735281607387403134789)
  ·
    refine ⟨21148262865301385138087773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 112790735281607387403134789 21148262865301385138087773)
    ·
      refine ⟨7930598574488019426782915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21148262865301385138087773 7930598574488019426782915)
      ·
        refine ⟨11895897861732029140174373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7930598574488019426782915 11895897861732029140174373)
        ·
          refine ⟨2230480849074755463782695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11895897861732029140174373 2230480849074755463782695)
          ·
            refine ⟨3345721273612133195674043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2230480849074755463782695 3345721273612133195674043)
            ·
              refine ⟨5018581910418199793511065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3345721273612133195674043 5018581910418199793511065)
              ·
                refine ⟨3763936432813649845133299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5018581910418199793511065 3763936432813649845133299)
                ·
                  refine ⟨5645904649220474767699949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3763936432813649845133299 5645904649220474767699949)
                  ·
                    refine ⟨2117214243457678037887481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5645904649220474767699949 2117214243457678037887481)
                    ·
                      refine ⟨1587910682593258528415611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2117214243457678037887481 1587910682593258528415611)
                      ·
                        rfl

theorem cell23_3092445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 1, 2, 1, 3, 2].length) (baseStart_3092445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3092445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3092445 prefixEnd_3092445 := by exact prefixLift 3092445
  have htrace : WordTrace (prefixWord ++ tailWord_3092445) baseStart_3092445 baseEnd_3092445 := by
    simpa [prefixWord, tailWord_3092445, baseEnd_3092445] using wordTrace_append hprefix tailTrace_3092445
  have hstable : (prefixWord ++ tailWord_3092445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3092445).length < 2 ^ (prefixWord ++ tailWord_3092445).sum := by decide
  have hdescent : baseEnd_3092445 < baseStart_3092445 := by decide
  rcases family_descends (prefixWord ++ tailWord_3092445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3092460 : List Nat := [2, 2, 1, 1, 2, 1, 1, 5, 1, 7]
def baseStart_3092460 : Nat := 118140960795 + 3092460 * 2 ^ 59
def prefixEnd_3092460 : Nat := 4983230072969 + 3 ^ 40 * 3092460 * 2
def baseEnd_3092460 : Nat := 529306128267691989909347

theorem tailTrace_3092460 : CollatzResearch.WordTrace tailWord_3092460 prefixEnd_3092460 529306128267691989909347 := by
  unfold tailWord_3092460
  simp only [CollatzResearch.WordTrace]
  refine ⟨56395641188276522482465417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75194188251035363309953889 56395641188276522482465417)
  ·
    refine ⟨42296730891207391861849063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56395641188276522482465417 42296730891207391861849063)
    ·
      refine ⟨63445096336811087792773595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42296730891207391861849063 63445096336811087792773595)
      ·
        refine ⟨95167644505216631689160393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63445096336811087792773595 95167644505216631689160393)
        ·
          refine ⟨71375733378912473766870295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95167644505216631689160393 71375733378912473766870295)
          ·
            refine ⟨107063600068368710650305443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71375733378912473766870295 107063600068368710650305443)
            ·
              refine ⟨160595400102553065975458165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107063600068368710650305443 160595400102553065975458165)
              ·
                refine ⟨15055818759614349935199203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 160595400102553065975458165 15055818759614349935199203)
                ·
                  refine ⟨22583728139421524902798805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15055818759614349935199203 22583728139421524902798805)
                  ·
                    refine ⟨529306128267691989909347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22583728139421524902798805 529306128267691989909347)
                    ·
                      rfl

theorem cell23_3092460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 7].length) (baseStart_3092460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3092460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3092460 prefixEnd_3092460 := by exact prefixLift 3092460
  have htrace : WordTrace (prefixWord ++ tailWord_3092460) baseStart_3092460 baseEnd_3092460 := by
    simpa [prefixWord, tailWord_3092460, baseEnd_3092460] using wordTrace_append hprefix tailTrace_3092460
  have hstable : (prefixWord ++ tailWord_3092460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3092460).length < 2 ^ (prefixWord ++ tailWord_3092460).sum := by decide
  have hdescent : baseEnd_3092460 < baseStart_3092460 := by decide
  rcases family_descends (prefixWord ++ tailWord_3092460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3092467 : List Nat := [1, 1, 1, 2, 2, 2, 1, 2, 4, 5, 2]
def baseStart_3092467 : Nat := 118140960795 + 3092467 * 2 ^ 59
def prefixEnd_3092467 : Nat := 4983230072969 + 3 ^ 40 * 3092467 * 2
def baseEnd_3092467 : Nat := 1587921979167657442340509

theorem tailTrace_3092467 : CollatzResearch.WordTrace tailWord_3092467 prefixEnd_3092467 1587921979167657442340509 := by
  unfold tailWord_3092467
  simp only [CollatzResearch.WordTrace]
  refine ⟨112791537687527685160435655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75194358458351790106957103 112791537687527685160435655)
  ·
    refine ⟨169187306531291527740653483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112791537687527685160435655 169187306531291527740653483)
    ·
      refine ⟨253780959796937291610980225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169187306531291527740653483 253780959796937291610980225)
      ·
        refine ⟨190335719847702968708235169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 253780959796937291610980225 190335719847702968708235169)
        ·
          refine ⟨142751789885777226531176377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 190335719847702968708235169 142751789885777226531176377)
          ·
            refine ⟨107063842414332919898382283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142751789885777226531176377 107063842414332919898382283)
            ·
              refine ⟨160595763621499379847573425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107063842414332919898382283 160595763621499379847573425)
              ·
                refine ⟨120446822716124534885680069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 160595763621499379847573425 120446822716124534885680069)
                ·
                  refine ⟨22583779259273350291065013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 120446822716124534885680069 22583779259273350291065013)
                  ·
                    refine ⟨2117229305556876589787345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22583779259273350291065013 2117229305556876589787345)
                    ·
                      refine ⟨1587921979167657442340509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2117229305556876589787345 1587921979167657442340509)
                      ·
                        rfl

theorem cell23_3092467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 4, 5, 2].length) (baseStart_3092467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3092467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3092467 prefixEnd_3092467 := by exact prefixLift 3092467
  have htrace : WordTrace (prefixWord ++ tailWord_3092467) baseStart_3092467 baseEnd_3092467 := by
    simpa [prefixWord, tailWord_3092467, baseEnd_3092467] using wordTrace_append hprefix tailTrace_3092467
  have hstable : (prefixWord ++ tailWord_3092467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3092467).length < 2 ^ (prefixWord ++ tailWord_3092467).sum := by decide
  have hdescent : baseEnd_3092467 < baseStart_3092467 := by decide
  rcases family_descends (prefixWord ++ tailWord_3092467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3092477 : List Nat := [1, 4, 1, 1, 1, 2, 4, 2, 2, 5]
def baseStart_3092477 : Nat := 118140960795 + 3092477 * 2 ^ 59
def prefixEnd_3092477 : Nat := 4983230072969 + 3 ^ 40 * 3092477 * 2
def baseEnd_3092477 : Nat := 529309037991400801071821

theorem tailTrace_3092477 : CollatzResearch.WordTrace tailWord_3092477 prefixEnd_3092477 529309037991400801071821 := by
  unfold tailWord_3092477
  simp only [CollatzResearch.WordTrace]
  refine ⟨112791902417491456868299685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75194601611660971245533123 112791902417491456868299685)
  ·
    refine ⟨21148481703279648162806191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 112791902417491456868299685 21148481703279648162806191)
    ·
      refine ⟨31722722554919472244209287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21148481703279648162806191 31722722554919472244209287)
      ·
        refine ⟨47584083832379208366313931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31722722554919472244209287 47584083832379208366313931)
        ·
          refine ⟨71376125748568812549470897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47584083832379208366313931 71376125748568812549470897)
          ·
            refine ⟨53532094311426609412103173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71376125748568812549470897 53532094311426609412103173)
            ·
              refine ⟨10037267683392489264769345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53532094311426609412103173 10037267683392489264769345)
              ·
                refine ⟨7527950762544366948577009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10037267683392489264769345 7527950762544366948577009)
                ·
                  refine ⟨5645963071908275211432757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7527950762544366948577009 5645963071908275211432757)
                  ·
                    refine ⟨529309037991400801071821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5645963071908275211432757 529309037991400801071821)
                    ·
                      rfl

theorem cell23_3092477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 2, 2, 5].length) (baseStart_3092477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3092477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3092477 prefixEnd_3092477 := by exact prefixLift 3092477
  have htrace : WordTrace (prefixWord ++ tailWord_3092477) baseStart_3092477 baseEnd_3092477 := by
    simpa [prefixWord, tailWord_3092477, baseEnd_3092477] using wordTrace_append hprefix tailTrace_3092477
  have hstable : (prefixWord ++ tailWord_3092477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3092477).length < 2 ^ (prefixWord ++ tailWord_3092477).sum := by decide
  have hdescent : baseEnd_3092477 < baseStart_3092477 := by decide
  rcases family_descends (prefixWord ++ tailWord_3092477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3092487 : List Nat := [1, 1, 4, 3, 1, 2, 2, 1, 1, 2, 5]
def baseStart_3092487 : Nat := 118140960795 + 3092487 * 2 ^ 59
def prefixEnd_3092487 : Nat := 4983230072969 + 3 ^ 40 * 3092487 * 2
def baseEnd_3092487 : Nat := 1587932248780747364090417

theorem tailTrace_3092487 : CollatzResearch.WordTrace tailWord_3092487 prefixEnd_3092487 1587932248780747364090417 := by
  unfold tailWord_3092487
  simp only [CollatzResearch.WordTrace]
  refine ⟨112792267147455228576163715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75194844764970152384109143 112792267147455228576163715)
  ·
    refine ⟨169188400721182842864245573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112792267147455228576163715 169188400721182842864245573)
    ·
      refine ⟨31722825135221783037046045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 169188400721182842864245573 31722825135221783037046045)
      ·
        refine ⟨11896059425708168638892267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31722825135221783037046045 11896059425708168638892267)
        ·
          refine ⟨17844089138562252958338401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11896059425708168638892267 17844089138562252958338401)
          ·
            refine ⟨13383066853921689718753801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17844089138562252958338401 13383066853921689718753801)
            ·
              refine ⟨10037300140441267289065351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13383066853921689718753801 10037300140441267289065351)
              ·
                refine ⟨15055950210661900933598027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10037300140441267289065351 15055950210661900933598027)
                ·
                  refine ⟨22583925315992851400397041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15055950210661900933598027 22583925315992851400397041)
                  ·
                    refine ⟨16937943986994638550297781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22583925315992851400397041 16937943986994638550297781)
                    ·
                      refine ⟨1587932248780747364090417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16937943986994638550297781 1587932248780747364090417)
                      ·
                        rfl

theorem cell23_3092487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 1, 1, 2, 5].length) (baseStart_3092487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3092487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3092487 prefixEnd_3092487 := by exact prefixLift 3092487
  have htrace : WordTrace (prefixWord ++ tailWord_3092487) baseStart_3092487 baseEnd_3092487 := by
    simpa [prefixWord, tailWord_3092487, baseEnd_3092487] using wordTrace_append hprefix tailTrace_3092487
  have hstable : (prefixWord ++ tailWord_3092487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3092487).length < 2 ^ (prefixWord ++ tailWord_3092487).sum := by decide
  have hdescent : baseEnd_3092487 < baseStart_3092487 := by decide
  rcases family_descends (prefixWord ++ tailWord_3092487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3092514 : List Nat := [3, 3, 1, 1, 1, 2, 1, 2, 1, 6, 2]
def baseStart_3092514 : Nat := 118140960795 + 3092514 * 2 ^ 59
def prefixEnd_3092514 : Nat := 4983230072969 + 3 ^ 40 * 3092514 * 2
def baseEnd_3092514 : Nat := 1587946112758418758452793

theorem tailTrace_3092514 : CollatzResearch.WordTrace tailWord_3092514 prefixEnd_3092514 1587946112758418758452793 := by
  unfold tailWord_3092514
  simp only [CollatzResearch.WordTrace]
  refine ⟨28198312979589353046849149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75195501278904941458264397 28198312979589353046849149)
  ·
    refine ⟨10574367367346007392568431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28198312979589353046849149 10574367367346007392568431)
    ·
      refine ⟨15861551051019011088852647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10574367367346007392568431 15861551051019011088852647)
      ·
        refine ⟨23792326576528516633278971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15861551051019011088852647 23792326576528516633278971)
        ·
          refine ⟨35688489864792774949918457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23792326576528516633278971 35688489864792774949918457)
          ·
            refine ⟨26766367398594581212438843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35688489864792774949918457 26766367398594581212438843)
            ·
              refine ⟨40149551097891871818658265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26766367398594581212438843 40149551097891871818658265)
              ·
                refine ⟨30112163323418903863993699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40149551097891871818658265 30112163323418903863993699)
                ·
                  refine ⟨45168244985128355795990549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30112163323418903863993699 45168244985128355795990549)
                  ·
                    refine ⟨2117261483677891677937057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 45168244985128355795990549 2117261483677891677937057)
                    ·
                      refine ⟨1587946112758418758452793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2117261483677891677937057 1587946112758418758452793)
                      ·
                        rfl

theorem cell23_3092514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 2, 1, 6, 2].length) (baseStart_3092514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3092514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3092514 prefixEnd_3092514 := by exact prefixLift 3092514
  have htrace : WordTrace (prefixWord ++ tailWord_3092514) baseStart_3092514 baseEnd_3092514 := by
    simpa [prefixWord, tailWord_3092514, baseEnd_3092514] using wordTrace_append hprefix tailTrace_3092514
  have hstable : (prefixWord ++ tailWord_3092514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3092514).length < 2 ^ (prefixWord ++ tailWord_3092514).sum := by decide
  have hdescent : baseEnd_3092514 < baseStart_3092514 := by decide
  rcases family_descends (prefixWord ++ tailWord_3092514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3092541 : List Nat := [1, 4, 1, 3, 1, 1, 1, 6, 1, 4]
def baseStart_3092541 : Nat := 118140960795 + 3092541 * 2 ^ 59
def prefixEnd_3092541 : Nat := 4983230072969 + 3 ^ 40 * 3092541 * 2
def baseEnd_3092541 : Nat := 529319992245363384271723

theorem tailTrace_3092541 : CollatzResearch.WordTrace tailWord_3092541 prefixEnd_3092541 529319992245363384271723 := by
  unfold tailWord_3092541
  simp only [CollatzResearch.WordTrace]
  refine ⟨112794236689259595798629477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75196157792839730532419651 112794236689259595798629477)
  ·
    refine ⟨21148919379236174212243027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 112794236689259595798629477 21148919379236174212243027)
    ·
      refine ⟨31723379068854261318364541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21148919379236174212243027 31723379068854261318364541)
      ·
        refine ⟨11896267150820347994386703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31723379068854261318364541 11896267150820347994386703)
        ·
          refine ⟨17844400726230521991580055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11896267150820347994386703 17844400726230521991580055)
          ·
            refine ⟨26766601089345782987370083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17844400726230521991580055 26766601089345782987370083)
            ·
              refine ⟨40149901634018674481055125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26766601089345782987370083 40149901634018674481055125)
              ·
                refine ⟨1882026639094625366299459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 40149901634018674481055125 1882026639094625366299459)
                ·
                  refine ⟨2823039958641938049449189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1882026639094625366299459 2823039958641938049449189)
                  ·
                    refine ⟨529319992245363384271723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2823039958641938049449189 529319992245363384271723)
                    ·
                      rfl

theorem cell23_3092541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 6, 1, 4].length) (baseStart_3092541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3092541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3092541 prefixEnd_3092541 := by exact prefixLift 3092541
  have htrace : WordTrace (prefixWord ++ tailWord_3092541) baseStart_3092541 baseEnd_3092541 := by
    simpa [prefixWord, tailWord_3092541, baseEnd_3092541] using wordTrace_append hprefix tailTrace_3092541
  have hstable : (prefixWord ++ tailWord_3092541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3092541).length < 2 ^ (prefixWord ++ tailWord_3092541).sum := by decide
  have hdescent : baseEnd_3092541 < baseStart_3092541 := by decide
  rcases family_descends (prefixWord ++ tailWord_3092541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3092567 : List Nat := [1, 1, 3, 2, 2, 1, 2, 3, 3, 5]
def baseStart_3092567 : Nat := 118140960795 + 3092567 * 2 ^ 59
def prefixEnd_3092567 : Nat := 4983230072969 + 3 ^ 40 * 3092567 * 2
def baseEnd_3092567 : Nat := 529324442411035683696683

theorem tailTrace_3092567 : CollatzResearch.WordTrace tailWord_3092567 prefixEnd_3092567 529324442411035683696683 := by
  unfold tailWord_3092567
  simp only [CollatzResearch.WordTrace]
  refine ⟨112795184987165402239075955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75196789991443601492717303 112795184987165402239075955)
  ·
    refine ⟨169192777480748103358613933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112795184987165402239075955 169192777480748103358613933)
    ·
      refine ⟨63447291555280538759480225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 169192777480748103358613933 63447291555280538759480225)
      ·
        refine ⟨47585468666460404069610169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63447291555280538759480225 47585468666460404069610169)
        ·
          refine ⟨35689101499845303052207627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47585468666460404069610169 35689101499845303052207627)
          ·
            refine ⟨53533652249767954578311441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35689101499845303052207627 53533652249767954578311441)
            ·
              refine ⟨40150239187325965933733581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53533652249767954578311441 40150239187325965933733581)
              ·
                refine ⟨15056339695247237225150093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40150239187325965933733581 15056339695247237225150093)
                ·
                  refine ⟨5646127385717713959431285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15056339695247237225150093 5646127385717713959431285)
                  ·
                    refine ⟨529324442411035683696683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5646127385717713959431285 529324442411035683696683)
                    ·
                      rfl

theorem cell23_3092567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 3, 3, 5].length) (baseStart_3092567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3092567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3092567 prefixEnd_3092567 := by exact prefixLift 3092567
  have htrace : WordTrace (prefixWord ++ tailWord_3092567) baseStart_3092567 baseEnd_3092567 := by
    simpa [prefixWord, tailWord_3092567, baseEnd_3092567] using wordTrace_append hprefix tailTrace_3092567
  have hstable : (prefixWord ++ tailWord_3092567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3092567).length < 2 ^ (prefixWord ++ tailWord_3092567).sum := by decide
  have hdescent : baseEnd_3092567 < baseStart_3092567 := by decide
  rcases family_descends (prefixWord ++ tailWord_3092567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3092591 : List Nat := [1, 1, 2, 1, 3, 5, 1, 2, 2, 3, 2]
def baseStart_3092591 : Nat := 118140960795 + 3092591 * 2 ^ 59
def prefixEnd_3092591 : Nat := 4983230072969 + 3 ^ 40 * 3092591 * 2
def baseEnd_3092591 : Nat := 1587985650768814957189939

theorem tailTrace_3092591 : CollatzResearch.WordTrace tailWord_3092591 prefixEnd_3092591 1587985650768814957189939 := by
  unfold tailWord_3092591
  simp only [CollatzResearch.WordTrace]
  refine ⟨112796060339078454337949627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75197373559385636225299751 112796060339078454337949627)
  ·
    refine ⟨169194090508617681506924441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112796060339078454337949627 169194090508617681506924441)
    ·
      refine ⟨126895567881463261130193331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169194090508617681506924441 126895567881463261130193331)
      ·
        refine ⟨190343351822194891695289997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126895567881463261130193331 190343351822194891695289997)
        ·
          refine ⟨71378756933323084385733749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 190343351822194891695289997 71378756933323084385733749)
          ·
            refine ⟨6691758462499039161162539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 71378756933323084385733749 6691758462499039161162539)
            ·
              refine ⟨10037637693748558741743809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6691758462499039161162539 10037637693748558741743809)
              ·
                refine ⟨7528228270311419056307857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10037637693748558741743809 7528228270311419056307857)
                ·
                  refine ⟨5646171202733564292230893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7528228270311419056307857 5646171202733564292230893)
                  ·
                    refine ⟨2117314201025086609586585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5646171202733564292230893 2117314201025086609586585)
                    ·
                      refine ⟨1587985650768814957189939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2117314201025086609586585 1587985650768814957189939)
                      ·
                        rfl

theorem cell23_3092591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 2, 2, 3, 2].length) (baseStart_3092591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3092591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3092591 prefixEnd_3092591 := by exact prefixLift 3092591
  have htrace : WordTrace (prefixWord ++ tailWord_3092591) baseStart_3092591 baseEnd_3092591 := by
    simpa [prefixWord, tailWord_3092591, baseEnd_3092591] using wordTrace_append hprefix tailTrace_3092591
  have hstable : (prefixWord ++ tailWord_3092591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3092591).length < 2 ^ (prefixWord ++ tailWord_3092591).sum := by decide
  have hdescent : baseEnd_3092591 < baseStart_3092591 := by decide
  rcases family_descends (prefixWord ++ tailWord_3092591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3092598 : List Nat := [5, 1, 1, 2, 1, 2, 3, 1, 3, 1, 3]
def baseStart_3092598 : Nat := 118140960795 + 3092598 * 2 ^ 59
def prefixEnd_3092598 : Nat := 4983230072969 + 3 ^ 40 * 3092598 * 2
def baseEnd_3092598 : Nat := 1587989245133396429802407

theorem tailTrace_3092598 : CollatzResearch.WordTrace tailWord_3092598 prefixEnd_3092598 1587989245133396429802407 := by
  unfold tailWord_3092598
  simp only [CollatzResearch.WordTrace]
  refine ⟨7049769728128318408340903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 75197543766702063022302965 7049769728128318408340903)
  ·
    refine ⟨10574654592192477612511355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7049769728128318408340903 10574654592192477612511355)
    ·
      refine ⟨15861981888288716418767033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10574654592192477612511355 15861981888288716418767033)
      ·
        refine ⟨11896486416216537314075275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15861981888288716418767033 11896486416216537314075275)
        ·
          refine ⟨17844729624324805971112913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11896486416216537314075275 17844729624324805971112913)
          ·
            refine ⟨13383547218243604478334685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17844729624324805971112913 13383547218243604478334685)
            ·
              refine ⟨5018830206841351679375507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13383547218243604478334685 5018830206841351679375507)
              ·
                refine ⟨7528245310262027519063261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5018830206841351679375507 7528245310262027519063261)
                ·
                  refine ⟨2823091991348260319648723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7528245310262027519063261 2823091991348260319648723)
                  ·
                    refine ⟨4234637987022390479473085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2823091991348260319648723 4234637987022390479473085)
                    ·
                      refine ⟨1587989245133396429802407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4234637987022390479473085 1587989245133396429802407)
                      ·
                        rfl

theorem cell23_3092598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 3, 1, 3, 1, 3].length) (baseStart_3092598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3092598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3092598 prefixEnd_3092598 := by exact prefixLift 3092598
  have htrace : WordTrace (prefixWord ++ tailWord_3092598) baseStart_3092598 baseEnd_3092598 := by
    simpa [prefixWord, tailWord_3092598, baseEnd_3092598] using wordTrace_append hprefix tailTrace_3092598
  have hstable : (prefixWord ++ tailWord_3092598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3092598).length < 2 ^ (prefixWord ++ tailWord_3092598).sum := by decide
  have hdescent : baseEnd_3092598 < baseStart_3092598 := by decide
  rcases family_descends (prefixWord ++ tailWord_3092598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3092617 : List Nat := [1, 2, 1, 1, 4, 2, 1, 3, 1, 1, 6]
def baseStart_3092617 : Nat := 118140960795 + 3092617 * 2 ^ 59
def prefixEnd_3092617 : Nat := 4983230072969 + 3 ^ 40 * 3092617 * 2
def baseEnd_3092617 : Nat := 1587999001265831855464819

theorem tailTrace_3092617 : CollatzResearch.WordTrace tailWord_3092617 prefixEnd_3092617 1587999001265831855464819 := by
  unfold tailWord_3092617
  simp only [CollatzResearch.WordTrace]
  refine ⟨112797008636984260778396105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75198005757989507185597403 112797008636984260778396105)
  ·
    refine ⟨84597756477738195583797079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112797008636984260778396105 84597756477738195583797079)
    ·
      refine ⟨126896634716607293375695619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84597756477738195583797079 126896634716607293375695619)
      ·
        refine ⟨190344952074910940063543429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126896634716607293375695619 190344952074910940063543429)
        ·
          refine ⟨35689678514045801261914393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 190344952074910940063543429 35689678514045801261914393)
          ·
            refine ⟨26767258885534350946435795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35689678514045801261914393 26767258885534350946435795)
            ·
              refine ⟨40150888328301526419653693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26767258885534350946435795 40150888328301526419653693)
              ·
                refine ⟨15056583123113072407370135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40150888328301526419653693 15056583123113072407370135)
                ·
                  refine ⟨22584874684669608611055203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15056583123113072407370135 22584874684669608611055203)
                  ·
                    refine ⟨33877312027004412916582805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22584874684669608611055203 33877312027004412916582805)
                    ·
                      refine ⟨1587999001265831855464819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33877312027004412916582805 1587999001265831855464819)
                      ·
                        rfl

theorem cell23_3092617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 3, 1, 1, 6].length) (baseStart_3092617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3092617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3092617 prefixEnd_3092617 := by exact prefixLift 3092617
  have htrace : WordTrace (prefixWord ++ tailWord_3092617) baseStart_3092617 baseEnd_3092617 := by
    simpa [prefixWord, tailWord_3092617, baseEnd_3092617] using wordTrace_append hprefix tailTrace_3092617
  have hstable : (prefixWord ++ tailWord_3092617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3092617).length < 2 ^ (prefixWord ++ tailWord_3092617).sum := by decide
  have hdescent : baseEnd_3092617 < baseStart_3092617 := by decide
  rcases family_descends (prefixWord ++ tailWord_3092617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3092624 : List Nat := [2, 1, 1, 1, 1, 1, 7, 1, 3, 2, 3]
def baseStart_3092624 : Nat := 118140960795 + 3092624 * 2 ^ 59
def prefixEnd_3092624 : Nat := 4983230072969 + 3 ^ 40 * 3092624 * 2
def baseEnd_3092624 : Nat := 1588002595630413328077287

theorem tailTrace_3092624 : CollatzResearch.WordTrace tailWord_3092624 prefixEnd_3092624 1588002595630413328077287 := by
  unfold tailWord_3092624
  simp only [CollatzResearch.WordTrace]
  refine ⟨56398631973979450486950463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75198175965305933982600617 56398631973979450486950463)
  ·
    refine ⟨84597947960969175730425695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56398631973979450486950463 84597947960969175730425695)
    ·
      refine ⟨126896921941453763595638543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84597947960969175730425695 126896921941453763595638543)
      ·
        refine ⟨190345382912180645393457815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126896921941453763595638543 190345382912180645393457815)
        ·
          refine ⟨285518074368270968090186723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190345382912180645393457815 285518074368270968090186723)
          ·
            refine ⟨428277111552406452135280085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 285518074368270968090186723 428277111552406452135280085)
            ·
              refine ⟨10037744802009526221920627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 428277111552406452135280085 10037744802009526221920627)
              ·
                refine ⟨15056617203014289332880941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10037744802009526221920627 15056617203014289332880941)
                ·
                  refine ⟨5646231451130358499830353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15056617203014289332880941 5646231451130358499830353)
                  ·
                    refine ⟨4234673588347768874872765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5646231451130358499830353 4234673588347768874872765)
                    ·
                      refine ⟨1588002595630413328077287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4234673588347768874872765 1588002595630413328077287)
                      ·
                        rfl

theorem cell23_3092624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 1, 3, 2, 3].length) (baseStart_3092624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3092624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3092624 prefixEnd_3092624 := by exact prefixLift 3092624
  have htrace : WordTrace (prefixWord ++ tailWord_3092624) baseStart_3092624 baseEnd_3092624 := by
    simpa [prefixWord, tailWord_3092624, baseEnd_3092624] using wordTrace_append hprefix tailTrace_3092624
  have hstable : (prefixWord ++ tailWord_3092624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3092624).length < 2 ^ (prefixWord ++ tailWord_3092624).sum := by decide
  have hdescent : baseEnd_3092624 < baseStart_3092624 := by decide
  rcases family_descends (prefixWord ++ tailWord_3092624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3092641 : List Nat := [1, 2, 3, 3, 1, 4, 1, 1, 1, 1, 5]
def baseStart_3092641 : Nat := 118140960795 + 3092641 * 2 ^ 59
def prefixEnd_3092641 : Nat := 4983230072969 + 3 ^ 40 * 3092641 * 2
def baseEnd_3092641 : Nat := 1588011324801539761564709

theorem tailTrace_3092641 : CollatzResearch.WordTrace tailWord_3092641 prefixEnd_3092641 1588011324801539761564709 := by
  unfold tailWord_3092641
  simp only [CollatzResearch.WordTrace]
  refine ⟨112797883988897312877269777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75198589325931541918179851 112797883988897312877269777)
  ·
    refine ⟨84598412991672984657952333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112797883988897312877269777 84598412991672984657952333)
    ·
      refine ⟨31724404871877369246732125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84598412991672984657952333 31724404871877369246732125)
      ·
        refine ⟨11896651826954013467524547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31724404871877369246732125 11896651826954013467524547)
        ·
          refine ⟨17844977740431020201286821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11896651826954013467524547 17844977740431020201286821)
          ·
            refine ⟨3345933326330816287741279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17844977740431020201286821 3345933326330816287741279)
            ·
              refine ⟨5018899989496224431611919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3345933326330816287741279 5018899989496224431611919)
              ·
                refine ⟨7528349984244336647417879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5018899989496224431611919 7528349984244336647417879)
                ·
                  refine ⟨11292524976366504971126819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7528349984244336647417879 11292524976366504971126819)
                  ·
                    refine ⟨16938787464549757456690229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11292524976366504971126819 16938787464549757456690229)
                    ·
                      refine ⟨1588011324801539761564709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16938787464549757456690229 1588011324801539761564709)
                      ·
                        rfl

theorem cell23_3092641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 1, 1, 1, 1, 5].length) (baseStart_3092641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3092641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3092641 prefixEnd_3092641 := by exact prefixLift 3092641
  have htrace : WordTrace (prefixWord ++ tailWord_3092641) baseStart_3092641 baseEnd_3092641 := by
    simpa [prefixWord, tailWord_3092641, baseEnd_3092641] using wordTrace_append hprefix tailTrace_3092641
  have hstable : (prefixWord ++ tailWord_3092641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3092641).length < 2 ^ (prefixWord ++ tailWord_3092641).sum := by decide
  have hdescent : baseEnd_3092641 < baseStart_3092641 := by decide
  rcases family_descends (prefixWord ++ tailWord_3092641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3092644 : List Nat := [2, 3, 1, 2, 5, 10]
def baseStart_3092644 : Nat := 118140960795 + 3092644 * 2 ^ 59
def prefixEnd_3092644 : Nat := 4983230072969 + 3 ^ 40 * 3092644 * 2
def baseEnd_3092644 : Nat := 6535032367257215019865

theorem tailTrace_3092644 : CollatzResearch.WordTrace tailWord_3092644 prefixEnd_3092644 6535032367257215019865 := by
  unfold tailWord_3092644
  simp only [CollatzResearch.WordTrace]
  refine ⟨56398996703943222194814493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75198662271924296259752657 56398996703943222194814493)
  ·
    refine ⟨21149623763978708323055435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56398996703943222194814493 21149623763978708323055435)
    ·
      refine ⟨31724435645968062484583153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21149623763978708323055435 31724435645968062484583153)
      ·
        refine ⟨23793326734476046863437365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31724435645968062484583153 23793326734476046863437365)
        ·
          refine ⟨2230624381357129393447253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23793326734476046863437365 2230624381357129393447253)
          ·
            refine ⟨6535032367257215019865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2230624381357129393447253 6535032367257215019865)
            ·
              rfl

theorem cell23_3092644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 10].length) (baseStart_3092644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3092644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3092644 prefixEnd_3092644 := by exact prefixLift 3092644
  have htrace : WordTrace (prefixWord ++ tailWord_3092644) baseStart_3092644 baseEnd_3092644 := by
    simpa [prefixWord, tailWord_3092644, baseEnd_3092644] using wordTrace_append hprefix tailTrace_3092644
  have hstable : (prefixWord ++ tailWord_3092644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3092644).length < 2 ^ (prefixWord ++ tailWord_3092644).sum := by decide
  have hdescent : baseEnd_3092644 < baseStart_3092644 := by decide
  rcases family_descends (prefixWord ++ tailWord_3092644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3092687 : List Nat := [1, 1, 2, 1, 1, 3, 3, 2, 1, 8]
def baseStart_3092687 : Nat := 118140960795 + 3092687 * 2 ^ 59
def prefixEnd_3092687 : Nat := 4983230072969 + 3 ^ 40 * 3092687 * 2
def baseEnd_3092687 : Nat := 529344981637215527196499

theorem tailTrace_3092687 : CollatzResearch.WordTrace tailWord_3092687 prefixEnd_3092687 529344981637215527196499 := by
  unfold tailWord_3092687
  simp only [CollatzResearch.WordTrace]
  refine ⟨112799561746730662733444315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75199707831153775155629543 112799561746730662733444315)
  ·
    refine ⟨169199342620095994100166473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112799561746730662733444315 169199342620095994100166473)
    ·
      refine ⟨126899506965071995575124855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169199342620095994100166473 126899506965071995575124855)
      ·
        refine ⟨190349260447607993362687283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126899506965071995575124855 190349260447607993362687283)
        ·
          refine ⟨285523890671411990044030925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190349260447607993362687283 285523890671411990044030925)
          ·
            refine ⟨107071459001779496266511597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 285523890671411990044030925 107071459001779496266511597)
            ·
              refine ⟨40151797125667311099941849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 107071459001779496266511597 40151797125667311099941849)
              ·
                refine ⟨30113847844250483324956387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40151797125667311099941849 30113847844250483324956387)
                ·
                  refine ⟨45170771766375724987434581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30113847844250483324956387 45170771766375724987434581)
                  ·
                    refine ⟨529344981637215527196499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 45170771766375724987434581 529344981637215527196499)
                    ·
                      rfl

theorem cell23_3092687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 2, 1, 8].length) (baseStart_3092687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3092687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3092687 prefixEnd_3092687 := by exact prefixLift 3092687
  have htrace : WordTrace (prefixWord ++ tailWord_3092687) baseStart_3092687 baseEnd_3092687 := by
    simpa [prefixWord, tailWord_3092687, baseEnd_3092687] using wordTrace_append hprefix tailTrace_3092687
  have hstable : (prefixWord ++ tailWord_3092687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3092687).length < 2 ^ (prefixWord ++ tailWord_3092687).sum := by decide
  have hdescent : baseEnd_3092687 < baseStart_3092687 := by decide
  rcases family_descends (prefixWord ++ tailWord_3092687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3092728 : List Nat := [2, 1, 2, 1, 1, 2, 1, 7, 2, 2, 2]
def baseStart_3092728 : Nat := 118140960795 + 3092728 * 2 ^ 59
def prefixEnd_3092728 : Nat := 4983230072969 + 3 ^ 40 * 3092728 * 2
def baseEnd_3092728 : Nat := 1588055997618480921176809

theorem tailTrace_3092728 : CollatzResearch.WordTrace tailWord_3092728 prefixEnd_3092728 1588055997618480921176809 := by
  unfold tailWord_3092728
  simp only [CollatzResearch.WordTrace]
  refine ⟨56400528569791063367843419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75200704759721417823791225 56400528569791063367843419)
  ·
    refine ⟨84600792854686595051765129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56400528569791063367843419 84600792854686595051765129)
    ·
      refine ⟨63450594641014946288823847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84600792854686595051765129 63450594641014946288823847)
      ·
        refine ⟨95175891961522419433235771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63450594641014946288823847 95175891961522419433235771)
        ·
          refine ⟨142763837942283629149853657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95175891961522419433235771 142763837942283629149853657)
          ·
            refine ⟨107072878456712721862390243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142763837942283629149853657 107072878456712721862390243)
            ·
              refine ⟨160609317685069082793585365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107072878456712721862390243 160609317685069082793585365)
              ·
                refine ⟨3764280883243806627974657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 160609317685069082793585365 3764280883243806627974657)
                ·
                  refine ⟨2823210662432854970980993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3764280883243806627974657 2823210662432854970980993)
                  ·
                    refine ⟨2117407996824641228235745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2823210662432854970980993 2117407996824641228235745)
                    ·
                      refine ⟨1588055997618480921176809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2117407996824641228235745 1588055997618480921176809)
                      ·
                        rfl

theorem cell23_3092728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 7, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 7, 2, 2, 2].length) (baseStart_3092728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3092728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3092728 prefixEnd_3092728 := by exact prefixLift 3092728
  have htrace : WordTrace (prefixWord ++ tailWord_3092728) baseStart_3092728 baseEnd_3092728 := by
    simpa [prefixWord, tailWord_3092728, baseEnd_3092728] using wordTrace_append hprefix tailTrace_3092728
  have hstable : (prefixWord ++ tailWord_3092728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3092728).length < 2 ^ (prefixWord ++ tailWord_3092728).sum := by decide
  have hdescent : baseEnd_3092728 < baseStart_3092728 := by decide
  rcases family_descends (prefixWord ++ tailWord_3092728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3092771 : List Nat := [1, 1, 1, 4, 2, 2, 2, 1, 2, 5, 2]
def baseStart_3092771 : Nat := 118140960795 + 3092771 * 2 ^ 59
def prefixEnd_3092771 : Nat := 4983230072969 + 3 ^ 40 * 3092771 * 2
def baseEnd_3092771 : Nat := 1588078077286624252939111

theorem tailTrace_3092771 : CollatzResearch.WordTrace tailWord_3092771 prefixEnd_3092771 1588078077286624252939111 := by
  unfold tailWord_3092771
  simp only [CollatzResearch.WordTrace]
  refine ⟨112802625478426345079502167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75201750318950896719668111 112802625478426345079502167)
  ·
    refine ⟨169203938217639517619253251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112802625478426345079502167 169203938217639517619253251)
    ·
      refine ⟨253805907326459276428879877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169203938217639517619253251 253805907326459276428879877)
      ·
        refine ⟨47588607623711114330414977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 253805907326459276428879877 47588607623711114330414977)
        ·
          refine ⟨35691455717783335747811233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47588607623711114330414977 35691455717783335747811233)
          ·
            refine ⟨26768591788337501810858425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35691455717783335747811233 26768591788337501810858425)
            ·
              refine ⟨20076443841253126358143819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26768591788337501810858425 20076443841253126358143819)
              ·
                refine ⟨30114665761879689537215729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20076443841253126358143819 30114665761879689537215729)
                ·
                  refine ⟨22585999321409767152911797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30114665761879689537215729 22585999321409767152911797)
                  ·
                    refine ⟨2117437436382165670585481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22585999321409767152911797 2117437436382165670585481)
                    ·
                      refine ⟨1588078077286624252939111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2117437436382165670585481 1588078077286624252939111)
                      ·
                        rfl

theorem cell23_3092771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 1, 2, 5, 2].length) (baseStart_3092771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3092771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3092771 prefixEnd_3092771 := by exact prefixLift 3092771
  have htrace : WordTrace (prefixWord ++ tailWord_3092771) baseStart_3092771 baseEnd_3092771 := by
    simpa [prefixWord, tailWord_3092771, baseEnd_3092771] using wordTrace_append hprefix tailTrace_3092771
  have hstable : (prefixWord ++ tailWord_3092771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3092771).length < 2 ^ (prefixWord ++ tailWord_3092771).sum := by decide
  have hdescent : baseEnd_3092771 < baseStart_3092771 := by decide
  rcases family_descends (prefixWord ++ tailWord_3092771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3092784 : List Nat := [2, 1, 1, 1, 2, 2, 2, 4, 1, 3, 4]
def baseStart_3092784 : Nat := 118140960795 + 3092784 * 2 ^ 59
def prefixEnd_3092784 : Nat := 4983230072969 + 3 ^ 40 * 3092784 * 2
def baseEnd_3092784 : Nat := 1588084752535132702076551

theorem tailTrace_3092784 : CollatzResearch.WordTrace tailWord_3092784 prefixEnd_3092784 1588084752535132702076551 := by
  unfold tailWord_3092784
  simp only [CollatzResearch.WordTrace]
  refine ⟨56401549813689624149862703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75202066418252832199816937 56401549813689624149862703)
  ·
    refine ⟨84602324720534436224794055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56401549813689624149862703 84602324720534436224794055)
    ·
      refine ⟨126903487080801654337191083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84602324720534436224794055 126903487080801654337191083)
      ·
        refine ⟨190355230621202481505786625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126903487080801654337191083 190355230621202481505786625)
        ·
          refine ⟨142766422965901861129339969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 190355230621202481505786625 142766422965901861129339969)
          ·
            refine ⟨107074817224426395847004977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142766422965901861129339969 107074817224426395847004977)
            ·
              refine ⟨80306112918319796885253733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107074817224426395847004977 80306112918319796885253733)
              ·
                refine ⟨15057396172184961915985075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 80306112918319796885253733 15057396172184961915985075)
                ·
                  refine ⟨22586094258277442873977613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15057396172184961915985075 22586094258277442873977613)
                  ·
                    refine ⟨8469785346854041077741605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22586094258277442873977613 8469785346854041077741605)
                    ·
                      refine ⟨1588084752535132702076551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8469785346854041077741605 1588084752535132702076551)
                      ·
                        rfl

theorem cell23_3092784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 4, 1, 3, 4].length) (baseStart_3092784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3092784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3092784 prefixEnd_3092784 := by exact prefixLift 3092784
  have htrace : WordTrace (prefixWord ++ tailWord_3092784) baseStart_3092784 baseEnd_3092784 := by
    simpa [prefixWord, tailWord_3092784, baseEnd_3092784] using wordTrace_append hprefix tailTrace_3092784
  have hstable : (prefixWord ++ tailWord_3092784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3092784).length < 2 ^ (prefixWord ++ tailWord_3092784).sum := by decide
  have hdescent : baseEnd_3092784 < baseStart_3092784 := by decide
  rcases family_descends (prefixWord ++ tailWord_3092784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3092798 : List Nat := [4, 2, 1, 2, 1, 3, 2, 1, 2, 5]
def baseStart_3092798 : Nat := 118140960795 + 3092798 * 2 ^ 59
def prefixEnd_3092798 : Nat := 4983230072969 + 3 ^ 40 * 3092798 * 2
def baseEnd_3092798 : Nat := 529363980421431882433829

theorem tailTrace_3092798 : CollatzResearch.WordTrace tailWord_3092798 prefixEnd_3092798 529363980421431882433829 := by
  unfold tailWord_3092798
  simp only [CollatzResearch.WordTrace]
  refine ⟨14100451281166066086341881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75202406832885685793823365 14100451281166066086341881)
  ·
    refine ⟨10575338460874549564756411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14100451281166066086341881 10575338460874549564756411)
    ·
      refine ⟨15863007691311824347134617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10575338460874549564756411 15863007691311824347134617)
      ·
        refine ⟨11897255768483868260350963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15863007691311824347134617 11897255768483868260350963)
        ·
          refine ⟨17845883652725802390526445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11897255768483868260350963 17845883652725802390526445)
          ·
            refine ⟨6692206369772175896447417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17845883652725802390526445 6692206369772175896447417)
            ·
              refine ⟨5019154777329131922335563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6692206369772175896447417 5019154777329131922335563)
              ·
                refine ⟨7528732165993697883503345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5019154777329131922335563 7528732165993697883503345)
                ·
                  refine ⟨5646549124495273412627509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7528732165993697883503345 5646549124495273412627509)
                  ·
                    refine ⟨529363980421431882433829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5646549124495273412627509 529363980421431882433829)
                    ·
                      rfl

theorem cell23_3092798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 2, 1, 2, 5].length) (baseStart_3092798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3092798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3092798 prefixEnd_3092798 := by exact prefixLift 3092798
  have htrace : WordTrace (prefixWord ++ tailWord_3092798) baseStart_3092798 baseEnd_3092798 := by
    simpa [prefixWord, tailWord_3092798, baseEnd_3092798] using wordTrace_append hprefix tailTrace_3092798
  have hstable : (prefixWord ++ tailWord_3092798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3092798).length < 2 ^ (prefixWord ++ tailWord_3092798).sum := by decide
  have hdescent : baseEnd_3092798 < baseStart_3092798 := by decide
  rcases family_descends (prefixWord ++ tailWord_3092798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3092864 : List Nat := [2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 5]
def baseStart_3092864 : Nat := 118140960795 + 3092864 * 2 ^ 59
def prefixEnd_3092864 : Nat := 4983230072969 + 3 ^ 40 * 3092864 * 2
def baseEnd_3092864 : Nat := 1588125830987492389076183

theorem tailTrace_3092864 : CollatzResearch.WordTrace tailWord_3092864 prefixEnd_3092864 1588125830987492389076183 := by
  unfold tailWord_3092864
  simp only [CollatzResearch.WordTrace]
  refine ⟨56403008733544710981318823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75204011644726281308425097 56403008733544710981318823)
  ·
    refine ⟨84604513100317066471978235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56403008733544710981318823 84604513100317066471978235)
    ·
      refine ⟨126906769650475599707967353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84604513100317066471978235 126906769650475599707967353)
      ·
        refine ⟨95180077237856699780975515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126906769650475599707967353 95180077237856699780975515)
        ·
          refine ⟨142770115856785049671463273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95180077237856699780975515 142770115856785049671463273)
          ·
            refine ⟨107077586892588787253597455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142770115856785049671463273 107077586892588787253597455)
            ·
              refine ⟨160616380338883180880396183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107077586892588787253597455 160616380338883180880396183)
              ·
                refine ⟨240924570508324771320594275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 160616380338883180880396183 240924570508324771320594275)
                ·
                  refine ⟨361386855762487156980891413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 240924570508324771320594275 361386855762487156980891413)
                  ·
                    refine ⟨16940008863866585483479285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 361386855762487156980891413 16940008863866585483479285)
                    ·
                      refine ⟨1588125830987492389076183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16940008863866585483479285 1588125830987492389076183)
                      ·
                        rfl

theorem cell23_3092864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 5].length) (baseStart_3092864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3092864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3092864 prefixEnd_3092864 := by exact prefixLift 3092864
  have htrace : WordTrace (prefixWord ++ tailWord_3092864) baseStart_3092864 baseEnd_3092864 := by
    simpa [prefixWord, tailWord_3092864, baseEnd_3092864] using wordTrace_append hprefix tailTrace_3092864
  have hstable : (prefixWord ++ tailWord_3092864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3092864).length < 2 ^ (prefixWord ++ tailWord_3092864).sum := by decide
  have hdescent : baseEnd_3092864 < baseStart_3092864 := by decide
  rcases family_descends (prefixWord ++ tailWord_3092864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3092868 : List Nat := [2, 3, 2, 1, 1, 2, 1, 2, 5, 1, 3]
def baseStart_3092868 : Nat := 118140960795 + 3092868 * 2 ^ 59
def prefixEnd_3092868 : Nat := 4983230072969 + 3 ^ 40 * 3092868 * 2
def baseEnd_3092868 : Nat := 1588127884910110373426165

theorem tailTrace_3092868 : CollatzResearch.WordTrace tailWord_3092868 prefixEnd_3092868 1588127884910110373426165 := by
  unfold tailWord_3092868
  simp only [CollatzResearch.WordTrace]
  refine ⟨56403081679537465322891629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75204108906049953763855505 56403081679537465322891629)
  ·
    refine ⟨21151155629826549496084361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56403081679537465322891629 21151155629826549496084361)
    ·
      refine ⟨15863366722369912122063271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21151155629826549496084361 15863366722369912122063271)
      ·
        refine ⟨23795050083554868183094907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15863366722369912122063271 23795050083554868183094907)
        ·
          refine ⟨35692575125332302274642361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23795050083554868183094907 35692575125332302274642361)
          ·
            refine ⟨26769431343999226705981771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35692575125332302274642361 26769431343999226705981771)
            ·
              refine ⟨40154147015998840058972657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26769431343999226705981771 40154147015998840058972657)
              ·
                refine ⟨30115610261999130044229493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40154147015998840058972657 30115610261999130044229493)
                ·
                  refine ⟨2823338462062418441646515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30115610261999130044229493 2823338462062418441646515)
                  ·
                    refine ⟨4235007693093627662469773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2823338462062418441646515 4235007693093627662469773)
                    ·
                      refine ⟨1588127884910110373426165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4235007693093627662469773 1588127884910110373426165)
                      ·
                        rfl

theorem cell23_3092868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 2, 5, 1, 3].length) (baseStart_3092868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3092868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3092868 prefixEnd_3092868 := by exact prefixLift 3092868
  have htrace : WordTrace (prefixWord ++ tailWord_3092868) baseStart_3092868 baseEnd_3092868 := by
    simpa [prefixWord, tailWord_3092868, baseEnd_3092868] using wordTrace_append hprefix tailTrace_3092868
  have hstable : (prefixWord ++ tailWord_3092868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3092868).length < 2 ^ (prefixWord ++ tailWord_3092868).sum := by decide
  have hdescent : baseEnd_3092868 < baseStart_3092868 := by decide
  rcases family_descends (prefixWord ++ tailWord_3092868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3092948 : List Nat := [2, 4, 1, 2, 2, 2, 2, 8]
def baseStart_3092948 : Nat := 118140960795 + 3092948 * 2 ^ 59
def prefixEnd_3092948 : Nat := 4983230072969 + 3 ^ 40 * 3092948 * 2
def baseEnd_3092948 : Nat := 58821072717128520756511

theorem tailTrace_3092948 : CollatzResearch.WordTrace tailWord_3092948 prefixEnd_3092948 58821072717128520756511 := by
  unfold tailWord_3092948
  simp only [CollatzResearch.WordTrace]
  refine ⟨56404540599392552154347749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75206054132523402872463665 56404540599392552154347749)
  ·
    refine ⟨10575851362386103528940203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56404540599392552154347749 10575851362386103528940203)
    ·
      refine ⟨15863777043579155293410305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10575851362386103528940203 15863777043579155293410305)
      ·
        refine ⟨11897832782684366470057729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15863777043579155293410305 11897832782684366470057729)
        ·
          refine ⟨8923374587013274852543297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11897832782684366470057729 8923374587013274852543297)
          ·
            refine ⟨6692530940259956139407473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8923374587013274852543297 6692530940259956139407473)
            ·
              refine ⟨5019398205194967104555605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6692530940259956139407473 5019398205194967104555605)
              ·
                refine ⟨58821072717128520756511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5019398205194967104555605 58821072717128520756511)
                ·
                  rfl

theorem cell23_3092948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 2, 8].length) (baseStart_3092948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3092948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3092948 prefixEnd_3092948 := by exact prefixLift 3092948
  have htrace : WordTrace (prefixWord ++ tailWord_3092948) baseStart_3092948 baseEnd_3092948 := by
    simpa [prefixWord, tailWord_3092948, baseEnd_3092948] using wordTrace_append hprefix tailTrace_3092948
  have hstable : (prefixWord ++ tailWord_3092948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3092948).length < 2 ^ (prefixWord ++ tailWord_3092948).sum := by decide
  have hdescent : baseEnd_3092948 < baseStart_3092948 := by decide
  rcases family_descends (prefixWord ++ tailWord_3092948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3092985 : List Nat := [1, 2, 1, 3, 1, 2, 2, 5, 1, 3, 2]
def baseStart_3092985 : Nat := 118140960795 + 3092985 * 2 ^ 59
def prefixEnd_3092985 : Nat := 4983230072969 + 3 ^ 40 * 3092985 * 2
def baseEnd_3092985 : Nat := 1588187962146686415663127

theorem tailTrace_3092985 : CollatzResearch.WordTrace tailWord_3092985 prefixEnd_3092985 1588187962146686415663127 := by
  unfold tailWord_3092985
  simp only [CollatzResearch.WordTrace]
  refine ⟨112810430699651059627792409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75206953799767373085194939 112810430699651059627792409)
  ·
    refine ⟨84607823024738294720844307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112810430699651059627792409 84607823024738294720844307)
    ·
      refine ⟨126911734537107442081266461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84607823024738294720844307 126911734537107442081266461)
      ·
        refine ⟨47591900451415290780474923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126911734537107442081266461 47591900451415290780474923)
        ·
          refine ⟨71387850677122936170712385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47591900451415290780474923 71387850677122936170712385)
          ·
            refine ⟨53540888007842202128034289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71387850677122936170712385 53540888007842202128034289)
            ·
              refine ⟨40155666005881651596025717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53540888007842202128034289 40155666005881651596025717)
              ·
                refine ⟨3764593688051404837127411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40155666005881651596025717 3764593688051404837127411)
                ·
                  refine ⟨5646890532077107255691117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3764593688051404837127411 5646890532077107255691117)
                  ·
                    refine ⟨2117583949528915220884169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5646890532077107255691117 2117583949528915220884169)
                    ·
                      refine ⟨1588187962146686415663127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2117583949528915220884169 1588187962146686415663127)
                      ·
                        rfl

theorem cell23_3092985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 5, 1, 3, 2].length) (baseStart_3092985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3092985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3092985 prefixEnd_3092985 := by exact prefixLift 3092985
  have htrace : WordTrace (prefixWord ++ tailWord_3092985) baseStart_3092985 baseEnd_3092985 := by
    simpa [prefixWord, tailWord_3092985, baseEnd_3092985] using wordTrace_append hprefix tailTrace_3092985
  have hstable : (prefixWord ++ tailWord_3092985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3092985).length < 2 ^ (prefixWord ++ tailWord_3092985).sum := by decide
  have hdescent : baseEnd_3092985 < baseStart_3092985 := by decide
  rcases family_descends (prefixWord ++ tailWord_3092985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3092991 : List Nat := [1, 1, 2, 2, 1, 2, 4, 2, 2, 6]
def baseStart_3092991 : Nat := 118140960795 + 3092991 * 2 ^ 59
def prefixEnd_3092991 : Nat := 4983230072969 + 3 ^ 40 * 3092991 * 2
def baseEnd_3092991 : Nat := 529397014343537797396033

theorem tailTrace_3092991 : CollatzResearch.WordTrace tailWord_3092991 prefixEnd_3092991 529397014343537797396033 := by
  unfold tailWord_3092991
  simp only [CollatzResearch.WordTrace]
  refine ⟨112810649537629322652510827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75207099691752881768340551 112810649537629322652510827)
  ·
    refine ⟨169215974306443983978766241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112810649537629322652510827 169215974306443983978766241)
    ·
      refine ⟨126911980729832987984074681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169215974306443983978766241 126911980729832987984074681)
      ·
        refine ⟨95183985547374740988056011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126911980729832987984074681 95183985547374740988056011)
        ·
          refine ⟨142775978321062111482084017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95183985547374740988056011 142775978321062111482084017)
          ·
            refine ⟨107081983740796583611563013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142775978321062111482084017 107081983740796583611563013)
            ·
              refine ⟨20077871951399359427168065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 107081983740796583611563013 20077871951399359427168065)
              ·
                refine ⟨15058403963549519570376049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20077871951399359427168065 15058403963549519570376049)
                ·
                  refine ⟨11293802972662139677782037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15058403963549519570376049 11293802972662139677782037)
                  ·
                    refine ⟨529397014343537797396033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11293802972662139677782037 529397014343537797396033)
                    ·
                      rfl

theorem cell23_3092991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 2, 2, 6].length) (baseStart_3092991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3092991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3092991 prefixEnd_3092991 := by exact prefixLift 3092991
  have htrace : WordTrace (prefixWord ++ tailWord_3092991) baseStart_3092991 baseEnd_3092991 := by
    simpa [prefixWord, tailWord_3092991, baseEnd_3092991] using wordTrace_append hprefix tailTrace_3092991
  have hstable : (prefixWord ++ tailWord_3092991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3092991).length < 2 ^ (prefixWord ++ tailWord_3092991).sum := by decide
  have hdescent : baseEnd_3092991 < baseStart_3092991 := by decide
  rcases family_descends (prefixWord ++ tailWord_3092991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3093001 : List Nat := [1, 2, 1, 1, 3, 1, 2, 2, 4, 1, 5]
def baseStart_3093001 : Nat := 118140960795 + 3093001 * 2 ^ 59
def prefixEnd_3093001 : Nat := 4983230072969 + 3 ^ 40 * 3093001 * 2
def baseEnd_3093001 : Nat := 1588196177837158353063053

theorem tailTrace_3093001 : CollatzResearch.WordTrace tailWord_3093001 prefixEnd_3093001 1588196177837158353063053 := by
  unfold tailWord_3093001
  simp only [CollatzResearch.WordTrace]
  refine ⟨112811014267593094360374857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75207342845062062906916571 112811014267593094360374857)
  ·
    refine ⟨84608260700694820770281143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112811014267593094360374857 84608260700694820770281143)
    ·
      refine ⟨126912391051042231155421715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84608260700694820770281143 126912391051042231155421715)
      ·
        refine ⟨190368586576563346733132573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126912391051042231155421715 190368586576563346733132573)
        ·
          refine ⟨71388219966211255024924715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 190368586576563346733132573 71388219966211255024924715)
          ·
            refine ⟨107082329949316882537387073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71388219966211255024924715 107082329949316882537387073)
            ·
              refine ⟨80311747461987661903040305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107082329949316882537387073 80311747461987661903040305)
              ·
                refine ⟨60233810596490746427280229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80311747461987661903040305 60233810596490746427280229)
                ·
                  refine ⟨11293839486842014955115043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60233810596490746427280229 11293839486842014955115043)
                  ·
                    refine ⟨16940759230263022432672565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11293839486842014955115043 16940759230263022432672565)
                    ·
                      refine ⟨1588196177837158353063053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16940759230263022432672565 1588196177837158353063053)
                      ·
                        rfl

theorem cell23_3093001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 2, 4, 1, 5].length) (baseStart_3093001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3093001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3093001 prefixEnd_3093001 := by exact prefixLift 3093001
  have htrace : WordTrace (prefixWord ++ tailWord_3093001) baseStart_3093001 baseEnd_3093001 := by
    simpa [prefixWord, tailWord_3093001, baseEnd_3093001] using wordTrace_append hprefix tailTrace_3093001
  have hstable : (prefixWord ++ tailWord_3093001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3093001).length < 2 ^ (prefixWord ++ tailWord_3093001).sum := by decide
  have hdescent : baseEnd_3093001 < baseStart_3093001 := by decide
  rcases family_descends (prefixWord ++ tailWord_3093001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3093032 : List Nat := [2, 1, 5, 2, 1, 1, 2, 2, 1, 4, 2]
def baseStart_3093032 : Nat := 118140960795 + 3093032 * 2 ^ 59
def prefixEnd_3093032 : Nat := 4983230072969 + 3 ^ 40 * 3093032 * 2
def baseEnd_3093032 : Nat := 1588212095737447731775411

theorem tailTrace_3093032 : CollatzResearch.WordTrace tailWord_3093032 prefixEnd_3093032 1588212095737447731775411 := by
  unfold tailWord_3093032
  simp only [CollatzResearch.WordTrace]
  refine ⟨56406072465240393327376675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75208096620320524436502233 56406072465240393327376675)
  ·
    refine ⟨84609108697860589991065013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56406072465240393327376675 84609108697860589991065013)
    ·
      refine ⟨7932103940424430311662345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 84609108697860589991065013 7932103940424430311662345)
      ·
        refine ⟨5949077955318322733746759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7932103940424430311662345 5949077955318322733746759)
        ·
          refine ⟨8923616932977484100620139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5949077955318322733746759 8923616932977484100620139)
          ·
            refine ⟨13385425399466226150930209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8923616932977484100620139 13385425399466226150930209)
            ·
              refine ⟨10039069049599669613197657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13385425399466226150930209 10039069049599669613197657)
              ·
                refine ⟨7529301787199752209898243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10039069049599669613197657 7529301787199752209898243)
                ·
                  refine ⟨11293952680799628314847365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7529301787199752209898243 11293952680799628314847365)
                  ·
                    refine ⟨2117616127649930309033881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11293952680799628314847365 2117616127649930309033881)
                    ·
                      refine ⟨1588212095737447731775411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2117616127649930309033881 1588212095737447731775411)
                      ·
                        rfl

theorem cell23_3093032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 2, 1, 4, 2].length) (baseStart_3093032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3093032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3093032 prefixEnd_3093032 := by exact prefixLift 3093032
  have htrace : WordTrace (prefixWord ++ tailWord_3093032) baseStart_3093032 baseEnd_3093032 := by
    simpa [prefixWord, tailWord_3093032, baseEnd_3093032] using wordTrace_append hprefix tailTrace_3093032
  have hstable : (prefixWord ++ tailWord_3093032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3093032).length < 2 ^ (prefixWord ++ tailWord_3093032).sum := by decide
  have hdescent : baseEnd_3093032 < baseStart_3093032 := by decide
  rcases family_descends (prefixWord ++ tailWord_3093032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3093048 : List Nat := [2, 1, 2, 1, 4, 1, 1, 1, 4, 3, 3]
def baseStart_3093048 : Nat := 118140960795 + 3093048 * 2 ^ 59
def prefixEnd_3093048 : Nat := 4983230072969 + 3 ^ 40 * 3093048 * 2
def baseEnd_3093048 : Nat := 1588220311427919669175337

theorem tailTrace_3093048 : CollatzResearch.WordTrace tailWord_3093048 prefixEnd_3093048 1588220311427919669175337 := by
  unfold tailWord_3093048
  simp only [CollatzResearch.WordTrace]
  refine ⟨56406364249211410693667899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75208485665615214258223865 56406364249211410693667899)
  ·
    refine ⟨84609546373817116040501849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56406364249211410693667899 84609546373817116040501849)
    ·
      refine ⟨63457159780362837030376387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84609546373817116040501849 63457159780362837030376387)
      ·
        refine ⟨95185739670544255545564581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63457159780362837030376387 95185739670544255545564581)
        ·
          refine ⟨17847326188227047914793359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 95185739670544255545564581 17847326188227047914793359)
          ·
            refine ⟨26770989282340571872190039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17847326188227047914793359 26770989282340571872190039)
            ·
              refine ⟨40156483923510857808285059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26770989282340571872190039 40156483923510857808285059)
              ·
                refine ⟨60234725885266286712427589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40156483923510857808285059 60234725885266286712427589)
                ·
                  refine ⟨11294011103487428758580173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60234725885266286712427589 11294011103487428758580173)
                  ·
                    refine ⟨4235254163807785784467565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11294011103487428758580173 4235254163807785784467565)
                    ·
                      refine ⟨1588220311427919669175337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4235254163807785784467565 1588220311427919669175337)
                      ·
                        rfl

theorem cell23_3093048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 1, 4, 3, 3].length) (baseStart_3093048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3093048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3093048 prefixEnd_3093048 := by exact prefixLift 3093048
  have htrace : WordTrace (prefixWord ++ tailWord_3093048) baseStart_3093048 baseEnd_3093048 := by
    simpa [prefixWord, tailWord_3093048, baseEnd_3093048] using wordTrace_append hprefix tailTrace_3093048
  have hstable : (prefixWord ++ tailWord_3093048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3093048).length < 2 ^ (prefixWord ++ tailWord_3093048).sum := by decide
  have hdescent : baseEnd_3093048 < baseStart_3093048 := by decide
  rcases family_descends (prefixWord ++ tailWord_3093048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3093062 : List Nat := [6, 1, 1, 1, 2, 1, 2, 1, 2, 2, 4]
def baseStart_3093062 : Nat := 118140960795 + 3093062 * 2 ^ 59
def prefixEnd_3093062 : Nat := 4983230072969 + 3 ^ 40 * 3093062 * 2
def baseEnd_3093062 : Nat := 1588227500157082614400273

theorem tailTrace_3093062 : CollatzResearch.WordTrace tailWord_3093062 prefixEnd_3093062 1588227500157082614400273 := by
  unfold tailWord_3093062
  simp only [CollatzResearch.WordTrace]
  refine ⟨3525413722511628180573295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 75208826080248067852230293 3525413722511628180573295)
  ·
    refine ⟨5288120583767442270859943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3525413722511628180573295 5288120583767442270859943)
    ·
      refine ⟨7932180875651163406289915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5288120583767442270859943 7932180875651163406289915)
      ·
        refine ⟨11898271313476745109434873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7932180875651163406289915 11898271313476745109434873)
        ·
          refine ⟨8923703485107558832076155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11898271313476745109434873 8923703485107558832076155)
          ·
            refine ⟨13385555227661338248114233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8923703485107558832076155 13385555227661338248114233)
            ·
              refine ⟨10039166420746003686085675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13385555227661338248114233 10039166420746003686085675)
              ·
                refine ⟨15058749631119005529128513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10039166420746003686085675 15058749631119005529128513)
                ·
                  refine ⟨11294062223339254146846385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15058749631119005529128513 11294062223339254146846385)
                  ·
                    refine ⟨8470546667504440610134789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11294062223339254146846385 8470546667504440610134789)
                    ·
                      refine ⟨1588227500157082614400273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8470546667504440610134789 1588227500157082614400273)
                      ·
                        rfl

theorem cell23_3093062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 1, 2, 2, 4].length) (baseStart_3093062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3093062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3093062 prefixEnd_3093062 := by exact prefixLift 3093062
  have htrace : WordTrace (prefixWord ++ tailWord_3093062) baseStart_3093062 baseEnd_3093062 := by
    simpa [prefixWord, tailWord_3093062, baseEnd_3093062] using wordTrace_append hprefix tailTrace_3093062
  have hstable : (prefixWord ++ tailWord_3093062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3093062).length < 2 ^ (prefixWord ++ tailWord_3093062).sum := by decide
  have hdescent : baseEnd_3093062 < baseStart_3093062 := by decide
  rcases family_descends (prefixWord ++ tailWord_3093062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3093088 : List Nat := [2, 1, 1, 3, 2, 1, 4, 1, 1, 3, 4]
def baseStart_3093088 : Nat := 118140960795 + 3093088 * 2 ^ 59
def prefixEnd_3093088 : Nat := 4983230072969 + 3 ^ 40 * 3093088 * 2
def baseEnd_3093088 : Nat := 1588240850654099512675153

theorem tailTrace_3093088 : CollatzResearch.WordTrace tailWord_3093088 prefixEnd_3093088 1588240850654099512675153 := by
  unfold tailWord_3093088
  simp only [CollatzResearch.WordTrace]
  refine ⟨56407093709138954109395959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75209458278851938812527945 56407093709138954109395959)
  ·
    refine ⟨84610640563708431164093939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56407093709138954109395959 84610640563708431164093939)
    ·
      refine ⟨126915960845562646746140909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84610640563708431164093939 126915960845562646746140909)
      ·
        refine ⟨47593485317085992529802841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126915960845562646746140909 47593485317085992529802841)
        ·
          refine ⟨35695113987814494397352131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47593485317085992529802841 35695113987814494397352131)
          ·
            refine ⟨53542670981721741596028197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35695113987814494397352131 53542670981721741596028197)
            ·
              refine ⟨10039250809072826549255287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53542670981721741596028197 10039250809072826549255287)
              ·
                refine ⟨15058876213609239823882931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10039250809072826549255287 15058876213609239823882931)
                ·
                  refine ⟨22588314320413859735824397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15058876213609239823882931 22588314320413859735824397)
                  ·
                    refine ⟨8470617870155197400934149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22588314320413859735824397 8470617870155197400934149)
                    ·
                      refine ⟨1588240850654099512675153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8470617870155197400934149 1588240850654099512675153)
                      ·
                        rfl

theorem cell23_3093088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 1, 1, 3, 4].length) (baseStart_3093088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3093088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3093088 prefixEnd_3093088 := by exact prefixLift 3093088
  have htrace : WordTrace (prefixWord ++ tailWord_3093088) baseStart_3093088 baseEnd_3093088 := by
    simpa [prefixWord, tailWord_3093088, baseEnd_3093088] using wordTrace_append hprefix tailTrace_3093088
  have hstable : (prefixWord ++ tailWord_3093088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3093088).length < 2 ^ (prefixWord ++ tailWord_3093088).sum := by decide
  have hdescent : baseEnd_3093088 < baseStart_3093088 := by decide
  rcases family_descends (prefixWord ++ tailWord_3093088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3093155 : List Nat := [1, 1, 1, 4, 1, 1, 2, 1, 7, 1, 3]
def baseStart_3093155 : Nat := 118140960795 + 3093155 * 2 ^ 59
def prefixEnd_3093155 : Nat := 4983230072969 + 3 ^ 40 * 3093155 * 2
def baseEnd_3093155 : Nat := 1588275253857950750537345

theorem tailTrace_3093155 : CollatzResearch.WordTrace tailWord_3093155 prefixEnd_3093155 1588275253857950750537345 := by
  unfold tailWord_3093155
  simp only [CollatzResearch.WordTrace]
  refine ⟨112816631109035178661480919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75211087406023452440987279 112816631109035178661480919)
  ·
    refine ⟨169224946663552767992221379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112816631109035178661480919 169224946663552767992221379)
    ·
      refine ⟨253837419995329151988332069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169224946663552767992221379 253837419995329151988332069)
      ·
        refine ⟨47594516249124215997812263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 253837419995329151988332069 47594516249124215997812263)
        ·
          refine ⟨71391774373686323996718395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47594516249124215997812263 71391774373686323996718395)
          ·
            refine ⟨107087661560529485995077593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71391774373686323996718395 107087661560529485995077593)
            ·
              refine ⟨80315746170397114496308195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107087661560529485995077593 80315746170397114496308195)
              ·
                refine ⟨120473619255595671744462293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80315746170397114496308195 120473619255595671744462293)
                ·
                  refine ⟨2823600451303023556510835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 120473619255595671744462293 2823600451303023556510835)
                  ·
                    refine ⟨4235400676954535334766253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2823600451303023556510835 4235400676954535334766253)
                    ·
                      refine ⟨1588275253857950750537345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4235400676954535334766253 1588275253857950750537345)
                      ·
                        rfl

theorem cell23_3093155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 1, 7, 1, 3].length) (baseStart_3093155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3093155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3093155 prefixEnd_3093155 := by exact prefixLift 3093155
  have htrace : WordTrace (prefixWord ++ tailWord_3093155) baseStart_3093155 baseEnd_3093155 := by
    simpa [prefixWord, tailWord_3093155, baseEnd_3093155] using wordTrace_append hprefix tailTrace_3093155
  have hstable : (prefixWord ++ tailWord_3093155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3093155).length < 2 ^ (prefixWord ++ tailWord_3093155).sum := by decide
  have hdescent : baseEnd_3093155 < baseStart_3093155 := by decide
  rcases family_descends (prefixWord ++ tailWord_3093155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3093166 : List Nat := [4, 1, 4, 1, 1, 2, 1, 4, 1, 4]
def baseStart_3093166 : Nat := 118140960795 + 3093166 * 2 ^ 59
def prefixEnd_3093166 : Nat := 4983230072969 + 3 ^ 40 * 3093166 * 2
def baseEnd_3093166 : Nat := 529426967381716735833265

theorem tailTrace_3093166 : CollatzResearch.WordTrace tailWord_3093166 prefixEnd_3093166 529426967381716735833265 := by
  unfold tailWord_3093166
  simp only [CollatzResearch.WordTrace]
  refine ⟨14102129038999415942516419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75211354874663551693420901 14102129038999415942516419)
  ·
    refine ⟨21153193558499123913774629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14102129038999415942516419 21153193558499123913774629)
    ·
      refine ⟨3966223792218585733832743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21153193558499123913774629 3966223792218585733832743)
      ·
        refine ⟨5949335688327878600749115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3966223792218585733832743 5949335688327878600749115)
        ·
          refine ⟨8924003532491817901123673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5949335688327878600749115 8924003532491817901123673)
          ·
            refine ⟨6693002649368863425842755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8924003532491817901123673 6693002649368863425842755)
            ·
              refine ⟨10039503974053295138764133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6693002649368863425842755 10039503974053295138764133)
              ·
                refine ⟨1882406995134992838518275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10039503974053295138764133 1882406995134992838518275)
                ·
                  refine ⟨2823610492702489257777413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1882406995134992838518275 2823610492702489257777413)
                  ·
                    refine ⟨529426967381716735833265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2823610492702489257777413 529426967381716735833265)
                    ·
                      rfl

theorem cell23_3093166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 4, 1, 4].length) (baseStart_3093166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3093166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3093166 prefixEnd_3093166 := by exact prefixLift 3093166
  have htrace : WordTrace (prefixWord ++ tailWord_3093166) baseStart_3093166 baseEnd_3093166 := by
    simpa [prefixWord, tailWord_3093166, baseEnd_3093166] using wordTrace_append hprefix tailTrace_3093166
  have hstable : (prefixWord ++ tailWord_3093166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3093166).length < 2 ^ (prefixWord ++ tailWord_3093166).sum := by decide
  have hdescent : baseEnd_3093166 < baseStart_3093166 := by decide
  rcases family_descends (prefixWord ++ tailWord_3093166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3093182 : List Nat := [4, 2, 1, 1, 2, 1, 2, 2, 1, 5, 2]
def baseStart_3093182 : Nat := 118140960795 + 3093182 * 2 ^ 59
def prefixEnd_3093182 : Nat := 4983230072969 + 3 ^ 40 * 3093182 * 2
def baseEnd_3093182 : Nat := 1588289117835622144899721

theorem tailTrace_3093182 : CollatzResearch.WordTrace tailWord_3093182 prefixEnd_3093182 1588289117835622144899721 := by
  unfold tailWord_3093182
  simp only [CollatzResearch.WordTrace]
  refine ⟨14102201984992170284089225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75211743919958241515142533 14102201984992170284089225)
  ·
    refine ⟨10576651488744127713066919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14102201984992170284089225 10576651488744127713066919)
    ·
      refine ⟨15864977233116191569600379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10576651488744127713066919 15864977233116191569600379)
      ·
        refine ⟨23797465849674287354400569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15864977233116191569600379 23797465849674287354400569)
        ·
          refine ⟨17848099387255715515800427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23797465849674287354400569 17848099387255715515800427)
          ·
            refine ⟨26772149080883573273700641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17848099387255715515800427 26772149080883573273700641)
            ·
              refine ⟨20079111810662679955275481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26772149080883573273700641 20079111810662679955275481)
              ·
                refine ⟨15059333857997009966456611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20079111810662679955275481 15059333857997009966456611)
                ·
                  refine ⟨22589000786995514949684917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15059333857997009966456611 22589000786995514949684917)
                  ·
                    refine ⟨2117718823780829526532961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22589000786995514949684917 2117718823780829526532961)
                    ·
                      refine ⟨1588289117835622144899721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2117718823780829526532961 1588289117835622144899721)
                      ·
                        rfl

theorem cell23_3093182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 2, 1, 5, 2].length) (baseStart_3093182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3093182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3093182 prefixEnd_3093182 := by exact prefixLift 3093182
  have htrace : WordTrace (prefixWord ++ tailWord_3093182) baseStart_3093182 baseEnd_3093182 := by
    simpa [prefixWord, tailWord_3093182, baseEnd_3093182] using wordTrace_append hprefix tailTrace_3093182
  have hstable : (prefixWord ++ tailWord_3093182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3093182).length < 2 ^ (prefixWord ++ tailWord_3093182).sum := by decide
  have hdescent : baseEnd_3093182 < baseStart_3093182 := by decide
  rcases family_descends (prefixWord ++ tailWord_3093182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3093228 : List Nat := [2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 7]
def baseStart_3093228 : Nat := 118140960795 + 3093228 * 2 ^ 59
def prefixEnd_3093228 : Nat := 4983230072969 + 3 ^ 40 * 3093228 * 2
def baseEnd_3093228 : Nat := 1588312737945728964924509

theorem tailTrace_3093228 : CollatzResearch.WordTrace tailWord_3093228 prefixEnd_3093228 1588312737945728964924509 := by
  unfold tailWord_3093228
  simp only [CollatzResearch.WordTrace]
  refine ⟨56409646818885356064444169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75212862425180474752592225 56409646818885356064444169)
  ·
    refine ⟨42307235114164017048333127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56409646818885356064444169 42307235114164017048333127)
    ·
      refine ⟨63460852671246025572499691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42307235114164017048333127 63460852671246025572499691)
      ·
        refine ⟨95191279006869038358749537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63460852671246025572499691 95191279006869038358749537)
        ·
          refine ⟨71393459255151778769062153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95191279006869038358749537 71393459255151778769062153)
          ·
            refine ⟨53545094441363834076796615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71393459255151778769062153 53545094441363834076796615)
            ·
              refine ⟨80317641662045751115194923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53545094441363834076796615 80317641662045751115194923)
              ·
                refine ⟨120476462493068626672792385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80317641662045751115194923 120476462493068626672792385)
                ·
                  refine ⟨90357346869801470004594289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 120476462493068626672792385 90357346869801470004594289)
                  ·
                    refine ⟨67768010152351102503445717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 90357346869801470004594289 67768010152351102503445717)
                    ·
                      refine ⟨1588312737945728964924509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 67768010152351102503445717 1588312737945728964924509)
                      ·
                        rfl

theorem cell23_3093228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 7].length) (baseStart_3093228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3093228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3093228 prefixEnd_3093228 := by exact prefixLift 3093228
  have htrace : WordTrace (prefixWord ++ tailWord_3093228) baseStart_3093228 baseEnd_3093228 := by
    simpa [prefixWord, tailWord_3093228, baseEnd_3093228] using wordTrace_append hprefix tailTrace_3093228
  have hstable : (prefixWord ++ tailWord_3093228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3093228).length < 2 ^ (prefixWord ++ tailWord_3093228).sum := by decide
  have hdescent : baseEnd_3093228 < baseStart_3093228 := by decide
  rcases family_descends (prefixWord ++ tailWord_3093228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3093246 : List Nat := [4, 2, 2, 1, 2, 1, 2, 2, 3, 2, 2]
def baseStart_3093246 : Nat := 118140960795 + 3093246 * 2 ^ 59
def prefixEnd_3093246 : Nat := 4983230072969 + 3 ^ 40 * 3093246 * 2
def baseEnd_3093246 : Nat := 1588321980597509894499427

theorem tailTrace_3093246 : CollatzResearch.WordTrace tailWord_3093246 prefixEnd_3093246 1588321980597509894499427 := by
  unfold tailWord_3093246
  simp only [CollatzResearch.WordTrace]
  refine ⟨14102493768963187650380449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75213300101137000802029061 14102493768963187650380449)
  ·
    refine ⟨10576870326722390737785337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14102493768963187650380449 10576870326722390737785337)
    ·
      refine ⟨7932652745041793053339003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10576870326722390737785337 7932652745041793053339003)
      ·
        refine ⟨11898979117562689580008505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7932652745041793053339003 11898979117562689580008505)
        ·
          refine ⟨8924234338172017185006379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11898979117562689580008505 8924234338172017185006379)
          ·
            refine ⟨13386351507258025777509569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8924234338172017185006379 13386351507258025777509569)
            ·
              refine ⟨10039763630443519333132177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13386351507258025777509569 10039763630443519333132177)
              ·
                refine ⟨7529822722832639499849133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10039763630443519333132177 7529822722832639499849133)
                ·
                  refine ⟨2823683521062239812443425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7529822722832639499849133 2823683521062239812443425)
                  ·
                    refine ⟨2117762640796679859332569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2823683521062239812443425 2117762640796679859332569)
                    ·
                      refine ⟨1588321980597509894499427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2117762640796679859332569 1588321980597509894499427)
                      ·
                        rfl

theorem cell23_3093246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 2, 3, 2, 2].length) (baseStart_3093246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3093246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3093246 prefixEnd_3093246 := by exact prefixLift 3093246
  have htrace : WordTrace (prefixWord ++ tailWord_3093246) baseStart_3093246 baseEnd_3093246 := by
    simpa [prefixWord, tailWord_3093246, baseEnd_3093246] using wordTrace_append hprefix tailTrace_3093246
  have hstable : (prefixWord ++ tailWord_3093246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3093246).length < 2 ^ (prefixWord ++ tailWord_3093246).sum := by decide
  have hdescent : baseEnd_3093246 < baseStart_3093246 := by decide
  rcases family_descends (prefixWord ++ tailWord_3093246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3093272 : List Nat := [2, 1, 2, 3, 1, 1, 1, 2, 5, 3, 2]
def baseStart_3093272 : Nat := 118140960795 + 3093272 * 2 ^ 59
def prefixEnd_3093272 : Nat := 4983230072969 + 3 ^ 40 * 3093272 * 2
def baseEnd_3093272 : Nat := 1588335331094526792774307

theorem tailTrace_3093272 : CollatzResearch.WordTrace tailWord_3093272 prefixEnd_3093272 1588335331094526792774307 := by
  unfold tailWord_3093272
  simp only [CollatzResearch.WordTrace]
  refine ⟨56410449224805653821745035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75213932299740871762326713 56410449224805653821745035)
  ·
    refine ⟨84615673837208480732617553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56410449224805653821745035 84615673837208480732617553)
    ·
      refine ⟨63461755377906360549463165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84615673837208480732617553 63461755377906360549463165)
      ·
        refine ⟨23798158266714885206048687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63461755377906360549463165 23798158266714885206048687)
        ·
          refine ⟨35697237400072327809073031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23798158266714885206048687 35697237400072327809073031)
          ·
            refine ⟨53545856100108491713609547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35697237400072327809073031 53545856100108491713609547)
            ·
              refine ⟨80318784150162737570414321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53545856100108491713609547 80318784150162737570414321)
              ·
                refine ⟨60239088112622053177810741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80318784150162737570414321 60239088112622053177810741)
                ·
                  refine ⟨5647414510558317485419757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 60239088112622053177810741 5647414510558317485419757)
                  ·
                    refine ⟨2117780441459369057032409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5647414510558317485419757 2117780441459369057032409)
                    ·
                      refine ⟨1588335331094526792774307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2117780441459369057032409 1588335331094526792774307)
                      ·
                        rfl

theorem cell23_3093272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 2, 5, 3, 2].length) (baseStart_3093272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3093272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3093272 prefixEnd_3093272 := by exact prefixLift 3093272
  have htrace : WordTrace (prefixWord ++ tailWord_3093272) baseStart_3093272 baseEnd_3093272 := by
    simpa [prefixWord, tailWord_3093272, baseEnd_3093272] using wordTrace_append hprefix tailTrace_3093272
  have hstable : (prefixWord ++ tailWord_3093272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3093272).length < 2 ^ (prefixWord ++ tailWord_3093272).sum := by decide
  have hdescent : baseEnd_3093272 < baseStart_3093272 := by decide
  rcases family_descends (prefixWord ++ tailWord_3093272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3093285 : List Nat := [1, 3, 1, 2, 3, 1, 2, 1, 2, 3, 4]
def baseStart_3093285 : Nat := 118140960795 + 3093285 * 2 ^ 59
def prefixEnd_3093285 : Nat := 4983230072969 + 3 ^ 40 * 3093285 * 2
def baseEnd_3093285 : Nat := 1588342006343035241911747

theorem tailTrace_3093285 : CollatzResearch.WordTrace tailWord_3093285 prefixEnd_3093285 1588342006343035241911747 := by
  unfold tailWord_3093285
  simp only [CollatzResearch.WordTrace]
  refine ⟨112821372598564210863713309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75214248399042807242475539 112821372598564210863713309)
  ·
    refine ⟨42308014724461579073892491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112821372598564210863713309 42308014724461579073892491)
    ·
      refine ⟨63462022086692368610838737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42308014724461579073892491 63462022086692368610838737)
      ·
        refine ⟨47596516565019276458129053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63462022086692368610838737 47596516565019276458129053)
        ·
          refine ⟨17848693711882228671798395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47596516565019276458129053 17848693711882228671798395)
          ·
            refine ⟨26773040567823343007697593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17848693711882228671798395 26773040567823343007697593)
            ·
              refine ⟨20079780425867507255773195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26773040567823343007697593 20079780425867507255773195)
              ·
                refine ⟨30119670638801260883659793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20079780425867507255773195 30119670638801260883659793)
                ·
                  refine ⟨22589752979100945662744845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30119670638801260883659793 22589752979100945662744845)
                  ·
                    refine ⟨8471157367162854623529317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22589752979100945662744845 8471157367162854623529317)
                    ·
                      refine ⟨1588342006343035241911747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8471157367162854623529317 1588342006343035241911747)
                      ·
                        rfl

theorem cell23_3093285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 1, 2, 3, 4].length) (baseStart_3093285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3093285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3093285 prefixEnd_3093285 := by exact prefixLift 3093285
  have htrace : WordTrace (prefixWord ++ tailWord_3093285) baseStart_3093285 baseEnd_3093285 := by
    simpa [prefixWord, tailWord_3093285, baseEnd_3093285] using wordTrace_append hprefix tailTrace_3093285
  have hstable : (prefixWord ++ tailWord_3093285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3093285).length < 2 ^ (prefixWord ++ tailWord_3093285).sum := by decide
  have hdescent : baseEnd_3093285 < baseStart_3093285 := by decide
  rcases family_descends (prefixWord ++ tailWord_3093285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3093290 : List Nat := [3, 1, 4, 3, 2, 1, 2, 1, 2, 4]
def baseStart_3093290 : Nat := 118140960795 + 3093290 * 2 ^ 59
def prefixEnd_3093290 : Nat := 4983230072969 + 3 ^ 40 * 3093290 * 2
def baseEnd_3093290 : Nat := 529448191248769240783075

theorem tailTrace_3093290 : CollatzResearch.WordTrace tailWord_3093290 prefixEnd_3093290 529448191248769240783075 := by
  unfold tailWord_3093290
  simp only [CollatzResearch.WordTrace]
  refine ⟨28205388740886524179411331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75214369975697397811763549 28205388740886524179411331)
  ·
    refine ⟨42308083111329786269116997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28205388740886524179411331 42308083111329786269116997)
    ·
      refine ⟨7932765583374334925459437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42308083111329786269116997 7932765583374334925459437)
      ·
        refine ⟨2974787093765375597047289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7932765583374334925459437 2974787093765375597047289)
        ·
          refine ⟨2231090320324031697785467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2974787093765375597047289 2231090320324031697785467)
          ·
            refine ⟨3346635480486047546678201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2231090320324031697785467 3346635480486047546678201)
            ·
              refine ⟨2509976610364535660008651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3346635480486047546678201 2509976610364535660008651)
              ·
                refine ⟨3764964915546803490012977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2509976610364535660008651 3764964915546803490012977)
                ·
                  refine ⟨2823723686660102617509733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3764964915546803490012977 2823723686660102617509733)
                  ·
                    refine ⟨529448191248769240783075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2823723686660102617509733 529448191248769240783075)
                    ·
                      rfl

theorem cell23_3093290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 2, 1, 2, 4].length) (baseStart_3093290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3093290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3093290 prefixEnd_3093290 := by exact prefixLift 3093290
  have htrace : WordTrace (prefixWord ++ tailWord_3093290) baseStart_3093290 baseEnd_3093290 := by
    simpa [prefixWord, tailWord_3093290, baseEnd_3093290] using wordTrace_append hprefix tailTrace_3093290
  have hstable : (prefixWord ++ tailWord_3093290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3093290).length < 2 ^ (prefixWord ++ tailWord_3093290).sum := by decide
  have hdescent : baseEnd_3093290 < baseStart_3093290 := by decide
  rcases family_descends (prefixWord ++ tailWord_3093290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3093352 : List Nat := [2, 1, 4, 2, 1, 2, 1, 1, 1, 5, 3]
def baseStart_3093352 : Nat := 118140960795 + 3093352 * 2 ^ 59
def prefixEnd_3093352 : Nat := 4983230072969 + 3 ^ 40 * 3093352 * 2
def baseEnd_3093352 : Nat := 1588376409546886479773939

theorem tailTrace_3093352 : CollatzResearch.WordTrace tailWord_3093352 prefixEnd_3093352 1588376409546886479773939 := by
  unfold tailWord_3093352
  simp only [CollatzResearch.WordTrace]
  refine ⟨56411908144660740653201155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75215877526214320870934873 56411908144660740653201155)
  ·
    refine ⟨84617862216991110979801733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56411908144660740653201155 84617862216991110979801733)
    ·
      refine ⟨15865849165685833308712825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 84617862216991110979801733 15865849165685833308712825)
      ·
        refine ⟨11899386874264374981534619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15865849165685833308712825 11899386874264374981534619)
        ·
          refine ⟨17849080311396562472301929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11899386874264374981534619 17849080311396562472301929)
          ·
            refine ⟨13386810233547421854226447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17849080311396562472301929 13386810233547421854226447)
            ·
              refine ⟨20080215350321132781339671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13386810233547421854226447 20080215350321132781339671)
              ·
                refine ⟨30120323025481699172009507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20080215350321132781339671 30120323025481699172009507)
                ·
                  refine ⟨45180484538222548758014261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30120323025481699172009507 45180484538222548758014261)
                  ·
                    refine ⟨4235670425458363946063837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 45180484538222548758014261 4235670425458363946063837)
                    ·
                      refine ⟨1588376409546886479773939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4235670425458363946063837 1588376409546886479773939)
                      ·
                        rfl

theorem cell23_3093352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 1, 1, 5, 3].length) (baseStart_3093352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3093352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3093352 prefixEnd_3093352 := by exact prefixLift 3093352
  have htrace : WordTrace (prefixWord ++ tailWord_3093352) baseStart_3093352 baseEnd_3093352 := by
    simpa [prefixWord, tailWord_3093352, baseEnd_3093352] using wordTrace_append hprefix tailTrace_3093352
  have hstable : (prefixWord ++ tailWord_3093352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3093352).length < 2 ^ (prefixWord ++ tailWord_3093352).sum := by decide
  have hdescent : baseEnd_3093352 < baseStart_3093352 := by decide
  rcases family_descends (prefixWord ++ tailWord_3093352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3093355 : List Nat := [1, 1, 1, 1, 2, 2, 4, 2, 4, 5]
def baseStart_3093355 : Nat := 118140960795 + 3093355 * 2 ^ 59
def prefixEnd_3093355 : Nat := 4983230072969 + 3 ^ 40 * 3093355 * 2
def baseEnd_3093355 : Nat := 529459316662949989345475

theorem tailTrace_3093355 : CollatzResearch.WordTrace tailWord_3093355 prefixEnd_3093355 529459316662949989345475 := by
  unfold tailWord_3093355
  simp only [CollatzResearch.WordTrace]
  refine ⟨112823925708310612818761519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75215950472207075212507679 112823925708310612818761519)
  ·
    refine ⟨169235888562465919228142279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112823925708310612818761519 169235888562465919228142279)
    ·
      refine ⟨253853832843698878842213419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169235888562465919228142279 253853832843698878842213419)
      ·
        refine ⟨380780749265548318263320129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253853832843698878842213419 380780749265548318263320129)
        ·
          refine ⟨285585561949161238697490097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 380780749265548318263320129 285585561949161238697490097)
          ·
            refine ⟨214189171461870929023117573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 285585561949161238697490097 214189171461870929023117573)
            ·
              refine ⟨40160469649100799191834545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 214189171461870929023117573 40160469649100799191834545)
              ·
                refine ⟨30120352236825599393875909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40160469649100799191834545 30120352236825599393875909)
                ·
                  refine ⟨5647566044404799886351733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30120352236825599393875909 5647566044404799886351733)
                  ·
                    refine ⟨529459316662949989345475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5647566044404799886351733 529459316662949989345475)
                    ·
                      rfl

theorem cell23_3093355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 2, 4, 5].length) (baseStart_3093355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3093355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3093355 prefixEnd_3093355 := by exact prefixLift 3093355
  have htrace : WordTrace (prefixWord ++ tailWord_3093355) baseStart_3093355 baseEnd_3093355 := by
    simpa [prefixWord, tailWord_3093355, baseEnd_3093355] using wordTrace_append hprefix tailTrace_3093355
  have hstable : (prefixWord ++ tailWord_3093355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3093355).length < 2 ^ (prefixWord ++ tailWord_3093355).sum := by decide
  have hdescent : baseEnd_3093355 < baseStart_3093355 := by decide
  rcases family_descends (prefixWord ++ tailWord_3093355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3093412 : List Nat := [2, 3, 1, 2, 1, 2, 1, 1, 3, 4, 3]
def baseStart_3093412 : Nat := 118140960795 + 3093412 * 2 ^ 59
def prefixEnd_3093412 : Nat := 4983230072969 + 3 ^ 40 * 3093412 * 2
def baseEnd_3093412 : Nat := 1588407218386156245023663

theorem tailTrace_3093412 : CollatzResearch.WordTrace tailWord_3093412 prefixEnd_3093412 1588407218386156245023663 := by
  unfold tailWord_3093412
  simp only [CollatzResearch.WordTrace]
  refine ⟨56413002334552055776793245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75217336446069407702390993 56413002334552055776793245)
  ·
    refine ⟨21154875875457020916297467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56413002334552055776793245 21154875875457020916297467)
    ·
      refine ⟨31732313813185531374446201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21154875875457020916297467 31732313813185531374446201)
      ·
        refine ⟨23799235359889148530834651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31732313813185531374446201 23799235359889148530834651)
        ·
          refine ⟨35698853039833722796251977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23799235359889148530834651 35698853039833722796251977)
          ·
            refine ⟨26774139779875292097188983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35698853039833722796251977 26774139779875292097188983)
            ·
              refine ⟨40161209669812938145783475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26774139779875292097188983 40161209669812938145783475)
              ·
                refine ⟨60241814504719407218675213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40161209669812938145783475 60241814504719407218675213)
                ·
                  refine ⟨22590680439269777707003205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60241814504719407218675213 22590680439269777707003205)
                  ·
                    refine ⟨4235752582363083320063101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22590680439269777707003205 4235752582363083320063101)
                    ·
                      refine ⟨1588407218386156245023663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4235752582363083320063101 1588407218386156245023663)
                      ·
                        rfl

theorem cell23_3093412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 1, 3, 4, 3].length) (baseStart_3093412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3093412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3093412 prefixEnd_3093412 := by exact prefixLift 3093412
  have htrace : WordTrace (prefixWord ++ tailWord_3093412) baseStart_3093412 baseEnd_3093412 := by
    simpa [prefixWord, tailWord_3093412, baseEnd_3093412] using wordTrace_append hprefix tailTrace_3093412
  have hstable : (prefixWord ++ tailWord_3093412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3093412).length < 2 ^ (prefixWord ++ tailWord_3093412).sum := by decide
  have hdescent : baseEnd_3093412 < baseStart_3093412 := by decide
  rcases family_descends (prefixWord ++ tailWord_3093412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3093429 : List Nat := [1, 3, 3, 2, 1, 1, 2, 3, 2, 2, 3]
def baseStart_3093429 : Nat := 118140960795 + 3093429 * 2 ^ 59
def prefixEnd_3093429 : Nat := 4983230072969 + 3 ^ 40 * 3093429 * 2
def baseEnd_3093429 : Nat := 1588415947557282678511085

theorem tailTrace_3093429 : CollatzResearch.WordTrace tailWord_3093429 prefixEnd_3093429 1588415947557282678511085 := by
  unfold tailWord_3093429
  simp only [CollatzResearch.WordTrace]
  refine ⟨112826624710042523456955341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75217749806695015637970227 112826624710042523456955341)
  ·
    refine ⟨42309984266265946296358253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112826624710042523456955341 42309984266265946296358253)
    ·
      refine ⟨15866244099849729861134345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42309984266265946296358253 15866244099849729861134345)
      ·
        refine ⟨11899683074887297395850759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15866244099849729861134345 11899683074887297395850759)
        ·
          refine ⟨17849524612330946093776139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11899683074887297395850759 17849524612330946093776139)
          ·
            refine ⟨26774286918496419140664209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17849524612330946093776139 26774286918496419140664209)
            ·
              refine ⟨20080715188872314355498157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26774286918496419140664209 20080715188872314355498157)
              ·
                refine ⟨7530268195827117883311809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20080715188872314355498157 7530268195827117883311809)
                ·
                  refine ⟨5647701146870338412483857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7530268195827117883311809 5647701146870338412483857)
                  ·
                    refine ⟨4235775860152753809362893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5647701146870338412483857 4235775860152753809362893)
                    ·
                      refine ⟨1588415947557282678511085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4235775860152753809362893 1588415947557282678511085)
                      ·
                        rfl

theorem cell23_3093429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 3, 2, 2, 3].length) (baseStart_3093429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3093429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3093429 prefixEnd_3093429 := by exact prefixLift 3093429
  have htrace : WordTrace (prefixWord ++ tailWord_3093429) baseStart_3093429 baseEnd_3093429 := by
    simpa [prefixWord, tailWord_3093429, baseEnd_3093429] using wordTrace_append hprefix tailTrace_3093429
  have hstable : (prefixWord ++ tailWord_3093429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3093429).length < 2 ^ (prefixWord ++ tailWord_3093429).sum := by decide
  have hdescent : baseEnd_3093429 < baseStart_3093429 := by decide
  rcases family_descends (prefixWord ++ tailWord_3093429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3093445 : List Nat := [1, 3, 1, 1, 1, 1, 1, 2, 1, 11]
def baseStart_3093445 : Nat := 118140960795 + 3093445 * 2 ^ 59
def prefixEnd_3093445 : Nat := 4983230072969 + 3 ^ 40 * 3093445 * 2
def baseEnd_3093445 : Nat := 529474721082584871970337

theorem tailTrace_3093445 : CollatzResearch.WordTrace tailWord_3093445 prefixEnd_3093445 529474721082584871970337 := by
  unfold tailWord_3093445
  simp only [CollatzResearch.WordTrace]
  refine ⟨112827208277984558189537789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75218138851989705459691859 112827208277984558189537789)
  ·
    refine ⟨42310203104244209321076671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112827208277984558189537789 42310203104244209321076671)
    ·
      refine ⟨63465304656366313981615007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42310203104244209321076671 63465304656366313981615007)
      ·
        refine ⟨95197956984549470972422511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63465304656366313981615007 95197956984549470972422511)
        ·
          refine ⟨142796935476824206458633767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95197956984549470972422511 142796935476824206458633767)
          ·
            refine ⟨214195403215236309687950651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142796935476824206458633767 214195403215236309687950651)
            ·
              refine ⟨321293104822854464531925977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 214195403215236309687950651 321293104822854464531925977)
              ·
                refine ⟨240969828617140848398944483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 321293104822854464531925977 240969828617140848398944483)
                ·
                  refine ⟨361454742925711272598416725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 240969828617140848398944483 361454742925711272598416725)
                  ·
                    refine ⟨529474721082584871970337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 361454742925711272598416725 529474721082584871970337)
                    ·
                      rfl

theorem cell23_3093445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 11].length) (baseStart_3093445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3093445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3093445 prefixEnd_3093445 := by exact prefixLift 3093445
  have htrace : WordTrace (prefixWord ++ tailWord_3093445) baseStart_3093445 baseEnd_3093445 := by
    simpa [prefixWord, tailWord_3093445, baseEnd_3093445] using wordTrace_append hprefix tailTrace_3093445
  have hstable : (prefixWord ++ tailWord_3093445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3093445).length < 2 ^ (prefixWord ++ tailWord_3093445).sum := by decide
  have hdescent : baseEnd_3093445 < baseStart_3093445 := by decide
  rcases family_descends (prefixWord ++ tailWord_3093445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3093466 : List Nat := [3, 1, 1, 2, 4, 3, 2, 1, 6]
def baseStart_3093466 : Nat := 118140960795 + 3093466 * 2 ^ 59
def prefixEnd_3093466 : Nat := 4983230072969 + 3 ^ 40 * 3093466 * 2
def baseEnd_3093466 : Nat := 176492771815722114860935

theorem tailTrace_3093466 : CollatzResearch.WordTrace tailWord_3093466 prefixEnd_3093466 176492771815722114860935 := by
  unfold tailWord_3093466
  simp only [CollatzResearch.WordTrace]
  refine ⟨28206993552727119694013063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75218649473938985850701501 28206993552727119694013063)
  ·
    refine ⟨42310490329090679541019595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28206993552727119694013063 42310490329090679541019595)
    ·
      refine ⟨63465735493636019311529393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42310490329090679541019595 63465735493636019311529393)
      ·
        refine ⟨47599301620227014483647045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63465735493636019311529393 47599301620227014483647045)
        ·
          refine ⟨8924869053792565215683821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47599301620227014483647045 8924869053792565215683821)
          ·
            refine ⟨3346825895172211955881433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8924869053792565215683821 3346825895172211955881433)
            ·
              refine ⟨2510119421379158966911075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3346825895172211955881433 2510119421379158966911075)
              ·
                refine ⟨3765179132068738450366613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2510119421379158966911075 3765179132068738450366613)
                ·
                  refine ⟨176492771815722114860935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3765179132068738450366613 176492771815722114860935)
                  ·
                    rfl

theorem cell23_3093466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 2, 1, 6].length) (baseStart_3093466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3093466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3093466 prefixEnd_3093466 := by exact prefixLift 3093466
  have htrace : WordTrace (prefixWord ++ tailWord_3093466) baseStart_3093466 baseEnd_3093466 := by
    simpa [prefixWord, tailWord_3093466, baseEnd_3093466] using wordTrace_append hprefix tailTrace_3093466
  have hstable : (prefixWord ++ tailWord_3093466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3093466).length < 2 ^ (prefixWord ++ tailWord_3093466).sum := by decide
  have hdescent : baseEnd_3093466 < baseStart_3093466 := by decide
  rcases family_descends (prefixWord ++ tailWord_3093466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3093479 : List Nat := [1, 1, 5, 2, 2, 2, 1, 1, 3, 5]
def baseStart_3093479 : Nat := 118140960795 + 3093479 * 2 ^ 59
def prefixEnd_3093479 : Nat := 4983230072969 + 3 ^ 40 * 3093479 * 2
def baseEnd_3093479 : Nat := 529480540530002494295285

theorem tailTrace_3093479 : CollatzResearch.WordTrace tailWord_3093479 prefixEnd_3093479 529480540530002494295285 := by
  unfold tailWord_3093479
  simp only [CollatzResearch.WordTrace]
  refine ⟨112828448359861381996275491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75218965573240921330850327 112828448359861381996275491)
  ·
    refine ⟨169242672539792072994413237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112828448359861381996275491 169242672539792072994413237)
    ·
      refine ⟨15866500550605506843226241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 169242672539792072994413237 15866500550605506843226241)
      ·
        refine ⟨11899875412954130132419681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15866500550605506843226241 11899875412954130132419681)
        ·
          refine ⟨8924906559715597599314761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11899875412954130132419681 8924906559715597599314761)
          ·
            refine ⟨6693679919786698199486071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8924906559715597599314761 6693679919786698199486071)
            ·
              refine ⟨10040519879680047299229107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6693679919786698199486071 10040519879680047299229107)
              ·
                refine ⟨15060779819520070948843661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10040519879680047299229107 15060779819520070948843661)
                ·
                  refine ⟨5647792432320026605816373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15060779819520070948843661 5647792432320026605816373)
                  ·
                    refine ⟨529480540530002494295285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5647792432320026605816373 529480540530002494295285)
                    ·
                      rfl

theorem cell23_3093479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 1, 3, 5].length) (baseStart_3093479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3093479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3093479 prefixEnd_3093479 := by exact prefixLift 3093479
  have htrace : WordTrace (prefixWord ++ tailWord_3093479) baseStart_3093479 baseEnd_3093479 := by
    simpa [prefixWord, tailWord_3093479, baseEnd_3093479] using wordTrace_append hprefix tailTrace_3093479
  have hstable : (prefixWord ++ tailWord_3093479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3093479).length < 2 ^ (prefixWord ++ tailWord_3093479).sum := by decide
  have hdescent : baseEnd_3093479 < baseStart_3093479 := by decide
  rcases family_descends (prefixWord ++ tailWord_3093479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3093539 : List Nat := [1, 1, 1, 4, 3, 3, 3, 7]
def baseStart_3093539 : Nat := 118140960795 + 3093539 * 2 ^ 59
def prefixEnd_3093539 : Nat := 4983230072969 + 3 ^ 40 * 3093539 * 2
def baseEnd_3093539 : Nat := 58832312238121379560577

theorem tailTrace_3093539 : CollatzResearch.WordTrace tailWord_3093539 prefixEnd_3093539 58832312238121379560577 := by
  unfold tailWord_3093539
  simp only [CollatzResearch.WordTrace]
  refine ⟨112830636739644012243459671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75220424493096008162306447 112830636739644012243459671)
  ·
    refine ⟨169245955109466018365189507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112830636739644012243459671 169245955109466018365189507)
    ·
      refine ⟨253868932664199027547784261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169245955109466018365189507 253868932664199027547784261)
      ·
        refine ⟨47600424874537317665209549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 253868932664199027547784261 47600424874537317665209549)
        ·
          refine ⟨17850159327951494124453581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47600424874537317665209549 17850159327951494124453581)
          ·
            refine ⟨6693809747981810296670093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17850159327951494124453581 6693809747981810296670093)
            ·
              refine ⟨2510178655493178861251285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6693809747981810296670093 2510178655493178861251285)
              ·
                refine ⟨58832312238121379560577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2510178655493178861251285 58832312238121379560577)
                ·
                  rfl

theorem cell23_3093539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 3, 7].length) (baseStart_3093539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3093539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3093539 prefixEnd_3093539 := by exact prefixLift 3093539
  have htrace : WordTrace (prefixWord ++ tailWord_3093539) baseStart_3093539 baseEnd_3093539 := by
    simpa [prefixWord, tailWord_3093539, baseEnd_3093539] using wordTrace_append hprefix tailTrace_3093539
  have hstable : (prefixWord ++ tailWord_3093539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3093539).length < 2 ^ (prefixWord ++ tailWord_3093539).sum := by decide
  have hdescent : baseEnd_3093539 < baseStart_3093539 := by decide
  rcases family_descends (prefixWord ++ tailWord_3093539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3093590 : List Nat := [5, 2, 2, 1, 2, 2, 2, 7]
def baseStart_3093590 : Nat := 118140960795 + 3093590 * 2 ^ 59
def prefixEnd_3093590 : Nat := 4983230072969 + 3 ^ 40 * 3093590 * 2
def baseEnd_3093590 : Nat := 58833282146024316614735

theorem tailTrace_3093590 : CollatzResearch.WordTrace tailWord_3093590 prefixEnd_3093590 58833282146024316614735 := by
  unfold tailWord_3093590
  simp only [CollatzResearch.WordTrace]
  refine ⟨7052031053903702997097889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 75221664574972831969044149 7052031053903702997097889)
  ·
    refine ⟨5289023290427777247823417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7052031053903702997097889 5289023290427777247823417)
    ·
      refine ⟨3966767467820832935867563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5289023290427777247823417 3966767467820832935867563)
      ·
        refine ⟨5950151201731249403801345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3966767467820832935867563 5950151201731249403801345)
        ·
          refine ⟨4462613401298437052851009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5950151201731249403801345 4462613401298437052851009)
          ·
            refine ⟨3346960050973827789638257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4462613401298437052851009 3346960050973827789638257)
            ·
              refine ⟨2510220038230370842228693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3346960050973827789638257 2510220038230370842228693)
              ·
                refine ⟨58833282146024316614735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2510220038230370842228693 58833282146024316614735)
                ·
                  rfl

theorem cell23_3093590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 2, 7].length) (baseStart_3093590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3093590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3093590 prefixEnd_3093590 := by exact prefixLift 3093590
  have htrace : WordTrace (prefixWord ++ tailWord_3093590) baseStart_3093590 baseEnd_3093590 := by
    simpa [prefixWord, tailWord_3093590, baseEnd_3093590] using wordTrace_append hprefix tailTrace_3093590
  have hstable : (prefixWord ++ tailWord_3093590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3093590).length < 2 ^ (prefixWord ++ tailWord_3093590).sum := by decide
  have hdescent : baseEnd_3093590 < baseStart_3093590 := by decide
  rcases family_descends (prefixWord ++ tailWord_3093590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3093609 : List Nat := [1, 2, 1, 1, 1, 7, 1, 1, 2, 1, 5]
def baseStart_3093609 : Nat := 118140960795 + 3093609 * 2 ^ 59
def prefixEnd_3093609 : Nat := 4983230072969 + 3 ^ 40 * 3093609 * 2
def baseEnd_3093609 : Nat := 1588508374075091974260257

theorem tailTrace_3093609 : CollatzResearch.WordTrace tailWord_3093609 prefixEnd_3093609 1588508374075091974260257 := by
  unfold tailWord_3093609
  simp only [CollatzResearch.WordTrace]
  refine ⟨112833189849390414198507881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75222126566260276132338587 112833189849390414198507881)
  ·
    refine ⟨84624892387042810648880911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112833189849390414198507881 84624892387042810648880911)
    ·
      refine ⟨126937338580564215973321367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84624892387042810648880911 126937338580564215973321367)
      ·
        refine ⟨190406007870846323959982051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126937338580564215973321367 190406007870846323959982051)
        ·
          refine ⟨285609011806269485939973077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190406007870846323959982051 285609011806269485939973077)
          ·
            refine ⟨6693961214209441076718119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 285609011806269485939973077 6693961214209441076718119)
            ·
              refine ⟨10040941821314161615077179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6693961214209441076718119 10040941821314161615077179)
              ·
                refine ⟨15061412731971242422615769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10040941821314161615077179 15061412731971242422615769)
                ·
                  refine ⟨11296059548978431816961827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15061412731971242422615769 11296059548978431816961827)
                  ·
                    refine ⟨16944089323467647725442741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11296059548978431816961827 16944089323467647725442741)
                    ·
                      refine ⟨1588508374075091974260257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16944089323467647725442741 1588508374075091974260257)
                      ·
                        rfl

theorem cell23_3093609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 1, 2, 1, 5].length) (baseStart_3093609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3093609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3093609 prefixEnd_3093609 := by exact prefixLift 3093609
  have htrace : WordTrace (prefixWord ++ tailWord_3093609) baseStart_3093609 baseEnd_3093609 := by
    simpa [prefixWord, tailWord_3093609, baseEnd_3093609] using wordTrace_append hprefix tailTrace_3093609
  have hstable : (prefixWord ++ tailWord_3093609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3093609).length < 2 ^ (prefixWord ++ tailWord_3093609).sum := by decide
  have hdescent : baseEnd_3093609 < baseStart_3093609 := by decide
  rcases family_descends (prefixWord ++ tailWord_3093609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3093623 : List Nat := [1, 1, 3, 1, 1, 4, 2, 4, 2, 2, 2]
def baseStart_3093623 : Nat := 118140960795 + 3093623 * 2 ^ 59
def prefixEnd_3093623 : Nat := 4983230072969 + 3 ^ 40 * 3093623 * 2
def baseEnd_3093623 : Nat := 1588515562804254919485193

theorem tailTrace_3093623 : CollatzResearch.WordTrace tailWord_3093623 prefixEnd_3093623 1588515562804254919485193 := by
  unfold tailWord_3093623
  simp only [CollatzResearch.WordTrace]
  refine ⟨112833700471339694589517523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75222466980893129726345015 112833700471339694589517523)
  ·
    refine ⟨169250550707009541884276285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112833700471339694589517523 169250550707009541884276285)
    ·
      refine ⟨63468956515128578206603607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 169250550707009541884276285 63468956515128578206603607)
      ·
        refine ⟨95203434772692867309905411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63468956515128578206603607 95203434772692867309905411)
        ·
          refine ⟨142805152159039300964858117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95203434772692867309905411 142805152159039300964858117)
          ·
            refine ⟨26775966029819868930910897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 142805152159039300964858117 26775966029819868930910897)
            ·
              refine ⟨20081974522364901698183173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26775966029819868930910897 20081974522364901698183173)
              ·
                refine ⟨3765370222943419068409345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20081974522364901698183173 3765370222943419068409345)
                ·
                  refine ⟨2824027667207564301307009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3765370222943419068409345 2824027667207564301307009)
                  ·
                    refine ⟨2118020750405673225980257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2824027667207564301307009 2118020750405673225980257)
                    ·
                      refine ⟨1588515562804254919485193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2118020750405673225980257 1588515562804254919485193)
                      ·
                        rfl

theorem cell23_3093623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 4, 2, 2, 2].length) (baseStart_3093623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3093623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3093623 prefixEnd_3093623 := by exact prefixLift 3093623
  have htrace : WordTrace (prefixWord ++ tailWord_3093623) baseStart_3093623 baseEnd_3093623 := by
    simpa [prefixWord, tailWord_3093623, baseEnd_3093623] using wordTrace_append hprefix tailTrace_3093623
  have hstable : (prefixWord ++ tailWord_3093623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3093623).length < 2 ^ (prefixWord ++ tailWord_3093623).sum := by decide
  have hdescent : baseEnd_3093623 < baseStart_3093623 := by decide
  rcases family_descends (prefixWord ++ tailWord_3093623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3093639 : List Nat := [1, 1, 4, 2, 1, 1, 1, 3, 1, 5, 3]
def baseStart_3093639 : Nat := 118140960795 + 3093639 * 2 ^ 59
def prefixEnd_3093639 : Nat := 4983230072969 + 3 ^ 40 * 3093639 * 2
def baseEnd_3093639 : Nat := 1588523778494726856885119

theorem tailTrace_3093639 : CollatzResearch.WordTrace tailWord_3093639 prefixEnd_3093639 1588523778494726856885119 := by
  unfold tailWord_3093639
  simp only [CollatzResearch.WordTrace]
  refine ⟨112834284039281729322099971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75222856026187819548066647 112834284039281729322099971)
  ·
    refine ⟨169251426058922593983149957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112834284039281729322099971 169251426058922593983149957)
    ·
      refine ⟨31734642386047986371840617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 169251426058922593983149957 31734642386047986371840617)
      ·
        refine ⟨23800981789535989778880463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31734642386047986371840617 23800981789535989778880463)
        ·
          refine ⟨35701472684303984668320695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23800981789535989778880463 35701472684303984668320695)
          ·
            refine ⟨53552209026455977002481043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35701472684303984668320695 53552209026455977002481043)
            ·
              refine ⟨80328313539683965503721565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53552209026455977002481043 80328313539683965503721565)
              ·
                refine ⟨30123117577381487063895587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80328313539683965503721565 30123117577381487063895587)
                ·
                  refine ⟨45184676366072230595843381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30123117577381487063895587 45184676366072230595843381)
                  ·
                    refine ⟨4236063409319271618360317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 45184676366072230595843381 4236063409319271618360317)
                    ·
                      refine ⟨1588523778494726856885119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4236063409319271618360317 1588523778494726856885119)
                      ·
                        rfl

theorem cell23_3093639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 3, 1, 5, 3].length) (baseStart_3093639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3093639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3093639 prefixEnd_3093639 := by exact prefixLift 3093639
  have htrace : WordTrace (prefixWord ++ tailWord_3093639) baseStart_3093639 baseEnd_3093639 := by
    simpa [prefixWord, tailWord_3093639, baseEnd_3093639] using wordTrace_append hprefix tailTrace_3093639
  have hstable : (prefixWord ++ tailWord_3093639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3093639).length < 2 ^ (prefixWord ++ tailWord_3093639).sum := by decide
  have hdescent : baseEnd_3093639 < baseStart_3093639 := by decide
  rcases family_descends (prefixWord ++ tailWord_3093639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3093669 : List Nat := [1, 3, 1, 2, 1, 4, 1, 2, 1, 2, 5]
def baseStart_3093669 : Nat := 118140960795 + 3093669 * 2 ^ 59
def prefixEnd_3093669 : Nat := 4983230072969 + 3 ^ 40 * 3093669 * 2
def baseEnd_3093669 : Nat := 1588539182914361739509981

theorem tailTrace_3093669 : CollatzResearch.WordTrace tailWord_3093669 prefixEnd_3093669 1588539182914361739509981 := by
  unfold tailWord_3093669
  simp only [CollatzResearch.WordTrace]
  refine ⟨112835378229173044445692061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75223585486115362963794707 112835378229173044445692061)
  ·
    refine ⟨42313266835939891667134523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112835378229173044445692061 42313266835939891667134523)
    ·
      refine ⟨63469900253909837500701785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42313266835939891667134523 63469900253909837500701785)
      ·
        refine ⟨47602425190432378125526339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63469900253909837500701785 47602425190432378125526339)
        ·
          refine ⟨71403637785648567188289509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47602425190432378125526339 71403637785648567188289509)
          ·
            refine ⟨13388182084809106347804283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71403637785648567188289509 13388182084809106347804283)
            ·
              refine ⟨20082273127213659521706425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13388182084809106347804283 20082273127213659521706425)
              ·
                refine ⟨15061704845410244641279819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20082273127213659521706425 15061704845410244641279819)
                ·
                  refine ⟨22592557268115366961919729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15061704845410244641279819 22592557268115366961919729)
                  ·
                    refine ⟨16944417951086525221439797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22592557268115366961919729 16944417951086525221439797)
                    ·
                      refine ⟨1588539182914361739509981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16944417951086525221439797 1588539182914361739509981)
                      ·
                        rfl

theorem cell23_3093669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 2, 1, 2, 5].length) (baseStart_3093669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3093669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3093669 prefixEnd_3093669 := by exact prefixLift 3093669
  have htrace : WordTrace (prefixWord ++ tailWord_3093669) baseStart_3093669 baseEnd_3093669 := by
    simpa [prefixWord, tailWord_3093669, baseEnd_3093669] using wordTrace_append hprefix tailTrace_3093669
  have hstable : (prefixWord ++ tailWord_3093669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3093669).length < 2 ^ (prefixWord ++ tailWord_3093669).sum := by decide
  have hdescent : baseEnd_3093669 < baseStart_3093669 := by decide
  rcases family_descends (prefixWord ++ tailWord_3093669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3093706 : List Nat := [3, 1, 2, 1, 3, 2, 1, 1, 5, 4]
def baseStart_3093706 : Nat := 118140960795 + 3093706 * 2 ^ 59
def prefixEnd_3093706 : Nat := 4983230072969 + 3 ^ 40 * 3093706 * 2
def baseEnd_3093706 : Nat := 529519393899526031582437

theorem tailTrace_3093706 : CollatzResearch.WordTrace tailWord_3093706 prefixEnd_3093706 529519393899526031582437 := by
  unfold tailWord_3093706
  simp only [CollatzResearch.WordTrace]
  refine ⟨28209181932509749941197243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75224485153359333176525981 28209181932509749941197243)
  ·
    refine ⟨42313772898764624911795865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28209181932509749941197243 42313772898764624911795865)
    ·
      refine ⟨31735329674073468683846899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42313772898764624911795865 31735329674073468683846899)
      ·
        refine ⟨47602994511110203025770349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31735329674073468683846899 47602994511110203025770349)
        ·
          refine ⟨17851122941666326134663881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47602994511110203025770349 17851122941666326134663881)
          ·
            refine ⟨13388342206249744600997911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17851122941666326134663881 13388342206249744600997911)
            ·
              refine ⟨20082513309374616901496867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13388342206249744600997911 20082513309374616901496867)
              ·
                refine ⟨30123769964061925352245301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20082513309374616901496867 30123769964061925352245301)
                ·
                  refine ⟨2824103434130805501772997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30123769964061925352245301 2824103434130805501772997)
                  ·
                    refine ⟨529519393899526031582437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2824103434130805501772997 529519393899526031582437)
                    ·
                      rfl

theorem cell23_3093706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 1, 5, 4].length) (baseStart_3093706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3093706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3093706 prefixEnd_3093706 := by exact prefixLift 3093706
  have htrace : WordTrace (prefixWord ++ tailWord_3093706) baseStart_3093706 baseEnd_3093706 := by
    simpa [prefixWord, tailWord_3093706, baseEnd_3093706] using wordTrace_append hprefix tailTrace_3093706
  have hstable : (prefixWord ++ tailWord_3093706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3093706).length < 2 ^ (prefixWord ++ tailWord_3093706).sum := by decide
  have hdescent : baseEnd_3093706 < baseStart_3093706 := by decide
  rcases family_descends (prefixWord ++ tailWord_3093706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3093710 : List Nat := [4, 1, 1, 1, 6, 1, 1, 1, 2, 5]
def baseStart_3093710 : Nat := 118140960795 + 3093710 * 2 ^ 59
def prefixEnd_3093710 : Nat := 4983230072969 + 3 ^ 40 * 3093710 * 2
def baseEnd_3093710 : Nat := 529520078540398693032431

theorem tailTrace_3093710 : CollatzResearch.WordTrace tailWord_3093710 prefixEnd_3093710 529520078540398693032431 := by
  unfold tailWord_3093710
  simp only [CollatzResearch.WordTrace]
  refine ⟨14104609202753063555991823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75224582414683005631956389 14104609202753063555991823)
  ·
    refine ⟨21156913804129595333987735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14104609202753063555991823 21156913804129595333987735)
    ·
      refine ⟨31735370706194393000981603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21156913804129595333987735 31735370706194393000981603)
      ·
        refine ⟨47603056059291589501472405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31735370706194393000981603 47603056059291589501472405)
        ·
          refine ⟨2231393252779293257881519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 47603056059291589501472405 2231393252779293257881519)
          ·
            refine ⟨3347089879168939886822279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2231393252779293257881519 3347089879168939886822279)
            ·
              refine ⟨5020634818753409830233419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3347089879168939886822279 5020634818753409830233419)
              ·
                refine ⟨7530952228130114745350129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5020634818753409830233419 7530952228130114745350129)
                ·
                  refine ⟨5648214171097586059012597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7530952228130114745350129 5648214171097586059012597)
                  ·
                    refine ⟨529520078540398693032431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5648214171097586059012597 529520078540398693032431)
                    ·
                      rfl

theorem cell23_3093710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 1, 1, 2, 5].length) (baseStart_3093710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3093710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3093710 prefixEnd_3093710 := by exact prefixLift 3093710
  have htrace : WordTrace (prefixWord ++ tailWord_3093710) baseStart_3093710 baseEnd_3093710 := by
    simpa [prefixWord, tailWord_3093710, baseEnd_3093710] using wordTrace_append hprefix tailTrace_3093710
  have hstable : (prefixWord ++ tailWord_3093710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3093710).length < 2 ^ (prefixWord ++ tailWord_3093710).sum := by decide
  have hdescent : baseEnd_3093710 < baseStart_3093710 := by decide
  rcases family_descends (prefixWord ++ tailWord_3093710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3093739 : List Nat := [1, 1, 1, 1, 2, 6, 1, 1, 1, 2, 6]
def baseStart_3093739 : Nat := 118140960795 + 3093739 * 2 ^ 59
def prefixEnd_3093739 : Nat := 4983230072969 + 3 ^ 40 * 3093739 * 2
def baseEnd_3093739 : Nat := 1588575126560176465634659

theorem tailTrace_3093739 : CollatzResearch.WordTrace tailWord_3093739 prefixEnd_3093739 1588575126560176465634659 := by
  unfold tailWord_3093739
  simp only [CollatzResearch.WordTrace]
  refine ⟨112837931338919446400740271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75225287559279630933826847 112837931338919446400740271)
  ·
    refine ⟨169256897008379169601110407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112837931338919446400740271 169256897008379169601110407)
    ·
      refine ⟨253885345512568754401665611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169256897008379169601110407 253885345512568754401665611)
      ·
        refine ⟨380828018268853131602498417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253885345512568754401665611 380828018268853131602498417)
        ·
          refine ⟨285621013701639848701873813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 380828018268853131602498417 285621013701639848701873813)
          ·
            refine ⟨13388485017264367907900335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 285621013701639848701873813 13388485017264367907900335)
            ·
              refine ⟨20082727525896551861850503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13388485017264367907900335 20082727525896551861850503)
              ·
                refine ⟨30124091288844827792775755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20082727525896551861850503 30124091288844827792775755)
                ·
                  refine ⟨45186136933267241689163633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30124091288844827792775755 45186136933267241689163633)
                  ·
                    refine ⟨33889602699950431266872725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45186136933267241689163633 33889602699950431266872725)
                    ·
                      refine ⟨1588575126560176465634659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33889602699950431266872725 1588575126560176465634659)
                      ·
                        rfl

theorem cell23_3093739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 1, 1, 2, 6].length) (baseStart_3093739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3093739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3093739 prefixEnd_3093739 := by exact prefixLift 3093739
  have htrace : WordTrace (prefixWord ++ tailWord_3093739) baseStart_3093739 baseEnd_3093739 := by
    simpa [prefixWord, tailWord_3093739, baseEnd_3093739] using wordTrace_append hprefix tailTrace_3093739
  have hstable : (prefixWord ++ tailWord_3093739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3093739).length < 2 ^ (prefixWord ++ tailWord_3093739).sum := by decide
  have hdescent : baseEnd_3093739 < baseStart_3093739 := by decide
  rcases family_descends (prefixWord ++ tailWord_3093739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3093763 : List Nat := [1, 1, 1, 3, 2, 4, 2, 2, 3, 1, 3]
def baseStart_3093763 : Nat := 118140960795 + 3093763 * 2 ^ 59
def prefixEnd_3093763 : Nat := 4983230072969 + 3 ^ 40 * 3093763 * 2
def baseEnd_3093763 : Nat := 1588587450095884371734549

theorem tailTrace_3093763 : CollatzResearch.WordTrace tailWord_3093763 prefixEnd_3093763 1588587450095884371734549 := by
  unfold tailWord_3093763
  simp only [CollatzResearch.WordTrace]
  refine ⟨112838806690832498499613943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75225871127221665666409295 112838806690832498499613943)
  ·
    refine ⟨169258210036248747749420915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112838806690832498499613943 169258210036248747749420915)
    ·
      refine ⟨253887315054373121624131373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169258210036248747749420915 253887315054373121624131373)
      ·
        refine ⟨95207743145389920609049265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 253887315054373121624131373 95207743145389920609049265)
        ·
          refine ⟨71405807359042440456786949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95207743145389920609049265 71405807359042440456786949)
          ·
            refine ⟨13388588879820457585647553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71405807359042440456786949 13388588879820457585647553)
            ·
              refine ⟨10041441659865343189235665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13388588879820457585647553 10041441659865343189235665)
              ·
                refine ⟨7531081244899007391926749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10041441659865343189235665 7531081244899007391926749)
                ·
                  refine ⟨2824155466837127771972531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7531081244899007391926749 2824155466837127771972531)
                  ·
                    refine ⟨4236233200255691657958797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2824155466837127771972531 4236233200255691657958797)
                    ·
                      refine ⟨1588587450095884371734549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4236233200255691657958797 1588587450095884371734549)
                      ·
                        rfl

theorem cell23_3093763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 2, 3, 1, 3].length) (baseStart_3093763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3093763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3093763 prefixEnd_3093763 := by exact prefixLift 3093763
  have htrace : WordTrace (prefixWord ++ tailWord_3093763) baseStart_3093763 baseEnd_3093763 := by
    simpa [prefixWord, tailWord_3093763, baseEnd_3093763] using wordTrace_append hprefix tailTrace_3093763
  have hstable : (prefixWord ++ tailWord_3093763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3093763).length < 2 ^ (prefixWord ++ tailWord_3093763).sum := by decide
  have hdescent : baseEnd_3093763 < baseStart_3093763 := by decide
  rcases family_descends (prefixWord ++ tailWord_3093763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3093803 : List Nat := [1, 1, 1, 1, 2, 1, 2, 1, 9, 2, 2]
def baseStart_3093803 : Nat := 118140960795 + 3093803 * 2 ^ 59
def prefixEnd_3093803 : Nat := 4983230072969 + 3 ^ 40 * 3093803 * 2
def baseEnd_3093803 : Nat := 1588607989322064215234365

theorem tailTrace_3093803 : CollatzResearch.WordTrace tailWord_3093803 prefixEnd_3093803 1588607989322064215234365 := by
  unfold tailWord_3093803
  simp only [CollatzResearch.WordTrace]
  refine ⟨112840265610687585331070063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75226843740458390220713375 112840265610687585331070063)
  ·
    refine ⟨169260398416031377996605095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112840265610687585331070063 169260398416031377996605095)
    ·
      refine ⟨253890597624047066994907643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169260398416031377996605095 253890597624047066994907643)
      ·
        refine ⟨380835896436070600492361465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253890597624047066994907643 380835896436070600492361465)
        ·
          refine ⟨285626922327052950369271099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 380835896436070600492361465 285626922327052950369271099)
          ·
            refine ⟨428440383490579425553906649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 285626922327052950369271099 428440383490579425553906649)
            ·
              refine ⟨321330287617934569165429987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 428440383490579425553906649 321330287617934569165429987)
              ·
                refine ⟨481995431426901853748144981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 321330287617934569165429987 481995431426901853748144981)
                ·
                  refine ⟨2824191981017003049305537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 481995431426901853748144981 2824191981017003049305537)
                  ·
                    refine ⟨2118143985762752286979153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2824191981017003049305537 2118143985762752286979153)
                    ·
                      refine ⟨1588607989322064215234365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2118143985762752286979153 1588607989322064215234365)
                      ·
                        rfl

theorem cell23_3093803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 9, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 9, 2, 2].length) (baseStart_3093803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3093803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3093803 prefixEnd_3093803 := by exact prefixLift 3093803
  have htrace : WordTrace (prefixWord ++ tailWord_3093803) baseStart_3093803 baseEnd_3093803 := by
    simpa [prefixWord, tailWord_3093803, baseEnd_3093803] using wordTrace_append hprefix tailTrace_3093803
  have hstable : (prefixWord ++ tailWord_3093803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3093803).length < 2 ^ (prefixWord ++ tailWord_3093803).sum := by decide
  have hdescent : baseEnd_3093803 < baseStart_3093803 := by decide
  rcases family_descends (prefixWord ++ tailWord_3093803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3093816 : List Nat := [2, 1, 2, 1, 3, 1, 1, 5, 1, 2, 4]
def baseStart_3093816 : Nat := 118140960795 + 3093816 * 2 ^ 59
def prefixEnd_3093816 : Nat := 4983230072969 + 3 ^ 40 * 3093816 * 2
def baseEnd_3093816 : Nat := 1588614664570572664371805

theorem tailTrace_3093816 : CollatzResearch.WordTrace tailWord_3093816 prefixEnd_3093816 1588614664570572664371805 := by
  unfold tailWord_3093816
  simp only [CollatzResearch.WordTrace]
  refine ⟨56420369879820244275646651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75227159839760325700862201 56420369879820244275646651)
  ·
    refine ⟨84630554819730366413469977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56420369879820244275646651 84630554819730366413469977)
    ·
      refine ⟨63472916114797774810102483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84630554819730366413469977 63472916114797774810102483)
      ·
        refine ⟨95209374172196662215153725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63472916114797774810102483 95209374172196662215153725)
        ·
          refine ⟨35703515314573748330682647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95209374172196662215153725 35703515314573748330682647)
          ·
            refine ⟨53555272971860622496023971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35703515314573748330682647 53555272971860622496023971)
            ·
              refine ⟨80332909457790933744035957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53555272971860622496023971 80332909457790933744035957)
              ·
                refine ⟨7531210261667900038503371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 80332909457790933744035957 7531210261667900038503371)
                ·
                  refine ⟨11296815392501850057755057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7531210261667900038503371 11296815392501850057755057)
                  ·
                    refine ⟨8472611544376387543316293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11296815392501850057755057 8472611544376387543316293)
                    ·
                      refine ⟨1588614664570572664371805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8472611544376387543316293 1588614664570572664371805)
                      ·
                        rfl

theorem cell23_3093816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 5, 1, 2, 4].length) (baseStart_3093816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3093816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3093816 prefixEnd_3093816 := by exact prefixLift 3093816
  have htrace : WordTrace (prefixWord ++ tailWord_3093816) baseStart_3093816 baseEnd_3093816 := by
    simpa [prefixWord, tailWord_3093816, baseEnd_3093816] using wordTrace_append hprefix tailTrace_3093816
  have hstable : (prefixWord ++ tailWord_3093816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3093816).length < 2 ^ (prefixWord ++ tailWord_3093816).sum := by decide
  have hdescent : baseEnd_3093816 < baseStart_3093816 := by decide
  rcases family_descends (prefixWord ++ tailWord_3093816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3093817 : List Nat := [1, 2, 1, 6, 3, 1, 1, 2, 1, 5]
def baseStart_3093817 : Nat := 118140960795 + 3093817 * 2 ^ 59
def prefixEnd_3093817 : Nat := 4983230072969 + 3 ^ 40 * 3093817 * 2
def baseEnd_3093817 : Nat := 529538392683742386819767

theorem tailTrace_3093817 : CollatzResearch.WordTrace tailWord_3093817 prefixEnd_3093817 529538392683742386819767 := by
  unfold tailWord_3093817
  simp only [CollatzResearch.WordTrace]
  refine ⟨112840776232636865722079705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75227184155091243814719803 112840776232636865722079705)
  ·
    refine ⟨84630582174477649291559779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112840776232636865722079705 84630582174477649291559779)
    ·
      refine ⟨126945873261716473937339669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84630582174477649291559779 126945873261716473937339669)
      ·
        refine ⟨5950587809142959715812797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 126945873261716473937339669 5950587809142959715812797)
        ·
          refine ⟨2231470428428609893429799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5950587809142959715812797 2231470428428609893429799)
          ·
            refine ⟨3347205642642914840144699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2231470428428609893429799 3347205642642914840144699)
            ·
              refine ⟨5020808463964372260217049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3347205642642914840144699 5020808463964372260217049)
              ·
                refine ⟨3765606347973279195162787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5020808463964372260217049 3765606347973279195162787)
                ·
                  refine ⟨5648409521959918792744181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3765606347973279195162787 5648409521959918792744181)
                  ·
                    refine ⟨529538392683742386819767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5648409521959918792744181 529538392683742386819767)
                    ·
                      rfl

theorem cell23_3093817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 1, 2, 1, 5].length) (baseStart_3093817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3093817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3093817 prefixEnd_3093817 := by exact prefixLift 3093817
  have htrace : WordTrace (prefixWord ++ tailWord_3093817) baseStart_3093817 baseEnd_3093817 := by
    simpa [prefixWord, tailWord_3093817, baseEnd_3093817] using wordTrace_append hprefix tailTrace_3093817
  have hstable : (prefixWord ++ tailWord_3093817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3093817).length < 2 ^ (prefixWord ++ tailWord_3093817).sum := by decide
  have hdescent : baseEnd_3093817 < baseStart_3093817 := by decide
  rcases family_descends (prefixWord ++ tailWord_3093817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3093820 : List Nat := [2, 2, 2, 2, 1, 5, 1, 2, 1, 1, 4]
def baseStart_3093820 : Nat := 118140960795 + 3093820 * 2 ^ 59
def prefixEnd_3093820 : Nat := 4983230072969 + 3 ^ 40 * 3093820 * 2
def baseEnd_3093820 : Nat := 1588616718493190648721787

theorem tailTrace_3093820 : CollatzResearch.WordTrace tailWord_3093820 prefixEnd_3093820 1588616718493190648721787 := by
  unfold tailWord_3093820
  simp only [CollatzResearch.WordTrace]
  refine ⟨56420442825812998617219457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75227257101083998156292609 56420442825812998617219457)
  ·
    refine ⟨42315332119359748962914593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56420442825812998617219457 42315332119359748962914593)
    ·
      refine ⟨31736499089519811722185945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42315332119359748962914593 31736499089519811722185945)
      ·
        refine ⟨23802374317139858791639459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31736499089519811722185945 23802374317139858791639459)
        ·
          refine ⟨35703561475709788187459189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23802374317139858791639459 35703561475709788187459189)
          ·
            refine ⟨3347208888347792642574299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 35703561475709788187459189 3347208888347792642574299)
            ·
              refine ⟨5020813332521688963861449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3347208888347792642574299 5020813332521688963861449)
              ·
                refine ⟨3765609999391266722896087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5020813332521688963861449 3765609999391266722896087)
                ·
                  refine ⟨5648414999086900084344131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3765609999391266722896087 5648414999086900084344131)
                  ·
                    refine ⟨8472622498630350126516197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5648414999086900084344131 8472622498630350126516197)
                    ·
                      refine ⟨1588616718493190648721787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8472622498630350126516197 1588616718493190648721787)
                      ·
                        rfl

theorem cell23_3093820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 1, 2, 1, 1, 4].length) (baseStart_3093820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3093820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3093820 prefixEnd_3093820 := by exact prefixLift 3093820
  have htrace : WordTrace (prefixWord ++ tailWord_3093820) baseStart_3093820 baseEnd_3093820 := by
    simpa [prefixWord, tailWord_3093820, baseEnd_3093820] using wordTrace_append hprefix tailTrace_3093820
  have hstable : (prefixWord ++ tailWord_3093820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3093820).length < 2 ^ (prefixWord ++ tailWord_3093820).sum := by decide
  have hdescent : baseEnd_3093820 < baseStart_3093820 := by decide
  rcases family_descends (prefixWord ++ tailWord_3093820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3093823 : List Nat := [1, 1, 2, 2, 4, 3, 1, 1, 3, 2, 3]
def baseStart_3093823 : Nat := 118140960795 + 3093823 * 2 ^ 59
def prefixEnd_3093823 : Nat := 4983230072969 + 3 ^ 40 * 3093823 * 2
def baseEnd_3093823 : Nat := 1588618258935154136984273

theorem tailTrace_3093823 : CollatzResearch.WordTrace tailWord_3093823 prefixEnd_3093823 1588618258935154136984273 := by
  unfold tailWord_3093823
  simp only [CollatzResearch.WordTrace]
  refine ⟨112840995070615128746798123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75227330047076752497865415 112840995070615128746798123)
  ·
    refine ⟨169261492605922693120197185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112840995070615128746798123 169261492605922693120197185)
    ·
      refine ⟨126946119454442019840147889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169261492605922693120197185 126946119454442019840147889)
      ·
        refine ⟨95209589590831514880110917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126946119454442019840147889 95209589590831514880110917)
        ·
          refine ⟨17851798048280909040020797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 95209589590831514880110917 17851798048280909040020797)
          ·
            refine ⟨6694424268105340890007799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17851798048280909040020797 6694424268105340890007799)
            ·
              refine ⟨10041636402158011335011699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6694424268105340890007799 10041636402158011335011699)
              ·
                refine ⟨15062454603237017002517549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10041636402158011335011699 15062454603237017002517549)
                ·
                  refine ⟨5648420476213881375944081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15062454603237017002517549 5648420476213881375944081)
                  ·
                    refine ⟨4236315357160411031958061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5648420476213881375944081 4236315357160411031958061)
                    ·
                      refine ⟨1588618258935154136984273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4236315357160411031958061 1588618258935154136984273)
                      ·
                        rfl

theorem cell23_3093823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 1, 3, 2, 3].length) (baseStart_3093823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3093823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3093823 prefixEnd_3093823 := by exact prefixLift 3093823
  have htrace : WordTrace (prefixWord ++ tailWord_3093823) baseStart_3093823 baseEnd_3093823 := by
    simpa [prefixWord, tailWord_3093823, baseEnd_3093823] using wordTrace_append hprefix tailTrace_3093823
  have hstable : (prefixWord ++ tailWord_3093823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3093823).length < 2 ^ (prefixWord ++ tailWord_3093823).sum := by decide
  have hdescent : baseEnd_3093823 < baseStart_3093823 := by decide
  rcases family_descends (prefixWord ++ tailWord_3093823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3093840 : List Nat := [2, 1, 1, 1, 1, 5, 5, 1, 1, 2, 3]
def baseStart_3093840 : Nat := 118140960795 + 3093840 * 2 ^ 59
def prefixEnd_3093840 : Nat := 4983230072969 + 3 ^ 40 * 3093840 * 2
def baseEnd_3093840 : Nat := 1588626988106280570471695

theorem tailTrace_3093840 : CollatzResearch.WordTrace tailWord_3093840 prefixEnd_3093840 1588626988106280570471695 := by
  unfold tailWord_3093840
  simp only [CollatzResearch.WordTrace]
  refine ⟨56420807555776770325083487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75227743407702360433444649 56420807555776770325083487)
  ·
    refine ⟨84631211333665155487625231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56420807555776770325083487 84631211333665155487625231)
    ·
      refine ⟨126946817000497733231437847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84631211333665155487625231 126946817000497733231437847)
      ·
        refine ⟨190420225500746599847156771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126946817000497733231437847 190420225500746599847156771)
        ·
          refine ⟨285630338251119899770735157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190420225500746599847156771 285630338251119899770735157)
          ·
            refine ⟨26777844211042490603506421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 285630338251119899770735157 26777844211042490603506421)
            ·
              refine ⟨2510422894785233494078727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26777844211042490603506421 2510422894785233494078727)
              ·
                refine ⟨3765634342177850241118091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2510422894785233494078727 3765634342177850241118091)
                ·
                  refine ⟨5648451513266775361677137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3765634342177850241118091 5648451513266775361677137)
                  ·
                    refine ⟨4236338634950081521257853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5648451513266775361677137 4236338634950081521257853)
                    ·
                      refine ⟨1588626988106280570471695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4236338634950081521257853 1588626988106280570471695)
                      ·
                        rfl

theorem cell23_3093840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 5, 1, 1, 2, 3].length) (baseStart_3093840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3093840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3093840 prefixEnd_3093840 := by exact prefixLift 3093840
  have htrace : WordTrace (prefixWord ++ tailWord_3093840) baseStart_3093840 baseEnd_3093840 := by
    simpa [prefixWord, tailWord_3093840, baseEnd_3093840] using wordTrace_append hprefix tailTrace_3093840
  have hstable : (prefixWord ++ tailWord_3093840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3093840).length < 2 ^ (prefixWord ++ tailWord_3093840).sum := by decide
  have hdescent : baseEnd_3093840 < baseStart_3093840 := by decide
  rcases family_descends (prefixWord ++ tailWord_3093840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3093856 : List Nat := [2, 1, 1, 3, 4, 1, 1, 1, 2, 7]
def baseStart_3093856 : Nat := 118140960795 + 3093856 * 2 ^ 59
def prefixEnd_3093856 : Nat := 4983230072969 + 3 ^ 40 * 3093856 * 2
def baseEnd_3093856 : Nat := 529545067932250835957207

theorem tailTrace_3093856 : CollatzResearch.WordTrace tailWord_3093856 prefixEnd_3093856 529545067932250835957207 := by
  unfold tailWord_3093856
  simp only [CollatzResearch.WordTrace]
  refine ⟨56421099339747787691374711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75228132452997050255166281 56421099339747787691374711)
  ·
    refine ⟨84631649009621681537062067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56421099339747787691374711 84631649009621681537062067)
    ·
      refine ⟨126947473514432522305593101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84631649009621681537062067 126947473514432522305593101)
      ·
        refine ⟨47605302567912195864597413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126947473514432522305593101 47605302567912195864597413)
        ·
          refine ⟨8925994231483536724612015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47605302567912195864597413 8925994231483536724612015)
          ·
            refine ⟨13388991347225305086918023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8925994231483536724612015 13388991347225305086918023)
            ·
              refine ⟨20083487020837957630377035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13388991347225305086918023 20083487020837957630377035)
              ·
                refine ⟨30125230531256936445565553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20083487020837957630377035 30125230531256936445565553)
                ·
                  refine ⟨22593922898442702334174165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30125230531256936445565553 22593922898442702334174165)
                  ·
                    refine ⟨529545067932250835957207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22593922898442702334174165 529545067932250835957207)
                    ·
                      rfl

theorem cell23_3093856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 1, 2, 7].length) (baseStart_3093856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3093856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3093856 prefixEnd_3093856 := by exact prefixLift 3093856
  have htrace : WordTrace (prefixWord ++ tailWord_3093856) baseStart_3093856 baseEnd_3093856 := by
    simpa [prefixWord, tailWord_3093856, baseEnd_3093856] using wordTrace_append hprefix tailTrace_3093856
  have hstable : (prefixWord ++ tailWord_3093856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3093856).length < 2 ^ (prefixWord ++ tailWord_3093856).sum := by decide
  have hdescent : baseEnd_3093856 < baseStart_3093856 := by decide
  rcases family_descends (prefixWord ++ tailWord_3093856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3093897 : List Nat := [1, 2, 1, 1, 7, 1, 1, 3, 1, 3, 2]
def baseStart_3093897 : Nat := 118140960795 + 3093897 * 2 ^ 59
def prefixEnd_3093897 : Nat := 4983230072969 + 3 ^ 40 * 3093897 * 2
def baseEnd_3093897 : Nat := 1588656256503586847458933

theorem tailTrace_3093897 : CollatzResearch.WordTrace tailWord_3093897 prefixEnd_3093897 1588656256503586847458933 := by
  unfold tailWord_3093897
  simp only [CollatzResearch.WordTrace]
  refine ⟨112843694072347039384991945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75229129381564692923327963 112843694072347039384991945)
  ·
    refine ⟨84632770554260279538743959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112843694072347039384991945 84632770554260279538743959)
    ·
      refine ⟨126949155831390419308115939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84632770554260279538743959 126949155831390419308115939)
      ·
        refine ⟨190423733747085628962173909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126949155831390419308115939 190423733747085628962173909)
        ·
          refine ⟨4463056259697319428800951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 190423733747085628962173909 4463056259697319428800951)
          ·
            refine ⟨6694584389545979143201427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4463056259697319428800951 6694584389545979143201427)
            ·
              refine ⟨10041876584318968714802141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6694584389545979143201427 10041876584318968714802141)
              ·
                refine ⟨3765703719119613268050803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10041876584318968714802141 3765703719119613268050803)
                ·
                  refine ⟨5648555578679419902076205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3765703719119613268050803 5648555578679419902076205)
                  ·
                    refine ⟨2118208342004782463278577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5648555578679419902076205 2118208342004782463278577)
                    ·
                      refine ⟨1588656256503586847458933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2118208342004782463278577 1588656256503586847458933)
                      ·
                        rfl

theorem cell23_3093897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 3, 1, 3, 2].length) (baseStart_3093897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3093897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3093897 prefixEnd_3093897 := by exact prefixLift 3093897
  have htrace : WordTrace (prefixWord ++ tailWord_3093897) baseStart_3093897 baseEnd_3093897 := by
    simpa [prefixWord, tailWord_3093897, baseEnd_3093897] using wordTrace_append hprefix tailTrace_3093897
  have hstable : (prefixWord ++ tailWord_3093897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3093897).length < 2 ^ (prefixWord ++ tailWord_3093897).sum := by decide
  have hdescent : baseEnd_3093897 < baseStart_3093897 := by decide
  rcases family_descends (prefixWord ++ tailWord_3093897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3093973 : List Nat := [1, 3, 2, 3, 1, 1, 3, 1, 1, 2, 5]
def baseStart_3093973 : Nat := 118140960795 + 3093973 * 2 ^ 59
def prefixEnd_3093973 : Nat := 4983230072969 + 3 ^ 40 * 3093973 * 2
def baseEnd_3093973 : Nat := 1588695281033328550108583

theorem tailTrace_3093973 : CollatzResearch.WordTrace tailWord_3093973 prefixEnd_3093973 1588695281033328550108583 := by
  unfold tailWord_3093973
  simp only [CollatzResearch.WordTrace]
  refine ⟨112846466020071704364758573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75230977346714469576505715 112846466020071704364758573)
  ·
    refine ⟨42317424757526889136784465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112846466020071704364758573 42317424757526889136784465)
    ·
      refine ⟨31738068568145166852588349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42317424757526889136784465 31738068568145166852588349)
      ·
        refine ⟨11901775713054437569720631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31738068568145166852588349 11901775713054437569720631)
        ·
          refine ⟨17852663569581656354580947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11901775713054437569720631 17852663569581656354580947)
          ·
            refine ⟨26778995354372484531871421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17852663569581656354580947 26778995354372484531871421)
            ·
              refine ⟨10042123257889681699451783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26778995354372484531871421 10042123257889681699451783)
              ·
                refine ⟨15063184886834522549177675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10042123257889681699451783 15063184886834522549177675)
                ·
                  refine ⟨22594777330251783823766513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15063184886834522549177675 22594777330251783823766513)
                  ·
                    refine ⟨16946082997688837867824885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22594777330251783823766513 16946082997688837867824885)
                    ·
                      refine ⟨1588695281033328550108583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16946082997688837867824885 1588695281033328550108583)
                      ·
                        rfl

theorem cell23_3093973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 1, 1, 2, 5].length) (baseStart_3093973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3093973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3093973 prefixEnd_3093973 := by exact prefixLift 3093973
  have htrace : WordTrace (prefixWord ++ tailWord_3093973) baseStart_3093973 baseEnd_3093973 := by
    simpa [prefixWord, tailWord_3093973, baseEnd_3093973] using wordTrace_append hprefix tailTrace_3093973
  have hstable : (prefixWord ++ tailWord_3093973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3093973).length < 2 ^ (prefixWord ++ tailWord_3093973).sum := by decide
  have hdescent : baseEnd_3093973 < baseStart_3093973 := by decide
  rcases family_descends (prefixWord ++ tailWord_3093973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3093983 : List Nat := [1, 1, 2, 3, 3, 1, 1, 2, 4, 1, 4]
def baseStart_3093983 : Nat := 118140960795 + 3093983 * 2 ^ 59
def prefixEnd_3093983 : Nat := 4983230072969 + 3 ^ 40 * 3093983 * 2
def baseEnd_3093983 : Nat := 1588700415839873510983537

theorem tailTrace_3093983 : CollatzResearch.WordTrace tailWord_3093983 prefixEnd_3093983 1588700415839873510983537 := by
  unfold tailWord_3093983
  simp only [CollatzResearch.WordTrace]
  refine ⟨112846830750035476072622603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75231220500023650715081735 112846830750035476072622603)
  ·
    refine ⟨169270246125053214108933905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112846830750035476072622603 169270246125053214108933905)
    ·
      refine ⟨126952684593789910581700429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169270246125053214108933905 126952684593789910581700429)
      ·
        refine ⟨47607256722671216468137661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126952684593789910581700429 47607256722671216468137661)
        ·
          refine ⟨17852721271001706175551623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47607256722671216468137661 17852721271001706175551623)
          ·
            refine ⟨26779081906502559263327435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17852721271001706175551623 26779081906502559263327435)
            ·
              refine ⟨40168622859753838894991153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26779081906502559263327435 40168622859753838894991153)
              ·
                refine ⟨30126467144815379171243365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40168622859753838894991153 30126467144815379171243365)
                ·
                  refine ⟨5648712589652883594608131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30126467144815379171243365 5648712589652883594608131)
                  ·
                    refine ⟨8473068884479325391912197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5648712589652883594608131 8473068884479325391912197)
                    ·
                      refine ⟨1588700415839873510983537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8473068884479325391912197 1588700415839873510983537)
                      ·
                        rfl

theorem cell23_3093983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 2, 4, 1, 4].length) (baseStart_3093983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3093983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3093983 prefixEnd_3093983 := by exact prefixLift 3093983
  have htrace : WordTrace (prefixWord ++ tailWord_3093983) baseStart_3093983 baseEnd_3093983 := by
    simpa [prefixWord, tailWord_3093983, baseEnd_3093983] using wordTrace_append hprefix tailTrace_3093983
  have hstable : (prefixWord ++ tailWord_3093983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3093983).length < 2 ^ (prefixWord ++ tailWord_3093983).sum := by decide
  have hdescent : baseEnd_3093983 < baseStart_3093983 := by decide
  rcases family_descends (prefixWord ++ tailWord_3093983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3093997 : List Nat := [1, 5, 1, 3, 2, 1, 2, 1, 2, 5]
def baseStart_3093997 : Nat := 118140960795 + 3093997 * 2 ^ 59
def prefixEnd_3093997 : Nat := 4983230072969 + 3 ^ 40 * 3093997 * 2
def baseEnd_3093997 : Nat := 529569201523012152069491

theorem tailTrace_3093997 : CollatzResearch.WordTrace tailWord_3093997 prefixEnd_3093997 529569201523012152069491 := by
  unfold tailWord_3093997
  simp only [CollatzResearch.WordTrace]
  refine ⟨112847341371984756463632245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75231560914656504309088163 112847341371984756463632245)
  ·
    refine ⟨10579438253623570918465523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 112847341371984756463632245 10579438253623570918465523)
    ·
      refine ⟨15869157380435356377698285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10579438253623570918465523 15869157380435356377698285)
      ·
        refine ⟨5950934017663258641636857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15869157380435356377698285 5950934017663258641636857)
        ·
          refine ⟨4463200513247443981227643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5950934017663258641636857 4463200513247443981227643)
          ·
            refine ⟨6694800769871165971841465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4463200513247443981227643 6694800769871165971841465)
            ·
              refine ⟨5021100577403374478881099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6694800769871165971841465 5021100577403374478881099)
              ·
                refine ⟨7531650866105061718321649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5021100577403374478881099 7531650866105061718321649)
                ·
                  refine ⟨5648738149578796288741237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7531650866105061718321649 5648738149578796288741237)
                  ·
                    refine ⟨529569201523012152069491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5648738149578796288741237 529569201523012152069491)
                    ·
                      rfl

theorem cell23_3093997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 2, 1, 2, 5].length) (baseStart_3093997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3093997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3093997 prefixEnd_3093997 := by exact prefixLift 3093997
  have htrace : WordTrace (prefixWord ++ tailWord_3093997) baseStart_3093997 baseEnd_3093997 := by
    simpa [prefixWord, tailWord_3093997, baseEnd_3093997] using wordTrace_append hprefix tailTrace_3093997
  have hstable : (prefixWord ++ tailWord_3093997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3093997).length < 2 ^ (prefixWord ++ tailWord_3093997).sum := by decide
  have hdescent : baseEnd_3093997 < baseStart_3093997 := by decide
  rcases family_descends (prefixWord ++ tailWord_3093997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3094000 : List Nat := [2, 1, 1, 1, 3, 5, 2, 1, 2, 1, 4]
def baseStart_3094000 : Nat := 118140960795 + 3094000 * 2 ^ 59
def prefixEnd_3094000 : Nat := 4983230072969 + 3 ^ 40 * 3094000 * 2
def baseEnd_3094000 : Nat := 1588709145010999944470959

theorem tailTrace_3094000 : CollatzResearch.WordTrace tailWord_3094000 prefixEnd_3094000 1588709145010999944470959 := by
  unfold tailWord_3094000
  simp only [CollatzResearch.WordTrace]
  refine ⟨56423725395486943987995727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75231633860649258650660969 56423725395486943987995727)
  ·
    refine ⟨84635588093230415981993591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56423725395486943987995727 84635588093230415981993591)
    ·
      refine ⟨126953382139845623972990387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84635588093230415981993591 126953382139845623972990387)
      ·
        refine ⟨190430073209768435959485581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126953382139845623972990387 190430073209768435959485581)
        ·
          refine ⟨71411277453663163484807093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 190430073209768435959485581 71411277453663163484807093)
          ·
            refine ⟨6694807261280921576700665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 71411277453663163484807093 6694807261280921576700665)
            ·
              refine ⟨5021105445960691182525499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6694807261280921576700665 5021105445960691182525499)
              ·
                refine ⟨7531658168941036773788249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5021105445960691182525499 7531658168941036773788249)
                ·
                  refine ⟨5648743626705777580341187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7531658168941036773788249 5648743626705777580341187)
                  ·
                    refine ⟨8473115440058666370511781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5648743626705777580341187 8473115440058666370511781)
                    ·
                      refine ⟨1588709145010999944470959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8473115440058666370511781 1588709145010999944470959)
                      ·
                        rfl

theorem cell23_3094000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 2, 1, 2, 1, 4].length) (baseStart_3094000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3094000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3094000 prefixEnd_3094000 := by exact prefixLift 3094000
  have htrace : WordTrace (prefixWord ++ tailWord_3094000) baseStart_3094000 baseEnd_3094000 := by
    simpa [prefixWord, tailWord_3094000, baseEnd_3094000] using wordTrace_append hprefix tailTrace_3094000
  have hstable : (prefixWord ++ tailWord_3094000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3094000).length < 2 ^ (prefixWord ++ tailWord_3094000).sum := by decide
  have hdescent : baseEnd_3094000 < baseStart_3094000 := by decide
  rcases family_descends (prefixWord ++ tailWord_3094000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3094113 : List Nat := [1, 2, 3, 1, 1, 3, 3, 9]
def baseStart_3094113 : Nat := 118140960795 + 3094113 * 2 ^ 59
def prefixEnd_3094113 : Nat := 4983230072969 + 3 ^ 40 * 3094113 * 2
def baseEnd_3094113 : Nat := 58843228456479926013257

theorem tailTrace_3094113 : CollatzResearch.WordTrace tailWord_3094113 prefixEnd_3094113 58843228456479926013257 := by
  unfold tailWord_3094113
  simp only [CollatzResearch.WordTrace]
  refine ⟨112851572239564508274854993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75234381493043005516569995 112851572239564508274854993)
  ·
    refine ⟨84638679179673381206141245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112851572239564508274854993 84638679179673381206141245)
    ·
      refine ⟨31739504692377517952302967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84638679179673381206141245 31739504692377517952302967)
      ·
        refine ⟨47609257038566276928454451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31739504692377517952302967 47609257038566276928454451)
        ·
          refine ⟨71413885557849415392681677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47609257038566276928454451 71413885557849415392681677)
          ·
            refine ⟨26780207084193530772255629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71413885557849415392681677 26780207084193530772255629)
            ·
              refine ⟨10042577656572574039595861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26780207084193530772255629 10042577656572574039595861)
              ·
                refine ⟨58843228456479926013257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10042577656572574039595861 58843228456479926013257)
                ·
                  rfl

theorem cell23_3094113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 9].length) (baseStart_3094113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3094113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3094113 prefixEnd_3094113 := by exact prefixLift 3094113
  have htrace : WordTrace (prefixWord ++ tailWord_3094113) baseStart_3094113 baseEnd_3094113 := by
    simpa [prefixWord, tailWord_3094113, baseEnd_3094113] using wordTrace_append hprefix tailTrace_3094113
  have hstable : (prefixWord ++ tailWord_3094113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3094113).length < 2 ^ (prefixWord ++ tailWord_3094113).sum := by decide
  have hdescent : baseEnd_3094113 < baseStart_3094113 := by decide
  rcases family_descends (prefixWord ++ tailWord_3094113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3094130 : List Nat := [3, 2, 1, 2, 3, 3, 9]
def baseStart_3094130 : Nat := 118140960795 + 3094130 * 2 ^ 59
def prefixEnd_3094130 : Nat := 4983230072969 + 3 ^ 40 * 3094130 * 2
def baseEnd_3094130 : Nat := 19614517253038079454881

theorem tailTrace_3094130 : CollatzResearch.WordTrace tailWord_3094130 prefixEnd_3094130 19614517253038079454881 := by
  unfold tailWord_3094130
  simp only [CollatzResearch.WordTrace]
  refine ⟨28213048070125730044555961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75234794853668613452149229 28213048070125730044555961)
  ·
    refine ⟨21159786052594297533416971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28213048070125730044555961 21159786052594297533416971)
    ·
      refine ⟨31739679078891446300125457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21159786052594297533416971 31739679078891446300125457)
      ·
        refine ⟨23804759309168584725094093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31739679078891446300125457 23804759309168584725094093)
        ·
          refine ⟨8926784740938219271910285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23804759309168584725094093 8926784740938219271910285)
          ·
            refine ⟨3347544277851832226966357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8926784740938219271910285 3347544277851832226966357)
            ·
              refine ⟨19614517253038079454881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3347544277851832226966357 19614517253038079454881)
              ·
                rfl

theorem cell23_3094130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 9].length) (baseStart_3094130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3094130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3094130 prefixEnd_3094130 := by exact prefixLift 3094130
  have htrace : WordTrace (prefixWord ++ tailWord_3094130) baseStart_3094130 baseEnd_3094130 := by
    simpa [prefixWord, tailWord_3094130, baseEnd_3094130] using wordTrace_append hprefix tailTrace_3094130
  have hstable : (prefixWord ++ tailWord_3094130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3094130).length < 2 ^ (prefixWord ++ tailWord_3094130).sum := by decide
  have hdescent : baseEnd_3094130 < baseStart_3094130 := by decide
  rcases family_descends (prefixWord ++ tailWord_3094130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3094141 : List Nat := [1, 4, 1, 1, 4, 3, 1, 1, 3, 2, 2]
def baseStart_3094141 : Nat := 118140960795 + 3094141 * 2 ^ 59
def prefixEnd_3094141 : Nat := 4983230072969 + 3 ^ 40 * 3094141 * 2
def baseEnd_3094141 : Nat := 1588781545783283892807811

theorem tailTrace_3094141 : CollatzResearch.WordTrace tailWord_3094141 prefixEnd_3094141 1588781545783283892807811 := by
  unfold tailWord_3094141
  simp only [CollatzResearch.WordTrace]
  refine ⟨112852593483463069056874277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75235062322308712704582851 112852593483463069056874277)
  ·
    refine ⟨21159861278149325448163927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 112852593483463069056874277 21159861278149325448163927)
    ·
      refine ⟨31739791917223988172245891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21159861278149325448163927 31739791917223988172245891)
      ·
        refine ⟨47609687875835982258368837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31739791917223988172245891 47609687875835982258368837)
        ·
          refine ⟨8926816476719246673444157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47609687875835982258368837 8926816476719246673444157)
          ·
            refine ⟨3347556178769717502541559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8926816476719246673444157 3347556178769717502541559)
            ·
              refine ⟨5021334268154576253812339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3347556178769717502541559 5021334268154576253812339)
              ·
                refine ⟨7532001402231864380718509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5021334268154576253812339 7532001402231864380718509)
                ·
                  refine ⟨2824500525836949142769441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7532001402231864380718509 2824500525836949142769441)
                  ·
                    refine ⟨2118375394377711857077081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2824500525836949142769441 2118375394377711857077081)
                    ·
                      refine ⟨1588781545783283892807811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2118375394377711857077081 1588781545783283892807811)
                      ·
                        rfl

theorem cell23_3094141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 1, 1, 3, 2, 2].length) (baseStart_3094141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3094141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3094141 prefixEnd_3094141 := by exact prefixLift 3094141
  have htrace : WordTrace (prefixWord ++ tailWord_3094141) baseStart_3094141 baseEnd_3094141 := by
    simpa [prefixWord, tailWord_3094141, baseEnd_3094141] using wordTrace_append hprefix tailTrace_3094141
  have hstable : (prefixWord ++ tailWord_3094141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3094141).length < 2 ^ (prefixWord ++ tailWord_3094141).sum := by decide
  have hdescent : baseEnd_3094141 < baseStart_3094141 := by decide
  rcases family_descends (prefixWord ++ tailWord_3094141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3094174 : List Nat := [4, 3, 1, 1, 1, 3, 1, 2, 1, 3, 3]
def baseStart_3094174 : Nat := 118140960795 + 3094174 * 2 ^ 59
def prefixEnd_3094174 : Nat := 4983230072969 + 3 ^ 40 * 3094174 * 2
def baseEnd_3094174 : Nat := 1588798490644882263695159

theorem tailTrace_3094174 : CollatzResearch.WordTrace tailWord_3094174 prefixEnd_3094174 1588798490644882263695159 := by
  unfold tailWord_3094174
  simp only [CollatzResearch.WordTrace]
  refine ⟨14106724636542939461603197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75235864728229010461883717 14106724636542939461603197)
  ·
    refine ⟨5290021738703602298101199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14106724636542939461603197 5290021738703602298101199)
    ·
      refine ⟨7935032608055403447151799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5290021738703602298101199 7935032608055403447151799)
      ·
        refine ⟨11902548912083105170727699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7935032608055403447151799 11902548912083105170727699)
        ·
          refine ⟨17853823368124657756091549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11902548912083105170727699 17853823368124657756091549)
          ·
            refine ⟨6695183763046746658534331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17853823368124657756091549 6695183763046746658534331)
            ·
              refine ⟨10042775644570119987801497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6695183763046746658534331 10042775644570119987801497)
              ·
                refine ⟨7532081733427589990851123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10042775644570119987801497 7532081733427589990851123)
                ·
                  refine ⟨11298122600141384986276685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7532081733427589990851123 11298122600141384986276685)
                  ·
                    refine ⟨4236795975053019369853757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11298122600141384986276685 4236795975053019369853757)
                    ·
                      refine ⟨1588798490644882263695159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4236795975053019369853757 1588798490644882263695159)
                      ·
                        rfl

theorem cell23_3094174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 2, 1, 3, 3].length) (baseStart_3094174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3094174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3094174 prefixEnd_3094174 := by exact prefixLift 3094174
  have htrace : WordTrace (prefixWord ++ tailWord_3094174) baseStart_3094174 baseEnd_3094174 := by
    simpa [prefixWord, tailWord_3094174, baseEnd_3094174] using wordTrace_append hprefix tailTrace_3094174
  have hstable : (prefixWord ++ tailWord_3094174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3094174).length < 2 ^ (prefixWord ++ tailWord_3094174).sum := by decide
  have hdescent : baseEnd_3094174 < baseStart_3094174 := by decide
  rcases family_descends (prefixWord ++ tailWord_3094174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3094178 : List Nat := [3, 3, 1, 4, 1, 1, 3, 1, 1, 2, 3]
def baseStart_3094178 : Nat := 118140960795 + 3094178 * 2 ^ 59
def prefixEnd_3094178 : Nat := 4983230072969 + 3 ^ 40 * 3094178 * 2
def baseEnd_3094178 : Nat := 1588800544567500248045141

theorem tailTrace_3094178 : CollatzResearch.WordTrace tailWord_3094178 prefixEnd_3094178 1588800544567500248045141 := by
  unfold tailWord_3094178
  simp only [CollatzResearch.WordTrace]
  refine ⟨28213485746082256093992797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75235961989552682917314125 28213485746082256093992797)
  ·
    refine ⟨10580057154780846035247299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28213485746082256093992797 10580057154780846035247299)
    ·
      refine ⟨15870085732171269052870949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10580057154780846035247299 15870085732171269052870949)
      ·
        refine ⟨2975641074782112947413303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15870085732171269052870949 2975641074782112947413303)
        ·
          refine ⟨4463461612173169421119955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2975641074782112947413303 4463461612173169421119955)
          ·
            refine ⟨6695192418259754131679933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4463461612173169421119955 6695192418259754131679933)
            ·
              refine ⟨2510697156847407799379975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6695192418259754131679933 2510697156847407799379975)
              ·
                refine ⟨3766045735271111699069963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2510697156847407799379975 3766045735271111699069963)
                ·
                  refine ⟨5649068602906667548604945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3766045735271111699069963 5649068602906667548604945)
                  ·
                    refine ⟨4236801452180000661453709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5649068602906667548604945 4236801452180000661453709)
                    ·
                      refine ⟨1588800544567500248045141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4236801452180000661453709 1588800544567500248045141)
                      ·
                        rfl

theorem cell23_3094178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 3, 1, 1, 2, 3].length) (baseStart_3094178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3094178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3094178 prefixEnd_3094178 := by exact prefixLift 3094178
  have htrace : WordTrace (prefixWord ++ tailWord_3094178) baseStart_3094178 baseEnd_3094178 := by
    simpa [prefixWord, tailWord_3094178, baseEnd_3094178] using wordTrace_append hprefix tailTrace_3094178
  have hstable : (prefixWord ++ tailWord_3094178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3094178).length < 2 ^ (prefixWord ++ tailWord_3094178).sum := by decide
  have hdescent : baseEnd_3094178 < baseStart_3094178 := by decide
  rcases family_descends (prefixWord ++ tailWord_3094178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3094203 : List Nat := [1, 1, 1, 1, 1, 2, 3, 2, 11]
def baseStart_3094203 : Nat := 118140960795 + 3094203 * 2 ^ 59
def prefixEnd_3094203 : Nat := 4983230072969 + 3 ^ 40 * 3094203 * 2
def baseEnd_3094203 : Nat := 176534820175984738914725

theorem tailTrace_3094203 : CollatzResearch.WordTrace tailWord_3094203 prefixEnd_3094203 176534820175984738914725 := by
  unfold tailWord_3094203
  simp only [CollatzResearch.WordTrace]
  refine ⟨112854854809238453645631263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75236569872825635763754175 112854854809238453645631263)
  ·
    refine ⟨169282282213857680468446895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112854854809238453645631263 169282282213857680468446895)
    ·
      refine ⟨253923423320786520702670343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169282282213857680468446895 253923423320786520702670343)
      ·
        refine ⟨380885134981179781054005515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253923423320786520702670343 380885134981179781054005515)
        ·
          refine ⟨571327702471769671581008273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 380885134981179781054005515 571327702471769671581008273)
          ·
            refine ⟨428495776853827253685756205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 571327702471769671581008273 428495776853827253685756205)
            ·
              refine ⟨160685916320185220132158577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 428495776853827253685756205 160685916320185220132158577)
              ·
                refine ⟨120514437240138915099118933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 160685916320185220132158577 120514437240138915099118933)
                ·
                  refine ⟨176534820175984738914725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 120514437240138915099118933 176534820175984738914725)
                  ·
                    rfl

theorem cell23_3094203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 2, 11].length) (baseStart_3094203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3094203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3094203 prefixEnd_3094203 := by exact prefixLift 3094203
  have htrace : WordTrace (prefixWord ++ tailWord_3094203) baseStart_3094203 baseEnd_3094203 := by
    simpa [prefixWord, tailWord_3094203, baseEnd_3094203] using wordTrace_append hprefix tailTrace_3094203
  have hstable : (prefixWord ++ tailWord_3094203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3094203).length < 2 ^ (prefixWord ++ tailWord_3094203).sum := by decide
  have hdescent : baseEnd_3094203 < baseStart_3094203 := by decide
  rcases family_descends (prefixWord ++ tailWord_3094203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3094248 : List Nat := [2, 1, 4, 1, 3, 3, 1, 2, 2, 2, 2]
def baseStart_3094248 : Nat := 118140960795 + 3094248 * 2 ^ 59
def prefixEnd_3094248 : Nat := 4983230072969 + 3 ^ 40 * 3094248 * 2
def baseEnd_3094248 : Nat := 1588836488213314974169819

theorem tailTrace_3094248 : CollatzResearch.WordTrace tailWord_3094248 prefixEnd_3094248 1588836488213314974169819 := by
  unfold tailWord_3094248
  simp only [CollatzResearch.WordTrace]
  refine ⟨56428248047037713165509699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75237664062716950887346265 56428248047037713165509699)
  ·
    refine ⟨84642372070556569748264549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56428248047037713165509699 84642372070556569748264549)
    ·
      refine ⟨15870444763229356827799603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 84642372070556569748264549 15870444763229356827799603)
      ·
        refine ⟨23805667144844035241699405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15870444763229356827799603 23805667144844035241699405)
        ·
          refine ⟨8927125179316513215637277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23805667144844035241699405 8927125179316513215637277)
          ·
            refine ⟨3347671942243692455863979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8927125179316513215637277 3347671942243692455863979)
            ·
              refine ⟨5021507913365538683795969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3347671942243692455863979 5021507913365538683795969)
              ·
                refine ⟨3766130935024154012846977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5021507913365538683795969 3766130935024154012846977)
                ·
                  refine ⟨2824598201268115509635233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3766130935024154012846977 2824598201268115509635233)
                  ·
                    refine ⟨2118448650951086632226425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2824598201268115509635233 2118448650951086632226425)
                    ·
                      refine ⟨1588836488213314974169819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2118448650951086632226425 1588836488213314974169819)
                      ·
                        rfl

theorem cell23_3094248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 1, 2, 2, 2, 2].length) (baseStart_3094248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3094248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3094248 prefixEnd_3094248 := by exact prefixLift 3094248
  have htrace : WordTrace (prefixWord ++ tailWord_3094248) baseStart_3094248 baseEnd_3094248 := by
    simpa [prefixWord, tailWord_3094248, baseEnd_3094248] using wordTrace_append hprefix tailTrace_3094248
  have hstable : (prefixWord ++ tailWord_3094248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3094248).length < 2 ^ (prefixWord ++ tailWord_3094248).sum := by decide
  have hdescent : baseEnd_3094248 < baseStart_3094248 := by decide
  rcases family_descends (prefixWord ++ tailWord_3094248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3094280 : List Nat := [2, 1, 3, 2, 2, 1, 1, 1, 2, 8]
def baseStart_3094280 : Nat := 118140960795 + 3094280 * 2 ^ 59
def prefixEnd_3094280 : Nat := 4983230072969 + 3 ^ 40 * 3094280 * 2
def baseEnd_3094280 : Nat := 529617639864752949656557

theorem tailTrace_3094280 : CollatzResearch.WordTrace tailWord_3094280 prefixEnd_3094280 529617639864752949656557 := by
  unfold tailWord_3094280
  simp only [CollatzResearch.WordTrace]
  refine ⟨56428831614979747898092147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75238442153306330530789529 56428831614979747898092147)
  ·
    refine ⟨84643247422469621847138221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56428831614979747898092147 84643247422469621847138221)
    ·
      refine ⟨31741217783426108192676833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84643247422469621847138221 31741217783426108192676833)
      ·
        refine ⟨23805913337569581144507625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31741217783426108192676833 23805913337569581144507625)
        ·
          refine ⟨17854435003177185858380719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23805913337569581144507625 17854435003177185858380719)
          ·
            refine ⟨26781652504765778787571079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17854435003177185858380719 26781652504765778787571079)
            ·
              refine ⟨40172478757148668181356619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26781652504765778787571079 40172478757148668181356619)
              ·
                refine ⟨60258718135723002272034929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40172478757148668181356619 60258718135723002272034929)
                ·
                  refine ⟨45194038601792251704026197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60258718135723002272034929 45194038601792251704026197)
                  ·
                    refine ⟨529617639864752949656557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 45194038601792251704026197 529617639864752949656557)
                    ·
                      rfl

theorem cell23_3094280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 1, 2, 8].length) (baseStart_3094280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3094280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3094280 prefixEnd_3094280 := by exact prefixLift 3094280
  have htrace : WordTrace (prefixWord ++ tailWord_3094280) baseStart_3094280 baseEnd_3094280 := by
    simpa [prefixWord, tailWord_3094280, baseEnd_3094280] using wordTrace_append hprefix tailTrace_3094280
  have hstable : (prefixWord ++ tailWord_3094280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3094280).length < 2 ^ (prefixWord ++ tailWord_3094280).sum := by decide
  have hdescent : baseEnd_3094280 < baseStart_3094280 := by decide
  rcases family_descends (prefixWord ++ tailWord_3094280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3094287 : List Nat := [1, 1, 2, 1, 1, 1, 4, 2, 4, 4, 2]
def baseStart_3094287 : Nat := 118140960795 + 3094287 * 2 ^ 59
def prefixEnd_3094287 : Nat := 4983230072969 + 3 ^ 40 * 3094287 * 2
def baseEnd_3094287 : Nat := 1588856513958840321582139

theorem tailTrace_3094287 : CollatzResearch.WordTrace tailWord_3094287 prefixEnd_3094287 1588856513958840321582139 := by
  unfold tailWord_3094287
  simp only [CollatzResearch.WordTrace]
  refine ⟨112857918540934135991689115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75238612360622757327792743 112857918540934135991689115)
  ·
    refine ⟨169286877811401203987533673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112857918540934135991689115 169286877811401203987533673)
    ·
      refine ⟨126965158358550902990650255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169286877811401203987533673 126965158358550902990650255)
      ·
        refine ⟨190447737537826354485975383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126965158358550902990650255 190447737537826354485975383)
        ·
          refine ⟨285671606306739531728963075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190447737537826354485975383 285671606306739531728963075)
          ·
            refine ⟨428507409460109297593444613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 285671606306739531728963075 428507409460109297593444613)
            ·
              refine ⟨80345139273770493298770865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 428507409460109297593444613 80345139273770493298770865)
              ·
                refine ⟨60258854455327869974078149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80345139273770493298770865 60258854455327869974078149)
                ·
                  refine ⟨11298535210373975620139653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60258854455327869974078149 11298535210373975620139653)
                  ·
                    refine ⟨2118475351945120428776185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11298535210373975620139653 2118475351945120428776185)
                    ·
                      refine ⟨1588856513958840321582139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2118475351945120428776185 1588856513958840321582139)
                      ·
                        rfl

theorem cell23_3094287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 2, 4, 4, 2].length) (baseStart_3094287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3094287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3094287 prefixEnd_3094287 := by exact prefixLift 3094287
  have htrace : WordTrace (prefixWord ++ tailWord_3094287) baseStart_3094287 baseEnd_3094287 := by
    simpa [prefixWord, tailWord_3094287, baseEnd_3094287] using wordTrace_append hprefix tailTrace_3094287
  have hstable : (prefixWord ++ tailWord_3094287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3094287).length < 2 ^ (prefixWord ++ tailWord_3094287).sum := by decide
  have hdescent : baseEnd_3094287 < baseStart_3094287 := by decide
  rcases family_descends (prefixWord ++ tailWord_3094287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3094307 : List Nat := [1, 1, 1, 4, 2, 1, 3, 1, 4, 2, 3]
def baseStart_3094307 : Nat := 118140960795 + 3094307 * 2 ^ 59
def prefixEnd_3094307 : Nat := 4983230072969 + 3 ^ 40 * 3094307 * 2
def baseEnd_3094307 : Nat := 1588866783571930243332047

theorem tailTrace_3094307 : CollatzResearch.WordTrace tailWord_3094307 prefixEnd_3094307 1588866783571930243332047 := by
  unfold tailWord_3094307
  simp only [CollatzResearch.WordTrace]
  refine ⟨112858648000861679407417175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75239098667241119604944783 112858648000861679407417175)
  ·
    refine ⟨169287972001292519111125763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112858648000861679407417175 169287972001292519111125763)
    ·
      refine ⟨253931958001938778666688645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169287972001292519111125763 253931958001938778666688645)
      ·
        refine ⟨47612242125363521000004121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 253931958001938778666688645 47612242125363521000004121)
        ·
          refine ⟨35709181594022640750003091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47612242125363521000004121 35709181594022640750003091)
          ·
            refine ⟨53563772391033961125004637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35709181594022640750003091 53563772391033961125004637)
            ·
              refine ⟨20086414646637735421876739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53563772391033961125004637 20086414646637735421876739)
              ·
                refine ⟨30129621969956603132815109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20086414646637735421876739 30129621969956603132815109)
                ·
                  refine ⟨5649304119366863087402833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30129621969956603132815109 5649304119366863087402833)
                  ·
                    refine ⟨4236978089525147315552125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5649304119366863087402833 4236978089525147315552125)
                    ·
                      refine ⟨1588866783571930243332047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4236978089525147315552125 1588866783571930243332047)
                      ·
                        rfl

theorem cell23_3094307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 1, 4, 2, 3].length) (baseStart_3094307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3094307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3094307 prefixEnd_3094307 := by exact prefixLift 3094307
  have htrace : WordTrace (prefixWord ++ tailWord_3094307) baseStart_3094307 baseEnd_3094307 := by
    simpa [prefixWord, tailWord_3094307, baseEnd_3094307] using wordTrace_append hprefix tailTrace_3094307
  have hstable : (prefixWord ++ tailWord_3094307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3094307).length < 2 ^ (prefixWord ++ tailWord_3094307).sum := by decide
  have hdescent : baseEnd_3094307 < baseStart_3094307 := by decide
  rcases family_descends (prefixWord ++ tailWord_3094307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3094387 : List Nat := [1, 1, 1, 2, 2, 1, 3, 2, 6, 4]
def baseStart_3094387 : Nat := 118140960795 + 3094387 * 2 ^ 59
def prefixEnd_3094387 : Nat := 4983230072969 + 3 ^ 40 * 3094387 * 2
def baseEnd_3094387 : Nat := 529635954008096643443893

theorem tailTrace_3094387 : CollatzResearch.WordTrace tailWord_3094387 prefixEnd_3094387 529635954008096643443893 := by
  unfold tailWord_3094387
  simp only [CollatzResearch.WordTrace]
  refine ⟨112861565840571853070329415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75241043893714568713552943 112861565840571853070329415)
  ·
    refine ⟨169292348760857779605494123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112861565840571853070329415 169292348760857779605494123)
    ·
      refine ⟨253938523141286669408241185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169292348760857779605494123 253938523141286669408241185)
      ·
        refine ⟨190453892355965002056180889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 253938523141286669408241185 190453892355965002056180889)
        ·
          refine ⟨142840419266973751542135667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 190453892355965002056180889 142840419266973751542135667)
          ·
            refine ⟨214260628900460627313203501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142840419266973751542135667 214260628900460627313203501)
            ·
              refine ⟨80347735837672735242451313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 214260628900460627313203501 80347735837672735242451313)
              ·
                refine ⟨60260801878254551431838485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80347735837672735242451313 60260801878254551431838485)
                ·
                  refine ⟨2824725088043182098367429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 60260801878254551431838485 2824725088043182098367429)
                  ·
                    refine ⟨529635954008096643443893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2824725088043182098367429 529635954008096643443893)
                    ·
                      rfl

theorem cell23_3094387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 2, 6, 4].length) (baseStart_3094387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3094387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3094387 prefixEnd_3094387 := by exact prefixLift 3094387
  have htrace : WordTrace (prefixWord ++ tailWord_3094387) baseStart_3094387 baseEnd_3094387 := by
    simpa [prefixWord, tailWord_3094387, baseEnd_3094387] using wordTrace_append hprefix tailTrace_3094387
  have hstable : (prefixWord ++ tailWord_3094387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3094387).length < 2 ^ (prefixWord ++ tailWord_3094387).sum := by decide
  have hdescent : baseEnd_3094387 < baseStart_3094387 := by decide
  rcases family_descends (prefixWord ++ tailWord_3094387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3094398 : List Nat := [4, 2, 3, 1, 1, 2, 1, 1, 1, 5, 2]
def baseStart_3094398 : Nat := 118140960795 + 3094398 * 2 ^ 59
def prefixEnd_3094398 : Nat := 4983230072969 + 3 ^ 40 * 3094398 * 2
def baseEnd_3094398 : Nat := 1588913510311489387294129

theorem tailTrace_3094398 : CollatzResearch.WordTrace tailWord_3094398 prefixEnd_3094398 1588913510311489387294129 := by
  unfold tailWord_3094398
  simp only [CollatzResearch.WordTrace]
  refine ⟨14107745880441500243622481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75241311362354667965986565 14107745880441500243622481)
  ·
    refine ⟨10580809410331125182716861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14107745880441500243622481 10580809410331125182716861)
    ·
      refine ⟨3967803528874171943518823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10580809410331125182716861 3967803528874171943518823)
      ·
        refine ⟨5951705293311257915278235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3967803528874171943518823 5951705293311257915278235)
        ·
          refine ⟨8927557939966886872917353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5951705293311257915278235 8927557939966886872917353)
          ·
            refine ⟨6695668454975165154688015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8927557939966886872917353 6695668454975165154688015)
            ·
              refine ⟨10043502682462747732032023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6695668454975165154688015 10043502682462747732032023)
              ·
                refine ⟨15065254023694121598048035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10043502682462747732032023 15065254023694121598048035)
                ·
                  refine ⟨22597881035541182397072053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15065254023694121598048035 22597881035541182397072053)
                  ·
                    refine ⟨2118551347081985849725505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22597881035541182397072053 2118551347081985849725505)
                    ·
                      refine ⟨1588913510311489387294129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2118551347081985849725505 1588913510311489387294129)
                      ·
                        rfl

theorem cell23_3094398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 1, 1, 5, 2].length) (baseStart_3094398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3094398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3094398 prefixEnd_3094398 := by exact prefixLift 3094398
  have htrace : WordTrace (prefixWord ++ tailWord_3094398) baseStart_3094398 baseEnd_3094398 := by
    simpa [prefixWord, tailWord_3094398, baseEnd_3094398] using wordTrace_append hprefix tailTrace_3094398
  have hstable : (prefixWord ++ tailWord_3094398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3094398).length < 2 ^ (prefixWord ++ tailWord_3094398).sum := by decide
  have hdescent : baseEnd_3094398 < baseStart_3094398 := by decide
  rcases family_descends (prefixWord ++ tailWord_3094398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3094408 : List Nat := [2, 1, 3, 3, 3, 2, 2, 1, 1, 5]
def baseStart_3094408 : Nat := 118140960795 + 3094408 * 2 ^ 59
def prefixEnd_3094408 : Nat := 4983230072969 + 3 ^ 40 * 3094408 * 2
def baseEnd_3094408 : Nat := 529639548372678116056361

theorem tailTrace_3094408 : CollatzResearch.WordTrace tailWord_3094408 prefixEnd_3094408 529639548372678116056361 := by
  unfold tailWord_3094408
  simp only [CollatzResearch.WordTrace]
  refine ⟨56431165886747886828421939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75241554515663849104562585 56431165886747886828421939)
  ·
    refine ⟨84646748830121830242632909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56431165886747886828421939 84646748830121830242632909)
    ·
      refine ⟨31742530811295686340987341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84646748830121830242632909 31742530811295686340987341)
      ·
        refine ⟨11903449054235882377870253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31742530811295686340987341 11903449054235882377870253)
        ·
          refine ⟨4463793395338455891701345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11903449054235882377870253 4463793395338455891701345)
          ·
            refine ⟨3347845046503841918776009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4463793395338455891701345 3347845046503841918776009)
            ·
              refine ⟨2510883784877881439082007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3347845046503841918776009 2510883784877881439082007)
              ·
                refine ⟨3766325677316822158623011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2510883784877881439082007 3766325677316822158623011)
                ·
                  refine ⟨5649488515975233237934517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3766325677316822158623011 5649488515975233237934517)
                  ·
                    refine ⟨529639548372678116056361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5649488515975233237934517 529639548372678116056361)
                    ·
                      rfl

theorem cell23_3094408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 2, 1, 1, 5].length) (baseStart_3094408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3094408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3094408 prefixEnd_3094408 := by exact prefixLift 3094408
  have htrace : WordTrace (prefixWord ++ tailWord_3094408) baseStart_3094408 baseEnd_3094408 := by
    simpa [prefixWord, tailWord_3094408, baseEnd_3094408] using wordTrace_append hprefix tailTrace_3094408
  have hstable : (prefixWord ++ tailWord_3094408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3094408).length < 2 ^ (prefixWord ++ tailWord_3094408).sum := by decide
  have hdescent : baseEnd_3094408 < baseStart_3094408 := by decide
  rcases family_descends (prefixWord ++ tailWord_3094408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3094422 : List Nat := [5, 3, 1, 1, 2, 1, 2, 1, 3, 1, 3]
def baseStart_3094422 : Nat := 118140960795 + 3094422 * 2 ^ 59
def prefixEnd_3094422 : Nat := 4983230072969 + 3 ^ 40 * 3094422 * 2
def baseEnd_3094422 : Nat := 1588925833847197293394019

theorem tailTrace_3094422 : CollatzResearch.WordTrace tailWord_3094422 prefixEnd_3094422 1588925833847197293394019 := by
  unfold tailWord_3094422
  simp only [CollatzResearch.WordTrace]
  refine ⟨7053927649715315877990845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 75241894930296702698569013 7053927649715315877990845)
  ·
    refine ⟨2645222868643243454246567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7053927649715315877990845 2645222868643243454246567)
    ·
      refine ⟨3967834302964865181369851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2645222868643243454246567 3967834302964865181369851)
      ·
        refine ⟨5951751454447297772054777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3967834302964865181369851 5951751454447297772054777)
        ·
          refine ⟨4463813590835473329041083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5951751454447297772054777 4463813590835473329041083)
          ·
            refine ⟨6695720386253209993561625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4463813590835473329041083 6695720386253209993561625)
            ·
              refine ⟨5021790289689907495171219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6695720386253209993561625 5021790289689907495171219)
              ·
                refine ⟨7532685434534861242756829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5021790289689907495171219 7532685434534861242756829)
                ·
                  refine ⟨2824757037950572966033811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7532685434534861242756829 2824757037950572966033811)
                  ·
                    refine ⟨4237135556925859449050717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2824757037950572966033811 4237135556925859449050717)
                    ·
                      refine ⟨1588925833847197293394019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4237135556925859449050717 1588925833847197293394019)
                      ·
                        rfl

theorem cell23_3094422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 2, 1, 3, 1, 3].length) (baseStart_3094422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3094422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3094422 prefixEnd_3094422 := by exact prefixLift 3094422
  have htrace : WordTrace (prefixWord ++ tailWord_3094422) baseStart_3094422 baseEnd_3094422 := by
    simpa [prefixWord, tailWord_3094422, baseEnd_3094422] using wordTrace_append hprefix tailTrace_3094422
  have hstable : (prefixWord ++ tailWord_3094422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3094422).length < 2 ^ (prefixWord ++ tailWord_3094422).sum := by decide
  have hdescent : baseEnd_3094422 < baseStart_3094422 := by decide
  rcases family_descends (prefixWord ++ tailWord_3094422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3094428 : List Nat := [2, 2, 3, 3, 1, 1, 1, 3, 3, 2, 2]
def baseStart_3094428 : Nat := 118140960795 + 3094428 * 2 ^ 59
def prefixEnd_3094428 : Nat := 4983230072969 + 3 ^ 40 * 3094428 * 2
def baseEnd_3094428 : Nat := 1588928914731124269918991

theorem tailTrace_3094428 : CollatzResearch.WordTrace tailWord_3094428 prefixEnd_3094428 1588928914731124269918991 := by
  unfold tailWord_3094428
  simp only [CollatzResearch.WordTrace]
  refine ⟨56431530616711658536285969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75242040822282211381714625 56431530616711658536285969)
  ·
    refine ⟨42323647962533743902214477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56431530616711658536285969 42323647962533743902214477)
    ·
      refine ⟨15871367985950153963330429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42323647962533743902214477 15871367985950153963330429)
      ·
        refine ⟨5951762994731307736248911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15871367985950153963330429 5951762994731307736248911)
        ·
          refine ⟨8927644492096961604373367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5951762994731307736248911 8927644492096961604373367)
          ·
            refine ⟨13391466738145442406560051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8927644492096961604373367 13391466738145442406560051)
            ·
              refine ⟨20087200107218163609840077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13391466738145442406560051 20087200107218163609840077)
              ·
                refine ⟨7532700040206811353690029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20087200107218163609840077 7532700040206811353690029)
                ·
                  refine ⟨2824762515077554257633761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7532700040206811353690029 2824762515077554257633761)
                  ·
                    refine ⟨2118571886308165693225321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2824762515077554257633761 2118571886308165693225321)
                    ·
                      refine ⟨1588928914731124269918991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2118571886308165693225321 1588928914731124269918991)
                      ·
                        rfl

theorem cell23_3094428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 3, 3, 2, 2].length) (baseStart_3094428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3094428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3094428 prefixEnd_3094428 := by exact prefixLift 3094428
  have htrace : WordTrace (prefixWord ++ tailWord_3094428) baseStart_3094428 baseEnd_3094428 := by
    simpa [prefixWord, tailWord_3094428, baseEnd_3094428] using wordTrace_append hprefix tailTrace_3094428
  have hstable : (prefixWord ++ tailWord_3094428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3094428).length < 2 ^ (prefixWord ++ tailWord_3094428).sum := by decide
  have hdescent : baseEnd_3094428 < baseStart_3094428 := by decide
  rcases family_descends (prefixWord ++ tailWord_3094428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3094444 : List Nat := [2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 3]
def baseStart_3094444 : Nat := 118140960795 + 3094444 * 2 ^ 59
def prefixEnd_3094444 : Nat := 4983230072969 + 3 ^ 40 * 3094444 * 2
def baseEnd_3094444 : Nat := 1588937130421596207318917

theorem tailTrace_3094444 : CollatzResearch.WordTrace tailWord_3094444 prefixEnd_3094444 1588937130421596207318917 := by
  unfold tailWord_3094444
  simp only [CollatzResearch.WordTrace]
  refine ⟨56431822400682675902577193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75242429867576901203436257 56431822400682675902577193)
  ·
    refine ⟨42323866800512006926932895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56431822400682675902577193 42323866800512006926932895)
    ·
      refine ⟨63485800200768010390399343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42323866800512006926932895 63485800200768010390399343)
      ·
        refine ⟨95228700301152015585599015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63485800200768010390399343 95228700301152015585599015)
        ·
          refine ⟨142843050451728023378398523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95228700301152015585599015 142843050451728023378398523)
          ·
            refine ⟨214264575677592035067597785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142843050451728023378398523 214264575677592035067597785)
            ·
              refine ⟨160698431758194026300698339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 214264575677592035067597785 160698431758194026300698339)
              ·
                refine ⟨241047647637291039451047509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 160698431758194026300698339 241047647637291039451047509)
                ·
                  refine ⟨2824777120749504368566963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 241047647637291039451047509 2824777120749504368566963)
                  ·
                    refine ⟨4237165681124256552850445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2824777120749504368566963 4237165681124256552850445)
                    ·
                      refine ⟨1588937130421596207318917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4237165681124256552850445 1588937130421596207318917)
                      ·
                        rfl

theorem cell23_3094444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 3].length) (baseStart_3094444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3094444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3094444 prefixEnd_3094444 := by exact prefixLift 3094444
  have htrace : WordTrace (prefixWord ++ tailWord_3094444) baseStart_3094444 baseEnd_3094444 := by
    simpa [prefixWord, tailWord_3094444, baseEnd_3094444] using wordTrace_append hprefix tailTrace_3094444
  have hstable : (prefixWord ++ tailWord_3094444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3094444).length < 2 ^ (prefixWord ++ tailWord_3094444).sum := by decide
  have hdescent : baseEnd_3094444 < baseStart_3094444 := by decide
  rcases family_descends (prefixWord ++ tailWord_3094444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3094457 : List Nat := [1, 2, 1, 4, 2, 1, 1, 1, 1, 4, 5]
def baseStart_3094457 : Nat := 118140960795 + 3094457 * 2 ^ 59
def prefixEnd_3094457 : Nat := 4983230072969 + 3 ^ 40 * 3094457 * 2
def baseEnd_3094457 : Nat := 1588943805670104656456357

theorem tailTrace_3094457 : CollatzResearch.WordTrace tailWord_3094457 prefixEnd_3094457 1588943805670104656456357 := by
  unfold tailWord_3094457
  simp only [CollatzResearch.WordTrace]
  refine ⟨112864118950318255025377625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75242745966878836683585083 112864118950318255025377625)
  ·
    refine ⟨84648089212738691269033219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112864118950318255025377625 84648089212738691269033219)
    ·
      refine ⟨126972133819108036903549829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84648089212738691269033219 126972133819108036903549829)
      ·
        refine ⟨23807275091082756919415593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 126972133819108036903549829 23807275091082756919415593)
        ·
          refine ⟨17855456318312067689561695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23807275091082756919415593 17855456318312067689561695)
          ·
            refine ⟨26783184477468101534342543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17855456318312067689561695 26783184477468101534342543)
            ·
              refine ⟨40174776716202152301513815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26783184477468101534342543 40174776716202152301513815)
              ·
                refine ⟨60262165074303228452270723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40174776716202152301513815 60262165074303228452270723)
                ·
                  refine ⟨90393247611454842678406085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60262165074303228452270723 90393247611454842678406085)
                  ·
                    refine ⟨16948733927147783002201141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 90393247611454842678406085 16948733927147783002201141)
                    ·
                      refine ⟨1588943805670104656456357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16948733927147783002201141 1588943805670104656456357)
                      ·
                        rfl

theorem cell23_3094457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 1, 1, 4, 5].length) (baseStart_3094457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3094457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3094457 prefixEnd_3094457 := by exact prefixLift 3094457
  have htrace : WordTrace (prefixWord ++ tailWord_3094457) baseStart_3094457 baseEnd_3094457 := by
    simpa [prefixWord, tailWord_3094457, baseEnd_3094457] using wordTrace_append hprefix tailTrace_3094457
  have hstable : (prefixWord ++ tailWord_3094457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3094457).length < 2 ^ (prefixWord ++ tailWord_3094457).sum := by decide
  have hdescent : baseEnd_3094457 < baseStart_3094457 := by decide
  rcases family_descends (prefixWord ++ tailWord_3094457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3094461 : List Nat := [1, 4, 1, 2, 3, 1, 1, 2, 4, 1, 3]
def baseStart_3094461 : Nat := 118140960795 + 3094461 * 2 ^ 59
def prefixEnd_3094461 : Nat := 4983230072969 + 3 ^ 40 * 3094461 * 2
def baseEnd_3094461 : Nat := 1588945859592722640806339

theorem tailTrace_3094461 : CollatzResearch.WordTrace tailWord_3094461 prefixEnd_3094461 1588945859592722640806339 := by
  unfold tailWord_3094461
  simp only [CollatzResearch.WordTrace]
  refine ⟨112864264842303763708523237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75242843228202509139015491 112864264842303763708523237)
  ·
    refine ⟨21162049657931955695348107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 112864264842303763708523237 21162049657931955695348107)
    ·
      refine ⟨31743074486897933543022161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21162049657931955695348107 31743074486897933543022161)
      ·
        refine ⟨23807305865173450157266621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31743074486897933543022161 23807305865173450157266621)
        ·
          refine ⟨8927739699440043808974983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23807305865173450157266621 8927739699440043808974983)
          ·
            refine ⟨13391609549160065713462475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8927739699440043808974983 13391609549160065713462475)
            ·
              refine ⟨20087414323740098570193713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13391609549160065713462475 20087414323740098570193713)
              ·
                refine ⟨15065560742805073927645285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20087414323740098570193713 15065560742805073927645285)
                ·
                  refine ⟨2824792639275951361433491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15065560742805073927645285 2824792639275951361433491)
                  ·
                    refine ⟨4237188958913927042150237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2824792639275951361433491 4237188958913927042150237)
                    ·
                      refine ⟨1588945859592722640806339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4237188958913927042150237 1588945859592722640806339)
                      ·
                        rfl

theorem cell23_3094461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 2, 4, 1, 3].length) (baseStart_3094461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3094461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3094461 prefixEnd_3094461 := by exact prefixLift 3094461
  have htrace : WordTrace (prefixWord ++ tailWord_3094461) baseStart_3094461 baseEnd_3094461 := by
    simpa [prefixWord, tailWord_3094461, baseEnd_3094461] using wordTrace_append hprefix tailTrace_3094461
  have hstable : (prefixWord ++ tailWord_3094461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3094461).length < 2 ^ (prefixWord ++ tailWord_3094461).sum := by decide
  have hdescent : baseEnd_3094461 < baseStart_3094461 := by decide
  rcases family_descends (prefixWord ++ tailWord_3094461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3094462 : List Nat := [4, 2, 1, 1, 1, 5, 1, 3, 1, 2, 2]
def baseStart_3094462 : Nat := 118140960795 + 3094462 * 2 ^ 59
def prefixEnd_3094462 : Nat := 4983230072969 + 3 ^ 40 * 3094462 * 2
def baseEnd_3094462 : Nat := 1588946373073377136893835

theorem tailTrace_3094462 : CollatzResearch.WordTrace tailWord_3094462 prefixEnd_3094462 1588946373073377136893835 := by
  unfold tailWord_3094462
  simp only [CollatzResearch.WordTrace]
  refine ⟨14108037664412517609913705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75242867543533427252873093 14108037664412517609913705)
  ·
    refine ⟨10581028248309388207435279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14108037664412517609913705 10581028248309388207435279)
    ·
      refine ⟨15871542372464082311152919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10581028248309388207435279 15871542372464082311152919)
      ·
        refine ⟨23807313558696123466729379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15871542372464082311152919 23807313558696123466729379)
        ·
          refine ⟨35710970338044185200094069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23807313558696123466729379 35710970338044185200094069)
          ·
            refine ⟨3347903469191642362508819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 35710970338044185200094069 3347903469191642362508819)
            ·
              refine ⟨5021855203787463543763229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3347903469191642362508819 5021855203787463543763229)
              ·
                refine ⟨1883195701420298828911211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5021855203787463543763229 1883195701420298828911211)
                ·
                  refine ⟨2824793552130448243366817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1883195701420298828911211 2824793552130448243366817)
                  ·
                    refine ⟨2118595164097836182525113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2824793552130448243366817 2118595164097836182525113)
                    ·
                      refine ⟨1588946373073377136893835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2118595164097836182525113 1588946373073377136893835)
                      ·
                        rfl

theorem cell23_3094462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 1, 3, 1, 2, 2].length) (baseStart_3094462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3094462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3094462 prefixEnd_3094462 := by exact prefixLift 3094462
  have htrace : WordTrace (prefixWord ++ tailWord_3094462) baseStart_3094462 baseEnd_3094462 := by
    simpa [prefixWord, tailWord_3094462, baseEnd_3094462] using wordTrace_append hprefix tailTrace_3094462
  have hstable : (prefixWord ++ tailWord_3094462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3094462).length < 2 ^ (prefixWord ++ tailWord_3094462).sum := by decide
  have hdescent : baseEnd_3094462 < baseStart_3094462 := by decide
  rcases family_descends (prefixWord ++ tailWord_3094462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3094484 : List Nat := [2, 4, 1, 2, 1, 1, 2, 1, 2, 3, 4]
def baseStart_3094484 : Nat := 118140960795 + 3094484 * 2 ^ 59
def prefixEnd_3094484 : Nat := 4983230072969 + 3 ^ 40 * 3094484 * 2
def baseEnd_3094484 : Nat := 1588957669647776050818733

theorem tailTrace_3094484 : CollatzResearch.WordTrace tailWord_3094484 prefixEnd_3094484 1588957669647776050818733 := by
  unfold tailWord_3094484
  simp only [CollatzResearch.WordTrace]
  refine ⟨56432551860610219318305253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75243402480813625757740337 56432551860610219318305253)
  ·
    refine ⟨10581103473864416122182235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56432551860610219318305253 10581103473864416122182235)
    ·
      refine ⟨15871655210796624183273353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10581103473864416122182235 15871655210796624183273353)
      ·
        refine ⟨11903741408097468137455015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15871655210796624183273353 11903741408097468137455015)
        ·
          refine ⟨17855612112146202206182523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11903741408097468137455015 17855612112146202206182523)
          ·
            refine ⟨26783418168219303309273785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17855612112146202206182523 26783418168219303309273785)
            ·
              refine ⟨20087563626164477481955339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26783418168219303309273785 20087563626164477481955339)
              ·
                refine ⟨30131345439246716222933009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20087563626164477481955339 30131345439246716222933009)
                ·
                  refine ⟨22598509079435037167199757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30131345439246716222933009 22598509079435037167199757)
                  ·
                    refine ⟨8474440904788138937699909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22598509079435037167199757 8474440904788138937699909)
                    ·
                      refine ⟨1588957669647776050818733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8474440904788138937699909 1588957669647776050818733)
                      ·
                        rfl

theorem cell23_3094484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 1, 2, 3, 4].length) (baseStart_3094484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3094484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3094484 prefixEnd_3094484 := by exact prefixLift 3094484
  have htrace : WordTrace (prefixWord ++ tailWord_3094484) baseStart_3094484 baseEnd_3094484 := by
    simpa [prefixWord, tailWord_3094484, baseEnd_3094484] using wordTrace_append hprefix tailTrace_3094484
  have hstable : (prefixWord ++ tailWord_3094484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3094484).length < 2 ^ (prefixWord ++ tailWord_3094484).sum := by decide
  have hdescent : baseEnd_3094484 < baseStart_3094484 := by decide
  rcases family_descends (prefixWord ++ tailWord_3094484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3094487 : List Nat := [1, 1, 3, 2, 1, 1, 3, 2, 1, 3, 5]
def baseStart_3094487 : Nat := 118140960795 + 3094487 * 2 ^ 59
def prefixEnd_3094487 : Nat := 4983230072969 + 3 ^ 40 * 3094487 * 2
def baseEnd_3094487 : Nat := 1588959210089739539081219

theorem tailTrace_3094487 : CollatzResearch.WordTrace tailWord_3094487 prefixEnd_3094487 1588959210089739539081219 := by
  unfold tailWord_3094487
  simp only [CollatzResearch.WordTrace]
  refine ⟨112865213140209570148969715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75243475426806380099313143 112865213140209570148969715)
  ·
    refine ⟨169297819710314355223454573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112865213140209570148969715 169297819710314355223454573)
    ·
      refine ⟨63486682391367883208795465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 169297819710314355223454573 63486682391367883208795465)
      ·
        refine ⟨47615011793525912406596599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63486682391367883208795465 47615011793525912406596599)
        ·
          refine ⟨71422517690288868609894899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47615011793525912406596599 71422517690288868609894899)
          ·
            refine ⟨107133776535433302914842349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71422517690288868609894899 107133776535433302914842349)
            ·
              refine ⟨40175166200787488593065881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 107133776535433302914842349 40175166200787488593065881)
              ·
                refine ⟨30131374650590616444799411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40175166200787488593065881 30131374650590616444799411)
                ·
                  refine ⟨45197061975885924667199117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30131374650590616444799411 45197061975885924667199117)
                  ·
                    refine ⟨16948898240957221750199669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45197061975885924667199117 16948898240957221750199669)
                    ·
                      refine ⟨1588959210089739539081219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16948898240957221750199669 1588959210089739539081219)
                      ·
                        rfl

theorem cell23_3094487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 2, 1, 3, 5].length) (baseStart_3094487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3094487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3094487 prefixEnd_3094487 := by exact prefixLift 3094487
  have htrace : WordTrace (prefixWord ++ tailWord_3094487) baseStart_3094487 baseEnd_3094487 := by
    simpa [prefixWord, tailWord_3094487, baseEnd_3094487] using wordTrace_append hprefix tailTrace_3094487
  have hstable : (prefixWord ++ tailWord_3094487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3094487).length < 2 ^ (prefixWord ++ tailWord_3094487).sum := by decide
  have hdescent : baseEnd_3094487 < baseStart_3094487 := by decide
  rcases family_descends (prefixWord ++ tailWord_3094487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3094495 : List Nat := [1, 1, 2, 3, 4, 3, 2, 1, 2, 1, 3]
def baseStart_3094495 : Nat := 118140960795 + 3094495 * 2 ^ 59
def prefixEnd_3094495 : Nat := 4983230072969 + 3 ^ 40 * 3094495 * 2
def baseEnd_3094495 : Nat := 1588963317934975507781183

theorem tailTrace_3094495 : CollatzResearch.WordTrace tailWord_3094495 prefixEnd_3094495 1588963317934975507781183 := by
  unfold tailWord_3094495
  simp only [CollatzResearch.WordTrace]
  refine ⟨112865504924180587515260939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75243669949453725010173959 112865504924180587515260939)
  ·
    refine ⟨169298257386270881272891409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112865504924180587515260939 169298257386270881272891409)
    ·
      refine ⟨126973693039703160954668557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169298257386270881272891409 126973693039703160954668557)
      ·
        refine ⟨47615134889888685358000709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126973693039703160954668557 47615134889888685358000709)
        ·
          refine ⟨8927837791854128504625133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47615134889888685358000709 8927837791854128504625133)
          ·
            refine ⟨3347939171945298189234425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8927837791854128504625133 3347939171945298189234425)
            ·
              refine ⟨2510954378958973641925819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3347939171945298189234425 2510954378958973641925819)
              ·
                refine ⟨3766431568438460462888729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2510954378958973641925819 3766431568438460462888729)
                ·
                  refine ⟨2824823676328845347166547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3766431568438460462888729 2824823676328845347166547)
                  ·
                    refine ⟨4237235514493268020749821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2824823676328845347166547 4237235514493268020749821)
                    ·
                      refine ⟨1588963317934975507781183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4237235514493268020749821 1588963317934975507781183)
                      ·
                        rfl

theorem cell23_3094495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 2, 1, 2, 1, 3].length) (baseStart_3094495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3094495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3094495 prefixEnd_3094495 := by exact prefixLift 3094495
  have htrace : WordTrace (prefixWord ++ tailWord_3094495) baseStart_3094495 baseEnd_3094495 := by
    simpa [prefixWord, tailWord_3094495, baseEnd_3094495] using wordTrace_append hprefix tailTrace_3094495
  have hstable : (prefixWord ++ tailWord_3094495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3094495).length < 2 ^ (prefixWord ++ tailWord_3094495).sum := by decide
  have hdescent : baseEnd_3094495 < baseStart_3094495 := by decide
  rcases family_descends (prefixWord ++ tailWord_3094495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3094507 : List Nat := [1, 1, 1, 1, 2, 3, 1, 6, 7]
def baseStart_3094507 : Nat := 118140960795 + 3094507 * 2 ^ 59
def prefixEnd_3094507 : Nat := 4983230072969 + 3 ^ 40 * 3094507 * 2
def baseEnd_3094507 : Nat := 176552164411425495647903

theorem tailTrace_3094507 : CollatzResearch.WordTrace tailWord_3094507 prefixEnd_3094507 176552164411425495647903 := by
  unfold tailWord_3094507
  simp only [CollatzResearch.WordTrace]
  refine ⟨112865942600137113564697775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75243961733424742376465183 112865942600137113564697775)
  ·
    refine ⟨169298913900205670347046663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112865942600137113564697775 169298913900205670347046663)
    ·
      refine ⟨253948370850308505520569995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169298913900205670347046663 253948370850308505520569995)
      ·
        refine ⟨380922556275462758280854993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253948370850308505520569995 380922556275462758280854993)
        ·
          refine ⟨285691917206597068710641245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 380922556275462758280854993 285691917206597068710641245)
          ·
            refine ⟨107134468952473900766490467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 285691917206597068710641245 107134468952473900766490467)
            ·
              refine ⟨160701703428710851149735701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107134468952473900766490467 160701703428710851149735701)
              ·
                refine ⟨7532892348220821147643861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 160701703428710851149735701 7532892348220821147643861)
                ·
                  refine ⟨176552164411425495647903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7532892348220821147643861 176552164411425495647903)
                  ·
                    rfl

theorem cell23_3094507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 6, 7].length) (baseStart_3094507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3094507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3094507 prefixEnd_3094507 := by exact prefixLift 3094507
  have htrace : WordTrace (prefixWord ++ tailWord_3094507) baseStart_3094507 baseEnd_3094507 := by
    simpa [prefixWord, tailWord_3094507, baseEnd_3094507] using wordTrace_append hprefix tailTrace_3094507
  have hstable : (prefixWord ++ tailWord_3094507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3094507).length < 2 ^ (prefixWord ++ tailWord_3094507).sum := by decide
  have hdescent : baseEnd_3094507 < baseStart_3094507 := by decide
  rcases family_descends (prefixWord ++ tailWord_3094507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3094535 : List Nat := [1, 1, 4, 3, 1, 3, 2, 2, 2, 2, 2]
def baseStart_3094535 : Nat := 118140960795 + 3094535 * 2 ^ 59
def prefixEnd_3094535 : Nat := 4983230072969 + 3 ^ 40 * 3094535 * 2
def baseEnd_3094535 : Nat := 1588983857161155351280999

theorem tailTrace_3094535 : CollatzResearch.WordTrace tailWord_3094535 prefixEnd_3094535 1588983857161155351280999 := by
  unfold tailWord_3094535
  simp only [CollatzResearch.WordTrace]
  refine ⟨112866963844035674346717059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75244642562690449564478039 112866963844035674346717059)
  ·
    refine ⟨169300445766053511520075589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112866963844035674346717059 169300445766053511520075589)
    ·
      refine ⟨31743833581135033410014173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 169300445766053511520075589 31743833581135033410014173)
      ·
        refine ⟨11903937592925637528755315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31743833581135033410014173 11903937592925637528755315)
        ·
          refine ⟨17855906389388456293132973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11903937592925637528755315 17855906389388456293132973)
          ·
            refine ⟨6695964896020671109924865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17855906389388456293132973 6695964896020671109924865)
            ·
              refine ⟨5021973672015503332443649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6695964896020671109924865 5021973672015503332443649)
              ·
                refine ⟨3766480254011627499332737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5021973672015503332443649 3766480254011627499332737)
                ·
                  refine ⟨2824860190508720624499553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3766480254011627499332737 2824860190508720624499553)
                  ·
                    refine ⟨2118645142881540468374665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2824860190508720624499553 2118645142881540468374665)
                    ·
                      refine ⟨1588983857161155351280999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2118645142881540468374665 1588983857161155351280999)
                      ·
                        rfl

theorem cell23_3094535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 2, 2, 2, 2, 2].length) (baseStart_3094535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3094535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3094535 prefixEnd_3094535 := by exact prefixLift 3094535
  have htrace : WordTrace (prefixWord ++ tailWord_3094535) baseStart_3094535 baseEnd_3094535 := by
    simpa [prefixWord, tailWord_3094535, baseEnd_3094535] using wordTrace_append hprefix tailTrace_3094535
  have hstable : (prefixWord ++ tailWord_3094535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3094535).length < 2 ^ (prefixWord ++ tailWord_3094535).sum := by decide
  have hdescent : baseEnd_3094535 < baseStart_3094535 := by decide
  rcases family_descends (prefixWord ++ tailWord_3094535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3094537 : List Nat := [1, 2, 1, 1, 3, 1, 1, 1, 5, 7]
def baseStart_3094537 : Nat := 118140960795 + 3094537 * 2 ^ 59
def prefixEnd_3094537 : Nat := 4983230072969 + 3 ^ 40 * 3094537 * 2
def baseEnd_3094537 : Nat := 529661628040821447818663

theorem tailTrace_3094537 : CollatzResearch.WordTrace tailWord_3094537 prefixEnd_3094537 529661628040821447818663 := by
  unfold tailWord_3094537
  simp only [CollatzResearch.WordTrace]
  refine ⟨112867036790028428688289865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75244691193352285792193243 112867036790028428688289865)
  ·
    refine ⟨84650277592521321516217399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112867036790028428688289865 84650277592521321516217399)
    ·
      refine ⟨126975416388781982274326099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84650277592521321516217399 126975416388781982274326099)
      ·
        refine ⟨190463124583172973411489149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126975416388781982274326099 190463124583172973411489149)
        ·
          refine ⟨71423671718689865029308431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 190463124583172973411489149 71423671718689865029308431)
          ·
            refine ⟨107135507578034797543962647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71423671718689865029308431 107135507578034797543962647)
            ·
              refine ⟨160703261367052196315943971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107135507578034797543962647 160703261367052196315943971)
              ·
                refine ⟨241054892050578294473915957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 160703261367052196315943971 241054892050578294473915957)
                ·
                  refine ⟨22598896129741715106929621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 241054892050578294473915957 22598896129741715106929621)
                  ·
                    refine ⟨529661628040821447818663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22598896129741715106929621 529661628040821447818663)
                    ·
                      rfl

theorem cell23_3094537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 5, 7].length) (baseStart_3094537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3094537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3094537 prefixEnd_3094537 := by exact prefixLift 3094537
  have htrace : WordTrace (prefixWord ++ tailWord_3094537) baseStart_3094537 baseEnd_3094537 := by
    simpa [prefixWord, tailWord_3094537, baseEnd_3094537] using wordTrace_append hprefix tailTrace_3094537
  have hstable : (prefixWord ++ tailWord_3094537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3094537).length < 2 ^ (prefixWord ++ tailWord_3094537).sum := by decide
  have hdescent : baseEnd_3094537 < baseStart_3094537 := by decide
  rcases family_descends (prefixWord ++ tailWord_3094537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3094591 : List Nat := [1, 1, 2, 2, 3, 1, 3, 2, 2, 4, 2]
def baseStart_3094591 : Nat := 118140960795 + 3094591 * 2 ^ 59
def prefixEnd_3094591 : Nat := 4983230072969 + 3 ^ 40 * 3094591 * 2
def baseEnd_3094591 : Nat := 1589012612077807132180741

theorem tailTrace_3094591 : CollatzResearch.WordTrace tailWord_3094591 prefixEnd_3094591 1589012612077807132180741 := by
  unfold tailWord_3094591
  simp only [CollatzResearch.WordTrace]
  refine ⟨112869006331832795910755627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75246004221221863940503751 112869006331832795910755627)
  ·
    refine ⟨169303509497749193866133441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112869006331832795910755627 169303509497749193866133441)
    ·
      refine ⟨126977632123311895399600081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169303509497749193866133441 126977632123311895399600081)
      ·
        refine ⟨95233224092483921549700061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126977632123311895399600081 95233224092483921549700061)
        ·
          refine ⟨35712459034681470581137523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95233224092483921549700061 35712459034681470581137523)
          ·
            refine ⟨53568688552022205871706285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35712459034681470581137523 53568688552022205871706285)
            ·
              refine ⟨20088258207008327201889857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53568688552022205871706285 20088258207008327201889857)
              ·
                refine ⟨15066193655256245401417393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20088258207008327201889857 15066193655256245401417393)
                ·
                  refine ⟨11299645241442184051063045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15066193655256245401417393 11299645241442184051063045)
                  ·
                    refine ⟨2118683482770409509574321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11299645241442184051063045 2118683482770409509574321)
                    ·
                      refine ⟨1589012612077807132180741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2118683482770409509574321 1589012612077807132180741)
                      ·
                        rfl

theorem cell23_3094591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 2, 2, 4, 2].length) (baseStart_3094591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3094591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3094591 prefixEnd_3094591 := by exact prefixLift 3094591
  have htrace : WordTrace (prefixWord ++ tailWord_3094591) baseStart_3094591 baseEnd_3094591 := by
    simpa [prefixWord, tailWord_3094591, baseEnd_3094591] using wordTrace_append hprefix tailTrace_3094591
  have hstable : (prefixWord ++ tailWord_3094591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3094591).length < 2 ^ (prefixWord ++ tailWord_3094591).sum := by decide
  have hdescent : baseEnd_3094591 < baseStart_3094591 := by decide
  rcases family_descends (prefixWord ++ tailWord_3094591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3094601 : List Nat := [1, 2, 1, 1, 2, 2, 6, 1, 3, 4]
def baseStart_3094601 : Nat := 118140960795 + 3094601 * 2 ^ 59
def prefixEnd_3094601 : Nat := 4983230072969 + 3 ^ 40 * 3094601 * 2
def baseEnd_3094601 : Nat := 529672582294784031018565

theorem tailTrace_3094601 : CollatzResearch.WordTrace tailWord_3094601 prefixEnd_3094601 529672582294784031018565 := by
  unfold tailWord_3094601
  simp only [CollatzResearch.WordTrace]
  refine ⟨112869371061796567618619657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75246247374531045079079771 112869371061796567618619657)
  ·
    refine ⟨84652028296347425713964743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112869371061796567618619657 84652028296347425713964743)
    ·
      refine ⟨126978042444521138570947115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84652028296347425713964743 126978042444521138570947115)
      ·
        refine ⟨190467063666781707856420673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126978042444521138570947115 190467063666781707856420673)
        ·
          refine ⟨142850297750086280892315505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 190467063666781707856420673 142850297750086280892315505)
          ·
            refine ⟨107137723312564710669236629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142850297750086280892315505 107137723312564710669236629)
            ·
              refine ⟨5022080780276470812620467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 107137723312564710669236629 5022080780276470812620467)
              ·
                refine ⟨7533121170414706218930701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5022080780276470812620467 7533121170414706218930701)
                ·
                  refine ⟨2824920438905514832099013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7533121170414706218930701 2824920438905514832099013)
                  ·
                    refine ⟨529672582294784031018565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2824920438905514832099013 529672582294784031018565)
                    ·
                      rfl

theorem cell23_3094601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 6, 1, 3, 4].length) (baseStart_3094601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3094601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3094601 prefixEnd_3094601 := by exact prefixLift 3094601
  have htrace : WordTrace (prefixWord ++ tailWord_3094601) baseStart_3094601 baseEnd_3094601 := by
    simpa [prefixWord, tailWord_3094601, baseEnd_3094601] using wordTrace_append hprefix tailTrace_3094601
  have hstable : (prefixWord ++ tailWord_3094601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3094601).length < 2 ^ (prefixWord ++ tailWord_3094601).sum := by decide
  have hdescent : baseEnd_3094601 < baseStart_3094601 := by decide
  rcases family_descends (prefixWord ++ tailWord_3094601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3094681 : List Nat := [1, 2, 1, 2, 1, 2, 1, 3, 2, 6, 2]
def baseStart_3094681 : Nat := 118140960795 + 3094681 * 2 ^ 59
def prefixEnd_3094681 : Nat := 4983230072969 + 3 ^ 40 * 3094681 * 2
def baseEnd_3094681 : Nat := 1589058825336711780055327

theorem tailTrace_3094681 : CollatzResearch.WordTrace tailWord_3094681 prefixEnd_3094681 1589058825336711780055327 := by
  unfold tailWord_3094681
  simp only [CollatzResearch.WordTrace]
  refine ⟨112872288901506741281531897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75248192601004494187687931 112872288901506741281531897)
  ·
    refine ⟨84654216676130055961148923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112872288901506741281531897 84654216676130055961148923)
    ·
      refine ⟨126981325014195083941723385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84654216676130055961148923 126981325014195083941723385)
      ·
        refine ⟨95235993760646312956292539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126981325014195083941723385 95235993760646312956292539)
        ·
          refine ⟨142853990640969469434438809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95235993760646312956292539 142853990640969469434438809)
          ·
            refine ⟨107140492980727102075829107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142853990640969469434438809 107140492980727102075829107)
            ·
              refine ⟨160710739471090653113743661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107140492980727102075829107 160710739471090653113743661)
              ·
                refine ⟨60266527301658994917653873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 160710739471090653113743661 60266527301658994917653873)
                ·
                  refine ⟨45199895476244246188240405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60266527301658994917653873 45199895476244246188240405)
                  ·
                    refine ⟨2118745100448949040073769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 45199895476244246188240405 2118745100448949040073769)
                    ·
                      refine ⟨1589058825336711780055327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2118745100448949040073769 1589058825336711780055327)
                      ·
                        rfl

theorem cell23_3094681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 3, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 3, 2, 6, 2].length) (baseStart_3094681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3094681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3094681 prefixEnd_3094681 := by exact prefixLift 3094681
  have htrace : WordTrace (prefixWord ++ tailWord_3094681) baseStart_3094681 baseEnd_3094681 := by
    simpa [prefixWord, tailWord_3094681, baseEnd_3094681] using wordTrace_append hprefix tailTrace_3094681
  have hstable : (prefixWord ++ tailWord_3094681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3094681).length < 2 ^ (prefixWord ++ tailWord_3094681).sum := by decide
  have hdescent : baseEnd_3094681 < baseStart_3094681 := by decide
  rcases family_descends (prefixWord ++ tailWord_3094681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3094685 : List Nat := [1, 4, 2, 1, 1, 4, 2, 1, 2, 3, 2]
def baseStart_3094685 : Nat := 118140960795 + 3094685 * 2 ^ 59
def prefixEnd_3094685 : Nat := 4983230072969 + 3 ^ 40 * 3094685 * 2
def baseEnd_3094685 : Nat := 1589060879259329764405309

theorem tailTrace_3094685 : CollatzResearch.WordTrace tailWord_3094685 prefixEnd_3094685 1589060879259329764405309 := by
  unfold tailWord_3094685
  simp only [CollatzResearch.WordTrace]
  refine ⟨112872434793492249964677509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75248289862328166643118339 112872434793492249964677509)
  ·
    refine ⟨21163581523779796868377033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 112872434793492249964677509 21163581523779796868377033)
    ·
      refine ⟨15872686142834847651282775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21163581523779796868377033 15872686142834847651282775)
      ·
        refine ⟨23809029214252271476924163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15872686142834847651282775 23809029214252271476924163)
        ·
          refine ⟨35713543821378407215386245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23809029214252271476924163 35713543821378407215386245)
          ·
            refine ⟨6696289466508451352884921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35713543821378407215386245 6696289466508451352884921)
            ·
              refine ⟨5022217099881338514663691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6696289466508451352884921 5022217099881338514663691)
              ·
                refine ⟨7533325649822007771995537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5022217099881338514663691 7533325649822007771995537)
                ·
                  refine ⟨5649994237366505828996653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7533325649822007771995537 5649994237366505828996653)
                  ·
                    refine ⟨2118747839012439685873745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5649994237366505828996653 2118747839012439685873745)
                    ·
                      refine ⟨1589060879259329764405309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2118747839012439685873745 1589060879259329764405309)
                      ·
                        rfl

theorem cell23_3094685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 2, 1, 2, 3, 2].length) (baseStart_3094685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3094685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3094685 prefixEnd_3094685 := by exact prefixLift 3094685
  have htrace : WordTrace (prefixWord ++ tailWord_3094685) baseStart_3094685 baseEnd_3094685 := by
    simpa [prefixWord, tailWord_3094685, baseEnd_3094685] using wordTrace_append hprefix tailTrace_3094685
  have hstable : (prefixWord ++ tailWord_3094685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3094685).length < 2 ^ (prefixWord ++ tailWord_3094685).sum := by decide
  have hdescent : baseEnd_3094685 < baseStart_3094685 := by decide
  rcases family_descends (prefixWord ++ tailWord_3094685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3094709 : List Nat := [1, 3, 3, 4, 1, 1, 1, 4, 1, 1, 3]
def baseStart_3094709 : Nat := 118140960795 + 3094709 * 2 ^ 59
def prefixEnd_3094709 : Nat := 4983230072969 + 3 ^ 40 * 3094709 * 2
def baseEnd_3094709 : Nat := 1589073202795037670505199

theorem tailTrace_3094709 : CollatzResearch.WordTrace tailWord_3094709 prefixEnd_3094709 1589073202795037670505199 := by
  unfold tailWord_3094709
  simp only [CollatzResearch.WordTrace]
  refine ⟨112873310145405302063551181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75248873430270201375700787 112873310145405302063551181)
  ·
    refine ⟨42327491304526988273831693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112873310145405302063551181 42327491304526988273831693)
    ·
      refine ⟨15872809239197620602686885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42327491304526988273831693 15872809239197620602686885)
      ·
        refine ⟨2976151732349553863003791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15872809239197620602686885 2976151732349553863003791)
        ·
          refine ⟨4464227598524330794505687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2976151732349553863003791 4464227598524330794505687)
          ·
            refine ⟨6696341397786496191758531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4464227598524330794505687 6696341397786496191758531)
            ·
              refine ⟨10044512096679744287637797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6696341397786496191758531 10044512096679744287637797)
              ·
                refine ⟨1883346018127452053932087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10044512096679744287637797 1883346018127452053932087)
                ·
                  refine ⟨2825019027191178080898131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1883346018127452053932087 2825019027191178080898131)
                  ·
                    refine ⟨4237528540786767121347197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2825019027191178080898131 4237528540786767121347197)
                    ·
                      refine ⟨1589073202795037670505199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4237528540786767121347197 1589073202795037670505199)
                      ·
                        rfl

theorem cell23_3094709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 4, 1, 1, 3].length) (baseStart_3094709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3094709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3094709 prefixEnd_3094709 := by exact prefixLift 3094709
  have htrace : WordTrace (prefixWord ++ tailWord_3094709) baseStart_3094709 baseEnd_3094709 := by
    simpa [prefixWord, tailWord_3094709, baseEnd_3094709] using wordTrace_append hprefix tailTrace_3094709
  have hstable : (prefixWord ++ tailWord_3094709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3094709).length < 2 ^ (prefixWord ++ tailWord_3094709).sum := by decide
  have hdescent : baseEnd_3094709 < baseStart_3094709 := by decide
  rcases family_descends (prefixWord ++ tailWord_3094709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3094738 : List Nat := [3, 2, 2, 2, 1, 3, 3, 7]
def baseStart_3094738 : Nat := 118140960795 + 3094738 * 2 ^ 59
def prefixEnd_3094738 : Nat := 4983230072969 + 3 ^ 40 * 3094738 * 2
def baseEnd_3094738 : Nat := 58855114582741409520095

theorem tailTrace_3094738 : CollatzResearch.WordTrace tailWord_3094738 prefixEnd_3094738 58855114582741409520095 := by
  unfold tailWord_3094738
  simp only [CollatzResearch.WordTrace]
  refine ⟨28218591965575060004089217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75249578574866826677571245 28218591965575060004089217)
  ·
    refine ⟨21163943974181295003066913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28218591965575060004089217 21163943974181295003066913)
    ·
      refine ⟨15872957980635971252300185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21163943974181295003066913 15872957980635971252300185)
      ·
        refine ⟨11904718485476978439225139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15872957980635971252300185 11904718485476978439225139)
        ·
          refine ⟨17857077728215467658837709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11904718485476978439225139 17857077728215467658837709)
          ·
            refine ⟨6696404148080800372064141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17857077728215467658837709 6696404148080800372064141)
            ·
              refine ⟨2511151555530300139524053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6696404148080800372064141 2511151555530300139524053)
              ·
                refine ⟨58855114582741409520095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2511151555530300139524053 58855114582741409520095)
                ·
                  rfl

theorem cell23_3094738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 3, 7].length) (baseStart_3094738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3094738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3094738 prefixEnd_3094738 := by exact prefixLift 3094738
  have htrace : WordTrace (prefixWord ++ tailWord_3094738) baseStart_3094738 baseEnd_3094738 := by
    simpa [prefixWord, tailWord_3094738, baseEnd_3094738] using wordTrace_append hprefix tailTrace_3094738
  have hstable : (prefixWord ++ tailWord_3094738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3094738).length < 2 ^ (prefixWord ++ tailWord_3094738).sum := by decide
  have hdescent : baseEnd_3094738 < baseStart_3094738 := by decide
  rcases family_descends (prefixWord ++ tailWord_3094738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3094749 : List Nat := [1, 4, 3, 2, 1, 1, 1, 5, 1, 2, 2]
def baseStart_3094749 : Nat := 118140960795 + 3094749 * 2 ^ 59
def prefixEnd_3094749 : Nat := 4983230072969 + 3 ^ 40 * 3094749 * 2
def baseEnd_3094749 : Nat := 1589093742021217514005015

theorem tailTrace_3094749 : CollatzResearch.WordTrace tailWord_3094749 prefixEnd_3094749 1589093742021217514005015 := by
  unfold tailWord_3094749
  simp only [CollatzResearch.WordTrace]
  refine ⟨112874769065260388895007301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75249846043506925930004867 112874769065260388895007301)
  ·
    refine ⟨21164019199736322917813869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 112874769065260388895007301 21164019199736322917813869)
    ·
      refine ⟨7936507199901121094180201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21164019199736322917813869 7936507199901121094180201)
      ·
        refine ⟨5952380399925840820635151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7936507199901121094180201 5952380399925840820635151)
        ·
          refine ⟨8928570599888761230952727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5952380399925840820635151 8928570599888761230952727)
          ·
            refine ⟨13392855899833141846429091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8928570599888761230952727 13392855899833141846429091)
            ·
              refine ⟨20089283849749712769643637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13392855899833141846429091 20089283849749712769643637)
              ·
                refine ⟨1883370360914035572154091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20089283849749712769643637 1883370360914035572154091)
                ·
                  refine ⟨2825055541371053358231137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1883370360914035572154091 2825055541371053358231137)
                  ·
                    refine ⟨2118791656028290018673353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2825055541371053358231137 2118791656028290018673353)
                    ·
                      refine ⟨1589093742021217514005015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2118791656028290018673353 1589093742021217514005015)
                      ·
                        rfl

theorem cell23_3094749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 5, 1, 2, 2].length) (baseStart_3094749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3094749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3094749 prefixEnd_3094749 := by exact prefixLift 3094749
  have htrace : WordTrace (prefixWord ++ tailWord_3094749) baseStart_3094749 baseEnd_3094749 := by
    simpa [prefixWord, tailWord_3094749, baseEnd_3094749] using wordTrace_append hprefix tailTrace_3094749
  have hstable : (prefixWord ++ tailWord_3094749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3094749).length < 2 ^ (prefixWord ++ tailWord_3094749).sum := by decide
  have hdescent : baseEnd_3094749 < baseStart_3094749 := by decide
  rcases family_descends (prefixWord ++ tailWord_3094749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3094792 : List Nat := [2, 1, 3, 2, 3, 2, 2, 2, 1, 3, 2]
def baseStart_3094792 : Nat := 118140960795 + 3094792 * 2 ^ 59
def prefixEnd_3094792 : Nat := 4983230072969 + 3 ^ 40 * 3094792 * 2
def baseEnd_3094792 : Nat := 1589115821689360845767317

theorem tailTrace_3094792 : CollatzResearch.WordTrace tailWord_3094792 prefixEnd_3094792 1589115821689360845767317 := by
  unfold tailWord_3094792
  simp only [CollatzResearch.WordTrace]
  refine ⟨56438168702052303619411315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75250891602736404825881753 56438168702052303619411315)
  ·
    refine ⟨84657253053078455429116973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56438168702052303619411315 84657253053078455429116973)
    ·
      refine ⟨31746469894904420785918865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84657253053078455429116973 31746469894904420785918865)
      ·
        refine ⟨23809852421178315589439149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31746469894904420785918865 23809852421178315589439149)
        ·
          refine ⟨8928694657941868346039681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23809852421178315589439149 8928694657941868346039681)
          ·
            refine ⟨6696520993456401259529761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8928694657941868346039681 6696520993456401259529761)
            ·
              refine ⟨5022390745092300944647321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6696520993456401259529761 5022390745092300944647321)
              ·
                refine ⟨3766793058819225708485491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5022390745092300944647321 3766793058819225708485491)
                ·
                  refine ⟨5650189588228838562728237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3766793058819225708485491 5650189588228838562728237)
                  ·
                    refine ⟨2118821095585814461023089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5650189588228838562728237 2118821095585814461023089)
                    ·
                      refine ⟨1589115821689360845767317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2118821095585814461023089 1589115821689360845767317)
                      ·
                        rfl

theorem cell23_3094792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 2, 2, 1, 3, 2].length) (baseStart_3094792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3094792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3094792 prefixEnd_3094792 := by exact prefixLift 3094792
  have htrace : WordTrace (prefixWord ++ tailWord_3094792) baseStart_3094792 baseEnd_3094792 := by
    simpa [prefixWord, tailWord_3094792, baseEnd_3094792] using wordTrace_append hprefix tailTrace_3094792
  have hstable : (prefixWord ++ tailWord_3094792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3094792).length < 2 ^ (prefixWord ++ tailWord_3094792).sum := by decide
  have hdescent : baseEnd_3094792 < baseStart_3094792 := by decide
  rcases family_descends (prefixWord ++ tailWord_3094792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3094805 : List Nat := [1, 3, 2, 1, 2, 1, 3, 2, 4, 2, 2]
def baseStart_3094805 : Nat := 118140960795 + 3094805 * 2 ^ 59
def prefixEnd_3094805 : Nat := 4983230072969 + 3 ^ 40 * 3094805 * 2
def baseEnd_3094805 : Nat := 1589122496937869294904757

theorem tailTrace_3094805 : CollatzResearch.WordTrace tailWord_3094805 prefixEnd_3094805 1589122496937869294904757 := by
  unfold tailWord_3094805
  simp only [CollatzResearch.WordTrace]
  refine ⟨112876811553057510459045869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75251207702038340306030579 112876811553057510459045869)
  ·
    refine ⟨42328804332396566422142201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112876811553057510459045869 42328804332396566422142201)
    ·
      refine ⟨31746603249297424816606651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42328804332396566422142201 31746603249297424816606651)
      ·
        refine ⟨47619904873946137224909977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31746603249297424816606651 47619904873946137224909977)
        ·
          refine ⟨35714928655459602918682483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47619904873946137224909977 35714928655459602918682483)
          ·
            refine ⟨53572392983189404378023725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35714928655459602918682483 53572392983189404378023725)
            ·
              refine ⟨20089647368696026641758897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53572392983189404378023725 20089647368696026641758897)
              ·
                refine ⟨15067235526522019981319173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20089647368696026641758897 15067235526522019981319173)
                ·
                  refine ⟨2825106661222878746497345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15067235526522019981319173 2825106661222878746497345)
                  ·
                    refine ⟨2118829995917159059873009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2825106661222878746497345 2118829995917159059873009)
                    ·
                      refine ⟨1589122496937869294904757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2118829995917159059873009 1589122496937869294904757)
                      ·
                        rfl

theorem cell23_3094805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 2, 4, 2, 2].length) (baseStart_3094805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3094805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3094805 prefixEnd_3094805 := by exact prefixLift 3094805
  have htrace : WordTrace (prefixWord ++ tailWord_3094805) baseStart_3094805 baseEnd_3094805 := by
    simpa [prefixWord, tailWord_3094805, baseEnd_3094805] using wordTrace_append hprefix tailTrace_3094805
  have hstable : (prefixWord ++ tailWord_3094805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3094805).length < 2 ^ (prefixWord ++ tailWord_3094805).sum := by decide
  have hdescent : baseEnd_3094805 < baseStart_3094805 := by decide
  rcases family_descends (prefixWord ++ tailWord_3094805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3094828 : List Nat := [2, 2, 1, 1, 1, 3, 2, 6, 5]
def baseStart_3094828 : Nat := 118140960795 + 3094828 * 2 ^ 59
def prefixEnd_3094828 : Nat := 4983230072969 + 3 ^ 40 * 3094828 * 2
def baseEnd_3094828 : Nat := 176570478554769189435239

theorem tailTrace_3094828 : CollatzResearch.WordTrace tailWord_3094828 prefixEnd_3094828 176570478554769189435239 := by
  unfold tailWord_3094828
  simp only [CollatzResearch.WordTrace]
  refine ⟨56438825215987092693566569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75251766954649456924755425 56438825215987092693566569)
  ·
    refine ⟨42329118911990319520174927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56438825215987092693566569 42329118911990319520174927)
    ·
      refine ⟨63493678367985479280262391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42329118911990319520174927 63493678367985479280262391)
      ·
        refine ⟨95240517551978218920393587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63493678367985479280262391 95240517551978218920393587)
        ·
          refine ⟨142860776327967328380590381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95240517551978218920393587 142860776327967328380590381)
          ·
            refine ⟨53572791122987748142721393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 142860776327967328380590381 53572791122987748142721393)
            ·
              refine ⟨40179593342240811107041045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53572791122987748142721393 40179593342240811107041045)
              ·
                refine ⟨1883418437917538020642549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 40179593342240811107041045 1883418437917538020642549)
                ·
                  refine ⟨176570478554769189435239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1883418437917538020642549 176570478554769189435239)
                  ·
                    rfl

theorem cell23_3094828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 6, 5].length) (baseStart_3094828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3094828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3094828 prefixEnd_3094828 := by exact prefixLift 3094828
  have htrace : WordTrace (prefixWord ++ tailWord_3094828) baseStart_3094828 baseEnd_3094828 := by
    simpa [prefixWord, tailWord_3094828, baseEnd_3094828] using wordTrace_append hprefix tailTrace_3094828
  have hstable : (prefixWord ++ tailWord_3094828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3094828).length < 2 ^ (prefixWord ++ tailWord_3094828).sum := by decide
  have hdescent : baseEnd_3094828 < baseStart_3094828 := by decide
  rcases family_descends (prefixWord ++ tailWord_3094828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3094848 : List Nat := [2, 1, 1, 2, 2, 1, 2, 1, 4, 5, 2]
def baseStart_3094848 : Nat := 118140960795 + 3094848 * 2 ^ 59
def prefixEnd_3094848 : Nat := 4983230072969 + 3 ^ 40 * 3094848 * 2
def baseEnd_3094848 : Nat := 1589144576606012626667059

theorem tailTrace_3094848 : CollatzResearch.WordTrace tailWord_3094848 prefixEnd_3094848 1589144576606012626667059 := by
  unfold tailWord_3094848
  simp only [CollatzResearch.WordTrace]
  refine ⟨56439189945950864401430599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75252253261267819201907465 56439189945950864401430599)
  ·
    refine ⟨84658784918926296602145899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56439189945950864401430599 84658784918926296602145899)
    ·
      refine ⟨126988177378389444903218849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84658784918926296602145899 126988177378389444903218849)
      ·
        refine ⟨95241133033792083677414137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126988177378389444903218849 95241133033792083677414137)
        ·
          refine ⟨71430849775344062758060603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95241133033792083677414137 71430849775344062758060603)
          ·
            refine ⟨107146274663016094137090905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71430849775344062758060603 107146274663016094137090905)
            ·
              refine ⟨80359705997262070602818179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107146274663016094137090905 80359705997262070602818179)
              ·
                refine ⟨120539558995893105904227269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80359705997262070602818179 120539558995893105904227269)
                ·
                  refine ⟨22601167311729957357042613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 120539558995893105904227269 22601167311729957357042613)
                  ·
                    refine ⟨2118859435474683502222745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22601167311729957357042613 2118859435474683502222745)
                    ·
                      refine ⟨1589144576606012626667059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2118859435474683502222745 1589144576606012626667059)
                      ·
                        rfl

theorem cell23_3094848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 4, 5, 2].length) (baseStart_3094848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3094848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3094848 prefixEnd_3094848 := by exact prefixLift 3094848
  have htrace : WordTrace (prefixWord ++ tailWord_3094848) baseStart_3094848 baseEnd_3094848 := by
    simpa [prefixWord, tailWord_3094848, baseEnd_3094848] using wordTrace_append hprefix tailTrace_3094848
  have hstable : (prefixWord ++ tailWord_3094848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3094848).length < 2 ^ (prefixWord ++ tailWord_3094848).sum := by decide
  have hdescent : baseEnd_3094848 < baseStart_3094848 := by decide
  rcases family_descends (prefixWord ++ tailWord_3094848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3094868 : List Nat := [2, 4, 1, 1, 2, 2, 1, 2, 1, 2, 5]
def baseStart_3094868 : Nat := 118140960795 + 3094868 * 2 ^ 59
def prefixEnd_3094868 : Nat := 4983230072969 + 3 ^ 40 * 3094868 * 2
def baseEnd_3094868 : Nat := 1589154846219102548416967

theorem tailTrace_3094868 : CollatzResearch.WordTrace tailWord_3094868 prefixEnd_3094868 1589154846219102548416967 := by
  unfold tailWord_3094868
  simp only [CollatzResearch.WordTrace]
  refine ⟨56439554675914636109294629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75252739567886181479059505 56439554675914636109294629)
  ·
    refine ⟨10582416501733994270492743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56439554675914636109294629 10582416501733994270492743)
    ·
      refine ⟨15873624752600991405739115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10582416501733994270492743 15873624752600991405739115)
      ·
        refine ⟨23810437128901487108608673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15873624752600991405739115 23810437128901487108608673)
        ·
          refine ⟨17857827846676115331456505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23810437128901487108608673 17857827846676115331456505)
          ·
            refine ⟨13393370885007086498592379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17857827846676115331456505 13393370885007086498592379)
            ·
              refine ⟨20090056327510629747888569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13393370885007086498592379 20090056327510629747888569)
              ·
                refine ⟨15067542245632972310916427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20090056327510629747888569 15067542245632972310916427)
                ·
                  refine ⟨22601313368449458466374641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15067542245632972310916427 22601313368449458466374641)
                  ·
                    refine ⟨16950985026337093849780981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22601313368449458466374641 16950985026337093849780981)
                    ·
                      refine ⟨1589154846219102548416967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16950985026337093849780981 1589154846219102548416967)
                      ·
                        rfl

theorem cell23_3094868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 2, 1, 2, 5].length) (baseStart_3094868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3094868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3094868 prefixEnd_3094868 := by exact prefixLift 3094868
  have htrace : WordTrace (prefixWord ++ tailWord_3094868) baseStart_3094868 baseEnd_3094868 := by
    simpa [prefixWord, tailWord_3094868, baseEnd_3094868] using wordTrace_append hprefix tailTrace_3094868
  have hstable : (prefixWord ++ tailWord_3094868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3094868).length < 2 ^ (prefixWord ++ tailWord_3094868).sum := by decide
  have hdescent : baseEnd_3094868 < baseStart_3094868 := by decide
  rcases family_descends (prefixWord ++ tailWord_3094868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3094891 : List Nat := [1, 1, 1, 1, 2, 2, 2, 4, 2, 1, 6]
def baseStart_3094891 : Nat := 118140960795 + 3094891 * 2 ^ 59
def prefixEnd_3094891 : Nat := 4983230072969 + 3 ^ 40 * 3094891 * 2
def baseEnd_3094891 : Nat := 1589166656274155958429361

theorem tailTrace_3094891 : CollatzResearch.WordTrace tailWord_3094891 prefixEnd_3094891 1589166656274155958429361 := by
  unfold tailWord_3094891
  simp only [CollatzResearch.WordTrace]
  refine ⟨112879948230745947146676527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75253298820497298097784351 112879948230745947146676527)
  ·
    refine ⟨169319922346118920720014791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112879948230745947146676527 169319922346118920720014791)
    ·
      refine ⟨253979883519178381080022187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169319922346118920720014791 253979883519178381080022187)
      ·
        refine ⟨380969825278767571620033281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253979883519178381080022187 380969825278767571620033281)
        ·
          refine ⟨285727368959075678715024961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 380969825278767571620033281 285727368959075678715024961)
          ·
            refine ⟨214295526719306759036268721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 285727368959075678715024961 214295526719306759036268721)
            ·
              refine ⟨160721645039480069277201541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 214295526719306759036268721 160721645039480069277201541)
              ·
                refine ⟨30135308444902512989475289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 160721645039480069277201541 30135308444902512989475289)
                ·
                  refine ⟨22601481333676884742106467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30135308444902512989475289 22601481333676884742106467)
                  ·
                    refine ⟨33902222000515327113159701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22601481333676884742106467 33902222000515327113159701)
                    ·
                      refine ⟨1589166656274155958429361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33902222000515327113159701 1589166656274155958429361)
                      ·
                        rfl

theorem cell23_3094891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4, 2, 1, 6].length) (baseStart_3094891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3094891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3094891 prefixEnd_3094891 := by exact prefixLift 3094891
  have htrace : WordTrace (prefixWord ++ tailWord_3094891) baseStart_3094891 baseEnd_3094891 := by
    simpa [prefixWord, tailWord_3094891, baseEnd_3094891] using wordTrace_append hprefix tailTrace_3094891
  have hstable : (prefixWord ++ tailWord_3094891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3094891).length < 2 ^ (prefixWord ++ tailWord_3094891).sum := by decide
  have hdescent : baseEnd_3094891 < baseStart_3094891 := by decide
  rcases family_descends (prefixWord ++ tailWord_3094891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3094915 : List Nat := [1, 1, 1, 3, 6, 1, 1, 1, 1, 4, 3]
def baseStart_3094915 : Nat := 118140960795 + 3094915 * 2 ^ 59
def prefixEnd_3094915 : Nat := 4983230072969 + 3 ^ 40 * 3094915 * 2
def baseEnd_3094915 : Nat := 1589178979809863864529251

theorem tailTrace_3094915 : CollatzResearch.WordTrace tailWord_3094915 prefixEnd_3094915 1589178979809863864529251 := by
  unfold tailWord_3094915
  simp only [CollatzResearch.WordTrace]
  refine ⟨112880823582658999245550199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75253882388439332830366799 112880823582658999245550199)
  ·
    refine ⟨169321235373988498868325299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112880823582658999245550199 169321235373988498868325299)
    ·
      refine ⟨253981853060982748302487949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169321235373988498868325299 253981853060982748302487949)
      ·
        refine ⟨95243194897868530613432981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 253981853060982748302487949 95243194897868530613432981)
        ·
          refine ⟨4464524760837587372504671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 95243194897868530613432981 4464524760837587372504671)
          ·
            refine ⟨6696787141256381058757007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4464524760837587372504671 6696787141256381058757007)
            ·
              refine ⟨10045180711884571588135511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6696787141256381058757007 10045180711884571588135511)
              ·
                refine ⟨15067771067826857382203267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10045180711884571588135511 15067771067826857382203267)
                ·
                  refine ⟨22601656601740286073304901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15067771067826857382203267 22601656601740286073304901)
                  ·
                    refine ⟨4237810612826303638744669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22601656601740286073304901 4237810612826303638744669)
                    ·
                      refine ⟨1589178979809863864529251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4237810612826303638744669 1589178979809863864529251)
                      ·
                        rfl

theorem cell23_3094915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 1, 1, 4, 3].length) (baseStart_3094915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3094915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3094915 prefixEnd_3094915 := by exact prefixLift 3094915
  have htrace : WordTrace (prefixWord ++ tailWord_3094915) baseStart_3094915 baseEnd_3094915 := by
    simpa [prefixWord, tailWord_3094915, baseEnd_3094915] using wordTrace_append hprefix tailTrace_3094915
  have hstable : (prefixWord ++ tailWord_3094915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3094915).length < 2 ^ (prefixWord ++ tailWord_3094915).sum := by decide
  have hdescent : baseEnd_3094915 < baseStart_3094915 := by decide
  rcases family_descends (prefixWord ++ tailWord_3094915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3094938 : List Nat := [3, 1, 1, 4, 1, 2, 1, 1, 1, 2, 6]
def baseStart_3094938 : Nat := 118140960795 + 3094938 * 2 ^ 59
def prefixEnd_3094938 : Nat := 4983230072969 + 3 ^ 40 * 3094938 * 2
def baseEnd_3094938 : Nat := 1589190789864917274541645

theorem tailTrace_3094938 : CollatzResearch.WordTrace tailWord_3094938 prefixEnd_3094938 1589190789864917274541645 := by
  unfold tailWord_3094938
  simp only [CollatzResearch.WordTrace]
  refine ⟨28220415615393918543409367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75254441641050449449091645 28220415615393918543409367)
  ·
    refine ⟨42330623423090877815114051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28220415615393918543409367 42330623423090877815114051)
    ·
      refine ⟨63495935134636316722671077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42330623423090877815114051 63495935134636316722671077)
      ·
        refine ⟨11905487837744309385500827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63495935134636316722671077 11905487837744309385500827)
        ·
          refine ⟨17858231756616464078251241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11905487837744309385500827 17858231756616464078251241)
          ·
            refine ⟨13393673817462348058688431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17858231756616464078251241 13393673817462348058688431)
            ·
              refine ⟨20090510726193522088032647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13393673817462348058688431 20090510726193522088032647)
              ·
                refine ⟨30135766089290283132048971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20090510726193522088032647 30135766089290283132048971)
                ·
                  refine ⟨45203649133935424698073457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30135766089290283132048971 45203649133935424698073457)
                  ·
                    refine ⟨33902736850451568523555093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45203649133935424698073457 33902736850451568523555093)
                    ·
                      refine ⟨1589190789864917274541645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33902736850451568523555093 1589190789864917274541645)
                      ·
                        rfl

theorem cell23_3094938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 1, 1, 2, 6].length) (baseStart_3094938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3094938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3094938 prefixEnd_3094938 := by exact prefixLift 3094938
  have htrace : WordTrace (prefixWord ++ tailWord_3094938) baseStart_3094938 baseEnd_3094938 := by
    simpa [prefixWord, tailWord_3094938, baseEnd_3094938] using wordTrace_append hprefix tailTrace_3094938
  have hstable : (prefixWord ++ tailWord_3094938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3094938).length < 2 ^ (prefixWord ++ tailWord_3094938).sum := by decide
  have hdescent : baseEnd_3094938 < baseStart_3094938 := by decide
  rcases family_descends (prefixWord ++ tailWord_3094938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3094948 : List Nat := [2, 3, 1, 2, 1, 1, 2, 1, 5, 5]
def baseStart_3094948 : Nat := 118140960795 + 3094948 * 2 ^ 59
def prefixEnd_3094948 : Nat := 4983230072969 + 3 ^ 40 * 3094948 * 2
def baseEnd_3094948 : Nat := 529731974890487411805533

theorem tailTrace_3094948 : CollatzResearch.WordTrace tailWord_3094948 prefixEnd_3094948 529731974890487411805533 := by
  unfold tailWord_3094948
  simp only [CollatzResearch.WordTrace]
  refine ⟨56441013595769722940750749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75254684794359630587667665 56441013595769722940750749)
  ·
    refine ⟨21165380098413646102781531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56441013595769722940750749 21165380098413646102781531)
    ·
      refine ⟨31748070147620469154172297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21165380098413646102781531 31748070147620469154172297)
      ·
        refine ⟨23811052610715351865629223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31748070147620469154172297 23811052610715351865629223)
        ·
          refine ⟨35716578916073027798443835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23811052610715351865629223 35716578916073027798443835)
          ·
            refine ⟨53574868374109541697665753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35716578916073027798443835 53574868374109541697665753)
            ·
              refine ⟨40181151280582156273249315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53574868374109541697665753 40181151280582156273249315)
              ·
                refine ⟨60271726920873234409873973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40181151280582156273249315 60271726920873234409873973)
                ·
                  refine ⟨5650474398831865725925685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 60271726920873234409873973 5650474398831865725925685)
                  ·
                    refine ⟨529731974890487411805533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5650474398831865725925685 529731974890487411805533)
                    ·
                      rfl

theorem cell23_3094948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 1, 5, 5].length) (baseStart_3094948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3094948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3094948 prefixEnd_3094948 := by exact prefixLift 3094948
  have htrace : WordTrace (prefixWord ++ tailWord_3094948) baseStart_3094948 baseEnd_3094948 := by
    simpa [prefixWord, tailWord_3094948, baseEnd_3094948] using wordTrace_append hprefix tailTrace_3094948
  have hstable : (prefixWord ++ tailWord_3094948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3094948).length < 2 ^ (prefixWord ++ tailWord_3094948).sum := by decide
  have hdescent : baseEnd_3094948 < baseStart_3094948 := by decide
  rcases family_descends (prefixWord ++ tailWord_3094948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3094972 : List Nat := [2, 2, 2, 4, 1, 1, 2, 1, 1, 5, 2]
def baseStart_3094972 : Nat := 118140960795 + 3094972 * 2 ^ 59
def prefixEnd_3094972 : Nat := 4983230072969 + 3 ^ 40 * 3094972 * 2
def baseEnd_3094972 : Nat := 1589208248207170141516489

theorem tailTrace_3094972 : CollatzResearch.WordTrace tailWord_3094972 prefixEnd_3094972 1589208248207170141516489 := by
  unfold tailWord_3094972
  simp only [CollatzResearch.WordTrace]
  refine ⟨56441451271726248990187585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75255268362301665320250113 56441451271726248990187585)
  ·
    refine ⟨42331088453794686742640689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56441451271726248990187585 42331088453794686742640689)
    ·
      refine ⟨31748316340346015056980517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42331088453794686742640689 31748316340346015056980517)
      ·
        refine ⟨5952809313814877823183847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31748316340346015056980517 5952809313814877823183847)
        ·
          refine ⟨8929213970722316734775771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5952809313814877823183847 8929213970722316734775771)
          ·
            refine ⟨13393820956083475102163657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8929213970722316734775771 13393820956083475102163657)
            ·
              refine ⟨10045365717062606326622743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13393820956083475102163657 10045365717062606326622743)
              ·
                refine ⟨15068048575593909489934115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10045365717062606326622743 15068048575593909489934115)
                ·
                  refine ⟨22602072863390864234901173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15068048575593909489934115 22602072863390864234901173)
                  ·
                    refine ⟨2118944330942893522021985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22602072863390864234901173 2118944330942893522021985)
                    ·
                      refine ⟨1589208248207170141516489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2118944330942893522021985 1589208248207170141516489)
                      ·
                        rfl

theorem cell23_3094972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 1, 1, 5, 2].length) (baseStart_3094972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3094972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3094972 prefixEnd_3094972 := by exact prefixLift 3094972
  have htrace : WordTrace (prefixWord ++ tailWord_3094972) baseStart_3094972 baseEnd_3094972 := by
    simpa [prefixWord, tailWord_3094972, baseEnd_3094972] using wordTrace_append hprefix tailTrace_3094972
  have hstable : (prefixWord ++ tailWord_3094972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3094972).length < 2 ^ (prefixWord ++ tailWord_3094972).sum := by decide
  have hdescent : baseEnd_3094972 < baseStart_3094972 := by decide
  rcases family_descends (prefixWord ++ tailWord_3094972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3094985 : List Nat := [1, 2, 1, 1, 2, 1, 6, 3, 1, 1, 4]
def baseStart_3094985 : Nat := 118140960795 + 3094985 * 2 ^ 59
def prefixEnd_3094985 : Nat := 4983230072969 + 3 ^ 40 * 3094985 * 2
def baseEnd_3094985 : Nat := 1589214923455678590653929

theorem tailTrace_3094985 : CollatzResearch.WordTrace tailWord_3094985 prefixEnd_3094985 1589214923455678590653929 := by
  unfold tailWord_3094985
  simp only [CollatzResearch.WordTrace]
  refine ⟨112883376692405401200598409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75255584461603600800398939 112883376692405401200598409)
  ·
    refine ⟨84662532519304050900448807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112883376692405401200598409 84662532519304050900448807)
    ·
      refine ⟨126993798778956076350673211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84662532519304050900448807 126993798778956076350673211)
      ·
        refine ⟨190490698168434114526009817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126993798778956076350673211 190490698168434114526009817)
        ·
          refine ⟨142868023626325585894507363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 190490698168434114526009817 142868023626325585894507363)
          ·
            refine ⟨214302035439488378841761045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142868023626325585894507363 214302035439488378841761045)
            ·
              refine ⟨10045407911226017758207549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 214302035439488378841761045 10045407911226017758207549)
              ·
                refine ⟨3767027966709756659327831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10045407911226017758207549 3767027966709756659327831)
                ·
                  refine ⟨5650541950064634988991747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3767027966709756659327831 5650541950064634988991747)
                  ·
                    refine ⟨8475812925096952483487621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5650541950064634988991747 8475812925096952483487621)
                    ·
                      refine ⟨1589214923455678590653929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8475812925096952483487621 1589214923455678590653929)
                      ·
                        rfl

theorem cell23_3094985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 3, 1, 1, 4].length) (baseStart_3094985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3094985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3094985 prefixEnd_3094985 := by exact prefixLift 3094985
  have htrace : WordTrace (prefixWord ++ tailWord_3094985) baseStart_3094985 baseEnd_3094985 := by
    simpa [prefixWord, tailWord_3094985, baseEnd_3094985] using wordTrace_append hprefix tailTrace_3094985
  have hstable : (prefixWord ++ tailWord_3094985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3094985).length < 2 ^ (prefixWord ++ tailWord_3094985).sum := by decide
  have hdescent : baseEnd_3094985 < baseStart_3094985 := by decide
  rcases family_descends (prefixWord ++ tailWord_3094985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3095005 : List Nat := [1, 4, 3, 1, 1, 1, 1, 4, 1, 1, 5]
def baseStart_3095005 : Nat := 118140960795 + 3095005 * 2 ^ 59
def prefixEnd_3095005 : Nat := 4983230072969 + 3 ^ 40 * 3095005 * 2
def baseEnd_3095005 : Nat := 1589225193068768512403837

theorem tailTrace_3095005 : CollatzResearch.WordTrace tailWord_3095005 prefixEnd_3095005 1589225193068768512403837 := by
  unfold tailWord_3095005
  simp only [CollatzResearch.WordTrace]
  refine ⟨112884106152332944616326469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75256070768221963077550979 112884106152332944616326469)
  ·
    refine ⟨21165769903562427115561213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 112884106152332944616326469 21165769903562427115561213)
    ·
      refine ⟨7937163713835910168335455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21165769903562427115561213 7937163713835910168335455)
      ·
        refine ⟨11905745570753865252503183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7937163713835910168335455 11905745570753865252503183)
        ·
          refine ⟨17858618356130797878754775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11905745570753865252503183 17858618356130797878754775)
          ·
            refine ⟨26787927534196196818132163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17858618356130797878754775 26787927534196196818132163)
            ·
              refine ⟨40181891301294295227198245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26787927534196196818132163 40181891301294295227198245)
              ·
                refine ⟨7534104618992680355099671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40181891301294295227198245 7534104618992680355099671)
                ·
                  refine ⟨11301156928489020532649507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7534104618992680355099671 11301156928489020532649507)
                  ·
                    refine ⟨16951735392733530798974261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11301156928489020532649507 16951735392733530798974261)
                    ·
                      refine ⟨1589225193068768512403837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16951735392733530798974261 1589225193068768512403837)
                      ·
                        rfl

theorem cell23_3095005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 4, 1, 1, 5].length) (baseStart_3095005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3095005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3095005 prefixEnd_3095005 := by exact prefixLift 3095005
  have htrace : WordTrace (prefixWord ++ tailWord_3095005) baseStart_3095005 baseEnd_3095005 := by
    simpa [prefixWord, tailWord_3095005, baseEnd_3095005] using wordTrace_append hprefix tailTrace_3095005
  have hstable : (prefixWord ++ tailWord_3095005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3095005).length < 2 ^ (prefixWord ++ tailWord_3095005).sum := by decide
  have hdescent : baseEnd_3095005 < baseStart_3095005 := by decide
  rcases family_descends (prefixWord ++ tailWord_3095005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3095008 : List Nat := [2, 1, 1, 3, 1, 1, 6, 8]
def baseStart_3095008 : Nat := 118140960795 + 3095008 * 2 ^ 59
def prefixEnd_3095008 : Nat := 4983230072969 + 3 ^ 40 * 3095008 * 2
def baseEnd_3095008 : Nat := 58860249389286370395049

theorem tailTrace_3095008 : CollatzResearch.WordTrace tailWord_3095008 prefixEnd_3095008 58860249389286370395049 := by
  unfold tailWord_3095008
  simp only [CollatzResearch.WordTrace]
  refine ⟨56442107785661038064342839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75256143714214717419123785 56442107785661038064342839)
  ·
    refine ⟨84663161678491557096514259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56442107785661038064342839 84663161678491557096514259)
    ·
      refine ⟨126994742517737335644771389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84663161678491557096514259 126994742517737335644771389)
      ·
        refine ⟨47623028444151500866789271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126994742517737335644771389 47623028444151500866789271)
        ·
          refine ⟨71434542666227251300183907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47623028444151500866789271 71434542666227251300183907)
          ·
            refine ⟨107151813999340876950275861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71434542666227251300183907 107151813999340876950275861)
            ·
              refine ⟨5022741281219103607044181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 107151813999340876950275861 5022741281219103607044181)
              ·
                refine ⟨58860249389286370395049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5022741281219103607044181 58860249389286370395049)
                ·
                  rfl

theorem cell23_3095008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 6, 8].length) (baseStart_3095008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3095008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3095008 prefixEnd_3095008 := by exact prefixLift 3095008
  have htrace : WordTrace (prefixWord ++ tailWord_3095008) baseStart_3095008 baseEnd_3095008 := by
    simpa [prefixWord, tailWord_3095008, baseEnd_3095008] using wordTrace_append hprefix tailTrace_3095008
  have hstable : (prefixWord ++ tailWord_3095008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3095008).length < 2 ^ (prefixWord ++ tailWord_3095008).sum := by decide
  have hdescent : baseEnd_3095008 < baseStart_3095008 := by decide
  rcases family_descends (prefixWord ++ tailWord_3095008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3095015 : List Nat := [1, 1, 5, 2, 1, 1, 2, 3, 1, 2, 4]
def baseStart_3095015 : Nat := 118140960795 + 3095015 * 2 ^ 59
def prefixEnd_3095015 : Nat := 4983230072969 + 3 ^ 40 * 3095015 * 2
def baseEnd_3095015 : Nat := 1589230327875313473278791

theorem tailTrace_3095015 : CollatzResearch.WordTrace tailWord_3095015 prefixEnd_3095015 1589230327875313473278791 := by
  unfold tailWord_3095015
  simp only [CollatzResearch.WordTrace]
  refine ⟨112884470882296716324190499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75256313921531144216126999 112884470882296716324190499)
  ·
    refine ⟨169326706323445074486285749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112884470882296716324190499 169326706323445074486285749)
    ·
      refine ⟨15874378717822975733089289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 169326706323445074486285749 15874378717822975733089289)
      ·
        refine ⟨11905784038367231799816967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15874378717822975733089289 11905784038367231799816967)
        ·
          refine ⟨17858676057550847699725451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11905784038367231799816967 17858676057550847699725451)
          ·
            refine ⟨26788014086326271549588177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17858676057550847699725451 26788014086326271549588177)
            ·
              refine ⟨20091010564744703662191133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26788014086326271549588177 20091010564744703662191133)
              ·
                refine ⟨7534128961779263873321675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20091010564744703662191133 7534128961779263873321675)
                ·
                  refine ⟨11301193442668895809982513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7534128961779263873321675 11301193442668895809982513)
                  ·
                    refine ⟨8475895082001671857486885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11301193442668895809982513 8475895082001671857486885)
                    ·
                      refine ⟨1589230327875313473278791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8475895082001671857486885 1589230327875313473278791)
                      ·
                        rfl

theorem cell23_3095015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 3, 1, 2, 4].length) (baseStart_3095015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3095015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3095015 prefixEnd_3095015 := by exact prefixLift 3095015
  have htrace : WordTrace (prefixWord ++ tailWord_3095015) baseStart_3095015 baseEnd_3095015 := by
    simpa [prefixWord, tailWord_3095015, baseEnd_3095015] using wordTrace_append hprefix tailTrace_3095015
  have hstable : (prefixWord ++ tailWord_3095015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3095015).length < 2 ^ (prefixWord ++ tailWord_3095015).sum := by decide
  have hdescent : baseEnd_3095015 < baseStart_3095015 := by decide
  rcases family_descends (prefixWord ++ tailWord_3095015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3095022 : List Nat := [4, 1, 2, 1, 2, 3, 1, 1, 3, 2, 3]
def baseStart_3095022 : Nat := 118140960795 + 3095022 * 2 ^ 59
def prefixEnd_3095022 : Nat := 4983230072969 + 3 ^ 40 * 3095022 * 2
def baseEnd_3095022 : Nat := 1589233922239894945891259

theorem tailTrace_3095022 : CollatzResearch.WordTrace tailWord_3095022 prefixEnd_3095022 1589233922239894945891259 := by
  unfold tailWord_3095022
  simp only [CollatzResearch.WordTrace]
  refine ⟨14110590774158919564961915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75256484128847571013130213 14110590774158919564961915)
  ·
    refine ⟨21165886161238379347442873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14110590774158919564961915 21165886161238379347442873)
    ·
      refine ⟨15874414620928784510582155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21165886161238379347442873 15874414620928784510582155)
      ·
        refine ⟨23811621931393176765873233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15874414620928784510582155 23811621931393176765873233)
        ·
          refine ⟨17858716448544882574404925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23811621931393176765873233 17858716448544882574404925)
          ·
            refine ⟨6697018668204330965401847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17858716448544882574404925 6697018668204330965401847)
            ·
              refine ⟨10045528002306496448102771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6697018668204330965401847 10045528002306496448102771)
              ·
                refine ⟨15068292003459744672154157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10045528002306496448102771 15068292003459744672154157)
                ·
                  refine ⟨5650609501297404252057809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15068292003459744672154157 5650609501297404252057809)
                  ·
                    refine ⟨4237957125973053189043357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5650609501297404252057809 4237957125973053189043357)
                    ·
                      refine ⟨1589233922239894945891259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4237957125973053189043357 1589233922239894945891259)
                      ·
                        rfl

theorem cell23_3095022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 1, 3, 2, 3].length) (baseStart_3095022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3095022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3095022 prefixEnd_3095022 := by exact prefixLift 3095022
  have htrace : WordTrace (prefixWord ++ tailWord_3095022) baseStart_3095022 baseEnd_3095022 := by
    simpa [prefixWord, tailWord_3095022, baseEnd_3095022] using wordTrace_append hprefix tailTrace_3095022
  have hstable : (prefixWord ++ tailWord_3095022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3095022).length < 2 ^ (prefixWord ++ tailWord_3095022).sum := by decide
  have hdescent : baseEnd_3095022 < baseStart_3095022 := by decide
  rcases family_descends (prefixWord ++ tailWord_3095022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3095042 : List Nat := [3, 4, 1, 2, 3, 10]
def baseStart_3095042 : Nat := 118140960795 + 3095042 * 2 ^ 59
def prefixEnd_3095042 : Nat := 4983230072969 + 3 ^ 40 * 3095042 * 2
def baseEnd_3095042 : Nat := 6540099554950555010869

theorem tailTrace_3095042 : CollatzResearch.WordTrace tailWord_3095042 prefixEnd_3095042 6540099554950555010869 := by
  unfold tailWord_3095042
  simp only [CollatzResearch.WordTrace]
  refine ⟨28221363913299724983855845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75256970435465933290282253 28221363913299724983855845)
  ·
    refine ⟨5291505733743698434472971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28221363913299724983855845 5291505733743698434472971)
    ·
      refine ⟨7937258600615547651709457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5291505733743698434472971 7937258600615547651709457)
      ·
        refine ⟨5952943950461660738782093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7937258600615547651709457 5952943950461660738782093)
        ·
          refine ⟨2232353981423122777043285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5952943950461660738782093 2232353981423122777043285)
          ·
            refine ⟨6540099554950555010869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2232353981423122777043285 6540099554950555010869)
            ·
              rfl

theorem cell23_3095042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 10].length) (baseStart_3095042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3095042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3095042 prefixEnd_3095042 := by exact prefixLift 3095042
  have htrace : WordTrace (prefixWord ++ tailWord_3095042) baseStart_3095042 baseEnd_3095042 := by
    simpa [prefixWord, tailWord_3095042, baseEnd_3095042] using wordTrace_append hprefix tailTrace_3095042
  have hstable : (prefixWord ++ tailWord_3095042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3095042).length < 2 ^ (prefixWord ++ tailWord_3095042).sum := by decide
  have hdescent : baseEnd_3095042 < baseStart_3095042 := by decide
  rcases family_descends (prefixWord ++ tailWord_3095042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3095069 : List Nat := [1, 4, 2, 2, 1, 2, 2, 3, 2, 1, 3]
def baseStart_3095069 : Nat := 118140960795 + 3095069 * 2 ^ 59
def prefixEnd_3095069 : Nat := 4983230072969 + 3 ^ 40 * 3095069 * 2
def baseEnd_3095069 : Nat := 1589258055830656262003543

theorem tailTrace_3095069 : CollatzResearch.WordTrace tailWord_3095069 prefixEnd_3095069 1589258055830656262003543 := by
  unfold tailWord_3095069
  simp only [CollatzResearch.WordTrace]
  refine ⟨112886440424101083546656261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75257626949400722364437507 112886440424101083546656261)
  ·
    refine ⟨21166207579518953164998049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 112886440424101083546656261 21166207579518953164998049)
    ·
      refine ⟨15874655684639214873748537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21166207579518953164998049 15874655684639214873748537)
      ·
        refine ⟨11905991763479411155311403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15874655684639214873748537 11905991763479411155311403)
        ·
          refine ⟨17858987645219116732967105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11905991763479411155311403 17858987645219116732967105)
          ·
            refine ⟨13394240733914337549725329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17858987645219116732967105 13394240733914337549725329)
            ·
              refine ⟨10045680550435753162293997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13394240733914337549725329 10045680550435753162293997)
              ·
                refine ⟨3767130206413407435860249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10045680550435753162293997 3767130206413407435860249)
                ·
                  refine ⟨2825347654810055576895187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3767130206413407435860249 2825347654810055576895187)
                  ·
                    refine ⟨4238021482215083365342781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2825347654810055576895187 4238021482215083365342781)
                    ·
                      refine ⟨1589258055830656262003543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4238021482215083365342781 1589258055830656262003543)
                      ·
                        rfl

theorem cell23_3095069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 3, 2, 1, 3].length) (baseStart_3095069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3095069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3095069 prefixEnd_3095069 := by exact prefixLift 3095069
  have htrace : WordTrace (prefixWord ++ tailWord_3095069) baseStart_3095069 baseEnd_3095069 := by
    simpa [prefixWord, tailWord_3095069, baseEnd_3095069] using wordTrace_append hprefix tailTrace_3095069
  have hstable : (prefixWord ++ tailWord_3095069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3095069).length < 2 ^ (prefixWord ++ tailWord_3095069).sum := by decide
  have hdescent : baseEnd_3095069 < baseStart_3095069 := by decide
  rcases family_descends (prefixWord ++ tailWord_3095069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3095109 : List Nat := [1, 3, 1, 1, 1, 6, 1, 1, 4, 2, 2]
def baseStart_3095109 : Nat := 118140960795 + 3095109 * 2 ^ 59
def prefixEnd_3095109 : Nat := 4983230072969 + 3 ^ 40 * 3095109 * 2
def baseEnd_3095109 : Nat := 1589278595056836105503359

theorem tailTrace_3095109 : CollatzResearch.WordTrace tailWord_3095109 prefixEnd_3095109 1589278595056836105503359 := by
  unfold tailWord_3095109
  simp only [CollatzResearch.WordTrace]
  refine ⟨112887899343956170378112381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75258599562637446918741587 112887899343956170378112381)
  ·
    refine ⟨42332962253983563891792143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112887899343956170378112381 42332962253983563891792143)
    ·
      refine ⟨63499443380975345837688215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42332962253983563891792143 63499443380975345837688215)
      ·
        refine ⟨95249165071463018756532323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63499443380975345837688215 95249165071463018756532323)
        ·
          refine ⟨142873747607194528134798485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95249165071463018756532323 142873747607194528134798485)
          ·
            refine ⟨6697206919087243506318679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 142873747607194528134798485 6697206919087243506318679)
            ·
              refine ⟨10045810378630865259478019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6697206919087243506318679 10045810378630865259478019)
              ·
                refine ⟨15068715567946297889217029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10045810378630865259478019 15068715567946297889217029)
                ·
                  refine ⟨2825384168989930854228193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15068715567946297889217029 2825384168989930854228193)
                  ·
                    refine ⟨2119038126742448140671145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2825384168989930854228193 2119038126742448140671145)
                    ·
                      refine ⟨1589278595056836105503359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2119038126742448140671145 1589278595056836105503359)
                      ·
                        rfl

theorem cell23_3095109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 1, 4, 2, 2].length) (baseStart_3095109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3095109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3095109 prefixEnd_3095109 := by exact prefixLift 3095109
  have htrace : WordTrace (prefixWord ++ tailWord_3095109) baseStart_3095109 baseEnd_3095109 := by
    simpa [prefixWord, tailWord_3095109, baseEnd_3095109] using wordTrace_append hprefix tailTrace_3095109
  have hstable : (prefixWord ++ tailWord_3095109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3095109).length < 2 ^ (prefixWord ++ tailWord_3095109).sum := by decide
  have hdescent : baseEnd_3095109 < baseStart_3095109 := by decide
  rcases family_descends (prefixWord ++ tailWord_3095109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3095145 : List Nat := [1, 2, 1, 1, 1, 4, 1, 5, 2, 5]
def baseStart_3095145 : Nat := 118140960795 + 3095145 * 2 ^ 59
def prefixEnd_3095145 : Nat := 4983230072969 + 3 ^ 40 * 3095145 * 2
def baseEnd_3095145 : Nat := 529765693453465988217731

theorem tailTrace_3095145 : CollatzResearch.WordTrace tailWord_3095145 prefixEnd_3095145 529765693453465988217731 := by
  unfold tailWord_3095145
  simp only [CollatzResearch.WordTrace]
  refine ⟨112889212371825748526422889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75259474914550499017615259 112889212371825748526422889)
  ·
    refine ⟨84666909278869311394817167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112889212371825748526422889 84666909278869311394817167)
    ·
      refine ⟨127000363918303967092225751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84666909278869311394817167 127000363918303967092225751)
      ·
        refine ⟨190500545877455950638338627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127000363918303967092225751 190500545877455950638338627)
        ·
          refine ⟨285750818816183925957507941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190500545877455950638338627 285750818816183925957507941)
          ·
            refine ⟨53578278528034486117032739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 285750818816183925957507941 53578278528034486117032739)
            ·
              refine ⟨80367417792051729175549109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53578278528034486117032739 80367417792051729175549109)
              ·
                refine ⟨7534445418004849610207729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 80367417792051729175549109 7534445418004849610207729)
                ·
                  refine ⟨5650834063503637207655797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7534445418004849610207729 5650834063503637207655797)
                  ·
                    refine ⟨529765693453465988217731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5650834063503637207655797 529765693453465988217731)
                    ·
                      rfl

theorem cell23_3095145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 5, 2, 5].length) (baseStart_3095145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3095145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3095145 prefixEnd_3095145 := by exact prefixLift 3095145
  have htrace : WordTrace (prefixWord ++ tailWord_3095145) baseStart_3095145 baseEnd_3095145 := by
    simpa [prefixWord, tailWord_3095145, baseEnd_3095145] using wordTrace_append hprefix tailTrace_3095145
  have hstable : (prefixWord ++ tailWord_3095145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3095145).length < 2 ^ (prefixWord ++ tailWord_3095145).sum := by decide
  have hdescent : baseEnd_3095145 < baseStart_3095145 := by decide
  rcases family_descends (prefixWord ++ tailWord_3095145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3095149 : List Nat := [1, 5, 1, 1, 3, 1, 3, 3, 5]
def baseStart_3095149 : Nat := 118140960795 + 3095149 * 2 ^ 59
def prefixEnd_3095149 : Nat := 4983230072969 + 3 ^ 40 * 3095149 * 2
def baseEnd_3095149 : Nat := 176588792698112883222575

theorem tailTrace_3095149 : CollatzResearch.WordTrace tailWord_3095149 prefixEnd_3095149 176588792698112883222575 := by
  unfold tailWord_3095149
  simp only [CollatzResearch.WordTrace]
  refine ⟨112889358263811257209568501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75259572175874171473045667 112889358263811257209568501)
  ·
    refine ⟨10583377337232305363397047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 112889358263811257209568501 10583377337232305363397047)
    ·
      refine ⟨15875066005848458045095571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10583377337232305363397047 15875066005848458045095571)
      ·
        refine ⟨23812599008772687067643357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15875066005848458045095571 23812599008772687067643357)
        ·
          refine ⟨8929724628289757650366259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23812599008772687067643357 8929724628289757650366259)
          ·
            refine ⟨13394586942434636475549389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8929724628289757650366259 13394586942434636475549389)
            ·
              refine ⟨5022970103412988678331021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13394586942434636475549389 5022970103412988678331021)
              ·
                refine ⟨1883613788779870754374133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5022970103412988678331021 1883613788779870754374133)
                ·
                  refine ⟨176588792698112883222575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1883613788779870754374133 176588792698112883222575)
                  ·
                    rfl

theorem cell23_3095149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 3, 3, 5].length) (baseStart_3095149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3095149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3095149 prefixEnd_3095149 := by exact prefixLift 3095149
  have htrace : WordTrace (prefixWord ++ tailWord_3095149) baseStart_3095149 baseEnd_3095149 := by
    simpa [prefixWord, tailWord_3095149, baseEnd_3095149] using wordTrace_append hprefix tailTrace_3095149
  have hstable : (prefixWord ++ tailWord_3095149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3095149).length < 2 ^ (prefixWord ++ tailWord_3095149).sum := by decide
  have hdescent : baseEnd_3095149 < baseStart_3095149 := by decide
  rcases family_descends (prefixWord ++ tailWord_3095149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3095172 : List Nat := [2, 3, 2, 1, 3, 2, 1, 1, 1, 2, 5]
def baseStart_3095172 : Nat := 118140960795 + 3095172 * 2 ^ 59
def prefixEnd_3095172 : Nat := 4983230072969 + 3 ^ 40 * 3095172 * 2
def baseEnd_3095172 : Nat := 1589310944338069359015569

theorem tailTrace_3095172 : CollatzResearch.WordTrace tailWord_3095172 prefixEnd_3095172 1589310944338069359015569 := by
  unfold tailWord_3095172
  simp only [CollatzResearch.WordTrace]
  refine ⟨56445098571363966068827885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75260131428485288091770513 56445098571363966068827885)
  ·
    refine ⟨21166911964261487275810457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56445098571363966068827885 21166911964261487275810457)
    ·
      refine ⟨15875183973196115456857843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21166911964261487275810457 15875183973196115456857843)
      ·
        refine ⟨23812775959794173185286765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15875183973196115456857843 23812775959794173185286765)
        ·
          refine ⟨8929790984922814944482537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23812775959794173185286765 8929790984922814944482537)
          ·
            refine ⟨6697343238692111208361903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8929790984922814944482537 6697343238692111208361903)
            ·
              refine ⟨10046014858038166812542855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6697343238692111208361903 10046014858038166812542855)
              ·
                refine ⟨15069022287057250218814283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10046014858038166812542855 15069022287057250218814283)
                ·
                  refine ⟨22603533430585875328221425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15069022287057250218814283 22603533430585875328221425)
                  ·
                    refine ⟨16952650072939406496166069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22603533430585875328221425 16952650072939406496166069)
                    ·
                      refine ⟨1589310944338069359015569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16952650072939406496166069 1589310944338069359015569)
                      ·
                        rfl

theorem cell23_3095172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 1, 1, 2, 5].length) (baseStart_3095172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3095172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3095172 prefixEnd_3095172 := by exact prefixLift 3095172
  have htrace : WordTrace (prefixWord ++ tailWord_3095172) baseStart_3095172 baseEnd_3095172 := by
    simpa [prefixWord, tailWord_3095172, baseEnd_3095172] using wordTrace_append hprefix tailTrace_3095172
  have hstable : (prefixWord ++ tailWord_3095172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3095172).length < 2 ^ (prefixWord ++ tailWord_3095172).sum := by decide
  have hdescent : baseEnd_3095172 < baseStart_3095172 := by decide
  rcases family_descends (prefixWord ++ tailWord_3095172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3095182 : List Nat := [4, 1, 1, 3, 1, 1, 1, 2, 4, 1, 4]
def baseStart_3095182 : Nat := 118140960795 + 3095182 * 2 ^ 59
def prefixEnd_3095182 : Nat := 4983230072969 + 3 ^ 40 * 3095182 * 2
def baseEnd_3095182 : Nat := 1589316079144614319890523

theorem tailTrace_3095182 : CollatzResearch.WordTrace tailWord_3095182 prefixEnd_3095182 1589316079144614319890523 := by
  unfold tailWord_3095182
  simp only [CollatzResearch.WordTrace]
  refine ⟨14111320234086462980689975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75260374581794469230346533 14111320234086462980689975)
  ·
    refine ⟨21166980351129694471034963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14111320234086462980689975 21166980351129694471034963)
    ·
      refine ⟨31750470526694541706552445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21166980351129694471034963 31750470526694541706552445)
      ·
        refine ⟨11906426447510453139957167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31750470526694541706552445 11906426447510453139957167)
        ·
          refine ⟨17859639671265679709935751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11906426447510453139957167 17859639671265679709935751)
          ·
            refine ⟨26789459506898519564903627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17859639671265679709935751 26789459506898519564903627)
            ·
              refine ⟨40184189260347779347355441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26789459506898519564903627 40184189260347779347355441)
              ·
                refine ⟨30138141945260834510516581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40184189260347779347355441 30138141945260834510516581)
                ·
                  refine ⟨5650901614736406470721859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30138141945260834510516581 5650901614736406470721859)
                  ·
                    refine ⟨8476352422104609706082789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5650901614736406470721859 8476352422104609706082789)
                    ·
                      refine ⟨1589316079144614319890523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8476352422104609706082789 1589316079144614319890523)
                      ·
                        rfl

theorem cell23_3095182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 2, 4, 1, 4].length) (baseStart_3095182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3095182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3095182 prefixEnd_3095182 := by exact prefixLift 3095182
  have htrace : WordTrace (prefixWord ++ tailWord_3095182) baseStart_3095182 baseEnd_3095182 := by
    simpa [prefixWord, tailWord_3095182, baseEnd_3095182] using wordTrace_append hprefix tailTrace_3095182
  have hstable : (prefixWord ++ tailWord_3095182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3095182).length < 2 ^ (prefixWord ++ tailWord_3095182).sum := by decide
  have hdescent : baseEnd_3095182 < baseStart_3095182 := by decide
  rcases family_descends (prefixWord ++ tailWord_3095182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3095192 : List Nat := [2, 1, 2, 4, 1, 1, 2, 1, 5, 4]
def baseStart_3095192 : Nat := 118140960795 + 3095192 * 2 ^ 59
def prefixEnd_3095192 : Nat := 4983230072969 + 3 ^ 40 * 3095192 * 2
def baseEnd_3095192 : Nat := 529773737983719760255159

theorem tailTrace_3095192 : CollatzResearch.WordTrace tailWord_3095192 prefixEnd_3095192 529773737983719760255159 := by
  unfold tailWord_3095192
  simp only [CollatzResearch.WordTrace]
  refine ⟨56445463301327737776691915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75260617735103650368922553 56445463301327737776691915)
  ·
    refine ⟨84668194951991606665037873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56445463301327737776691915 84668194951991606665037873)
    ·
      refine ⟨63501146213993704998778405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84668194951991606665037873 63501146213993704998778405)
      ·
        refine ⟨11906464915123819687270951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63501146213993704998778405 11906464915123819687270951)
        ·
          refine ⟨17859697372685729530906427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11906464915123819687270951 17859697372685729530906427)
          ·
            refine ⟨26789546059028594296359641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17859697372685729530906427 26789546059028594296359641)
            ·
              refine ⟨20092159544271445722269731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26789546059028594296359641 20092159544271445722269731)
              ·
                refine ⟨30138239316407168583404597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20092159544271445722269731 30138239316407168583404597)
                ·
                  refine ⟨2825459935913172054694181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30138239316407168583404597 2825459935913172054694181)
                  ·
                    refine ⟨529773737983719760255159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2825459935913172054694181 529773737983719760255159)
                    ·
                      rfl

theorem cell23_3095192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 1, 5, 4].length) (baseStart_3095192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3095192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3095192 prefixEnd_3095192 := by exact prefixLift 3095192
  have htrace : WordTrace (prefixWord ++ tailWord_3095192) baseStart_3095192 baseEnd_3095192 := by
    simpa [prefixWord, tailWord_3095192, baseEnd_3095192] using wordTrace_append hprefix tailTrace_3095192
  have hstable : (prefixWord ++ tailWord_3095192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3095192).length < 2 ^ (prefixWord ++ tailWord_3095192).sum := by decide
  have hdescent : baseEnd_3095192 < baseStart_3095192 := by decide
  rcases family_descends (prefixWord ++ tailWord_3095192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3095225 : List Nat := [1, 2, 1, 4, 1, 1, 1, 3, 1, 2, 6]
def baseStart_3095225 : Nat := 118140960795 + 3095225 * 2 ^ 59
def prefixEnd_3095225 : Nat := 4983230072969 + 3 ^ 40 * 3095225 * 2
def baseEnd_3095225 : Nat := 1589338158812757651652825

theorem tailTrace_3095225 : CollatzResearch.WordTrace tailWord_3095225 prefixEnd_3095225 1589338158812757651652825 := by
  unfold tailWord_3095225
  simp only [CollatzResearch.WordTrace]
  refine ⟨112892130211535922189335129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75261420141023948126223419 112892130211535922189335129)
  ·
    refine ⟨84669097658651941642001347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112892130211535922189335129 84669097658651941642001347)
    ·
      refine ⟨127003646487977912463002021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84669097658651941642001347 127003646487977912463002021)
      ·
        refine ⟨23813183716495858586812879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 127003646487977912463002021 23813183716495858586812879)
        ·
          refine ⟨35719775574743787880219319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23813183716495858586812879 35719775574743787880219319)
          ·
            refine ⟨53579663362115681820328979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35719775574743787880219319 53579663362115681820328979)
            ·
              refine ⟨80369495043173522730493469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53579663362115681820328979 80369495043173522730493469)
              ·
                refine ⟨30138560641190071023935051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80369495043173522730493469 30138560641190071023935051)
                ·
                  refine ⟨45207840961785106535902577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30138560641190071023935051 45207840961785106535902577)
                  ·
                    refine ⟨33905880721338829901926933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45207840961785106535902577 33905880721338829901926933)
                    ·
                      refine ⟨1589338158812757651652825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33905880721338829901926933 1589338158812757651652825)
                      ·
                        rfl

theorem cell23_3095225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 3, 1, 2, 6].length) (baseStart_3095225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3095225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3095225 prefixEnd_3095225 := by exact prefixLift 3095225
  have htrace : WordTrace (prefixWord ++ tailWord_3095225) baseStart_3095225 baseEnd_3095225 := by
    simpa [prefixWord, tailWord_3095225, baseEnd_3095225] using wordTrace_append hprefix tailTrace_3095225
  have hstable : (prefixWord ++ tailWord_3095225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3095225).length < 2 ^ (prefixWord ++ tailWord_3095225).sum := by decide
  have hdescent : baseEnd_3095225 < baseStart_3095225 := by decide
  rcases family_descends (prefixWord ++ tailWord_3095225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3095233 : List Nat := [1, 2, 6, 2, 1, 1, 1, 1, 2, 4, 2]
def baseStart_3095233 : Nat := 118140960795 + 3095233 * 2 ^ 59
def prefixEnd_3095233 : Nat := 4983230072969 + 3 ^ 40 * 3095233 * 2
def baseEnd_3095233 : Nat := 1589342266657993620352789

theorem tailTrace_3095233 : CollatzResearch.WordTrace tailWord_3095233 prefixEnd_3095233 1589342266657993620352789 := by
  unfold tailWord_3095233
  simp only [CollatzResearch.WordTrace]
  refine ⟨112892421995506939555626353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75261614663671293037084235 112892421995506939555626353)
  ·
    refine ⟨84669316496630204666719765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112892421995506939555626353 84669316496630204666719765)
    ·
      refine ⟨3968874210779540843752489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 84669316496630204666719765 3968874210779540843752489)
      ·
        refine ⟨2976655658084655632814367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3968874210779540843752489 2976655658084655632814367)
        ·
          refine ⟨4464983487126983449221551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2976655658084655632814367 4464983487126983449221551)
          ·
            refine ⟨6697475230690475173832327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4464983487126983449221551 6697475230690475173832327)
            ·
              refine ⟨10046212846035712760748491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6697475230690475173832327 10046212846035712760748491)
              ·
                refine ⟨15069319269053569141122737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10046212846035712760748491 15069319269053569141122737)
                ·
                  refine ⟨11301989451790176855842053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15069319269053569141122737 11301989451790176855842053)
                  ·
                    refine ⟨2119123022210658160470385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11301989451790176855842053 2119123022210658160470385)
                    ·
                      refine ⟨1589342266657993620352789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2119123022210658160470385 1589342266657993620352789)
                      ·
                        rfl

theorem cell23_3095233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 1, 2, 4, 2].length) (baseStart_3095233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3095233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3095233 prefixEnd_3095233 := by exact prefixLift 3095233
  have htrace : WordTrace (prefixWord ++ tailWord_3095233) baseStart_3095233 baseEnd_3095233 := by
    simpa [prefixWord, tailWord_3095233, baseEnd_3095233] using wordTrace_append hprefix tailTrace_3095233
  have hstable : (prefixWord ++ tailWord_3095233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3095233).length < 2 ^ (prefixWord ++ tailWord_3095233).sum := by decide
  have hdescent : baseEnd_3095233 < baseStart_3095233 := by decide
  rcases family_descends (prefixWord ++ tailWord_3095233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3095249 : List Nat := [1, 2, 2, 1, 2, 3, 3, 2, 3, 1, 3]
def baseStart_3095249 : Nat := 118140960795 + 3095249 * 2 ^ 59
def prefixEnd_3095249 : Nat := 4983230072969 + 3 ^ 40 * 3095249 * 2
def baseEnd_3095249 : Nat := 1589350482348465557752715

theorem tailTrace_3095249 : CollatzResearch.WordTrace tailWord_3095249 prefixEnd_3095249 1589350482348465557752715 := by
  unfold tailWord_3095249
  simp only [CollatzResearch.WordTrace]
  refine ⟨112893005563448974288208801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75262003708965982858805867 112893005563448974288208801)
  ·
    refine ⟨84669754172586730716156601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112893005563448974288208801 84669754172586730716156601)
    ·
      refine ⟨63502315629440048037117451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84669754172586730716156601 63502315629440048037117451)
      ·
        refine ⟨95253473444160072055676177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63502315629440048037117451 95253473444160072055676177)
        ·
          refine ⟨71440105083120054041757133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95253473444160072055676177 71440105083120054041757133)
          ·
            refine ⟨26790039406170020265658925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71440105083120054041757133 26790039406170020265658925)
            ·
              refine ⟨10046264777313757599622097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26790039406170020265658925 10046264777313757599622097)
              ·
                refine ⟨7534698582985318199716573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10046264777313757599622097 7534698582985318199716573)
                ·
                  refine ⟨2825511968619494324893715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7534698582985318199716573 2825511968619494324893715)
                  ·
                    refine ⟨4238267952929241487340573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2825511968619494324893715 4238267952929241487340573)
                    ·
                      refine ⟨1589350482348465557752715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4238267952929241487340573 1589350482348465557752715)
                      ·
                        rfl

theorem cell23_3095249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 2, 3, 1, 3].length) (baseStart_3095249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3095249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3095249 prefixEnd_3095249 := by exact prefixLift 3095249
  have htrace : WordTrace (prefixWord ++ tailWord_3095249) baseStart_3095249 baseEnd_3095249 := by
    simpa [prefixWord, tailWord_3095249, baseEnd_3095249] using wordTrace_append hprefix tailTrace_3095249
  have hstable : (prefixWord ++ tailWord_3095249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3095249).length < 2 ^ (prefixWord ++ tailWord_3095249).sum := by decide
  have hdescent : baseEnd_3095249 < baseStart_3095249 := by decide
  rcases family_descends (prefixWord ++ tailWord_3095249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3095253 : List Nat := [1, 3, 2, 5, 1, 2, 1, 1, 2, 2, 3]
def baseStart_3095253 : Nat := 118140960795 + 3095253 * 2 ^ 59
def prefixEnd_3095253 : Nat := 4983230072969 + 3 ^ 40 * 3095253 * 2
def baseEnd_3095253 : Nat := 1589352536271083542102697

theorem tailTrace_3095253 : CollatzResearch.WordTrace tailWord_3095253 prefixEnd_3095253 1589352536271083542102697 := by
  unfold tailWord_3095253
  simp only [CollatzResearch.WordTrace]
  refine ⟨112893151455434482971354413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75262100970289655314236275 112893151455434482971354413)
  ·
    refine ⟨42334931795787931114257905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112893151455434482971354413 42334931795787931114257905)
    ·
      refine ⟨31751198846840948335693429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42334931795787931114257905 31751198846840948335693429)
      ·
        refine ⟨2976674891891338906471259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 31751198846840948335693429 2976674891891338906471259)
        ·
          refine ⟨4465012337837008359706889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2976674891891338906471259 4465012337837008359706889)
          ·
            refine ⟨3348759253377756269780167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4465012337837008359706889 3348759253377756269780167)
            ·
              refine ⟨5023138880066634404670251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3348759253377756269780167 5023138880066634404670251)
              ·
                refine ⟨7534708320099951607005377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5023138880066634404670251 7534708320099951607005377)
                ·
                  refine ⟨5651031240074963705254033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7534708320099951607005377 5651031240074963705254033)
                  ·
                    refine ⟨4238273430056222778940525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5651031240074963705254033 4238273430056222778940525)
                    ·
                      refine ⟨1589352536271083542102697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4238273430056222778940525 1589352536271083542102697)
                      ·
                        rfl

theorem cell23_3095253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_3095253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3095253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3095253 prefixEnd_3095253 := by exact prefixLift 3095253
  have htrace : WordTrace (prefixWord ++ tailWord_3095253) baseStart_3095253 baseEnd_3095253 := by
    simpa [prefixWord, tailWord_3095253, baseEnd_3095253] using wordTrace_append hprefix tailTrace_3095253
  have hstable : (prefixWord ++ tailWord_3095253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3095253).length < 2 ^ (prefixWord ++ tailWord_3095253).sum := by decide
  have hdescent : baseEnd_3095253 < baseStart_3095253 := by decide
  rcases family_descends (prefixWord ++ tailWord_3095253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3095269 : List Nat := [1, 3, 1, 4, 1, 3, 1, 3, 1, 5]
def baseStart_3095269 : Nat := 118140960795 + 3095269 * 2 ^ 59
def prefixEnd_3095269 : Nat := 4983230072969 + 3 ^ 40 * 3095269 * 2
def baseEnd_3095269 : Nat := 529786917320518493167541

theorem tailTrace_3095269 : CollatzResearch.WordTrace tailWord_3095269 prefixEnd_3095269 529786917320518493167541 := by
  unfold tailWord_3095269
  simp only [CollatzResearch.WordTrace]
  refine ⟨112893735023376517703936861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75262490015584345135957907 112893735023376517703936861)
  ·
    refine ⟨42335150633766194138976323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112893735023376517703936861 42335150633766194138976323)
    ·
      refine ⟨63502725950649291208464485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42335150633766194138976323 63502725950649291208464485)
      ·
        refine ⟨11906761115746742101587091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63502725950649291208464485 11906761115746742101587091)
        ·
          refine ⟨17860141673620113152380637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11906761115746742101587091 17860141673620113152380637)
          ·
            refine ⟨6697553127607542432142739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17860141673620113152380637 6697553127607542432142739)
            ·
              refine ⟨10046329691411313648214109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6697553127607542432142739 10046329691411313648214109)
              ·
                refine ⟨3767373634279242618080291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10046329691411313648214109 3767373634279242618080291)
                ·
                  refine ⟨5651060451418863927120437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3767373634279242618080291 5651060451418863927120437)
                  ·
                    refine ⟨529786917320518493167541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5651060451418863927120437 529786917320518493167541)
                    ·
                      rfl

theorem cell23_3095269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 3, 1, 5].length) (baseStart_3095269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3095269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3095269 prefixEnd_3095269 := by exact prefixLift 3095269
  have htrace : WordTrace (prefixWord ++ tailWord_3095269) baseStart_3095269 baseEnd_3095269 := by
    simpa [prefixWord, tailWord_3095269, baseEnd_3095269] using wordTrace_append hprefix tailTrace_3095269
  have hstable : (prefixWord ++ tailWord_3095269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3095269).length < 2 ^ (prefixWord ++ tailWord_3095269).sum := by decide
  have hdescent : baseEnd_3095269 < baseStart_3095269 := by decide
  rcases family_descends (prefixWord ++ tailWord_3095269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3095292 : List Nat := [2, 2, 2, 1, 3, 2, 1, 1, 3, 1, 5]
def baseStart_3095292 : Nat := 118140960795 + 3095292 * 2 ^ 59
def prefixEnd_3095292 : Nat := 4983230072969 + 3 ^ 40 * 3095292 * 2
def baseEnd_3095292 : Nat := 1589372562016608889515017

theorem tailTrace_3095292 : CollatzResearch.WordTrace tailWord_3095292 prefixEnd_3095292 1589372562016608889515017 := by
  unfold tailWord_3095292
  simp only [CollatzResearch.WordTrace]
  refine ⟨56447286951146596316012065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75263049268195461754682753 56447286951146596316012065)
  ·
    refine ⟨42335465213359947237009049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56447286951146596316012065 42335465213359947237009049)
    ·
      refine ⟨31751598910019960427756787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42335465213359947237009049 31751598910019960427756787)
      ·
        refine ⟨47627398365029940641635181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31751598910019960427756787 47627398365029940641635181)
        ·
          refine ⟨17860274386886227740613193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47627398365029940641635181 17860274386886227740613193)
          ·
            refine ⟨13395205790164670805459895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17860274386886227740613193 13395205790164670805459895)
            ·
              refine ⟨20092808685247006208189843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13395205790164670805459895 20092808685247006208189843)
              ·
                refine ⟨30139213027870509312284765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20092808685247006208189843 30139213027870509312284765)
                ·
                  refine ⟨11302204885451440992106787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30139213027870509312284765 11302204885451440992106787)
                  ·
                    refine ⟨16953307328177161488160181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11302204885451440992106787 16953307328177161488160181)
                    ·
                      refine ⟨1589372562016608889515017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16953307328177161488160181 1589372562016608889515017)
                      ·
                        rfl

theorem cell23_3095292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 1, 3, 1, 5].length) (baseStart_3095292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3095292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3095292 prefixEnd_3095292 := by exact prefixLift 3095292
  have htrace : WordTrace (prefixWord ++ tailWord_3095292) baseStart_3095292 baseEnd_3095292 := by
    simpa [prefixWord, tailWord_3095292, baseEnd_3095292] using wordTrace_append hprefix tailTrace_3095292
  have hstable : (prefixWord ++ tailWord_3095292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3095292).length < 2 ^ (prefixWord ++ tailWord_3095292).sum := by decide
  have hdescent : baseEnd_3095292 < baseStart_3095292 := by decide
  rcases family_descends (prefixWord ++ tailWord_3095292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3095295 : List Nat := [1, 1, 2, 2, 1, 3, 1, 12]
def baseStart_3095295 : Nat := 118140960795 + 3095295 * 2 ^ 59
def prefixEnd_3095295 : Nat := 4983230072969 + 3 ^ 40 * 3095295 * 2
def baseEnd_3095295 : Nat := 58865707498465643621389

theorem tailTrace_3095295 : CollatzResearch.WordTrace tailWord_3095295 prefixEnd_3095295 58865707498465643621389 := by
  unfold tailWord_3095295
  simp only [CollatzResearch.WordTrace]
  refine ⟨112894683321282324144383339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75263122214188216096255559 112894683321282324144383339)
  ·
    refine ⟨169342024981923486216575009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112894683321282324144383339 169342024981923486216575009)
    ·
      refine ⟨127006518736442614662431257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169342024981923486216575009 127006518736442614662431257)
      ·
        refine ⟨95254889052331960996823443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127006518736442614662431257 95254889052331960996823443)
        ·
          refine ⟨142882333578497941495235165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95254889052331960996823443 142882333578497941495235165)
          ·
            refine ⟨53580875091936728060713187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 142882333578497941495235165 53580875091936728060713187)
            ·
              refine ⟨80371312637905092091069781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53580875091936728060713187 80371312637905092091069781)
              ·
                refine ⟨58865707498465643621389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 80371312637905092091069781 58865707498465643621389)
                ·
                  rfl

theorem cell23_3095295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 12].length) (baseStart_3095295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3095295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3095295 prefixEnd_3095295 := by exact prefixLift 3095295
  have htrace : WordTrace (prefixWord ++ tailWord_3095295) baseStart_3095295 baseEnd_3095295 := by
    simpa [prefixWord, tailWord_3095295, baseEnd_3095295] using wordTrace_append hprefix tailTrace_3095295
  have hstable : (prefixWord ++ tailWord_3095295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3095295).length < 2 ^ (prefixWord ++ tailWord_3095295).sum := by decide
  have hdescent : baseEnd_3095295 < baseStart_3095295 := by decide
  rcases family_descends (prefixWord ++ tailWord_3095295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3095306 : List Nat := [3, 1, 2, 2, 1, 2, 1, 4, 3, 2, 2]
def baseStart_3095306 : Nat := 118140960795 + 3095306 * 2 ^ 59
def prefixEnd_3095306 : Nat := 4983230072969 + 3 ^ 40 * 3095306 * 2
def baseEnd_3095306 : Nat := 1589379750745771834739953

theorem tailTrace_3095306 : CollatzResearch.WordTrace tailWord_3095306 prefixEnd_3095306 1589379750745771834739953 := by
  unfold tailWord_3095306
  simp only [CollatzResearch.WordTrace]
  refine ⟨28223771131060618255758443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75263389682828315348689181 28223771131060618255758443)
  ·
    refine ⟨42335656696590927383637665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28223771131060618255758443 42335656696590927383637665)
    ·
      refine ⟨31751742522443195537728249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42335656696590927383637665 31751742522443195537728249)
      ·
        refine ⟨23813806891832396653296187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31751742522443195537728249 23813806891832396653296187)
        ·
          refine ⟨35720710337748594979944281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23813806891832396653296187 35720710337748594979944281)
          ·
            refine ⟨26790532753311446234958211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35720710337748594979944281 26790532753311446234958211)
            ·
              refine ⟨40185799129967169352437317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26790532753311446234958211 40185799129967169352437317)
              ·
                refine ⟨7534837336868844253581997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40185799129967169352437317 7534837336868844253581997)
                ·
                  refine ⟨2825564001325816595093249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7534837336868844253581997 2825564001325816595093249)
                  ·
                    refine ⟨2119173000994362446319937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2825564001325816595093249 2119173000994362446319937)
                    ·
                      refine ⟨1589379750745771834739953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2119173000994362446319937 1589379750745771834739953)
                      ·
                        rfl

theorem cell23_3095306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 4, 3, 2, 2].length) (baseStart_3095306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3095306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3095306 prefixEnd_3095306 := by exact prefixLift 3095306
  have htrace : WordTrace (prefixWord ++ tailWord_3095306) baseStart_3095306 baseEnd_3095306 := by
    simpa [prefixWord, tailWord_3095306, baseEnd_3095306] using wordTrace_append hprefix tailTrace_3095306
  have hstable : (prefixWord ++ tailWord_3095306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3095306).length < 2 ^ (prefixWord ++ tailWord_3095306).sum := by decide
  have hdescent : baseEnd_3095306 < baseStart_3095306 := by decide
  rcases family_descends (prefixWord ++ tailWord_3095306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3095340 : List Nat := [2, 2, 1, 1, 1, 4, 5, 2, 1, 2, 2]
def baseStart_3095340 : Nat := 118140960795 + 3095340 * 2 ^ 59
def prefixEnd_3095340 : Nat := 4983230072969 + 3 ^ 40 * 3095340 * 2
def baseEnd_3095340 : Nat := 1589397209088024701714797

theorem tailTrace_3095340 : CollatzResearch.WordTrace tailWord_3095340 prefixEnd_3095340 1589397209088024701714797 := by
  unfold tailWord_3095340
  simp only [CollatzResearch.WordTrace]
  refine ⟨56448162303059648414885737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75264216404079531219847649 56448162303059648414885737)
  ·
    refine ⟨42336121727294736311164303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56448162303059648414885737 42336121727294736311164303)
    ·
      refine ⟨63504182590942104466746455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42336121727294736311164303 63504182590942104466746455)
      ·
        refine ⟨95256273886413156700119683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63504182590942104466746455 95256273886413156700119683)
        ·
          refine ⟨142884410829619735050179525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95256273886413156700119683 142884410829619735050179525)
          ·
            refine ⟨26790827030553700321908661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 142884410829619735050179525 26790827030553700321908661)
            ·
              refine ⟨2511640034114409405178937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26790827030553700321908661 2511640034114409405178937)
              ·
                refine ⟨1883730025585807053884203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2511640034114409405178937 1883730025585807053884203)
                ·
                  refine ⟨2825595038378710580826305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1883730025585807053884203 2825595038378710580826305)
                  ·
                    refine ⟨2119196278784032935619729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2825595038378710580826305 2119196278784032935619729)
                    ·
                      refine ⟨1589397209088024701714797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2119196278784032935619729 1589397209088024701714797)
                      ·
                        rfl

theorem cell23_3095340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 5, 2, 1, 2, 2].length) (baseStart_3095340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3095340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3095340 prefixEnd_3095340 := by exact prefixLift 3095340
  have htrace : WordTrace (prefixWord ++ tailWord_3095340) baseStart_3095340 baseEnd_3095340 := by
    simpa [prefixWord, tailWord_3095340, baseEnd_3095340] using wordTrace_append hprefix tailTrace_3095340
  have hstable : (prefixWord ++ tailWord_3095340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3095340).length < 2 ^ (prefixWord ++ tailWord_3095340).sum := by decide
  have hdescent : baseEnd_3095340 < baseStart_3095340 := by decide
  rcases family_descends (prefixWord ++ tailWord_3095340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3095373 : List Nat := [1, 6, 1, 2, 2, 1, 1, 2, 1, 3, 3]
def baseStart_3095373 : Nat := 118140960795 + 3095373 * 2 ^ 59
def prefixEnd_3095373 : Nat := 4983230072969 + 3 ^ 40 * 3095373 * 2
def baseEnd_3095373 : Nat := 1589414153949623072602145

theorem tailTrace_3095373 : CollatzResearch.WordTrace tailWord_3095373 prefixEnd_3095373 1589414153949623072602145 := by
  unfold tailWord_3095373
  simp only [CollatzResearch.WordTrace]
  refine ⟨112897528214999743465722773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75265018809999828977148515 112897528214999743465722773)
  ·
    refine ⟨5292071635078112974955755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 112897528214999743465722773 5292071635078112974955755)
    ·
      refine ⟨7938107452617169462433633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5292071635078112974955755 7938107452617169462433633)
      ·
        refine ⟨5953580589462877096825225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7938107452617169462433633 5953580589462877096825225)
        ·
          refine ⟨4465185442097157822618919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5953580589462877096825225 4465185442097157822618919)
          ·
            refine ⟨6697778163145736733928379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4465185442097157822618919 6697778163145736733928379)
            ·
              refine ⟨10046667244718605100892569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6697778163145736733928379 10046667244718605100892569)
              ·
                refine ⟨7535000433538953825669427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10046667244718605100892569 7535000433538953825669427)
                ·
                  refine ⟨11302500650308430738504141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7535000433538953825669427 11302500650308430738504141)
                  ·
                    refine ⟨4238437743865661526939053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11302500650308430738504141 4238437743865661526939053)
                    ·
                      refine ⟨1589414153949623072602145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4238437743865661526939053 1589414153949623072602145)
                      ·
                        rfl

theorem cell23_3095373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 2, 1, 3, 3].length) (baseStart_3095373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3095373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3095373 prefixEnd_3095373 := by exact prefixLift 3095373
  have htrace : WordTrace (prefixWord ++ tailWord_3095373) baseStart_3095373 baseEnd_3095373 := by
    simpa [prefixWord, tailWord_3095373, baseEnd_3095373] using wordTrace_append hprefix tailTrace_3095373
  have hstable : (prefixWord ++ tailWord_3095373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3095373).length < 2 ^ (prefixWord ++ tailWord_3095373).sum := by decide
  have hdescent : baseEnd_3095373 < baseStart_3095373 := by decide
  rcases family_descends (prefixWord ++ tailWord_3095373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3095399 : List Nat := [1, 1, 5, 1, 2, 2, 1, 1, 2, 4, 3]
def baseStart_3095399 : Nat := 118140960795 + 3095399 * 2 ^ 59
def prefixEnd_3095399 : Nat := 4983230072969 + 3 ^ 40 * 3095399 * 2
def baseEnd_3095399 : Nat := 1589427504446639970877025

theorem tailTrace_3095399 : CollatzResearch.WordTrace tailWord_3095399 prefixEnd_3095399 1589427504446639970877025 := by
  unfold tailWord_3095399
  simp only [CollatzResearch.WordTrace]
  refine ⟨112898476512905549906169251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75265651008603699937446167 112898476512905549906169251)
  ·
    refine ⟨169347714769358324859253877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112898476512905549906169251 169347714769358324859253877)
    ·
      refine ⟨15876348259627342955555051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 169347714769358324859253877 15876348259627342955555051)
      ·
        refine ⟨23814522389441014433332577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15876348259627342955555051 23814522389441014433332577)
        ·
          refine ⟨17860891792080760824999433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23814522389441014433332577 17860891792080760824999433)
          ·
            refine ⟨13395668844060570618749575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17860891792080760824999433 13395668844060570618749575)
            ·
              refine ⟨20093503266090855928124363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13395668844060570618749575 20093503266090855928124363)
              ·
                refine ⟨30140254899136283892186545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20093503266090855928124363 30140254899136283892186545)
                ·
                  refine ⟨22605191174352212919139909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30140254899136283892186545 22605191174352212919139909)
                  ·
                    refine ⟨4238473345191039922338733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22605191174352212919139909 4238473345191039922338733)
                    ·
                      refine ⟨1589427504446639970877025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4238473345191039922338733 1589427504446639970877025)
                      ·
                        rfl

theorem cell23_3095399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 1, 2, 4, 3].length) (baseStart_3095399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3095399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3095399 prefixEnd_3095399 := by exact prefixLift 3095399
  have htrace : WordTrace (prefixWord ++ tailWord_3095399) baseStart_3095399 baseEnd_3095399 := by
    simpa [prefixWord, tailWord_3095399, baseEnd_3095399] using wordTrace_append hprefix tailTrace_3095399
  have hstable : (prefixWord ++ tailWord_3095399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3095399).length < 2 ^ (prefixWord ++ tailWord_3095399).sum := by decide
  have hdescent : baseEnd_3095399 < baseStart_3095399 := by decide
  rcases family_descends (prefixWord ++ tailWord_3095399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3095406 : List Nat := [4, 1, 2, 3, 2, 1, 1, 1, 2, 6]
def baseStart_3095406 : Nat := 118140960795 + 3095406 * 2 ^ 59
def prefixEnd_3095406 : Nat := 4983230072969 + 3 ^ 40 * 3095406 * 2
def baseEnd_3095406 : Nat := 529810366270407147829831

theorem tailTrace_3095406 : CollatzResearch.WordTrace tailWord_3095406 prefixEnd_3095406 529810366270407147829831 := by
  unfold tailWord_3095406
  simp only [CollatzResearch.WordTrace]
  refine ⟨14112341477985023762709259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75265821215920126734449381 14112341477985023762709259)
  ·
    refine ⟨21168512216977535644063889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14112341477985023762709259 21168512216977535644063889)
    ·
      refine ⟨15876384162733151733047917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21168512216977535644063889 15876384162733151733047917)
      ·
        refine ⟨5953644061024931899892969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15876384162733151733047917 5953644061024931899892969)
        ·
          refine ⟨4465233045768698924919727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5953644061024931899892969 4465233045768698924919727)
          ·
            refine ⟨6697849568653048387379591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4465233045768698924919727 6697849568653048387379591)
            ·
              refine ⟨10046774352979572581069387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6697849568653048387379591 10046774352979572581069387)
              ·
                refine ⟨15070161529469358871604081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10046774352979572581069387 15070161529469358871604081)
                ·
                  refine ⟨11302621147102019153703061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15070161529469358871604081 11302621147102019153703061)
                  ·
                    refine ⟨529810366270407147829831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11302621147102019153703061 529810366270407147829831)
                    ·
                      rfl

theorem cell23_3095406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 1, 2, 6].length) (baseStart_3095406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3095406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3095406 prefixEnd_3095406 := by exact prefixLift 3095406
  have htrace : WordTrace (prefixWord ++ tailWord_3095406) baseStart_3095406 baseEnd_3095406 := by
    simpa [prefixWord, tailWord_3095406, baseEnd_3095406] using wordTrace_append hprefix tailTrace_3095406
  have hstable : (prefixWord ++ tailWord_3095406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3095406).length < 2 ^ (prefixWord ++ tailWord_3095406).sum := by decide
  have hdescent : baseEnd_3095406 < baseStart_3095406 := by decide
  rcases family_descends (prefixWord ++ tailWord_3095406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3095409 : List Nat := [1, 2, 2, 2, 1, 5, 1, 1, 2, 2, 4]
def baseStart_3095409 : Nat := 118140960795 + 3095409 * 2 ^ 59
def prefixEnd_3095409 : Nat := 4983230072969 + 3 ^ 40 * 3095409 * 2
def baseEnd_3095409 : Nat := 1589432639253184931751979

theorem tailTrace_3095409 : CollatzResearch.WordTrace tailWord_3095409 prefixEnd_3095409 1589432639253184931751979 := by
  unfold tailWord_3095409
  simp only [CollatzResearch.WordTrace]
  refine ⟨112898841242869321614033281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75265894161912881076022187 112898841242869321614033281)
  ·
    refine ⟨84674130932151991210524961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112898841242869321614033281 84674130932151991210524961)
    ·
      refine ⟨63505598199113993407893721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84674130932151991210524961 63505598199113993407893721)
      ·
        refine ⟨47629198649335495055920291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63505598199113993407893721 47629198649335495055920291)
        ·
          refine ⟨71443797974003242583880437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47629198649335495055920291 71443797974003242583880437)
          ·
            refine ⟨6697856060062803992238791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 71443797974003242583880437 6697856060062803992238791)
            ·
              refine ⟨10046784090094205988358187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6697856060062803992238791 10046784090094205988358187)
              ·
                refine ⟨15070176135141308982537281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10046784090094205988358187 15070176135141308982537281)
                ·
                  refine ⟨11302632101355981736902961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15070176135141308982537281 11302632101355981736902961)
                  ·
                    refine ⟨8476974076016986302677221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11302632101355981736902961 8476974076016986302677221)
                    ·
                      refine ⟨1589432639253184931751979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8476974076016986302677221 1589432639253184931751979)
                      ·
                        rfl

theorem cell23_3095409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 1, 2, 2, 4].length) (baseStart_3095409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3095409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3095409 prefixEnd_3095409 := by exact prefixLift 3095409
  have htrace : WordTrace (prefixWord ++ tailWord_3095409) baseStart_3095409 baseEnd_3095409 := by
    simpa [prefixWord, tailWord_3095409, baseEnd_3095409] using wordTrace_append hprefix tailTrace_3095409
  have hstable : (prefixWord ++ tailWord_3095409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3095409).length < 2 ^ (prefixWord ++ tailWord_3095409).sum := by decide
  have hdescent : baseEnd_3095409 < baseStart_3095409 := by decide
  rcases family_descends (prefixWord ++ tailWord_3095409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3095413 : List Nat := [1, 3, 4, 1, 1, 3, 2, 1, 1, 4, 2]
def baseStart_3095413 : Nat := 118140960795 + 3095413 * 2 ^ 59
def prefixEnd_3095413 : Nat := 4983230072969 + 3 ^ 40 * 3095413 * 2
def baseEnd_3095413 : Nat := 1589434693175802916101961

theorem tailTrace_3095413 : CollatzResearch.WordTrace tailWord_3095413 prefixEnd_3095413 1589434693175802916101961 := by
  unfold tailWord_3095413
  simp only [CollatzResearch.WordTrace]
  refine ⟨112898987134854830297178893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75265991423236553531452595 112898987134854830297178893)
  ·
    refine ⟨42337120175570561361442085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112898987134854830297178893 42337120175570561361442085)
    ·
      refine ⟨7938210032919480255270391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42337120175570561361442085 7938210032919480255270391)
      ·
        refine ⟨11907315049379220382905587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7938210032919480255270391 11907315049379220382905587)
        ·
          refine ⟨17860972574068830574358381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11907315049379220382905587 17860972574068830574358381)
          ·
            refine ⟨6697864715275811465384393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17860972574068830574358381 6697864715275811465384393)
            ·
              refine ⟨5023398536456858599038295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6697864715275811465384393 5023398536456858599038295)
              ·
                refine ⟨7535097804685287898557443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5023398536456858599038295 7535097804685287898557443)
                ·
                  refine ⟨11302646707027931847836165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7535097804685287898557443 11302646707027931847836165)
                  ·
                    refine ⟨2119246257567737221469281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11302646707027931847836165 2119246257567737221469281)
                    ·
                      refine ⟨1589434693175802916101961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2119246257567737221469281 1589434693175802916101961)
                      ·
                        rfl

theorem cell23_3095413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 2, 1, 1, 4, 2].length) (baseStart_3095413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3095413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3095413 prefixEnd_3095413 := by exact prefixLift 3095413
  have htrace : WordTrace (prefixWord ++ tailWord_3095413) baseStart_3095413 baseEnd_3095413 := by
    simpa [prefixWord, tailWord_3095413, baseEnd_3095413] using wordTrace_append hprefix tailTrace_3095413
  have hstable : (prefixWord ++ tailWord_3095413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3095413).length < 2 ^ (prefixWord ++ tailWord_3095413).sum := by decide
  have hdescent : baseEnd_3095413 < baseStart_3095413 := by decide
  rcases family_descends (prefixWord ++ tailWord_3095413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3095486 : List Nat := [4, 2, 1, 1, 1, 2, 2, 3, 2, 1, 4]
def baseStart_3095486 : Nat := 118140960795 + 3095486 * 2 ^ 59
def prefixEnd_3095486 : Nat := 4983230072969 + 3 ^ 40 * 3095486 * 2
def baseEnd_3095486 : Nat := 1589472177263581130489125

theorem tailTrace_3095486 : CollatzResearch.WordTrace tailWord_3095486 prefixEnd_3095486 1589472177263581130489125 := by
  unfold tailWord_3095486
  simp only [CollatzResearch.WordTrace]
  refine ⟨14112706207948795470573289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75267766442393575843057541 14112706207948795470573289)
  ·
    refine ⟨10584529655961596602929967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14112706207948795470573289 10584529655961596602929967)
    ·
      refine ⟨15876794483942394904394951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10584529655961596602929967 15876794483942394904394951)
      ·
        refine ⟨23815191725913592356592427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15876794483942394904394951 23815191725913592356592427)
        ·
          refine ⟨35722787588870388534888641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23815191725913592356592427 35722787588870388534888641)
          ·
            refine ⟨26792090691652791401166481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35722787588870388534888641 26792090691652791401166481)
            ·
              refine ⟨20094068018739593550874861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26792090691652791401166481 20094068018739593550874861)
              ·
                refine ⟨7535275507027347581578073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20094068018739593550874861 7535275507027347581578073)
                ·
                  refine ⟨5651456630270510686183555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7535275507027347581578073 5651456630270510686183555)
                  ·
                    refine ⟨8477184945405766029275333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5651456630270510686183555 8477184945405766029275333)
                    ·
                      refine ⟨1589472177263581130489125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8477184945405766029275333 1589472177263581130489125)
                      ·
                        rfl

theorem cell23_3095486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 3, 2, 1, 4].length) (baseStart_3095486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3095486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3095486 prefixEnd_3095486 := by exact prefixLift 3095486
  have htrace : WordTrace (prefixWord ++ tailWord_3095486) baseStart_3095486 baseEnd_3095486 := by
    simpa [prefixWord, tailWord_3095486, baseEnd_3095486] using wordTrace_append hprefix tailTrace_3095486
  have hstable : (prefixWord ++ tailWord_3095486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3095486).length < 2 ^ (prefixWord ++ tailWord_3095486).sum := by decide
  have hdescent : baseEnd_3095486 < baseStart_3095486 := by decide
  rcases family_descends (prefixWord ++ tailWord_3095486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3095513 : List Nat := [1, 2, 1, 2, 5, 3, 1, 1, 3, 4]
def baseStart_3095513 : Nat := 118140960795 + 3095513 * 2 ^ 59
def prefixEnd_3095513 : Nat := 4983230072969 + 3 ^ 40 * 3095513 * 2
def baseEnd_3095513 : Nat := 529828680413750841617167

theorem tailTrace_3095513 : CollatzResearch.WordTrace tailWord_3095513 prefixEnd_3095513 529828680413750841617167 := by
  unfold tailWord_3095513
  simp only [CollatzResearch.WordTrace]
  refine ⟨112902634434492547375819193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75268422956328364917212795 112902634434492547375819193)
  ·
    refine ⟨84676975825869410531864395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112902634434492547375819193 84676975825869410531864395)
    ·
      refine ⟨127015463738804115797796593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84676975825869410531864395 127015463738804115797796593)
      ·
        refine ⟨95261597804103086848347445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127015463738804115797796593 95261597804103086848347445)
        ·
          refine ⟨8930774794134664392032573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 95261597804103086848347445 8930774794134664392032573)
          ·
            refine ⟨3349040547800499147012215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8930774794134664392032573 3349040547800499147012215)
            ·
              refine ⟨5023560821700748720518323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3349040547800499147012215 5023560821700748720518323)
              ·
                refine ⟨7535341232551123080777485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5023560821700748720518323 7535341232551123080777485)
                ·
                  refine ⟨2825752962206671155291557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7535341232551123080777485 2825752962206671155291557)
                  ·
                    refine ⟨529828680413750841617167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2825752962206671155291557 529828680413750841617167)
                    ·
                      rfl

theorem cell23_3095513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 1, 1, 3, 4].length) (baseStart_3095513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3095513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3095513 prefixEnd_3095513 := by exact prefixLift 3095513
  have htrace : WordTrace (prefixWord ++ tailWord_3095513) baseStart_3095513 baseEnd_3095513 := by
    simpa [prefixWord, tailWord_3095513, baseEnd_3095513] using wordTrace_append hprefix tailTrace_3095513
  have hstable : (prefixWord ++ tailWord_3095513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3095513).length < 2 ^ (prefixWord ++ tailWord_3095513).sum := by decide
  have hdescent : baseEnd_3095513 < baseStart_3095513 := by decide
  rcases family_descends (prefixWord ++ tailWord_3095513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3095536 : List Nat := [2, 1, 1, 1, 3, 2, 1, 3, 5, 1, 3]
def baseStart_3095536 : Nat := 118140960795 + 3095536 * 2 ^ 59
def prefixEnd_3095536 : Nat := 4983230072969 + 3 ^ 40 * 3095536 * 2
def baseEnd_3095536 : Nat := 1589497851296305934863895

theorem tailTrace_3095536 : CollatzResearch.WordTrace tailWord_3095536 prefixEnd_3095536 1589497851296305934863895 := by
  unfold tailWord_3095536
  simp only [CollatzResearch.WordTrace]
  refine ⟨56451736656704611151953231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75268982208939481535937641 56451736656704611151953231)
  ·
    refine ⟨84677604985056916727929847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56451736656704611151953231 84677604985056916727929847)
    ·
      refine ⟨127016407477585375091894771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84677604985056916727929847 127016407477585375091894771)
      ·
        refine ⟨190524611216378062637842157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127016407477585375091894771 190524611216378062637842157)
        ·
          refine ⟨71446729206141773489190809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 190524611216378062637842157 71446729206141773489190809)
          ·
            refine ⟨53585046904606330116893107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71446729206141773489190809 53585046904606330116893107)
            ·
              refine ⟨80377570356909495175339661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53585046904606330116893107 80377570356909495175339661)
              ·
                refine ⟨30141588883841060690752373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80377570356909495175339661 30141588883841060690752373)
                ·
                  refine ⟨2825773957860099439758035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30141588883841060690752373 2825773957860099439758035)
                  ·
                    refine ⟨4238660936790149159637053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2825773957860099439758035 4238660936790149159637053)
                    ·
                      refine ⟨1589497851296305934863895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4238660936790149159637053 1589497851296305934863895)
                      ·
                        rfl

theorem cell23_3095536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 3, 5, 1, 3].length) (baseStart_3095536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3095536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3095536 prefixEnd_3095536 := by exact prefixLift 3095536
  have htrace : WordTrace (prefixWord ++ tailWord_3095536) baseStart_3095536 baseEnd_3095536 := by
    simpa [prefixWord, tailWord_3095536, baseEnd_3095536] using wordTrace_append hprefix tailTrace_3095536
  have hstable : (prefixWord ++ tailWord_3095536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3095536).length < 2 ^ (prefixWord ++ tailWord_3095536).sum := by decide
  have hdescent : baseEnd_3095536 < baseStart_3095536 := by decide
  rcases family_descends (prefixWord ++ tailWord_3095536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3095546 : List Nat := [3, 1, 1, 1, 1, 2, 1, 5, 1, 5, 2]
def baseStart_3095546 : Nat := 118140960795 + 3095546 * 2 ^ 59
def prefixEnd_3095546 : Nat := 4983230072969 + 3 ^ 40 * 3095546 * 2
def baseEnd_3095546 : Nat := 1589502986102850895738849

theorem tailTrace_3095546 : CollatzResearch.WordTrace tailWord_3095546 prefixEnd_3095546 1589502986102850895738849 := by
  unfold tailWord_3095546
  simp only [CollatzResearch.WordTrace]
  refine ⟨28225959510843248502942623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75269225362248662674513661 28225959510843248502942623)
  ·
    refine ⟨42338939266264872754413935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28225959510843248502942623 42338939266264872754413935)
    ·
      refine ⟨63508408899397309131620903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42338939266264872754413935 63508408899397309131620903)
      ·
        refine ⟨95262613349095963697431355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63508408899397309131620903 95262613349095963697431355)
        ·
          refine ⟨142893920023643945546147033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95262613349095963697431355 142893920023643945546147033)
          ·
            refine ⟨107170440017732959159610275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142893920023643945546147033 107170440017732959159610275)
            ·
              refine ⟨160755660026599438739415413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107170440017732959159610275 160755660026599438739415413)
              ·
                refine ⟨15070843127493697381820195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 160755660026599438739415413 15070843127493697381820195)
                ·
                  refine ⟨22606264691240546072730293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15070843127493697381820195 22606264691240546072730293)
                  ·
                    refine ⟨2119337314803801194318465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22606264691240546072730293 2119337314803801194318465)
                    ·
                      refine ⟨1589502986102850895738849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2119337314803801194318465 1589502986102850895738849)
                      ·
                        rfl

theorem cell23_3095546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 5, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 5, 1, 5, 2].length) (baseStart_3095546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3095546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3095546 prefixEnd_3095546 := by exact prefixLift 3095546
  have htrace : WordTrace (prefixWord ++ tailWord_3095546) baseStart_3095546 baseEnd_3095546 := by
    simpa [prefixWord, tailWord_3095546, baseEnd_3095546] using wordTrace_append hprefix tailTrace_3095546
  have hstable : (prefixWord ++ tailWord_3095546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3095546).length < 2 ^ (prefixWord ++ tailWord_3095546).sum := by decide
  have hdescent : baseEnd_3095546 < baseStart_3095546 := by decide
  rcases family_descends (prefixWord ++ tailWord_3095546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3095563 : List Nat := [1, 1, 1, 1, 6, 2, 2, 2, 2, 3, 2]
def baseStart_3095563 : Nat := 118140960795 + 3095563 * 2 ^ 59
def prefixEnd_3095563 : Nat := 4983230072969 + 3 ^ 40 * 3095563 * 2
def baseEnd_3095563 : Nat := 1589511715273977329226271

theorem tailTrace_3095563 : CollatzResearch.WordTrace tailWord_3095563 prefixEnd_3095563 1589511715273977329226271 := by
  unfold tailWord_3095563
  simp only [CollatzResearch.WordTrace]
  refine ⟨112904458084311405915139343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75269638722874270610092895 112904458084311405915139343)
  ·
    refine ⟨169356687126467108872709015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112904458084311405915139343 169356687126467108872709015)
    ·
      refine ⟨254035030689700663309063523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169356687126467108872709015 254035030689700663309063523)
      ·
        refine ⟨381052546034550994963595285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254035030689700663309063523 381052546034550994963595285)
        ·
          refine ⟨17861838095369577888918529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 381052546034550994963595285 17861838095369577888918529)
          ·
            refine ⟨13396378571527183416688897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17861838095369577888918529 13396378571527183416688897)
            ·
              refine ⟨10047283928645387562516673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13396378571527183416688897 10047283928645387562516673)
              ·
                refine ⟨7535462946484040671887505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10047283928645387562516673 7535462946484040671887505)
                ·
                  refine ⟨5651597209863030503915629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7535462946484040671887505 5651597209863030503915629)
                  ·
                    refine ⟨2119348953698636438968361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5651597209863030503915629 2119348953698636438968361)
                    ·
                      refine ⟨1589511715273977329226271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2119348953698636438968361 1589511715273977329226271)
                      ·
                        rfl

theorem cell23_3095563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 2, 2, 3, 2].length) (baseStart_3095563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3095563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3095563 prefixEnd_3095563 := by exact prefixLift 3095563
  have htrace : WordTrace (prefixWord ++ tailWord_3095563) baseStart_3095563 baseEnd_3095563 := by
    simpa [prefixWord, tailWord_3095563, baseEnd_3095563] using wordTrace_append hprefix tailTrace_3095563
  have hstable : (prefixWord ++ tailWord_3095563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3095563).length < 2 ^ (prefixWord ++ tailWord_3095563).sum := by decide
  have hdescent : baseEnd_3095563 < baseStart_3095563 := by decide
  rcases family_descends (prefixWord ++ tailWord_3095563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3095576 : List Nat := [2, 1, 2, 3, 2, 2, 1, 2, 3, 1, 4]
def baseStart_3095576 : Nat := 118140960795 + 3095576 * 2 ^ 59
def prefixEnd_3095576 : Nat := 4983230072969 + 3 ^ 40 * 3095576 * 2
def baseEnd_3095576 : Nat := 1589518390522485778363711

theorem tailTrace_3095576 : CollatzResearch.WordTrace tailWord_3095576 prefixEnd_3095576 1589518390522485778363711 := by
  unfold tailWord_3095576
  simp only [CollatzResearch.WordTrace]
  refine ⟨56452466116632154567681291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75269954822176206090241721 56452466116632154567681291)
  ·
    refine ⟨84678699174948231851521937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56452466116632154567681291 84678699174948231851521937)
    ·
      refine ⟨63509024381211173888641453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84678699174948231851521937 63509024381211173888641453)
      ·
        refine ⟨23815884142954190208240545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63509024381211173888641453 23815884142954190208240545)
        ·
          refine ⟨17861913107215642656180409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23815884142954190208240545 17861913107215642656180409)
          ·
            refine ⟨13396434830411731992135307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17861913107215642656180409 13396434830411731992135307)
            ·
              refine ⟨20094652245617597988202961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13396434830411731992135307 20094652245617597988202961)
              ·
                refine ⟨15070989184213198491152221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20094652245617597988202961 15070989184213198491152221)
                ·
                  refine ⟨5651620944079949434182083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15070989184213198491152221 5651620944079949434182083)
                  ·
                    refine ⟨8477431416119924151273125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5651620944079949434182083 8477431416119924151273125)
                    ·
                      refine ⟨1589518390522485778363711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8477431416119924151273125 1589518390522485778363711)
                      ·
                        rfl

theorem cell23_3095576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 2, 3, 1, 4].length) (baseStart_3095576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3095576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3095576 prefixEnd_3095576 := by exact prefixLift 3095576
  have htrace : WordTrace (prefixWord ++ tailWord_3095576) baseStart_3095576 baseEnd_3095576 := by
    simpa [prefixWord, tailWord_3095576, baseEnd_3095576] using wordTrace_append hprefix tailTrace_3095576
  have hstable : (prefixWord ++ tailWord_3095576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3095576).length < 2 ^ (prefixWord ++ tailWord_3095576).sum := by decide
  have hdescent : baseEnd_3095576 < baseStart_3095576 := by decide
  rcases family_descends (prefixWord ++ tailWord_3095576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3095586 : List Nat := [3, 3, 1, 1, 1, 3, 1, 3, 1, 6]
def baseStart_3095586 : Nat := 118140960795 + 3095586 * 2 ^ 59
def prefixEnd_3095586 : Nat := 4983230072969 + 3 ^ 40 * 3095586 * 2
def baseEnd_3095586 : Nat := 529841175109676913079555

theorem tailTrace_3095586 : CollatzResearch.WordTrace tailWord_3095586 prefixEnd_3095586 529841175109676913079555 := by
  unfold tailWord_3095586
  simp only [CollatzResearch.WordTrace]
  refine ⟨28226324240807020210806653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75270197975485387228817741 28226324240807020210806653)
  ·
    refine ⟨10584871590302632579052495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28226324240807020210806653 10584871590302632579052495)
    ·
      refine ⟨15877307385453948868578743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10584871590302632579052495 15877307385453948868578743)
      ·
        refine ⟨23815961078180923302868115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15877307385453948868578743 23815961078180923302868115)
        ·
          refine ⟨35723941617271384954302173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23815961078180923302868115 35723941617271384954302173)
          ·
            refine ⟨13396478106476769357863315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35723941617271384954302173 13396478106476769357863315)
            ·
              refine ⟨20094717159715154036794973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13396478106476769357863315 20094717159715154036794973)
              ·
                refine ⟨7535518934893182763798115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20094717159715154036794973 7535518934893182763798115)
                ·
                  refine ⟨11303278402339774145697173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7535518934893182763798115 11303278402339774145697173)
                  ·
                    refine ⟨529841175109676913079555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11303278402339774145697173 529841175109676913079555)
                    ·
                      rfl

theorem cell23_3095586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 3, 1, 6].length) (baseStart_3095586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3095586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3095586 prefixEnd_3095586 := by exact prefixLift 3095586
  have htrace : WordTrace (prefixWord ++ tailWord_3095586) baseStart_3095586 baseEnd_3095586 := by
    simpa [prefixWord, tailWord_3095586, baseEnd_3095586] using wordTrace_append hprefix tailTrace_3095586
  have hstable : (prefixWord ++ tailWord_3095586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3095586).length < 2 ^ (prefixWord ++ tailWord_3095586).sum := by decide
  have hdescent : baseEnd_3095586 < baseStart_3095586 := by decide
  rcases family_descends (prefixWord ++ tailWord_3095586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3095596 : List Nat := [2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 3]
def baseStart_3095596 : Nat := 118140960795 + 3095596 * 2 ^ 59
def prefixEnd_3095596 : Nat := 4983230072969 + 3 ^ 40 * 3095596 * 2
def baseEnd_3095596 : Nat := 1589528660135575700113619

theorem tailTrace_3095596 : CollatzResearch.WordTrace tailWord_3095596 prefixEnd_3095596 1589528660135575700113619 := by
  unfold tailWord_3095596
  simp only [CollatzResearch.WordTrace]
  refine ⟨56452830846595926275545321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75270441128794568367393761 56452830846595926275545321)
  ·
    refine ⟨42339623134946944706658991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56452830846595926275545321 42339623134946944706658991)
    ·
      refine ⟨63509434702420417059988487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42339623134946944706658991 63509434702420417059988487)
      ·
        refine ⟨95264152053630625589982731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63509434702420417059988487 95264152053630625589982731)
        ·
          refine ⟨142896228080445938384974097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95264152053630625589982731 142896228080445938384974097)
          ·
            refine ⟨107172171060334453788730573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142896228080445938384974097 107172171060334453788730573)
            ·
              refine ⟨40189564147625420170773965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 107172171060334453788730573 40189564147625420170773965)
              ·
                refine ⟨15071086555359532564040237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40189564147625420170773965 15071086555359532564040237)
                ·
                  refine ⟨5651657458259824711515089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15071086555359532564040237 5651657458259824711515089)
                  ·
                    refine ⟨4238743093694868533636317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5651657458259824711515089 4238743093694868533636317)
                    ·
                      refine ⟨1589528660135575700113619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4238743093694868533636317 1589528660135575700113619)
                      ·
                        rfl

theorem cell23_3095596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 3].length) (baseStart_3095596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3095596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3095596 prefixEnd_3095596 := by exact prefixLift 3095596
  have htrace : WordTrace (prefixWord ++ tailWord_3095596) baseStart_3095596 baseEnd_3095596 := by
    simpa [prefixWord, tailWord_3095596, baseEnd_3095596] using wordTrace_append hprefix tailTrace_3095596
  have hstable : (prefixWord ++ tailWord_3095596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3095596).length < 2 ^ (prefixWord ++ tailWord_3095596).sum := by decide
  have hdescent : baseEnd_3095596 < baseStart_3095596 := by decide
  rcases family_descends (prefixWord ++ tailWord_3095596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3095604 : List Nat := [2, 5, 1, 2, 1, 2, 2, 3, 1, 1, 3]
def baseStart_3095604 : Nat := 118140960795 + 3095604 * 2 ^ 59
def prefixEnd_3095604 : Nat := 4983230072969 + 3 ^ 40 * 3095604 * 2
def baseEnd_3095604 : Nat := 1589532767980811668813583

theorem tailTrace_3095604 : CollatzResearch.WordTrace tailWord_3095604 prefixEnd_3095604 1589532767980811668813583 := by
  unfold tailWord_3095604
  simp only [CollatzResearch.WordTrace]
  refine ⟨56452976738581434958690933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75270635651441913278254577 56452976738581434958690933)
  ·
    refine ⟨5292466569242009527377275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 56452976738581434958690933 5292466569242009527377275)
    ·
      refine ⟨7938699853863014291065913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5292466569242009527377275 7938699853863014291065913)
      ·
        refine ⟨5954024890397260718299435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7938699853863014291065913 5954024890397260718299435)
        ·
          refine ⟨8931037335595891077449153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5954024890397260718299435 8931037335595891077449153)
          ·
            refine ⟨6698278001696918308086865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8931037335595891077449153 6698278001696918308086865)
            ·
              refine ⟨5023708501272688731065149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6698278001696918308086865 5023708501272688731065149)
              ·
                refine ⟨1883890687977258274149431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5023708501272688731065149 1883890687977258274149431)
                ·
                  refine ⟨2825836031965887411224147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1883890687977258274149431 2825836031965887411224147)
                  ·
                    refine ⟨4238754047948831116836221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2825836031965887411224147 4238754047948831116836221)
                    ·
                      refine ⟨1589532767980811668813583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4238754047948831116836221 1589532767980811668813583)
                      ·
                        rfl

theorem cell23_3095604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 2, 3, 1, 1, 3].length) (baseStart_3095604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3095604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3095604 prefixEnd_3095604 := by exact prefixLift 3095604
  have htrace : WordTrace (prefixWord ++ tailWord_3095604) baseStart_3095604 baseEnd_3095604 := by
    simpa [prefixWord, tailWord_3095604, baseEnd_3095604] using wordTrace_append hprefix tailTrace_3095604
  have hstable : (prefixWord ++ tailWord_3095604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3095604).length < 2 ^ (prefixWord ++ tailWord_3095604).sum := by decide
  have hdescent : baseEnd_3095604 < baseStart_3095604 := by decide
  rcases family_descends (prefixWord ++ tailWord_3095604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3095626 : List Nat := [3, 1, 2, 1, 1, 2, 2, 2, 3, 3, 3]
def baseStart_3095626 : Nat := 118140960795 + 3095626 * 2 ^ 59
def prefixEnd_3095626 : Nat := 4983230072969 + 3 ^ 40 * 3095626 * 2
def baseEnd_3095626 : Nat := 1589544064555210582738481

theorem tailTrace_3095626 : CollatzResearch.WordTrace tailWord_3095626 prefixEnd_3095626 1589544064555210582738481 := by
  unfold tailWord_3095626
  simp only [CollatzResearch.WordTrace]
  refine ⟨28226688970770791918670683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75271170588722111783121821 28226688970770791918670683)
  ·
    refine ⟨42340033456156187878006025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28226688970770791918670683 42340033456156187878006025)
    ·
      refine ⟨31755025092117140908504519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42340033456156187878006025 31755025092117140908504519)
      ·
        refine ⟨47632537638175711362756779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31755025092117140908504519 47632537638175711362756779)
        ·
          refine ⟨71448806457263567044135169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47632537638175711362756779 71448806457263567044135169)
          ·
            refine ⟨53586604842947675283101377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71448806457263567044135169 53586604842947675283101377)
            ·
              refine ⟨40189953632210756462326033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53586604842947675283101377 40189953632210756462326033)
              ·
                refine ⟨30142465224158067346744525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40189953632210756462326033 30142465224158067346744525)
                ·
                  refine ⟨11303424459059275255029197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30142465224158067346744525 11303424459059275255029197)
                  ·
                    refine ⟨4238784172147228220635949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11303424459059275255029197 4238784172147228220635949)
                    ·
                      refine ⟨1589544064555210582738481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4238784172147228220635949 1589544064555210582738481)
                      ·
                        rfl

theorem cell23_3095626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 2, 3, 3, 3].length) (baseStart_3095626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3095626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3095626 prefixEnd_3095626 := by exact prefixLift 3095626
  have htrace : WordTrace (prefixWord ++ tailWord_3095626) baseStart_3095626 baseEnd_3095626 := by
    simpa [prefixWord, tailWord_3095626, baseEnd_3095626] using wordTrace_append hprefix tailTrace_3095626
  have hstable : (prefixWord ++ tailWord_3095626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3095626).length < 2 ^ (prefixWord ++ tailWord_3095626).sum := by decide
  have hdescent : baseEnd_3095626 < baseStart_3095626 := by decide
  rcases family_descends (prefixWord ++ tailWord_3095626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3095650 : List Nat := [3, 3, 2, 2, 1, 3, 2, 7]
def baseStart_3095650 : Nat := 118140960795 + 3095650 * 2 ^ 59
def prefixEnd_3095650 : Nat := 4983230072969 + 3 ^ 40 * 3095650 * 2
def baseEnd_3095650 : Nat := 58872458818182166253273

theorem tailTrace_3095650 : CollatzResearch.WordTrace tailWord_3095650 prefixEnd_3095650 58872458818182166253273 := by
  unfold tailWord_3095650
  simp only [CollatzResearch.WordTrace]
  refine ⟨28226907808749054943389101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75271754156664146515704269 28226907808749054943389101)
  ·
    refine ⟨10585090428280895603770913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28226907808749054943389101 10585090428280895603770913)
    ·
      refine ⟨7938817821210671702828185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10585090428280895603770913 7938817821210671702828185)
      ·
        refine ⟨5954113365908003777121139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7938817821210671702828185 5954113365908003777121139)
        ·
          refine ⟨8931170048862005665681709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5954113365908003777121139 8931170048862005665681709)
          ·
            refine ⟨3349188768323252124630641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8931170048862005665681709 3349188768323252124630641)
            ·
              refine ⟨2511891576242439093472981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3349188768323252124630641 2511891576242439093472981)
              ·
                refine ⟨58872458818182166253273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2511891576242439093472981 58872458818182166253273)
                ·
                  rfl

theorem cell23_3095650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 2, 7].length) (baseStart_3095650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3095650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3095650 prefixEnd_3095650 := by exact prefixLift 3095650
  have htrace : WordTrace (prefixWord ++ tailWord_3095650) baseStart_3095650 baseEnd_3095650 := by
    simpa [prefixWord, tailWord_3095650, baseEnd_3095650] using wordTrace_append hprefix tailTrace_3095650
  have hstable : (prefixWord ++ tailWord_3095650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3095650).length < 2 ^ (prefixWord ++ tailWord_3095650).sum := by decide
  have hdescent : baseEnd_3095650 < baseStart_3095650 := by decide
  rcases family_descends (prefixWord ++ tailWord_3095650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3095678 : List Nat := [4, 2, 4, 1, 1, 2, 1, 1, 3, 2, 2]
def baseStart_3095678 : Nat := 118140960795 + 3095678 * 2 ^ 59
def prefixEnd_3095678 : Nat := 4983230072969 + 3 ^ 40 * 3095678 * 2
def baseEnd_3095678 : Nat := 1589570765549244379288243

theorem tailTrace_3095678 : CollatzResearch.WordTrace tailWord_3095678 prefixEnd_3095678 1589570765549244379288243 := by
  unfold tailWord_3095678
  simp only [CollatzResearch.WordTrace]
  refine ⟨14113581559861847569446961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75272434985929853703717125 14113581559861847569446961)
  ·
    refine ⟨10585186169896385677085221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14113581559861847569446961 10585186169896385677085221)
    ·
      refine ⟨1984722406855572314453479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10585186169896385677085221 1984722406855572314453479)
      ·
        refine ⟨2977083610283358471680219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1984722406855572314453479 2977083610283358471680219)
        ·
          refine ⟨4465625415425037707520329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2977083610283358471680219 4465625415425037707520329)
          ·
            refine ⟨3349219061568778280640247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4465625415425037707520329 3349219061568778280640247)
            ·
              refine ⟨5023828592353167420960371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3349219061568778280640247 5023828592353167420960371)
              ·
                refine ⟨7535742888529751131440557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5023828592353167420960371 7535742888529751131440557)
                ·
                  refine ⟨2825903583198656674290209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7535742888529751131440557 2825903583198656674290209)
                  ·
                    refine ⟨2119427687398992505717657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2825903583198656674290209 2119427687398992505717657)
                    ·
                      refine ⟨1589570765549244379288243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2119427687398992505717657 1589570765549244379288243)
                      ·
                        rfl

theorem cell23_3095678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 1, 1, 3, 2, 2].length) (baseStart_3095678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3095678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3095678 prefixEnd_3095678 := by exact prefixLift 3095678
  have htrace : WordTrace (prefixWord ++ tailWord_3095678) baseStart_3095678 baseEnd_3095678 := by
    simpa [prefixWord, tailWord_3095678, baseEnd_3095678] using wordTrace_append hprefix tailTrace_3095678
  have hstable : (prefixWord ++ tailWord_3095678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3095678).length < 2 ^ (prefixWord ++ tailWord_3095678).sum := by decide
  have hdescent : baseEnd_3095678 < baseStart_3095678 := by decide
  rcases family_descends (prefixWord ++ tailWord_3095678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3095694 : List Nat := [4, 1, 1, 3, 2, 3, 2, 1, 2, 1, 3]
def baseStart_3095694 : Nat := 118140960795 + 3095694 * 2 ^ 59
def prefixEnd_3095694 : Nat := 4983230072969 + 3 ^ 40 * 3095694 * 2
def baseEnd_3095694 : Nat := 1589578981239716316688169

theorem tailTrace_3095694 : CollatzResearch.WordTrace tailWord_3095694 prefixEnd_3095694 1589578981239716316688169 := by
  unfold tailWord_3095694
  simp only [CollatzResearch.WordTrace]
  refine ⟨14113654505854601911019767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75272824031224543525438757 14113654505854601911019767)
  ·
    refine ⟨21170481758781902866529651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14113654505854601911019767 21170481758781902866529651)
    ·
      refine ⟨31755722638172854299794477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21170481758781902866529651 31755722638172854299794477)
      ·
        refine ⟨11908395989314820362422929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31755722638172854299794477 11908395989314820362422929)
        ·
          refine ⟨8931296991986115271817197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11908395989314820362422929 8931296991986115271817197)
          ·
            refine ⟨3349236371994793226931449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8931296991986115271817197 3349236371994793226931449)
            ·
              refine ⟨2511927278996094920198587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3349236371994793226931449 2511927278996094920198587)
              ·
                refine ⟨3767890918494142380297881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2511927278996094920198587 3767890918494142380297881)
                ·
                  refine ⟨2825918188870606785223411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3767890918494142380297881 2825918188870606785223411)
                  ·
                    refine ⟨4238877283305910177835117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2825918188870606785223411 4238877283305910177835117)
                    ·
                      refine ⟨1589578981239716316688169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4238877283305910177835117 1589578981239716316688169)
                      ·
                        rfl

theorem cell23_3095694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 2, 1, 2, 1, 3].length) (baseStart_3095694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3095694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3095694 prefixEnd_3095694 := by exact prefixLift 3095694
  have htrace : WordTrace (prefixWord ++ tailWord_3095694) baseStart_3095694 baseEnd_3095694 := by
    simpa [prefixWord, tailWord_3095694, baseEnd_3095694] using wordTrace_append hprefix tailTrace_3095694
  have hstable : (prefixWord ++ tailWord_3095694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3095694).length < 2 ^ (prefixWord ++ tailWord_3095694).sum := by decide
  have hdescent : baseEnd_3095694 < baseStart_3095694 := by decide
  rcases family_descends (prefixWord ++ tailWord_3095694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3095736 : List Nat := [2, 1, 2, 1, 2, 1, 2, 3, 4, 5]
def baseStart_3095736 : Nat := 118140960795 + 3095736 * 2 ^ 59
def prefixEnd_3095736 : Nat := 4983230072969 + 3 ^ 40 * 3095736 * 2
def baseEnd_3095736 : Nat := 529866849142401717454325

theorem tailTrace_3095736 : CollatzResearch.WordTrace tailWord_3095736 prefixEnd_3095736 529866849142401717454325 := by
  unfold tailWord_3095736
  simp only [CollatzResearch.WordTrace]
  refine ⟨56455383956342328230593531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75273845275123104307458041 56455383956342328230593531)
  ·
    refine ⟨84683075934513492345890297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56455383956342328230593531 84683075934513492345890297)
    ·
      refine ⟨63512306950885119259417723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84683075934513492345890297 63512306950885119259417723)
      ·
        refine ⟨95268460426327678889126585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63512306950885119259417723 95268460426327678889126585)
        ·
          refine ⟨71451345319745759166844939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95268460426327678889126585 71451345319745759166844939)
          ·
            refine ⟨107177017979618638750267409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71451345319745759166844939 107177017979618638750267409)
            ·
              refine ⟨80382763484713979062700557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107177017979618638750267409 80382763484713979062700557)
              ·
                refine ⟨30143536306767742148512709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80382763484713979062700557 30143536306767742148512709)
                ·
                  refine ⟨5651913057518951652846133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30143536306767742148512709 5651913057518951652846133)
                  ·
                    refine ⟨529866849142401717454325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5651913057518951652846133 529866849142401717454325)
                    ·
                      rfl

theorem cell23_3095736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 3, 4, 5].length) (baseStart_3095736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3095736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3095736 prefixEnd_3095736 := by exact prefixLift 3095736
  have htrace : WordTrace (prefixWord ++ tailWord_3095736) baseStart_3095736 baseEnd_3095736 := by
    simpa [prefixWord, tailWord_3095736, baseEnd_3095736] using wordTrace_append hprefix tailTrace_3095736
  have hstable : (prefixWord ++ tailWord_3095736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3095736).length < 2 ^ (prefixWord ++ tailWord_3095736).sum := by decide
  have hdescent : baseEnd_3095736 < baseStart_3095736 := by decide
  rcases family_descends (prefixWord ++ tailWord_3095736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3095740 : List Nat := [2, 2, 2, 3, 2, 2, 1, 4, 5]
def baseStart_3095740 : Nat := 118140960795 + 3095740 * 2 ^ 59
def prefixEnd_3095740 : Nat := 4983230072969 + 3 ^ 40 * 3095740 * 2
def baseEnd_3095740 : Nat := 176622511261091459634773

theorem tailTrace_3095740 : CollatzResearch.WordTrace tailWord_3095740 prefixEnd_3095740 176622511261091459634773 := by
  unfold tailWord_3095740
  simp only [CollatzResearch.WordTrace]
  refine ⟨56455456902335082572166337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75273942536446776762888449 56455456902335082572166337)
  ·
    refine ⟨42341592676751311929124753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56455456902335082572166337 42341592676751311929124753)
    ·
      refine ⟨31756194507563483946843565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42341592676751311929124753 31756194507563483946843565)
      ·
        refine ⟨11908572940336306480066337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31756194507563483946843565 11908572940336306480066337)
        ·
          refine ⟨8931429705252229860049753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11908572940336306480066337 8931429705252229860049753)
          ·
            refine ⟨6698572278939172395037315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8931429705252229860049753 6698572278939172395037315)
            ·
              refine ⟨10047858418408758592555973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6698572278939172395037315 10047858418408758592555973)
              ·
                refine ⟨1883973453451642236104245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10047858418408758592555973 1883973453451642236104245)
                ·
                  refine ⟨176622511261091459634773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1883973453451642236104245 176622511261091459634773)
                  ·
                    rfl

theorem cell23_3095740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 4, 5].length) (baseStart_3095740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3095740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3095740 prefixEnd_3095740 := by exact prefixLift 3095740
  have htrace : WordTrace (prefixWord ++ tailWord_3095740) baseStart_3095740 baseEnd_3095740 := by
    simpa [prefixWord, tailWord_3095740, baseEnd_3095740] using wordTrace_append hprefix tailTrace_3095740
  have hstable : (prefixWord ++ tailWord_3095740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3095740).length < 2 ^ (prefixWord ++ tailWord_3095740).sum := by decide
  have hdescent : baseEnd_3095740 < baseStart_3095740 := by decide
  rcases family_descends (prefixWord ++ tailWord_3095740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3095743 : List Nat := [1, 1, 2, 2, 2, 2, 3, 1, 2, 5, 2]
def baseStart_3095743 : Nat := 118140960795 + 3095743 * 2 ^ 59
def prefixEnd_3095743 : Nat := 4983230072969 + 3 ^ 40 * 3095743 * 2
def baseEnd_3095743 : Nat := 1589604141791786624975443

theorem tailTrace_3095743 : CollatzResearch.WordTrace tailWord_3095743 prefixEnd_3095743 1589604141791786624975443 := by
  unfold tailWord_3095743
  simp only [CollatzResearch.WordTrace]
  refine ⟨112911023223659296656691883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75274015482439531104461255 112911023223659296656691883)
  ·
    refine ⟨169366534835488944985037825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112911023223659296656691883 169366534835488944985037825)
    ·
      refine ⟨127024901126616708738778369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169366534835488944985037825 127024901126616708738778369)
      ·
        refine ⟨95268675844962531554083777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127024901126616708738778369 95268675844962531554083777)
        ·
          refine ⟨71451506883721898665562833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95268675844962531554083777 71451506883721898665562833)
          ·
            refine ⟨53588630162791423999172125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71451506883721898665562833 53588630162791423999172125)
            ·
              refine ⟨20095736311046783999689547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53588630162791423999172125 20095736311046783999689547)
              ·
                refine ⟨30143604466570175999534321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20095736311046783999689547 30143604466570175999534321)
                ·
                  refine ⟨22607703349927631999650741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30143604466570175999534321 22607703349927631999650741)
                  ·
                    refine ⟨2119472189055715499967257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22607703349927631999650741 2119472189055715499967257)
                    ·
                      refine ⟨1589604141791786624975443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2119472189055715499967257 1589604141791786624975443)
                      ·
                        rfl

theorem cell23_3095743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 1, 2, 5, 2].length) (baseStart_3095743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3095743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3095743 prefixEnd_3095743 := by exact prefixLift 3095743
  have htrace : WordTrace (prefixWord ++ tailWord_3095743) baseStart_3095743 baseEnd_3095743 := by
    simpa [prefixWord, tailWord_3095743, baseEnd_3095743] using wordTrace_append hprefix tailTrace_3095743
  have hstable : (prefixWord ++ tailWord_3095743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3095743).length < 2 ^ (prefixWord ++ tailWord_3095743).sum := by decide
  have hdescent : baseEnd_3095743 < baseStart_3095743 := by decide
  rcases family_descends (prefixWord ++ tailWord_3095743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3095757 : List Nat := [1, 6, 2, 2, 1, 1, 1, 2, 7]
def baseStart_3095757 : Nat := 118140960795 + 3095757 * 2 ^ 59
def prefixEnd_3095757 : Nat := 4983230072969 + 3 ^ 40 * 3095757 * 2
def baseEnd_3095757 : Nat := 176623481168994396688931

theorem tailTrace_3095757 : CollatzResearch.WordTrace tailWord_3095757 prefixEnd_3095757 176623481168994396688931 := by
  unfold tailWord_3095757
  simp only [CollatzResearch.WordTrace]
  refine ⟨112911533845608577047701525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75274355897072384698467683 112911533845608577047701525)
  ·
    refine ⟨5292728149012902049111009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 112911533845608577047701525 5292728149012902049111009)
    ·
      refine ⟨3969546111759676536833257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5292728149012902049111009 3969546111759676536833257)
      ·
        refine ⟨2977159583819757402624943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3969546111759676536833257 2977159583819757402624943)
        ·
          refine ⟨4465739375729636103937415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2977159583819757402624943 4465739375729636103937415)
          ·
            refine ⟨6698609063594454155906123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4465739375729636103937415 6698609063594454155906123)
            ·
              refine ⟨10047913595391681233859185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6698609063594454155906123 10047913595391681233859185)
              ·
                refine ⟨7535935196543760925394389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10047913595391681233859185 7535935196543760925394389)
                ·
                  refine ⟨176623481168994396688931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7535935196543760925394389 176623481168994396688931)
                  ·
                    rfl

theorem cell23_3095757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 2, 7].length) (baseStart_3095757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3095757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3095757 prefixEnd_3095757 := by exact prefixLift 3095757
  have htrace : WordTrace (prefixWord ++ tailWord_3095757) baseStart_3095757 baseEnd_3095757 := by
    simpa [prefixWord, tailWord_3095757, baseEnd_3095757] using wordTrace_append hprefix tailTrace_3095757
  have hstable : (prefixWord ++ tailWord_3095757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3095757).length < 2 ^ (prefixWord ++ tailWord_3095757).sum := by decide
  have hdescent : baseEnd_3095757 < baseStart_3095757 := by decide
  rcases family_descends (prefixWord ++ tailWord_3095757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3095790 : List Nat := [4, 1, 2, 1, 1, 1, 3, 2, 2, 4, 2]
def baseStart_3095790 : Nat := 118140960795 + 3095790 * 2 ^ 59
def prefixEnd_3095790 : Nat := 4983230072969 + 3 ^ 40 * 3095790 * 2
def baseEnd_3095790 : Nat := 1589628275382547941087727

theorem tailTrace_3095790 : CollatzResearch.WordTrace tailWord_3095790 prefixEnd_3095790 1589628275382547941087727 := by
  unfold tailWord_3095790
  simp only [CollatzResearch.WordTrace]
  refine ⟨14114092181811127960456603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75275158302992682455768549 14114092181811127960456603)
  ·
    refine ⟨21171138272716691940684905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14114092181811127960456603 21171138272716691940684905)
    ·
      refine ⟨15878353704537518955513679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21171138272716691940684905 15878353704537518955513679)
      ·
        refine ⟨23817530556806278433270519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15878353704537518955513679 23817530556806278433270519)
        ·
          refine ⟨35726295835209417649905779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23817530556806278433270519 35726295835209417649905779)
          ·
            refine ⟨53589443752814126474858669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35726295835209417649905779 53589443752814126474858669)
            ·
              refine ⟨20096041407305297428072001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53589443752814126474858669 20096041407305297428072001)
              ·
                refine ⟨15072031055478973071054001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20096041407305297428072001 15072031055478973071054001)
                ·
                  refine ⟨11304023291609229803290501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15072031055478973071054001 11304023291609229803290501)
                  ·
                    refine ⟨2119504367176730588116969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11304023291609229803290501 2119504367176730588116969)
                    ·
                      refine ⟨1589628275382547941087727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2119504367176730588116969 1589628275382547941087727)
                      ·
                        rfl

theorem cell23_3095790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 2, 2, 4, 2].length) (baseStart_3095790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3095790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3095790 prefixEnd_3095790 := by exact prefixLift 3095790
  have htrace : WordTrace (prefixWord ++ tailWord_3095790) baseStart_3095790 baseEnd_3095790 := by
    simpa [prefixWord, tailWord_3095790, baseEnd_3095790] using wordTrace_append hprefix tailTrace_3095790
  have hstable : (prefixWord ++ tailWord_3095790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3095790).length < 2 ^ (prefixWord ++ tailWord_3095790).sum := by decide
  have hdescent : baseEnd_3095790 < baseStart_3095790 := by decide
  rcases family_descends (prefixWord ++ tailWord_3095790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3095793 : List Nat := [1, 2, 2, 2, 2, 1, 1, 3, 4, 2, 3]
def baseStart_3095793 : Nat := 118140960795 + 3095793 * 2 ^ 59
def prefixEnd_3095793 : Nat := 4983230072969 + 3 ^ 40 * 3095793 * 2
def baseEnd_3095793 : Nat := 1589629815824511429350213

theorem tailTrace_3095793 : CollatzResearch.WordTrace tailWord_3095793 prefixEnd_3095793 1589629815824511429350213 := by
  unfold tailWord_3095793
  simp only [CollatzResearch.WordTrace]
  refine ⟨112912846873478155196012033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75275231248985436797341355 112912846873478155196012033)
  ·
    refine ⟨84684635155108616397009025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112912846873478155196012033 84684635155108616397009025)
    ·
      refine ⟨63513476366331462297756769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84684635155108616397009025 63513476366331462297756769)
      ·
        refine ⟨47635107274748596723317577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63513476366331462297756769 47635107274748596723317577)
        ·
          refine ⟨35726330456061447542488183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47635107274748596723317577 35726330456061447542488183)
          ·
            refine ⟨53589495684092171313732275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35726330456061447542488183 53589495684092171313732275)
            ·
              refine ⟨80384243526138256970598413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53589495684092171313732275 80384243526138256970598413)
              ·
                refine ⟨30144091322301846363974405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80384243526138256970598413 30144091322301846363974405)
                ·
                  refine ⟨5652017122931596193245201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30144091322301846363974405 5652017122931596193245201)
                  ·
                    refine ⟨4239012842198697144933901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5652017122931596193245201 4239012842198697144933901)
                    ·
                      refine ⟨1589629815824511429350213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4239012842198697144933901 1589629815824511429350213)
                      ·
                        rfl

theorem cell23_3095793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 3, 4, 2, 3].length) (baseStart_3095793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3095793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3095793 prefixEnd_3095793 := by exact prefixLift 3095793
  have htrace : WordTrace (prefixWord ++ tailWord_3095793) baseStart_3095793 baseEnd_3095793 := by
    simpa [prefixWord, tailWord_3095793, baseEnd_3095793] using wordTrace_append hprefix tailTrace_3095793
  have hstable : (prefixWord ++ tailWord_3095793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3095793).length < 2 ^ (prefixWord ++ tailWord_3095793).sum := by decide
  have hdescent : baseEnd_3095793 < baseStart_3095793 := by decide
  rcases family_descends (prefixWord ++ tailWord_3095793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3095834 : List Nat := [3, 1, 1, 3, 3, 3, 1, 3, 1, 4]
def baseStart_3095834 : Nat := 118140960795 + 3095834 * 2 ^ 59
def prefixEnd_3095834 : Nat := 4983230072969 + 3 ^ 40 * 3095834 * 2
def baseEnd_3095834 : Nat := 529883622843781922979175

theorem tailTrace_3095834 : CollatzResearch.WordTrace tailWord_3095834 prefixEnd_3095834 529883622843781922979175 := by
  unfold tailWord_3095834
  simp only [CollatzResearch.WordTrace]
  refine ⟨28228585566582404799563639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75276228177553079465503037 28228585566582404799563639)
  ·
    refine ⟨42342878349873607199345459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28228585566582404799563639 42342878349873607199345459)
    ·
      refine ⟨63514317524810410799018189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42342878349873607199345459 63514317524810410799018189)
      ·
        refine ⟨23817869071803904049631821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63514317524810410799018189 23817869071803904049631821)
        ·
          refine ⟨8931700901926464018611933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23817869071803904049631821 8931700901926464018611933)
          ·
            refine ⟨3349387838222424006979475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8931700901926464018611933 3349387838222424006979475)
            ·
              refine ⟨5024081757333636010469213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3349387838222424006979475 5024081757333636010469213)
              ·
                refine ⟨1884030659000113503925955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5024081757333636010469213 1884030659000113503925955)
                ·
                  refine ⟨2826045988500170255888933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1884030659000113503925955 2826045988500170255888933)
                  ·
                    refine ⟨529883622843781922979175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2826045988500170255888933 529883622843781922979175)
                    ·
                      rfl

theorem cell23_3095834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 1, 3, 1, 4].length) (baseStart_3095834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3095834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3095834 prefixEnd_3095834 := by exact prefixLift 3095834
  have htrace : WordTrace (prefixWord ++ tailWord_3095834) baseStart_3095834 baseEnd_3095834 := by
    simpa [prefixWord, tailWord_3095834, baseEnd_3095834] using wordTrace_append hprefix tailTrace_3095834
  have hstable : (prefixWord ++ tailWord_3095834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3095834).length < 2 ^ (prefixWord ++ tailWord_3095834).sum := by decide
  have hdescent : baseEnd_3095834 < baseStart_3095834 := by decide
  rcases family_descends (prefixWord ++ tailWord_3095834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3095857 : List Nat := [1, 2, 2, 3, 3, 1, 3, 1, 3, 1, 3]
def baseStart_3095857 : Nat := 118140960795 + 3095857 * 2 ^ 59
def prefixEnd_3095857 : Nat := 4983230072969 + 3 ^ 40 * 3095857 * 2
def baseEnd_3095857 : Nat := 1589662678586399178949919

theorem tailTrace_3095857 : CollatzResearch.WordTrace tailWord_3095857 prefixEnd_3095857 1589662678586399178949919 := by
  unfold tailWord_3095857
  simp only [CollatzResearch.WordTrace]
  refine ⟨112915181145246294126341825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75276787430164196084227883 112915181145246294126341825)
  ·
    refine ⟨84686385858934720594756369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112915181145246294126341825 84686385858934720594756369)
    ·
      refine ⟨63514789394201040446067277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84686385858934720594756369 63514789394201040446067277)
      ·
        refine ⟨23818046022825390167275229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63514789394201040446067277 23818046022825390167275229)
        ·
          refine ⟨8931767258559521312728211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23818046022825390167275229 8931767258559521312728211)
          ·
            refine ⟨13397650887839281969092317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8931767258559521312728211 13397650887839281969092317)
            ·
              refine ⟨5024119082939730738409619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13397650887839281969092317 5024119082939730738409619)
              ·
                refine ⟨7536178624409596107614429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5024119082939730738409619 7536178624409596107614429)
                ·
                  refine ⟨2826066984153598540355411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7536178624409596107614429 2826066984153598540355411)
                  ·
                    refine ⟨4239100476230397810533117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2826066984153598540355411 4239100476230397810533117)
                    ·
                      refine ⟨1589662678586399178949919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4239100476230397810533117 1589662678586399178949919)
                      ·
                        rfl

theorem cell23_3095857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 3, 1, 3, 1, 3].length) (baseStart_3095857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3095857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3095857 prefixEnd_3095857 := by exact prefixLift 3095857
  have htrace : WordTrace (prefixWord ++ tailWord_3095857) baseStart_3095857 baseEnd_3095857 := by
    simpa [prefixWord, tailWord_3095857, baseEnd_3095857] using wordTrace_append hprefix tailTrace_3095857
  have hstable : (prefixWord ++ tailWord_3095857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3095857).length < 2 ^ (prefixWord ++ tailWord_3095857).sum := by decide
  have hdescent : baseEnd_3095857 < baseStart_3095857 := by decide
  rcases family_descends (prefixWord ++ tailWord_3095857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3095860 : List Nat := [2, 5, 1, 1, 1, 1, 2, 2, 3, 5]
def baseStart_3095860 : Nat := 118140960795 + 3095860 * 2 ^ 59
def prefixEnd_3095860 : Nat := 4983230072969 + 3 ^ 40 * 3095860 * 2
def baseEnd_3095860 : Nat := 529888073009454222404135

theorem tailTrace_3095860 : CollatzResearch.WordTrace tailWord_3095860 prefixEnd_3095860 529888073009454222404135 := by
  unfold tailWord_3095860
  simp only [CollatzResearch.WordTrace]
  refine ⟨56457645282117712819350517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75276860376156950425800689 56457645282117712819350517)
  ·
    refine ⟨5292904245198535576814111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 56457645282117712819350517 5292904245198535576814111)
    ·
      refine ⟨7939356367797803365221167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5292904245198535576814111 7939356367797803365221167)
      ·
        refine ⟨11909034551696705047831751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7939356367797803365221167 11909034551696705047831751)
        ·
          refine ⟨17863551827545057571747627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11909034551696705047831751 17863551827545057571747627)
          ·
            refine ⟨26795327741317586357621441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17863551827545057571747627 26795327741317586357621441)
            ·
              refine ⟨20096495805988189768216081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26795327741317586357621441 20096495805988189768216081)
              ·
                refine ⟨15072371854491142326162061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20096495805988189768216081 15072371854491142326162061)
                ·
                  refine ⟨5652139445434178372310773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15072371854491142326162061 5652139445434178372310773)
                  ·
                    refine ⟨529888073009454222404135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5652139445434178372310773 529888073009454222404135)
                    ·
                      rfl

theorem cell23_3095860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 2, 3, 5].length) (baseStart_3095860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3095860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3095860 prefixEnd_3095860 := by exact prefixLift 3095860
  have htrace : WordTrace (prefixWord ++ tailWord_3095860) baseStart_3095860 baseEnd_3095860 := by
    simpa [prefixWord, tailWord_3095860, baseEnd_3095860] using wordTrace_append hprefix tailTrace_3095860
  have hstable : (prefixWord ++ tailWord_3095860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3095860).length < 2 ^ (prefixWord ++ tailWord_3095860).sum := by decide
  have hdescent : baseEnd_3095860 < baseStart_3095860 := by decide
  rcases family_descends (prefixWord ++ tailWord_3095860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3095907 : List Nat := [1, 1, 1, 5, 2, 3, 2, 2, 2, 4]
def baseStart_3095907 : Nat := 118140960795 + 3095907 * 2 ^ 59
def prefixEnd_3095907 : Nat := 4983230072969 + 3 ^ 40 * 3095907 * 2
def baseEnd_3095907 : Nat := 529896117539707994441563

theorem tailTrace_3095907 : CollatzResearch.WordTrace tailWord_3095907 prefixEnd_3095907 529896117539707994441563 := by
  unfold tailWord_3095907
  simp only [CollatzResearch.WordTrace]
  refine ⟨112917004795065152665661975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75278003196710101777107983 112917004795065152665661975)
  ·
    refine ⟨169375507192597728998492963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112917004795065152665661975 169375507192597728998492963)
    ·
      refine ⟨254063260788896593497739445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169375507192597728998492963 254063260788896593497739445)
      ·
        refine ⟨23818430698959055640413073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 254063260788896593497739445 23818430698959055640413073)
        ·
          refine ⟨17863823024219291730309805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23818430698959055640413073 17863823024219291730309805)
          ·
            refine ⟨6698933634082234398866177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17863823024219291730309805 6698933634082234398866177)
            ·
              refine ⟨5024200225561675799149633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6698933634082234398866177 5024200225561675799149633)
              ·
                refine ⟨3768150169171256849362225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5024200225561675799149633 3768150169171256849362225)
                ·
                  refine ⟨2826112626878442637021669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3768150169171256849362225 2826112626878442637021669)
                  ·
                    refine ⟨529896117539707994441563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2826112626878442637021669 529896117539707994441563)
                    ·
                      rfl

theorem cell23_3095907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 2, 2, 2, 4].length) (baseStart_3095907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3095907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3095907 prefixEnd_3095907 := by exact prefixLift 3095907
  have htrace : WordTrace (prefixWord ++ tailWord_3095907) baseStart_3095907 baseEnd_3095907 := by
    simpa [prefixWord, tailWord_3095907, baseEnd_3095907] using wordTrace_append hprefix tailTrace_3095907
  have hstable : (prefixWord ++ tailWord_3095907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3095907).length < 2 ^ (prefixWord ++ tailWord_3095907).sum := by decide
  have hdescent : baseEnd_3095907 < baseStart_3095907 := by decide
  rcases family_descends (prefixWord ++ tailWord_3095907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3095933 : List Nat := [1, 4, 1, 1, 2, 2, 1, 2, 2, 7]
def baseStart_3095933 : Nat := 118140960795 + 3095933 * 2 ^ 59
def prefixEnd_3095933 : Nat := 4983230072969 + 3 ^ 40 * 3095933 * 2
def baseEnd_3095933 : Nat := 529900567705380293866523

theorem tailTrace_3095933 : CollatzResearch.WordTrace tailWord_3095933 prefixEnd_3095933 529900567705380293866523 := by
  unfold tailWord_3095933
  simp only [CollatzResearch.WordTrace]
  refine ⟨112917953092970959106108453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75278635395313972737405635 112917953092970959106108453)
  ·
    refine ⟨21172116204932054832395335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 112917953092970959106108453 21172116204932054832395335)
    ·
      refine ⟨31758174307398082248593003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21172116204932054832395335 31758174307398082248593003)
      ·
        refine ⟨47637261461097123372889505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31758174307398082248593003 47637261461097123372889505)
        ·
          refine ⟨35727946095822842529667129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47637261461097123372889505 35727946095822842529667129)
          ·
            refine ⟨26795959571867131897250347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35727946095822842529667129 26795959571867131897250347)
            ·
              refine ⟨40193939357800697845875521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26795959571867131897250347 40193939357800697845875521)
              ·
                refine ⟨30145454518350523384406641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40193939357800697845875521 30145454518350523384406641)
                ·
                  refine ⟨22609090888762892538304981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30145454518350523384406641 22609090888762892538304981)
                  ·
                    refine ⟨529900567705380293866523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22609090888762892538304981 529900567705380293866523)
                    ·
                      rfl

theorem cell23_3095933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 2, 2, 7].length) (baseStart_3095933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3095933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3095933 prefixEnd_3095933 := by exact prefixLift 3095933
  have htrace : WordTrace (prefixWord ++ tailWord_3095933) baseStart_3095933 baseEnd_3095933 := by
    simpa [prefixWord, tailWord_3095933, baseEnd_3095933] using wordTrace_append hprefix tailTrace_3095933
  have hstable : (prefixWord ++ tailWord_3095933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3095933).length < 2 ^ (prefixWord ++ tailWord_3095933).sum := by decide
  have hdescent : baseEnd_3095933 < baseStart_3095933 := by decide
  rcases family_descends (prefixWord ++ tailWord_3095933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3095937 : List Nat := [1, 2, 4, 3, 2, 1, 3, 7]
def baseStart_3095937 : Nat := 118140960795 + 3095937 * 2 ^ 59
def prefixEnd_3095937 : Nat := 4983230072969 + 3 ^ 40 * 3095937 * 2
def baseEnd_3095937 : Nat := 58877916927361439479613

theorem tailTrace_3095937 : CollatzResearch.WordTrace tailWord_3095937 prefixEnd_3095937 58877916927361439479613 := by
  unfold tailWord_3095937
  simp only [CollatzResearch.WordTrace]
  refine ⟨112918098984956467789254065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75278732656637645192836043 112918098984956467789254065)
  ·
    refine ⟨84688574238717350841940549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112918098984956467789254065 84688574238717350841940549)
    ·
      refine ⟨15879107669759503282863853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 84688574238717350841940549 15879107669759503282863853)
      ·
        refine ⟨5954665376159813731073945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15879107669759503282863853 5954665376159813731073945)
        ·
          refine ⟨4465999032119860298305459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5954665376159813731073945 4465999032119860298305459)
          ·
            refine ⟨6698998548179790447458189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4465999032119860298305459 6698998548179790447458189)
            ·
              refine ⟨2512124455567421417796821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6698998548179790447458189 2512124455567421417796821)
              ·
                refine ⟨58877916927361439479613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2512124455567421417796821 58877916927361439479613)
                ·
                  rfl

theorem cell23_3095937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 3, 7].length) (baseStart_3095937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3095937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3095937 prefixEnd_3095937 := by exact prefixLift 3095937
  have htrace : WordTrace (prefixWord ++ tailWord_3095937) baseStart_3095937 baseEnd_3095937 := by
    simpa [prefixWord, tailWord_3095937, baseEnd_3095937] using wordTrace_append hprefix tailTrace_3095937
  have hstable : (prefixWord ++ tailWord_3095937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3095937).length < 2 ^ (prefixWord ++ tailWord_3095937).sum := by decide
  have hdescent : baseEnd_3095937 < baseStart_3095937 := by decide
  rcases family_descends (prefixWord ++ tailWord_3095937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3095953 : List Nat := [1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 4]
def baseStart_3095953 : Nat := 118140960795 + 3095953 * 2 ^ 59
def prefixEnd_3095953 : Nat := 4983230072969 + 3 ^ 40 * 3095953 * 2
def baseEnd_3095953 : Nat := 1589711972729230803349477

theorem tailTrace_3095953 : CollatzResearch.WordTrace tailWord_3095953 prefixEnd_3095953 1589711972729230803349477 := by
  unfold tailWord_3095953
  simp only [CollatzResearch.WordTrace]
  refine ⟨112918682552898502521836513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75279121701932335014557675 112918682552898502521836513)
  ·
    refine ⟨84689011914673876891377385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112918682552898502521836513 84689011914673876891377385)
    ·
      refine ⟨63516758936005407668533039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84689011914673876891377385 63516758936005407668533039)
      ·
        refine ⟨95275138404008111502799559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63516758936005407668533039 95275138404008111502799559)
        ·
          refine ⟨142912707606012167254199339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95275138404008111502799559 142912707606012167254199339)
          ·
            refine ⟨214369061409018250881299009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142912707606012167254199339 214369061409018250881299009)
            ·
              refine ⟨160776796056763688160974257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 214369061409018250881299009 160776796056763688160974257)
              ·
                refine ⟨120582597042572766120730693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 160776796056763688160974257 120582597042572766120730693)
                ·
                  refine ⟨22609236945482393647637005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 120582597042572766120730693 22609236945482393647637005)
                  ·
                    refine ⟨8478463854555897617863877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22609236945482393647637005 8478463854555897617863877)
                    ·
                      refine ⟨1589711972729230803349477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8478463854555897617863877 1589711972729230803349477)
                      ·
                        rfl

theorem cell23_3095953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 4].length) (baseStart_3095953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3095953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3095953 prefixEnd_3095953 := by exact prefixLift 3095953
  have htrace : WordTrace (prefixWord ++ tailWord_3095953) baseStart_3095953 baseEnd_3095953 := by
    simpa [prefixWord, tailWord_3095953, baseEnd_3095953] using wordTrace_append hprefix tailTrace_3095953
  have hstable : (prefixWord ++ tailWord_3095953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3095953).length < 2 ^ (prefixWord ++ tailWord_3095953).sum := by decide
  have hdescent : baseEnd_3095953 < baseStart_3095953 := by decide
  rcases family_descends (prefixWord ++ tailWord_3095953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3095973 : List Nat := [1, 3, 1, 2, 1, 1, 2, 1, 3, 3, 5]
def baseStart_3095973 : Nat := 118140960795 + 3095973 * 2 ^ 59
def prefixEnd_3095973 : Nat := 4983230072969 + 3 ^ 40 * 3095973 * 2
def baseEnd_3095973 : Nat := 1589722242342320725099385

theorem tailTrace_3095973 : CollatzResearch.WordTrace tailWord_3095973 prefixEnd_3095973 1589722242342320725099385 := by
  unfold tailWord_3095973
  simp only [CollatzResearch.WordTrace]
  refine ⟨112919412012826045937564573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75279608008550697291709715 112919412012826045937564573)
  ·
    refine ⟨42344779504809767226586715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112919412012826045937564573 42344779504809767226586715)
    ·
      refine ⟨63517169257214650839880073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42344779504809767226586715 63517169257214650839880073)
      ·
        refine ⟨47637876942910988129910055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63517169257214650839880073 47637876942910988129910055)
        ·
          refine ⟨71456815414366482194865083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47637876942910988129910055 71456815414366482194865083)
          ·
            refine ⟨107185223121549723292297625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71456815414366482194865083 107185223121549723292297625)
            ·
              refine ⟨80388917341162292469223219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107185223121549723292297625 80388917341162292469223219)
              ·
                refine ⟨120583376011743438703834829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80388917341162292469223219 120583376011743438703834829)
                ·
                  refine ⟨45218766004403789513938061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 120583376011743438703834829 45218766004403789513938061)
                  ·
                    refine ⟨16957037251651421067726773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45218766004403789513938061 16957037251651421067726773)
                    ·
                      refine ⟨1589722242342320725099385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16957037251651421067726773 1589722242342320725099385)
                      ·
                        rfl

theorem cell23_3095973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 1, 3, 3, 5].length) (baseStart_3095973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3095973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3095973 prefixEnd_3095973 := by exact prefixLift 3095973
  have htrace : WordTrace (prefixWord ++ tailWord_3095973) baseStart_3095973 baseEnd_3095973 := by
    simpa [prefixWord, tailWord_3095973, baseEnd_3095973] using wordTrace_append hprefix tailTrace_3095973
  have hstable : (prefixWord ++ tailWord_3095973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3095973).length < 2 ^ (prefixWord ++ tailWord_3095973).sum := by decide
  have hdescent : baseEnd_3095973 < baseStart_3095973 := by decide
  rcases family_descends (prefixWord ++ tailWord_3095973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3096040 : List Nat := [2, 1, 4, 1, 1, 2, 1, 2, 4, 5]
def baseStart_3096040 : Nat := 118140960795 + 3096040 * 2 ^ 59
def prefixEnd_3096040 : Nat := 4983230072969 + 3 ^ 40 * 3096040 * 2
def baseEnd_3096040 : Nat := 529918881848723987653859

theorem tailTrace_3096040 : CollatzResearch.WordTrace tailWord_3096040 prefixEnd_3096040 529918881848723987653859 := by
  unfold tailWord_3096040
  simp only [CollatzResearch.WordTrace]
  refine ⟨56460927851791658190126787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75281237135722210920169049 56460927851791658190126787)
  ·
    refine ⟨84691391777687487285190181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56460927851791658190126787 84691391777687487285190181)
    ·
      refine ⟨15879635958316403865973159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 84691391777687487285190181 15879635958316403865973159)
      ·
        refine ⟨23819453937474605798959739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15879635958316403865973159 23819453937474605798959739)
        ·
          refine ⟨35729180906211908698439609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23819453937474605798959739 35729180906211908698439609)
          ·
            refine ⟨26796885679658931523829707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35729180906211908698439609 26796885679658931523829707)
            ·
              refine ⟨40195328519488397285744561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26796885679658931523829707 40195328519488397285744561)
              ·
                refine ⟨30146496389616297964308421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40195328519488397285744561 30146496389616297964308421)
                ·
                  refine ⟨5652468073053055868307829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30146496389616297964308421 5652468073053055868307829)
                  ·
                    refine ⟨529918881848723987653859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5652468073053055868307829 529918881848723987653859)
                    ·
                      rfl

theorem cell23_3096040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 2, 4, 5].length) (baseStart_3096040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3096040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3096040 prefixEnd_3096040 := by exact prefixLift 3096040
  have htrace : WordTrace (prefixWord ++ tailWord_3096040) baseStart_3096040 baseEnd_3096040 := by
    simpa [prefixWord, tailWord_3096040, baseEnd_3096040] using wordTrace_append hprefix tailTrace_3096040
  have hstable : (prefixWord ++ tailWord_3096040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3096040).length < 2 ^ (prefixWord ++ tailWord_3096040).sum := by decide
  have hdescent : baseEnd_3096040 < baseStart_3096040 := by decide
  rcases family_descends (prefixWord ++ tailWord_3096040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3096060 : List Nat := [2, 2, 2, 1, 2, 1, 2, 3, 1, 3, 4]
def baseStart_3096060 : Nat := 118140960795 + 3096060 * 2 ^ 59
def prefixEnd_3096060 : Nat := 4983230072969 + 3 ^ 40 * 3096060 * 2
def baseEnd_3096060 : Nat := 1589766915159261884711485

theorem tailTrace_3096060 : CollatzResearch.WordTrace tailWord_3096060 prefixEnd_3096060 1589766915159261884711485 := by
  unfold tailWord_3096060
  simp only [CollatzResearch.WordTrace]
  refine ⟨56461292581755429897990817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75281723442340573197321089 56461292581755429897990817)
  ·
    refine ⟨42345969436316572423493113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56461292581755429897990817 42345969436316572423493113)
    ·
      refine ⟨31759477077237429317619835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42345969436316572423493113 31759477077237429317619835)
      ·
        refine ⟨47639215615856143976429753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31759477077237429317619835 47639215615856143976429753)
        ·
          refine ⟨35729411711892107982322315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47639215615856143976429753 35729411711892107982322315)
          ·
            refine ⟨53594117567838161973483473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35729411711892107982322315 53594117567838161973483473)
            ·
              refine ⟨40195588175878621480112605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53594117567838161973483473 40195588175878621480112605)
              ·
                refine ⟨15073345565954483055042227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40195588175878621480112605 15073345565954483055042227)
                ·
                  refine ⟨22610018348931724582563341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15073345565954483055042227 22610018348931724582563341)
                  ·
                    refine ⟨8478756880849396718461253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22610018348931724582563341 8478756880849396718461253)
                    ·
                      refine ⟨1589766915159261884711485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8478756880849396718461253 1589766915159261884711485)
                      ·
                        rfl

theorem cell23_3096060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 3, 1, 3, 4].length) (baseStart_3096060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3096060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3096060 prefixEnd_3096060 := by exact prefixLift 3096060
  have htrace : WordTrace (prefixWord ++ tailWord_3096060) baseStart_3096060 baseEnd_3096060 := by
    simpa [prefixWord, tailWord_3096060, baseEnd_3096060] using wordTrace_append hprefix tailTrace_3096060
  have hstable : (prefixWord ++ tailWord_3096060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3096060).length < 2 ^ (prefixWord ++ tailWord_3096060).sum := by decide
  have hdescent : baseEnd_3096060 < baseStart_3096060 := by decide
  rcases family_descends (prefixWord ++ tailWord_3096060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3096078 : List Nat := [4, 1, 1, 2, 5, 1, 2, 2, 5]
def baseStart_3096078 : Nat := 118140960795 + 3096078 * 2 ^ 59
def prefixEnd_3096078 : Nat := 4983230072969 + 3 ^ 40 * 3096078 * 2
def baseEnd_3096078 : Nat := 176641795312338090476267

theorem tailTrace_3096078 : CollatzResearch.WordTrace tailWord_3096078 prefixEnd_3096078 176641795312338090476267 := by
  unfold tailWord_3096078
  simp only [CollatzResearch.WordTrace]
  refine ⟨14115405209680706108767111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75282161118297099246757925 14115405209680706108767111)
  ·
    refine ⟨21173107814521059163150667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14115405209680706108767111 21173107814521059163150667)
    ·
      refine ⟨31759661721781588744726001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21173107814521059163150667 31759661721781588744726001)
      ·
        refine ⟨23819746291336191558544501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31759661721781588744726001 23819746291336191558544501)
        ·
          refine ⟨2233101214812767958613547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23819746291336191558544501 2233101214812767958613547)
          ·
            refine ⟨3349651822219151937920321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2233101214812767958613547 3349651822219151937920321)
            ·
              refine ⟨2512238866664363953440241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3349651822219151937920321 2512238866664363953440241)
              ·
                refine ⟨1884179149998272965080181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2512238866664363953440241 1884179149998272965080181)
                ·
                  refine ⟨176641795312338090476267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1884179149998272965080181 176641795312338090476267)
                  ·
                    rfl

theorem cell23_3096078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 2, 2, 5].length) (baseStart_3096078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3096078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3096078 prefixEnd_3096078 := by exact prefixLift 3096078
  have htrace : WordTrace (prefixWord ++ tailWord_3096078) baseStart_3096078 baseEnd_3096078 := by
    simpa [prefixWord, tailWord_3096078, baseEnd_3096078] using wordTrace_append hprefix tailTrace_3096078
  have hstable : (prefixWord ++ tailWord_3096078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3096078).length < 2 ^ (prefixWord ++ tailWord_3096078).sum := by decide
  have hdescent : baseEnd_3096078 < baseStart_3096078 := by decide
  rcases family_descends (prefixWord ++ tailWord_3096078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3096090 : List Nat := [3, 1, 1, 3, 1, 1, 1, 2, 2, 4, 4]
def baseStart_3096090 : Nat := 118140960795 + 3096090 * 2 ^ 59
def prefixEnd_3096090 : Nat := 4983230072969 + 3 ^ 40 * 3096090 * 2
def baseEnd_3096090 : Nat := 1589782319578896767336347

theorem tailTrace_3096090 : CollatzResearch.WordTrace tailWord_3096090 prefixEnd_3096090 1589782319578896767336347 := by
  unfold tailWord_3096090
  simp only [CollatzResearch.WordTrace]
  refine ⟨28230919838350543729893431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75282452902268116613049149 28230919838350543729893431)
  ·
    refine ⟨42346379757525815594840147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28230919838350543729893431 42346379757525815594840147)
    ·
      refine ⟨63519569636288723392260221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42346379757525815594840147 63519569636288723392260221)
      ·
        refine ⟨23819838613608271272097583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63519569636288723392260221 23819838613608271272097583)
        ·
          refine ⟨35729757920412406908146375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23819838613608271272097583 35729757920412406908146375)
          ·
            refine ⟨53594636880618610362219563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35729757920412406908146375 53594636880618610362219563)
            ·
              refine ⟨80391955320927915543329345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53594636880618610362219563 80391955320927915543329345)
              ·
                refine ⟨60293966490695936657497009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80391955320927915543329345 60293966490695936657497009)
                ·
                  refine ⟨45220474868021952493122757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60293966490695936657497009 45220474868021952493122757)
                  ·
                    refine ⟨8478839037754116092460517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45220474868021952493122757 8478839037754116092460517)
                    ·
                      refine ⟨1589782319578896767336347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8478839037754116092460517 1589782319578896767336347)
                      ·
                        rfl

theorem cell23_3096090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 2, 2, 4, 4].length) (baseStart_3096090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3096090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3096090 prefixEnd_3096090 := by exact prefixLift 3096090
  have htrace : WordTrace (prefixWord ++ tailWord_3096090) baseStart_3096090 baseEnd_3096090 := by
    simpa [prefixWord, tailWord_3096090, baseEnd_3096090] using wordTrace_append hprefix tailTrace_3096090
  have hstable : (prefixWord ++ tailWord_3096090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3096090).length < 2 ^ (prefixWord ++ tailWord_3096090).sum := by decide
  have hdescent : baseEnd_3096090 < baseStart_3096090 := by decide
  rcases family_descends (prefixWord ++ tailWord_3096090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3096121 : List Nat := [1, 2, 1, 5, 1, 3, 2, 3, 1, 4]
def baseStart_3096121 : Nat := 118140960795 + 3096121 * 2 ^ 59
def prefixEnd_3096121 : Nat := 4983230072969 + 3 ^ 40 * 3096121 * 2
def baseEnd_3096121 : Nat := 529932745826395382016235

theorem tailTrace_3096121 : CollatzResearch.WordTrace tailWord_3096121 prefixEnd_3096121 529932745826395382016235 := by
  unfold tailWord_3096121
  simp only [CollatzResearch.WordTrace]
  refine ⟨112924810016289867213952217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75283206677526578142634811 112924810016289867213952217)
  ·
    refine ⟨84693607512217400410464163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112924810016289867213952217 84693607512217400410464163)
    ·
      refine ⟨127040411268326100615696245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84693607512217400410464163 127040411268326100615696245)
      ·
        refine ⟨11910038556405571932721523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 127040411268326100615696245 11910038556405571932721523)
        ·
          refine ⟨17865057834608357899082285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11910038556405571932721523 17865057834608357899082285)
          ·
            refine ⟨6699396687978134212155857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17865057834608357899082285 6699396687978134212155857)
            ·
              refine ⟨5024547515983600659116893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6699396687978134212155857 5024547515983600659116893)
              ·
                refine ⟨1884205318493850247168835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5024547515983600659116893 1884205318493850247168835)
                ·
                  refine ⟨2826307977740775370753253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1884205318493850247168835 2826307977740775370753253)
                  ·
                    refine ⟨529932745826395382016235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2826307977740775370753253 529932745826395382016235)
                    ·
                      rfl

theorem cell23_3096121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 2, 3, 1, 4].length) (baseStart_3096121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3096121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3096121 prefixEnd_3096121 := by exact prefixLift 3096121
  have htrace : WordTrace (prefixWord ++ tailWord_3096121) baseStart_3096121 baseEnd_3096121 := by
    simpa [prefixWord, tailWord_3096121, baseEnd_3096121] using wordTrace_append hprefix tailTrace_3096121
  have hstable : (prefixWord ++ tailWord_3096121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3096121).length < 2 ^ (prefixWord ++ tailWord_3096121).sum := by decide
  have hdescent : baseEnd_3096121 < baseStart_3096121 := by decide
  rcases family_descends (prefixWord ++ tailWord_3096121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3096144 : List Nat := [2, 1, 1, 1, 1, 3, 6, 1, 3, 1, 3]
def baseStart_3096144 : Nat := 118140960795 + 3096144 * 2 ^ 59
def prefixEnd_3096144 : Nat := 4983230072969 + 3 ^ 40 * 3096144 * 2
def baseEnd_3096144 : Nat := 1589810047534239556061099

theorem tailTrace_3096144 : CollatzResearch.WordTrace tailWord_3096144 prefixEnd_3096144 1589810047534239556061099 := by
  unfold tailWord_3096144
  simp only [CollatzResearch.WordTrace]
  refine ⟨56462824447603271071019743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75283765930137694761359657 56462824447603271071019743)
  ·
    refine ⟨84694236671404906606529615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56462824447603271071019743 84694236671404906606529615)
    ·
      refine ⟨127041355007107359909794423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84694236671404906606529615 127041355007107359909794423)
      ·
        refine ⟨190562032510661039864691635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127041355007107359909794423 190562032510661039864691635)
        ·
          refine ⟨285843048765991559797037453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190562032510661039864691635 285843048765991559797037453)
          ·
            refine ⟨107191143287246834923889045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 285843048765991559797037453 107191143287246834923889045)
            ·
              refine ⟨5024584841589695387057299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 107191143287246834923889045 5024584841589695387057299)
              ·
                refine ⟨7536877262384543080585949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5024584841589695387057299 7536877262384543080585949)
                ·
                  refine ⟨2826328973394203655219731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7536877262384543080585949 2826328973394203655219731)
                  ·
                    refine ⟨4239493460091305482829597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2826328973394203655219731 4239493460091305482829597)
                    ·
                      refine ⟨1589810047534239556061099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4239493460091305482829597 1589810047534239556061099)
                      ·
                        rfl

theorem cell23_3096144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 6, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 6, 1, 3, 1, 3].length) (baseStart_3096144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3096144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3096144 prefixEnd_3096144 := by exact prefixLift 3096144
  have htrace : WordTrace (prefixWord ++ tailWord_3096144) baseStart_3096144 baseEnd_3096144 := by
    simpa [prefixWord, tailWord_3096144, baseEnd_3096144] using wordTrace_append hprefix tailTrace_3096144
  have hstable : (prefixWord ++ tailWord_3096144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3096144).length < 2 ^ (prefixWord ++ tailWord_3096144).sum := by decide
  have hdescent : baseEnd_3096144 < baseStart_3096144 := by decide
  rcases family_descends (prefixWord ++ tailWord_3096144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3096164 : List Nat := [2, 3, 1, 1, 2, 4, 2, 2, 1, 5]
def baseStart_3096164 : Nat := 118140960795 + 3096164 * 2 ^ 59
def prefixEnd_3096164 : Nat := 4983230072969 + 3 ^ 40 * 3096164 * 2
def baseEnd_3096164 : Nat := 529940105715776492603669

theorem tailTrace_3096164 : CollatzResearch.WordTrace tailWord_3096164 prefixEnd_3096164 529940105715776492603669 := by
  unfold tailWord_3096164
  simp only [CollatzResearch.WordTrace]
  refine ⟨56463189177567042778883773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75284252236756057038511697 56463189177567042778883773)
  ·
    refine ⟨21173695941587641042081415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56463189177567042778883773 21173695941587641042081415)
    ·
      refine ⟨31760543912381461563122123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21173695941587641042081415 31760543912381461563122123)
      ·
        refine ⟨47640815868572192344683185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31760543912381461563122123 47640815868572192344683185)
        ·
          refine ⟨35730611901429144258512389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47640815868572192344683185 35730611901429144258512389)
          ·
            refine ⟨6699489731517964548471073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35730611901429144258512389 6699489731517964548471073)
            ·
              refine ⟨5024617298638473411353305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6699489731517964548471073 5024617298638473411353305)
              ·
                refine ⟨3768462973978855058514979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5024617298638473411353305 3768462973978855058514979)
                ·
                  refine ⟨5652694460968282587772469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3768462973978855058514979 5652694460968282587772469)
                  ·
                    refine ⟨529940105715776492603669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5652694460968282587772469 529940105715776492603669)
                    ·
                      rfl

theorem cell23_3096164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 2, 2, 1, 5].length) (baseStart_3096164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3096164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3096164 prefixEnd_3096164 := by exact prefixLift 3096164
  have htrace : WordTrace (prefixWord ++ tailWord_3096164) baseStart_3096164 baseEnd_3096164 := by
    simpa [prefixWord, tailWord_3096164, baseEnd_3096164] using wordTrace_append hprefix tailTrace_3096164
  have hstable : (prefixWord ++ tailWord_3096164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3096164).length < 2 ^ (prefixWord ++ tailWord_3096164).sum := by decide
  have hdescent : baseEnd_3096164 < baseStart_3096164 := by decide
  rcases family_descends (prefixWord ++ tailWord_3096164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3096167 : List Nat := [1, 1, 5, 1, 1, 1, 2, 3, 3, 1, 4]
def baseStart_3096167 : Nat := 118140960795 + 3096167 * 2 ^ 59
def prefixEnd_3096167 : Nat := 4983230072969 + 3 ^ 40 * 3096167 * 2
def baseEnd_3096167 : Nat := 1589821857589292966073493

theorem tailTrace_3096167 : CollatzResearch.WordTrace tailWord_3096167 prefixEnd_3096167 1589821857589292966073493 := by
  unfold tailWord_3096167
  simp only [CollatzResearch.WordTrace]
  refine ⟨112926487774123217070126755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75284325182748811380084503 112926487774123217070126755)
  ·
    refine ⟨169389731661184825605190133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112926487774123217070126755 169389731661184825605190133)
    ·
      refine ⟨15880287343236077400486575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 169389731661184825605190133 15880287343236077400486575)
      ·
        refine ⟨23820431014854116100729863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15880287343236077400486575 23820431014854116100729863)
        ·
          refine ⟨35730646522281174151094795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23820431014854116100729863 35730646522281174151094795)
          ·
            refine ⟨53595969783421761226642193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35730646522281174151094795 53595969783421761226642193)
            ·
              refine ⟨40196977337566320919981645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53595969783421761226642193 40196977337566320919981645)
              ·
                refine ⟨15073866501587370344993117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40196977337566320919981645 15073866501587370344993117)
                ·
                  refine ⟨5652699938095263879372419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15073866501587370344993117 5652699938095263879372419)
                  ·
                    refine ⟨8479049907142895819058629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5652699938095263879372419 8479049907142895819058629)
                    ·
                      refine ⟨1589821857589292966073493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8479049907142895819058629 1589821857589292966073493)
                      ·
                        rfl

theorem cell23_3096167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 3, 3, 1, 4].length) (baseStart_3096167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3096167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3096167 prefixEnd_3096167 := by exact prefixLift 3096167
  have htrace : WordTrace (prefixWord ++ tailWord_3096167) baseStart_3096167 baseEnd_3096167 := by
    simpa [prefixWord, tailWord_3096167, baseEnd_3096167] using wordTrace_append hprefix tailTrace_3096167
  have hstable : (prefixWord ++ tailWord_3096167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3096167).length < 2 ^ (prefixWord ++ tailWord_3096167).sum := by decide
  have hdescent : baseEnd_3096167 < baseStart_3096167 := by decide
  rcases family_descends (prefixWord ++ tailWord_3096167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3096178 : List Nat := [3, 2, 1, 2, 3, 1, 3, 3, 1, 1, 3]
def baseStart_3096178 : Nat := 118140960795 + 3096178 * 2 ^ 59
def prefixEnd_3096178 : Nat := 4983230072969 + 3 ^ 40 * 3096178 * 2
def baseEnd_3096178 : Nat := 1589827505876492423035943

theorem tailTrace_3096178 : CollatzResearch.WordTrace tailWord_3096178 prefixEnd_3096178 1589827505876492423035943 := by
  unfold tailWord_3096178
  simp only [CollatzResearch.WordTrace]
  refine ⟨28231722244270841487194297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75284592651388910632518125 28231722244270841487194297)
  ·
    refine ⟨21173791683203131115395723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28231722244270841487194297 21173791683203131115395723)
    ·
      refine ⟨31760687524804696673093585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21173791683203131115395723 31760687524804696673093585)
      ·
        refine ⟨23820515643603522504820189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31760687524804696673093585 23820515643603522504820189)
        ·
          refine ⟨8932693366351320939307571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23820515643603522504820189 8932693366351320939307571)
          ·
            refine ⟨13399040049526981408961357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8932693366351320939307571 13399040049526981408961357)
            ·
              refine ⟨5024640018572618028360509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13399040049526981408961357 5024640018572618028360509)
              ·
                refine ⟨1884240006964731760635191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5024640018572618028360509 1884240006964731760635191)
                ·
                  refine ⟨2826360010447097640952787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1884240006964731760635191 2826360010447097640952787)
                  ·
                    refine ⟨4239540015670646461429181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2826360010447097640952787 4239540015670646461429181)
                    ·
                      refine ⟨1589827505876492423035943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4239540015670646461429181 1589827505876492423035943)
                      ·
                        rfl

theorem cell23_3096178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 3, 3, 1, 1, 3].length) (baseStart_3096178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3096178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3096178 prefixEnd_3096178 := by exact prefixLift 3096178
  have htrace : WordTrace (prefixWord ++ tailWord_3096178) baseStart_3096178 baseEnd_3096178 := by
    simpa [prefixWord, tailWord_3096178, baseEnd_3096178] using wordTrace_append hprefix tailTrace_3096178
  have hstable : (prefixWord ++ tailWord_3096178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3096178).length < 2 ^ (prefixWord ++ tailWord_3096178).sum := by decide
  have hdescent : baseEnd_3096178 < baseStart_3096178 := by decide
  rcases family_descends (prefixWord ++ tailWord_3096178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3096187 : List Nat := [1, 1, 1, 1, 1, 4, 6, 1, 1, 1, 5]
def baseStart_3096187 : Nat := 118140960795 + 3096187 * 2 ^ 59
def prefixEnd_3096187 : Nat := 4983230072969 + 3 ^ 40 * 3096187 * 2
def baseEnd_3096187 : Nat := 1589832127202382887823401

theorem tailTrace_3096187 : CollatzResearch.WordTrace tailWord_3096187 prefixEnd_3096187 1589832127202382887823401 := by
  unfold tailWord_3096187
  simp only [CollatzResearch.WordTrace]
  refine ⟨112927217234050760485854815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75284811489367173657236543 112927217234050760485854815)
  ·
    refine ⟨169390825851076140728782223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112927217234050760485854815 169390825851076140728782223)
    ·
      refine ⟨254086238776614211093173335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169390825851076140728782223 254086238776614211093173335)
      ·
        refine ⟨381129358164921316639760003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254086238776614211093173335 381129358164921316639760003)
        ·
          refine ⟨571694037247381974959640005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 381129358164921316639760003 571694037247381974959640005)
          ·
            refine ⟨107192631983884120304932501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 571694037247381974959640005 107192631983884120304932501)
            ·
              refine ⟨5024654624244568139293711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 107192631983884120304932501 5024654624244568139293711)
              ·
                refine ⟨7536981936366852208940567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5024654624244568139293711 7536981936366852208940567)
                ·
                  refine ⟨11305472904550278313410851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7536981936366852208940567 11305472904550278313410851)
                  ·
                    refine ⟨16958209356825417470116277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11305472904550278313410851 16958209356825417470116277)
                    ·
                      refine ⟨1589832127202382887823401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16958209356825417470116277 1589832127202382887823401)
                      ·
                        rfl

theorem cell23_3096187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 6, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 6, 1, 1, 1, 5].length) (baseStart_3096187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3096187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3096187 prefixEnd_3096187 := by exact prefixLift 3096187
  have htrace : WordTrace (prefixWord ++ tailWord_3096187) baseStart_3096187 baseEnd_3096187 := by
    simpa [prefixWord, tailWord_3096187, baseEnd_3096187] using wordTrace_append hprefix tailTrace_3096187
  have hstable : (prefixWord ++ tailWord_3096187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3096187).length < 2 ^ (prefixWord ++ tailWord_3096187).sum := by decide
  have hdescent : baseEnd_3096187 < baseStart_3096187 := by decide
  rcases family_descends (prefixWord ++ tailWord_3096187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3096201 : List Nat := [1, 2, 1, 1, 4, 1, 5, 1, 3, 2, 2]
def baseStart_3096201 : Nat := 118140960795 + 3096201 * 2 ^ 59
def prefixEnd_3096201 : Nat := 4983230072969 + 3 ^ 40 * 3096201 * 2
def baseEnd_3096201 : Nat := 1589839315931545833048337

theorem tailTrace_3096201 : CollatzResearch.WordTrace tailWord_3096201 prefixEnd_3096201 1589839315931545833048337 := by
  unfold tailWord_3096201
  simp only [CollatzResearch.WordTrace]
  refine ⟨112927727856000040876864457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75285151904000027251242971 112927727856000040876864457)
  ·
    refine ⟨84695795892000030657648343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112927727856000040876864457 84695795892000030657648343)
    ·
      refine ⟨127043693838000045986472515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84695795892000030657648343 127043693838000045986472515)
      ·
        refine ⟨190565540757000068979708773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127043693838000045986472515 190565540757000068979708773)
        ·
          refine ⟨35731038891937512933695395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 190565540757000068979708773 35731038891937512933695395)
          ·
            refine ⟨53596558337906269400543093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35731038891937512933695395 53596558337906269400543093)
            ·
              refine ⟨5024677344178712756300915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 53596558337906269400543093 5024677344178712756300915)
              ·
                refine ⟨7537016016268069134451373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5024677344178712756300915 7537016016268069134451373)
                ·
                  refine ⟨2826381006100525925419265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7537016016268069134451373 2826381006100525925419265)
                  ·
                    refine ⟨2119785754575394444064449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2826381006100525925419265 2119785754575394444064449)
                    ·
                      refine ⟨1589839315931545833048337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2119785754575394444064449 1589839315931545833048337)
                      ·
                        rfl

theorem cell23_3096201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 5, 1, 3, 2, 2].length) (baseStart_3096201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3096201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3096201 prefixEnd_3096201 := by exact prefixLift 3096201
  have htrace : WordTrace (prefixWord ++ tailWord_3096201) baseStart_3096201 baseEnd_3096201 := by
    simpa [prefixWord, tailWord_3096201, baseEnd_3096201] using wordTrace_append hprefix tailTrace_3096201
  have hstable : (prefixWord ++ tailWord_3096201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3096201).length < 2 ^ (prefixWord ++ tailWord_3096201).sum := by decide
  have hdescent : baseEnd_3096201 < baseStart_3096201 := by decide
  rcases family_descends (prefixWord ++ tailWord_3096201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3096238 : List Nat := [4, 1, 4, 1, 2, 2, 1, 1, 1, 1, 5]
def baseStart_3096238 : Nat := 118140960795 + 3096238 * 2 ^ 59
def prefixEnd_3096238 : Nat := 4983230072969 + 3 ^ 40 * 3096238 * 2
def baseEnd_3096238 : Nat := 1589858314715762188285667

theorem tailTrace_3096238 : CollatzResearch.WordTrace tailWord_3096238 prefixEnd_3096238 1589858314715762188285667 := by
  unfold tailWord_3096238
  simp only [CollatzResearch.WordTrace]
  refine ⟨14116134669608249524495171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75286051571243997463974245 14116134669608249524495171)
  ·
    refine ⟨21174202004412374286742757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14116134669608249524495171 21174202004412374286742757)
    ·
      refine ⟨3970162875827320178764267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21174202004412374286742757 3970162875827320178764267)
      ·
        refine ⟨5955244313740980268146401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3970162875827320178764267 5955244313740980268146401)
        ·
          refine ⟨4466433235305735201109801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5955244313740980268146401 4466433235305735201109801)
          ·
            refine ⟨3349824926479301400832351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4466433235305735201109801 3349824926479301400832351)
            ·
              refine ⟨5024737389718952101248527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3349824926479301400832351 5024737389718952101248527)
              ·
                refine ⟨7537106084578428151872791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5024737389718952101248527 7537106084578428151872791)
                ·
                  refine ⟨11305659126867642227809187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7537106084578428151872791 11305659126867642227809187)
                  ·
                    refine ⟨16958488690301463341713781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11305659126867642227809187 16958488690301463341713781)
                    ·
                      refine ⟨1589858314715762188285667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16958488690301463341713781 1589858314715762188285667)
                      ·
                        rfl

theorem cell23_3096238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 1, 1, 1, 1, 5].length) (baseStart_3096238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3096238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3096238 prefixEnd_3096238 := by exact prefixLift 3096238
  have htrace : WordTrace (prefixWord ++ tailWord_3096238) baseStart_3096238 baseEnd_3096238 := by
    simpa [prefixWord, tailWord_3096238, baseEnd_3096238] using wordTrace_append hprefix tailTrace_3096238
  have hstable : (prefixWord ++ tailWord_3096238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3096238).length < 2 ^ (prefixWord ++ tailWord_3096238).sum := by decide
  have hdescent : baseEnd_3096238 < baseStart_3096238 := by decide
  rcases family_descends (prefixWord ++ tailWord_3096238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3096252 : List Nat := [2, 2, 2, 3, 1, 4, 2, 2, 1, 2, 2]
def baseStart_3096252 : Nat := 118140960795 + 3096252 * 2 ^ 59
def prefixEnd_3096252 : Nat := 4983230072969 + 3 ^ 40 * 3096252 * 2
def baseEnd_3096252 : Nat := 1589865503444925133510603

theorem tailTrace_3096252 : CollatzResearch.WordTrace tailWord_3096252 prefixEnd_3096252 1589865503444925133510603 := by
  unfold tailWord_3096252
  simp only [CollatzResearch.WordTrace]
  refine ⟨56464793989407638293485505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75286391985876851057980673 56464793989407638293485505)
  ·
    refine ⟨42348595492055728720114129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56464793989407638293485505 42348595492055728720114129)
    ·
      refine ⟨31761446619041796540085597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42348595492055728720114129 31761446619041796540085597)
      ·
        refine ⟨11910542482140673702532099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31761446619041796540085597 11910542482140673702532099)
        ·
          refine ⟨17865813723211010553798149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11910542482140673702532099 17865813723211010553798149)
          ·
            refine ⟨3349840073102064478837153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17865813723211010553798149 3349840073102064478837153)
            ·
              refine ⟨2512380054826548359127865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3349840073102064478837153 2512380054826548359127865)
              ·
                refine ⟨1884285041119911269345899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2512380054826548359127865 1884285041119911269345899)
                ·
                  refine ⟨2826427561679866904018849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1884285041119911269345899 2826427561679866904018849)
                  ·
                    refine ⟨2119820671259900178014137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2826427561679866904018849 2119820671259900178014137)
                    ·
                      refine ⟨1589865503444925133510603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2119820671259900178014137 1589865503444925133510603)
                      ·
                        rfl

theorem cell23_3096252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 2, 2, 1, 2, 2].length) (baseStart_3096252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3096252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3096252 prefixEnd_3096252 := by exact prefixLift 3096252
  have htrace : WordTrace (prefixWord ++ tailWord_3096252) baseStart_3096252 baseEnd_3096252 := by
    simpa [prefixWord, tailWord_3096252, baseEnd_3096252] using wordTrace_append hprefix tailTrace_3096252
  have hstable : (prefixWord ++ tailWord_3096252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3096252).length < 2 ^ (prefixWord ++ tailWord_3096252).sum := by decide
  have hdescent : baseEnd_3096252 < baseStart_3096252 := by decide
  rcases family_descends (prefixWord ++ tailWord_3096252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3096287 : List Nat := [1, 1, 2, 3, 2, 2, 1, 2, 1, 4, 4]
def baseStart_3096287 : Nat := 118140960795 + 3096287 * 2 ^ 59
def prefixEnd_3096287 : Nat := 4983230072969 + 3 ^ 40 * 3096287 * 2
def baseEnd_3096287 : Nat := 1589883475267832496572941

theorem tailTrace_3096287 : CollatzResearch.WordTrace tailWord_3096287 prefixEnd_3096287 1589883475267832496572941 := by
  unfold tailWord_3096287
  simp only [CollatzResearch.WordTrace]
  refine ⟨112930864533688477564495115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75287243022458985042996743 112930864533688477564495115)
  ·
    refine ⟨169396296800532716346742673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112930864533688477564495115 169396296800532716346742673)
    ·
      refine ⟨127047222600399537260057005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169396296800532716346742673 127047222600399537260057005)
      ·
        refine ⟨47642708475149826472521377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 127047222600399537260057005 47642708475149826472521377)
        ·
          refine ⟨35732031356362369854391033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47642708475149826472521377 35732031356362369854391033)
          ·
            refine ⟨26799023517271777390793275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35732031356362369854391033 26799023517271777390793275)
            ·
              refine ⟨40198535275907666086189913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26799023517271777390793275 40198535275907666086189913)
              ·
                refine ⟨30148901456930749564642435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40198535275907666086189913 30148901456930749564642435)
                ·
                  refine ⟨45223352185396124346963653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30148901456930749564642435 45223352185396124346963653)
                  ·
                    refine ⟨8479378534761773315055685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45223352185396124346963653 8479378534761773315055685)
                    ·
                      refine ⟨1589883475267832496572941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8479378534761773315055685 1589883475267832496572941)
                      ·
                        rfl

theorem cell23_3096287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 2, 1, 4, 4].length) (baseStart_3096287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3096287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3096287 prefixEnd_3096287 := by exact prefixLift 3096287
  have htrace : WordTrace (prefixWord ++ tailWord_3096287) baseStart_3096287 baseEnd_3096287 := by
    simpa [prefixWord, tailWord_3096287, baseEnd_3096287] using wordTrace_append hprefix tailTrace_3096287
  have hstable : (prefixWord ++ tailWord_3096287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3096287).length < 2 ^ (prefixWord ++ tailWord_3096287).sum := by decide
  have hdescent : baseEnd_3096287 < baseStart_3096287 := by decide
  rcases family_descends (prefixWord ++ tailWord_3096287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3096295 : List Nat := [1, 1, 5, 4, 1, 1, 1, 3, 1, 3, 2]
def baseStart_3096295 : Nat := 118140960795 + 3096295 * 2 ^ 59
def prefixEnd_3096295 : Nat := 4983230072969 + 3 ^ 40 * 3096295 * 2
def baseEnd_3096295 : Nat := 1589887583113068465272905

theorem tailTrace_3096295 : CollatzResearch.WordTrace tailWord_3096295 prefixEnd_3096295 1589887583113068465272905 := by
  unfold tailWord_3096295
  simp only [CollatzResearch.WordTrace]
  refine ⟨112931156317659494930786339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75287437545106329953857559 112931156317659494930786339)
  ·
    refine ⟨169396734476489242396179509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112931156317659494930786339 169396734476489242396179509)
    ·
      refine ⟨15880943857170866474641829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 169396734476489242396179509 15880943857170866474641829)
      ·
        refine ⟨2977676973219537463995343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15880943857170866474641829 2977676973219537463995343)
        ·
          refine ⟨4466515459829306195993015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2977676973219537463995343 4466515459829306195993015)
          ·
            refine ⟨6699773189743959293989523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4466515459829306195993015 6699773189743959293989523)
            ·
              refine ⟨10049659784615938940984285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6699773189743959293989523 10049659784615938940984285)
              ·
                refine ⟨3768622419230977102869107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10049659784615938940984285 3768622419230977102869107)
                ·
                  refine ⟨5652933628846465654303661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3768622419230977102869107 5652933628846465654303661)
                  ·
                    refine ⟨2119850110817424620363873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5652933628846465654303661 2119850110817424620363873)
                    ·
                      refine ⟨1589887583113068465272905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2119850110817424620363873 1589887583113068465272905)
                      ·
                        rfl

theorem cell23_3096295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 3, 1, 3, 2].length) (baseStart_3096295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3096295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3096295 prefixEnd_3096295 := by exact prefixLift 3096295
  have htrace : WordTrace (prefixWord ++ tailWord_3096295) baseStart_3096295 baseEnd_3096295 := by
    simpa [prefixWord, tailWord_3096295, baseEnd_3096295] using wordTrace_append hprefix tailTrace_3096295
  have hstable : (prefixWord ++ tailWord_3096295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3096295).length < 2 ^ (prefixWord ++ tailWord_3096295).sum := by decide
  have hdescent : baseEnd_3096295 < baseStart_3096295 := by decide
  rcases family_descends (prefixWord ++ tailWord_3096295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3096337 : List Nat := [1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 5]
def baseStart_3096337 : Nat := 118140960795 + 3096337 * 2 ^ 59
def prefixEnd_3096337 : Nat := 4983230072969 + 3 ^ 40 * 3096337 * 2
def baseEnd_3096337 : Nat := 1589909149300557300947711

theorem tailTrace_3096337 : CollatzResearch.WordTrace tailWord_3096337 prefixEnd_3096337 1589909149300557300947711 := by
  unfold tailWord_3096337
  simp only [CollatzResearch.WordTrace]
  refine ⟨112932688183507336103815265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75288458789004890735876843 112932688183507336103815265)
  ·
    refine ⟨84699516137630502077861449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112932688183507336103815265 84699516137630502077861449)
    ·
      refine ⟨63524637103222876558396087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84699516137630502077861449 63524637103222876558396087)
      ·
        refine ⟨95286955654834314837594131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63524637103222876558396087 95286955654834314837594131)
        ·
          refine ⟨142930433482251472256391197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95286955654834314837594131 142930433482251472256391197)
          ·
            refine ⟨53598912555844302096146699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 142930433482251472256391197 53598912555844302096146699)
            ·
              refine ⟨80398368833766453144220049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53598912555844302096146699 80398368833766453144220049)
              ·
                refine ⟨60298776625324839858165037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80398368833766453144220049 60298776625324839858165037)
                ·
                  refine ⟨22612041234496814946811889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60298776625324839858165037 22612041234496814946811889)
                  ·
                    refine ⟨16959030925872611210108917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22612041234496814946811889 16959030925872611210108917)
                    ·
                      refine ⟨1589909149300557300947711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16959030925872611210108917 1589909149300557300947711)
                      ·
                        rfl

theorem cell23_3096337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 5].length) (baseStart_3096337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3096337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3096337 prefixEnd_3096337 := by exact prefixLift 3096337
  have htrace : WordTrace (prefixWord ++ tailWord_3096337) baseStart_3096337 baseEnd_3096337 := by
    simpa [prefixWord, tailWord_3096337, baseEnd_3096337] using wordTrace_append hprefix tailTrace_3096337
  have hstable : (prefixWord ++ tailWord_3096337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3096337).length < 2 ^ (prefixWord ++ tailWord_3096337).sum := by decide
  have hdescent : baseEnd_3096337 < baseStart_3096337 := by decide
  rcases family_descends (prefixWord ++ tailWord_3096337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3096354 : List Nat := [3, 3, 1, 1, 2, 1, 2, 2, 1, 2, 5]
def baseStart_3096354 : Nat := 118140960795 + 3096354 * 2 ^ 59
def prefixEnd_3096354 : Nat := 4983230072969 + 3 ^ 40 * 3096354 * 2
def baseEnd_3096354 : Nat := 1589917878471683734435133

theorem tailTrace_3096354 : CollatzResearch.WordTrace tailWord_3096354 prefixEnd_3096354 1589917878471683734435133 := by
  unfold tailWord_3096354
  simp only [CollatzResearch.WordTrace]
  refine ⟨28233327056111437001796029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75288872149630498671456077 28233327056111437001796029)
  ·
    refine ⟨10587497646041788875673511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28233327056111437001796029 10587497646041788875673511)
    ·
      refine ⟨15881246469062683313510267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10587497646041788875673511 15881246469062683313510267)
      ·
        refine ⟨23821869703594024970265401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15881246469062683313510267 23821869703594024970265401)
        ·
          refine ⟨17866402277695518727699051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23821869703594024970265401 17866402277695518727699051)
          ·
            refine ⟨26799603416543278091548577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17866402277695518727699051 26799603416543278091548577)
            ·
              refine ⟨20099702562407458568661433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26799603416543278091548577 20099702562407458568661433)
              ·
                refine ⟨15074776921805593926496075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20099702562407458568661433 15074776921805593926496075)
                ·
                  refine ⟨22612165382708390889744113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15074776921805593926496075 22612165382708390889744113)
                  ·
                    refine ⟨16959124037031293167308085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22612165382708390889744113 16959124037031293167308085)
                    ·
                      refine ⟨1589917878471683734435133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16959124037031293167308085 1589917878471683734435133)
                      ·
                        rfl

theorem cell23_3096354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 2, 1, 2, 5].length) (baseStart_3096354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3096354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3096354 prefixEnd_3096354 := by exact prefixLift 3096354
  have htrace : WordTrace (prefixWord ++ tailWord_3096354) baseStart_3096354 baseEnd_3096354 := by
    simpa [prefixWord, tailWord_3096354, baseEnd_3096354] using wordTrace_append hprefix tailTrace_3096354
  have hstable : (prefixWord ++ tailWord_3096354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3096354).length < 2 ^ (prefixWord ++ tailWord_3096354).sum := by decide
  have hdescent : baseEnd_3096354 < baseStart_3096354 := by decide
  rcases family_descends (prefixWord ++ tailWord_3096354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3096364 : List Nat := [2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 4]
def baseStart_3096364 : Nat := 118140960795 + 3096364 * 2 ^ 59
def prefixEnd_3096364 : Nat := 4983230072969 + 3 ^ 40 * 3096364 * 2
def baseEnd_3096364 : Nat := 1589923013278228695310087

theorem tailTrace_3096364 : CollatzResearch.WordTrace tailWord_3096364 prefixEnd_3096364 1589923013278228695310087 := by
  unfold tailWord_3096364
  simp only [CollatzResearch.WordTrace]
  refine ⟨56466836477204759857524073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75289115302939679810032097 56466836477204759857524073)
  ·
    refine ⟨42350127357903569893143055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56466836477204759857524073 42350127357903569893143055)
    ·
      refine ⟨63525191036855354839714583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42350127357903569893143055 63525191036855354839714583)
      ·
        refine ⟨95287786555283032259571875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63525191036855354839714583 95287786555283032259571875)
        ·
          refine ⟨142931679832924548389357813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95287786555283032259571875 142931679832924548389357813)
          ·
            refine ⟨13399844984336676411502295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 142931679832924548389357813 13399844984336676411502295)
            ·
              refine ⟨20099767476505014617253443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13399844984336676411502295 20099767476505014617253443)
              ·
                refine ⟨30149651214757521925880165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20099767476505014617253443 30149651214757521925880165)
                ·
                  refine ⟨5653059602767035361102531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30149651214757521925880165 5653059602767035361102531)
                  ·
                    refine ⟨8479589404150553041653797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5653059602767035361102531 8479589404150553041653797)
                    ·
                      refine ⟨1589923013278228695310087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8479589404150553041653797 1589923013278228695310087)
                      ·
                        rfl

theorem cell23_3096364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 4].length) (baseStart_3096364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3096364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3096364 prefixEnd_3096364 := by exact prefixLift 3096364
  have htrace : WordTrace (prefixWord ++ tailWord_3096364) baseStart_3096364 baseEnd_3096364 := by
    simpa [prefixWord, tailWord_3096364, baseEnd_3096364] using wordTrace_append hprefix tailTrace_3096364
  have hstable : (prefixWord ++ tailWord_3096364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3096364).length < 2 ^ (prefixWord ++ tailWord_3096364).sum := by decide
  have hdescent : baseEnd_3096364 < baseStart_3096364 := by decide
  rcases family_descends (prefixWord ++ tailWord_3096364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3096367 : List Nat := [1, 1, 2, 1, 2, 1, 2, 3, 2, 3, 5]
def baseStart_3096367 : Nat := 118140960795 + 3096367 * 2 ^ 59
def prefixEnd_3096367 : Nat := 4983230072969 + 3 ^ 40 * 3096367 * 2
def baseEnd_3096367 : Nat := 1589924553720192183572573

theorem tailTrace_3096367 : CollatzResearch.WordTrace tailWord_3096367 prefixEnd_3096367 1589924553720192183572573 := by
  unfold tailWord_3096367
  simp only [CollatzResearch.WordTrace]
  refine ⟨112933782373398651227407355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75289188248932434151604903 112933782373398651227407355)
  ·
    refine ⟨169400673560097976841111033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112933782373398651227407355 169400673560097976841111033)
    ·
      refine ⟨127050505170073482630833275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169400673560097976841111033 127050505170073482630833275)
      ·
        refine ⟨190575757755110223946249913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127050505170073482630833275 190575757755110223946249913)
        ·
          refine ⟨142931818316332667959687435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 190575757755110223946249913 142931818316332667959687435)
          ·
            refine ⟨214397727474499001939531153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142931818316332667959687435 214397727474499001939531153)
            ·
              refine ⟨160798295605874251454648365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 214397727474499001939531153 160798295605874251454648365)
              ·
                refine ⟨60299360852202844295493137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 160798295605874251454648365 60299360852202844295493137)
                ·
                  refine ⟨45224520639152133221619853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60299360852202844295493137 45224520639152133221619853)
                  ·
                    refine ⟨16959195239682049958107445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45224520639152133221619853 16959195239682049958107445)
                    ·
                      refine ⟨1589924553720192183572573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16959195239682049958107445 1589924553720192183572573)
                      ·
                        rfl

theorem cell23_3096367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 3, 2, 3, 5].length) (baseStart_3096367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3096367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3096367 prefixEnd_3096367 := by exact prefixLift 3096367
  have htrace : WordTrace (prefixWord ++ tailWord_3096367) baseStart_3096367 baseEnd_3096367 := by
    simpa [prefixWord, tailWord_3096367, baseEnd_3096367] using wordTrace_append hprefix tailTrace_3096367
  have hstable : (prefixWord ++ tailWord_3096367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3096367).length < 2 ^ (prefixWord ++ tailWord_3096367).sum := by decide
  have hdescent : baseEnd_3096367 < baseStart_3096367 := by decide
  rcases family_descends (prefixWord ++ tailWord_3096367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3096401 : List Nat := [1, 2, 2, 1, 5, 1, 1, 3, 2, 2, 3]
def baseStart_3096401 : Nat := 118140960795 + 3096401 * 2 ^ 59
def prefixEnd_3096401 : Nat := 4983230072969 + 3 ^ 40 * 3096401 * 2
def baseEnd_3096401 : Nat := 1589942012062445050547417

theorem tailTrace_3096401 : CollatzResearch.WordTrace tailWord_3096401 prefixEnd_3096401 1589942012062445050547417 := by
  unfold tailWord_3096401
  simp only [CollatzResearch.WordTrace]
  refine ⟨112935022455275475034145057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75290014970183650022763371 112935022455275475034145057)
  ·
    refine ⟨84701266841456606275608793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112935022455275475034145057 84701266841456606275608793)
    ·
      refine ⟨63525950131092454706706595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84701266841456606275608793 63525950131092454706706595)
      ·
        refine ⟨95288925196638682060059893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63525950131092454706706595 95288925196638682060059893)
        ·
          refine ⟨8933336737184876443130615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 95288925196638682060059893 8933336737184876443130615)
          ·
            refine ⟨13400005105777314664695923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8933336737184876443130615 13400005105777314664695923)
            ·
              refine ⟨20100007658665971997043885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13400005105777314664695923 20100007658665971997043885)
              ·
                refine ⟨7537502871999739498891457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20100007658665971997043885 7537502871999739498891457)
                ·
                  refine ⟨5653127153999804624168593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7537502871999739498891457 5653127153999804624168593)
                  ·
                    refine ⟨4239845365499853468126445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5653127153999804624168593 4239845365499853468126445)
                    ·
                      refine ⟨1589942012062445050547417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4239845365499853468126445 1589942012062445050547417)
                      ·
                        rfl

theorem cell23_3096401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 3, 2, 2, 3].length) (baseStart_3096401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3096401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3096401 prefixEnd_3096401 := by exact prefixLift 3096401
  have htrace : WordTrace (prefixWord ++ tailWord_3096401) baseStart_3096401 baseEnd_3096401 := by
    simpa [prefixWord, tailWord_3096401, baseEnd_3096401] using wordTrace_append hprefix tailTrace_3096401
  have hstable : (prefixWord ++ tailWord_3096401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3096401).length < 2 ^ (prefixWord ++ tailWord_3096401).sum := by decide
  have hdescent : baseEnd_3096401 < baseStart_3096401 := by decide
  rcases family_descends (prefixWord ++ tailWord_3096401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3096418 : List Nat := [3, 3, 2, 1, 2, 1, 2, 2, 2, 2, 3]
def baseStart_3096418 : Nat := 118140960795 + 3096418 * 2 ^ 59
def prefixEnd_3096418 : Nat := 4983230072969 + 3 ^ 40 * 3096418 * 2
def baseEnd_3096418 : Nat := 1589950741233571484034839

theorem tailTrace_3096418 : CollatzResearch.WordTrace tailWord_3096418 prefixEnd_3096418 1589950741233571484034839 := by
  unfold tailWord_3096418
  simp only [CollatzResearch.WordTrace]
  refine ⟨28233910624053471734378477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75290428330809257958342605 28233910624053471734378477)
  ·
    refine ⟨10587716484020051900391929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28233910624053471734378477 10587716484020051900391929)
    ·
      refine ⟨7940787363015038925293947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10587716484020051900391929 7940787363015038925293947)
      ·
        refine ⟨11911181044522558387940921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7940787363015038925293947 11911181044522558387940921)
        ·
          refine ⟨8933385783391918790955691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11911181044522558387940921 8933385783391918790955691)
          ·
            refine ⟨13400078675087878186433537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8933385783391918790955691 13400078675087878186433537)
            ·
              refine ⟨10050059006315908639825153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13400078675087878186433537 10050059006315908639825153)
              ·
                refine ⟨7537544254736931479868865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10050059006315908639825153 7537544254736931479868865)
                ·
                  refine ⟨5653158191052698609901649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7537544254736931479868865 5653158191052698609901649)
                  ·
                    refine ⟨4239868643289523957426237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5653158191052698609901649 4239868643289523957426237)
                    ·
                      refine ⟨1589950741233571484034839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4239868643289523957426237 1589950741233571484034839)
                      ·
                        rfl

theorem cell23_3096418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 2, 2, 2, 3].length) (baseStart_3096418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3096418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3096418 prefixEnd_3096418 := by exact prefixLift 3096418
  have htrace : WordTrace (prefixWord ++ tailWord_3096418) baseStart_3096418 baseEnd_3096418 := by
    simpa [prefixWord, tailWord_3096418, baseEnd_3096418] using wordTrace_append hprefix tailTrace_3096418
  have hstable : (prefixWord ++ tailWord_3096418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3096418).length < 2 ^ (prefixWord ++ tailWord_3096418).sum := by decide
  have hdescent : baseEnd_3096418 < baseStart_3096418 := by decide
  rcases family_descends (prefixWord ++ tailWord_3096418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3096424 : List Nat := [2, 1, 4, 2, 1, 1, 2, 1, 1, 2, 6]
def baseStart_3096424 : Nat := 118140960795 + 3096424 * 2 ^ 59
def prefixEnd_3096424 : Nat := 4983230072969 + 3 ^ 40 * 3096424 * 2
def baseEnd_3096424 : Nat := 1589953822117498460559811

theorem tailTrace_3096424 : CollatzResearch.WordTrace tailWord_3096424 prefixEnd_3096424 1589953822117498460559811 := by
  unfold tailWord_3096424
  simp only [CollatzResearch.WordTrace]
  refine ⟨56467930667096074981116163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75290574222794766641488217 56467930667096074981116163)
  ·
    refine ⟨84701896000644112471674245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56467930667096074981116163 84701896000644112471674245)
    ·
      refine ⟨15881605500120771088438921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 84701896000644112471674245 15881605500120771088438921)
      ·
        refine ⟨11911204125090578316329191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15881605500120771088438921 11911204125090578316329191)
        ·
          refine ⟨17866806187635867474493787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11911204125090578316329191 17866806187635867474493787)
          ·
            refine ⟨26800209281453801211740681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17866806187635867474493787 26800209281453801211740681)
            ·
              refine ⟨20100156961090350908805511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26800209281453801211740681 20100156961090350908805511)
              ·
                refine ⟨30150235441635526363208267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20100156961090350908805511 30150235441635526363208267)
                ·
                  refine ⟨45225353162453289544812401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30150235441635526363208267 45225353162453289544812401)
                  ·
                    refine ⟨33919014871839967158609301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45225353162453289544812401 33919014871839967158609301)
                    ·
                      refine ⟨1589953822117498460559811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33919014871839967158609301 1589953822117498460559811)
                      ·
                        rfl

theorem cell23_3096424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 1, 1, 2, 6].length) (baseStart_3096424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3096424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3096424 prefixEnd_3096424 := by exact prefixLift 3096424
  have htrace : WordTrace (prefixWord ++ tailWord_3096424) baseStart_3096424 baseEnd_3096424 := by
    simpa [prefixWord, tailWord_3096424, baseEnd_3096424] using wordTrace_append hprefix tailTrace_3096424
  have hstable : (prefixWord ++ tailWord_3096424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3096424).length < 2 ^ (prefixWord ++ tailWord_3096424).sum := by decide
  have hdescent : baseEnd_3096424 < baseStart_3096424 := by decide
  rcases family_descends (prefixWord ++ tailWord_3096424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3096441 : List Nat := [1, 2, 1, 3, 2, 2, 2, 2, 1, 5, 2]
def baseStart_3096441 : Nat := 118140960795 + 3096441 * 2 ^ 59
def prefixEnd_3096441 : Nat := 4983230072969 + 3 ^ 40 * 3096441 * 2
def baseEnd_3096441 : Nat := 1589962551288624894047233

theorem tailTrace_3096441 : CollatzResearch.WordTrace tailWord_3096441 prefixEnd_3096441 1589962551288624894047233 := by
  unfold tailWord_3096441
  simp only [CollatzResearch.WordTrace]
  refine ⟨112936481375130561865601177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75290987583420374577067451 112936481375130561865601177)
  ·
    refine ⟨84702361031347921399200883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112936481375130561865601177 84702361031347921399200883)
    ·
      refine ⟨127053541547021882098801325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84702361031347921399200883 127053541547021882098801325)
      ·
        refine ⟨47645078080133205787050497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 127053541547021882098801325 47645078080133205787050497)
        ·
          refine ⟨35733808560099904340287873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47645078080133205787050497 35733808560099904340287873)
          ·
            refine ⟨26800356420074928255215905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35733808560099904340287873 26800356420074928255215905)
            ·
              refine ⟨20100267315056196191411929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26800356420074928255215905 20100267315056196191411929)
              ·
                refine ⟨15075200486292147143558947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20100267315056196191411929 15075200486292147143558947)
                ·
                  refine ⟨22612800729438220715338421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15075200486292147143558947 22612800729438220715338421)
                  ·
                    refine ⟨2119950068384833192062977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22612800729438220715338421 2119950068384833192062977)
                    ·
                      refine ⟨1589962551288624894047233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2119950068384833192062977 1589962551288624894047233)
                      ·
                        rfl

theorem cell23_3096441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 2, 1, 5, 2].length) (baseStart_3096441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3096441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3096441 prefixEnd_3096441 := by exact prefixLift 3096441
  have htrace : WordTrace (prefixWord ++ tailWord_3096441) baseStart_3096441 baseEnd_3096441 := by
    simpa [prefixWord, tailWord_3096441, baseEnd_3096441] using wordTrace_append hprefix tailTrace_3096441
  have hstable : (prefixWord ++ tailWord_3096441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3096441).length < 2 ^ (prefixWord ++ tailWord_3096441).sum := by decide
  have hdescent : baseEnd_3096441 < baseStart_3096441 := by decide
  rcases family_descends (prefixWord ++ tailWord_3096441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3096468 : List Nat := [2, 4, 2, 1, 1, 3, 1, 3, 1, 5]
def baseStart_3096468 : Nat := 118140960795 + 3096468 * 2 ^ 59
def prefixEnd_3096468 : Nat := 4983230072969 + 3 ^ 40 * 3096468 * 2
def baseEnd_3096468 : Nat := 529992138422098762803203

theorem tailTrace_3096468 : CollatzResearch.WordTrace tailWord_3096468 prefixEnd_3096468 529992138422098762803203 := by
  unfold tailWord_3096468
  simp only [CollatzResearch.WordTrace]
  refine ⟨56468733073016372738417029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75291644097355163651222705 56468733073016372738417029)
  ·
    refine ⟨10587887451190569888453193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56468733073016372738417029 10587887451190569888453193)
    ·
      refine ⟨7940915588392927416339895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10587887451190569888453193 7940915588392927416339895)
      ·
        refine ⟨11911373382589391124509843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7940915588392927416339895 11911373382589391124509843)
        ·
          refine ⟨17867060073884086686764765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11911373382589391124509843 17867060073884086686764765)
          ·
            refine ⟨6700147527706532507536787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17867060073884086686764765 6700147527706532507536787)
            ·
              refine ⟨10050221291559798761305181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6700147527706532507536787 10050221291559798761305181)
              ·
                refine ⟨3768832984334924535489443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10050221291559798761305181 3768832984334924535489443)
                ·
                  refine ⟨5653249476502386803234165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3768832984334924535489443 5653249476502386803234165)
                  ·
                    refine ⟨529992138422098762803203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5653249476502386803234165 529992138422098762803203)
                    ·
                      rfl

theorem cell23_3096468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 3, 1, 5].length) (baseStart_3096468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3096468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3096468 prefixEnd_3096468 := by exact prefixLift 3096468
  have htrace : WordTrace (prefixWord ++ tailWord_3096468) baseStart_3096468 baseEnd_3096468 := by
    simpa [prefixWord, tailWord_3096468, baseEnd_3096468] using wordTrace_append hprefix tailTrace_3096468
  have hstable : (prefixWord ++ tailWord_3096468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3096468).length < 2 ^ (prefixWord ++ tailWord_3096468).sum := by decide
  have hdescent : baseEnd_3096468 < baseStart_3096468 := by decide
  rcases family_descends (prefixWord ++ tailWord_3096468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3096501 : List Nat := [1, 3, 3, 2, 1, 3, 1, 1, 1, 1, 6]
def baseStart_3096501 : Nat := 118140960795 + 3096501 * 2 ^ 59
def prefixEnd_3096501 : Nat := 4983230072969 + 3 ^ 40 * 3096501 * 2
def baseEnd_3096501 : Nat := 1589993360127894659296957

theorem tailTrace_3096501 : CollatzResearch.WordTrace tailWord_3096501 prefixEnd_3096501 1589993360127894659296957 := by
  unfold tailWord_3096501
  simp only [CollatzResearch.WordTrace]
  refine ⟨112938669754913192112785357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75292446503275461408523571 112938669754913192112785357)
  ·
    refine ⟨42352001158092447042294509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112938669754913192112785357 42352001158092447042294509)
    ·
      refine ⟨15882000434284667640860441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42352001158092447042294509 15882000434284667640860441)
      ·
        refine ⟨11911500325713500730645331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15882000434284667640860441 11911500325713500730645331)
        ·
          refine ⟨17867250488570251095967997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11911500325713500730645331 17867250488570251095967997)
          ·
            refine ⟨6700218933213844160987999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17867250488570251095967997 6700218933213844160987999)
            ·
              refine ⟨10050328399820766241481999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6700218933213844160987999 10050328399820766241481999)
              ·
                refine ⟨15075492599731149362222999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10050328399820766241481999 15075492599731149362222999)
                ·
                  refine ⟨22613238899596724043334499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15075492599731149362222999 22613238899596724043334499)
                  ·
                    refine ⟨33919858349395086065001749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22613238899596724043334499 33919858349395086065001749)
                    ·
                      refine ⟨1589993360127894659296957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33919858349395086065001749 1589993360127894659296957)
                      ·
                        rfl

theorem cell23_3096501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 1, 1, 1, 6].length) (baseStart_3096501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3096501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3096501 prefixEnd_3096501 := by exact prefixLift 3096501
  have htrace : WordTrace (prefixWord ++ tailWord_3096501) baseStart_3096501 baseEnd_3096501 := by
    simpa [prefixWord, tailWord_3096501, baseEnd_3096501] using wordTrace_append hprefix tailTrace_3096501
  have hstable : (prefixWord ++ tailWord_3096501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3096501).length < 2 ^ (prefixWord ++ tailWord_3096501).sum := by decide
  have hdescent : baseEnd_3096501 < baseStart_3096501 := by decide
  rcases family_descends (prefixWord ++ tailWord_3096501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3096522 : List Nat := [3, 1, 2, 1, 2, 1, 5, 3, 1, 2, 2]
def baseStart_3096522 : Nat := 118140960795 + 3096522 * 2 ^ 59
def prefixEnd_3096522 : Nat := 4983230072969 + 3 ^ 40 * 3096522 * 2
def baseEnd_3096522 : Nat := 1590004143221639077134361

theorem tailTrace_3096522 : CollatzResearch.WordTrace tailWord_3096522 prefixEnd_3096522 1590004143221639077134361 := by
  unfold tailWord_3096522
  simp only [CollatzResearch.WordTrace]
  refine ⟨28234858921959278174824955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75292957125224741799533213 28234858921959278174824955)
  ·
    refine ⟨42352288382938917262237433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28234858921959278174824955 42352288382938917262237433)
    ·
      refine ⟨31764216287204187946678075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42352288382938917262237433 31764216287204187946678075)
      ·
        refine ⟨47646324430806281920017113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31764216287204187946678075 47646324430806281920017113)
        ·
          refine ⟨35734743323104711440012835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47646324430806281920017113 35734743323104711440012835)
          ·
            refine ⟨53602114984657067160019253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35734743323104711440012835 53602114984657067160019253)
            ·
              refine ⟨5025198279811600046251805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 53602114984657067160019253 5025198279811600046251805)
              ·
                refine ⟨1884449354929350017344427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5025198279811600046251805 1884449354929350017344427)
                ·
                  refine ⟨2826674032394025026016641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1884449354929350017344427 2826674032394025026016641)
                  ·
                    refine ⟨2120005524295518769512481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2826674032394025026016641 2120005524295518769512481)
                    ·
                      refine ⟨1590004143221639077134361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2120005524295518769512481 1590004143221639077134361)
                      ·
                        rfl

theorem cell23_3096522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 5, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 5, 3, 1, 2, 2].length) (baseStart_3096522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3096522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3096522 prefixEnd_3096522 := by exact prefixLift 3096522
  have htrace : WordTrace (prefixWord ++ tailWord_3096522) baseStart_3096522 baseEnd_3096522 := by
    simpa [prefixWord, tailWord_3096522, baseEnd_3096522] using wordTrace_append hprefix tailTrace_3096522
  have hstable : (prefixWord ++ tailWord_3096522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3096522).length < 2 ^ (prefixWord ++ tailWord_3096522).sum := by decide
  have hdescent : baseEnd_3096522 < baseStart_3096522 := by decide
  rcases family_descends (prefixWord ++ tailWord_3096522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3096548 : List Nat := [2, 3, 1, 1, 1, 1, 4, 2, 3, 3, 2]
def baseStart_3096548 : Nat := 118140960795 + 3096548 * 2 ^ 59
def prefixEnd_3096548 : Nat := 4983230072969 + 3 ^ 40 * 3096548 * 2
def baseEnd_3096548 : Nat := 1590017493718655975409241

theorem tailTrace_3096548 : CollatzResearch.WordTrace tailWord_3096548 prefixEnd_3096548 1590017493718655975409241 := by
  unfold tailWord_3096548
  simp only [CollatzResearch.WordTrace]
  refine ⟨56470191992871459569873149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75293589323828612759830865 56470191992871459569873149)
  ·
    refine ⟨21176321997326797338702431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56470191992871459569873149 21176321997326797338702431)
    ·
      refine ⟨31764482995990196008053647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21176321997326797338702431 31764482995990196008053647)
      ·
        refine ⟨47646724493985294012080471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31764482995990196008053647 47646724493985294012080471)
        ·
          refine ⟨71470086740977941018120707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47646724493985294012080471 71470086740977941018120707)
          ·
            refine ⟨107205130111466911527181061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71470086740977941018120707 107205130111466911527181061)
            ·
              refine ⟨20100961895900045911346449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 107205130111466911527181061 20100961895900045911346449)
              ·
                refine ⟨15075721421925034433509837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20100961895900045911346449 15075721421925034433509837)
                ·
                  refine ⟨5653395533221887912566189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15075721421925034433509837 5653395533221887912566189)
                  ·
                    refine ⟨2120023324958207967212321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5653395533221887912566189 2120023324958207967212321)
                    ·
                      refine ⟨1590017493718655975409241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2120023324958207967212321 1590017493718655975409241)
                      ·
                        rfl

theorem cell23_3096548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 2, 3, 3, 2].length) (baseStart_3096548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3096548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3096548 prefixEnd_3096548 := by exact prefixLift 3096548
  have htrace : WordTrace (prefixWord ++ tailWord_3096548) baseStart_3096548 baseEnd_3096548 := by
    simpa [prefixWord, tailWord_3096548, baseEnd_3096548] using wordTrace_append hprefix tailTrace_3096548
  have hstable : (prefixWord ++ tailWord_3096548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3096548).length < 2 ^ (prefixWord ++ tailWord_3096548).sum := by decide
  have hdescent : baseEnd_3096548 < baseStart_3096548 := by decide
  rcases family_descends (prefixWord ++ tailWord_3096548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3096581 : List Nat := [1, 3, 1, 1, 2, 4, 2, 1, 2, 1, 5]
def baseStart_3096581 : Nat := 118140960795 + 3096581 * 2 ^ 59
def prefixEnd_3096581 : Nat := 4983230072969 + 3 ^ 40 * 3096581 * 2
def baseEnd_3096581 : Nat := 1590034438580254346296589

theorem tailTrace_3096581 : CollatzResearch.WordTrace tailWord_3096581 prefixEnd_3096581 1590034438580254346296589 := by
  unfold tailWord_3096581
  simp only [CollatzResearch.WordTrace]
  refine ⟨112941587594623365775697597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75294391729748910517131731 112941587594623365775697597)
  ·
    refine ⟨42353095347983762165886599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112941587594623365775697597 42353095347983762165886599)
    ·
      refine ⟨63529643021975643248829899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42353095347983762165886599 63529643021975643248829899)
      ·
        refine ⟨95294464532963464873244849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63529643021975643248829899 95294464532963464873244849)
        ·
          refine ⟨71470848399722598654933637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95294464532963464873244849 71470848399722598654933637)
          ·
            refine ⟨13400784074947987247800057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71470848399722598654933637 13400784074947987247800057)
            ·
              refine ⟨10050588056210990435850043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13400784074947987247800057 10050588056210990435850043)
              ·
                refine ⟨15075882084316485653775065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10050588056210990435850043 15075882084316485653775065)
                ·
                  refine ⟨11306911563237364240331299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15075882084316485653775065 11306911563237364240331299)
                  ·
                    refine ⟨16960367344856046360496949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11306911563237364240331299 16960367344856046360496949)
                    ·
                      refine ⟨1590034438580254346296589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16960367344856046360496949 1590034438580254346296589)
                      ·
                        rfl

theorem cell23_3096581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 1, 2, 1, 5].length) (baseStart_3096581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3096581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3096581 prefixEnd_3096581 := by exact prefixLift 3096581
  have htrace : WordTrace (prefixWord ++ tailWord_3096581) baseStart_3096581 baseEnd_3096581 := by
    simpa [prefixWord, tailWord_3096581, baseEnd_3096581] using wordTrace_append hprefix tailTrace_3096581
  have hstable : (prefixWord ++ tailWord_3096581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3096581).length < 2 ^ (prefixWord ++ tailWord_3096581).sum := by decide
  have hdescent : baseEnd_3096581 < baseStart_3096581 := by decide
  rcases family_descends (prefixWord ++ tailWord_3096581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3096595 : List Nat := [1, 1, 1, 2, 1, 4, 3, 4, 2, 2, 2]
def baseStart_3096595 : Nat := 118140960795 + 3096595 * 2 ^ 59
def prefixEnd_3096595 : Nat := 4983230072969 + 3 ^ 40 * 3096595 * 2
def baseEnd_3096595 : Nat := 1590041627309417291521525

theorem tailTrace_3096595 : CollatzResearch.WordTrace tailWord_3096595 prefixEnd_3096595 1590041627309417291521525 := by
  unfold tailWord_3096595
  simp only [CollatzResearch.WordTrace]
  refine ⟨112942098216572646166707239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75294732144381764111138159 112942098216572646166707239)
  ·
    refine ⟨169413147324858969250060859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112942098216572646166707239 169413147324858969250060859)
    ·
      refine ⟨254119720987288453875091289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169413147324858969250060859 254119720987288453875091289)
      ·
        refine ⟨190589790740466340406318467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 254119720987288453875091289 190589790740466340406318467)
        ·
          refine ⟨285884686110699510609477701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190589790740466340406318467 285884686110699510609477701)
          ·
            refine ⟨53603378645756158239277069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 285884686110699510609477701 53603378645756158239277069)
            ·
              refine ⟨20101266992158559339728901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53603378645756158239277069 20101266992158559339728901)
              ·
                refine ⟨3768987561029729876199169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20101266992158559339728901 3768987561029729876199169)
                ·
                  refine ⟨2826740670772297407149377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3768987561029729876199169 2826740670772297407149377)
                  ·
                    refine ⟨2120055503079223055362033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2826740670772297407149377 2120055503079223055362033)
                    ·
                      refine ⟨1590041627309417291521525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2120055503079223055362033 1590041627309417291521525)
                      ·
                        rfl

theorem cell23_3096595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 4, 2, 2, 2].length) (baseStart_3096595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3096595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3096595 prefixEnd_3096595 := by exact prefixLift 3096595
  have htrace : WordTrace (prefixWord ++ tailWord_3096595) baseStart_3096595 baseEnd_3096595 := by
    simpa [prefixWord, tailWord_3096595, baseEnd_3096595] using wordTrace_append hprefix tailTrace_3096595
  have hstable : (prefixWord ++ tailWord_3096595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3096595).length < 2 ^ (prefixWord ++ tailWord_3096595).sum := by decide
  have hdescent : baseEnd_3096595 < baseStart_3096595 := by decide
  rcases family_descends (prefixWord ++ tailWord_3096595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3096612 : List Nat := [2, 3, 1, 4, 2, 1, 2, 1, 1, 4, 2]
def baseStart_3096612 : Nat := 118140960795 + 3096612 * 2 ^ 59
def prefixEnd_3096612 : Nat := 4983230072969 + 3 ^ 40 * 3096612 * 2
def baseEnd_3096612 : Nat := 1590050356480543725008947

theorem tailTrace_3096612 : CollatzResearch.WordTrace tailWord_3096612 prefixEnd_3096612 1590050356480543725008947 := by
  unfold tailWord_3096612
  simp only [CollatzResearch.WordTrace]
  refine ⟨56471359128755529035038045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75295145505007372046717393 56471359128755529035038045)
  ·
    refine ⟨21176759673283323388139267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56471359128755529035038045 21176759673283323388139267)
    ·
      refine ⟨31765139509924985082208901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21176759673283323388139267 31765139509924985082208901)
      ·
        refine ⟨5955963658110934702914169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31765139509924985082208901 5955963658110934702914169)
        ·
          refine ⟨4466972743583201027185627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5955963658110934702914169 4466972743583201027185627)
          ·
            refine ⟨6700459115374801540778441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4466972743583201027185627 6700459115374801540778441)
            ·
              refine ⟨5025344336531101155583831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6700459115374801540778441 5025344336531101155583831)
              ·
                refine ⟨7538016504796651733375747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5025344336531101155583831 7538016504796651733375747)
                ·
                  refine ⟨11307024757194977600063621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7538016504796651733375747 11307024757194977600063621)
                  ·
                    refine ⟨2120067141974058300011929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11307024757194977600063621 2120067141974058300011929)
                    ·
                      refine ⟨1590050356480543725008947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2120067141974058300011929 1590050356480543725008947)
                      ·
                        rfl

theorem cell23_3096612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 2, 1, 1, 4, 2].length) (baseStart_3096612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3096612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3096612 prefixEnd_3096612 := by exact prefixLift 3096612
  have htrace : WordTrace (prefixWord ++ tailWord_3096612) baseStart_3096612 baseEnd_3096612 := by
    simpa [prefixWord, tailWord_3096612, baseEnd_3096612] using wordTrace_append hprefix tailTrace_3096612
  have hstable : (prefixWord ++ tailWord_3096612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3096612).length < 2 ^ (prefixWord ++ tailWord_3096612).sum := by decide
  have hdescent : baseEnd_3096612 < baseStart_3096612 := by decide
  rcases family_descends (prefixWord ++ tailWord_3096612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3096618 : List Nat := [3, 1, 4, 1, 2, 2, 1, 2, 7]
def baseStart_3096618 : Nat := 118140960795 + 3096618 * 2 ^ 59
def prefixEnd_3096618 : Nat := 4983230072969 + 3 ^ 40 * 3096618 * 2
def baseEnd_3096618 : Nat := 176672604151607855725991

theorem tailTrace_3096618 : CollatzResearch.WordTrace tailWord_3096618 prefixEnd_3096618 176672604151607855725991 := by
  unfold tailWord_3096618
  simp only [CollatzResearch.WordTrace]
  refine ⟨28235734273872330273698627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75295291396992880729863005 28235734273872330273698627)
  ·
    refine ⟨42353601410808495410547941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28235734273872330273698627 42353601410808495410547941)
    ·
      refine ⟨7941300264526592889477739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42353601410808495410547941 7941300264526592889477739)
      ·
        refine ⟨11911950396789889334216609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7941300264526592889477739 11911950396789889334216609)
        ·
          refine ⟨8933962797592417000662457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11911950396789889334216609 8933962797592417000662457)
          ·
            refine ⟨6700472098194312750496843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8933962797592417000662457 6700472098194312750496843)
            ·
              refine ⟨10050708147291469125745265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6700472098194312750496843 10050708147291469125745265)
              ·
                refine ⟨7538031110468601844308949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10050708147291469125745265 7538031110468601844308949)
                ·
                  refine ⟨176672604151607855725991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7538031110468601844308949 176672604151607855725991)
                  ·
                    rfl

theorem cell23_3096618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 2, 7].length) (baseStart_3096618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3096618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3096618 prefixEnd_3096618 := by exact prefixLift 3096618
  have htrace : WordTrace (prefixWord ++ tailWord_3096618) baseStart_3096618 baseEnd_3096618 := by
    simpa [prefixWord, tailWord_3096618, baseEnd_3096618] using wordTrace_append hprefix tailTrace_3096618
  have hstable : (prefixWord ++ tailWord_3096618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3096618).length < 2 ^ (prefixWord ++ tailWord_3096618).sum := by decide
  have hdescent : baseEnd_3096618 < baseStart_3096618 := by decide
  rcases family_descends (prefixWord ++ tailWord_3096618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3096662 : List Nat := [5, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3]
def baseStart_3096662 : Nat := 118140960795 + 3096662 * 2 ^ 59
def prefixEnd_3096662 : Nat := 4983230072969 + 3 ^ 40 * 3096662 * 2
def baseEnd_3096662 : Nat := 1590076030513268529383717

theorem tailTrace_3096662 : CollatzResearch.WordTrace tailWord_3096662 prefixEnd_3096662 1590076030513268529383717 := by
  unfold tailWord_3096662
  simp only [CollatzResearch.WordTrace]
  refine ⟨7059033869208119788087265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 75296361271553277739597493 7059033869208119788087265)
  ·
    refine ⟨5294275401906089841065449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7059033869208119788087265 5294275401906089841065449)
    ·
      refine ⟨3970706551429567380799087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5294275401906089841065449 3970706551429567380799087)
      ·
        refine ⟨5956059827144351071198631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3970706551429567380799087 5956059827144351071198631)
        ·
          refine ⟨8934089740716526606797947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5956059827144351071198631 8934089740716526606797947)
          ·
            refine ⟨13401134611074789910196921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8934089740716526606797947 13401134611074789910196921)
            ·
              refine ⟨10050850958306092432647691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13401134611074789910196921 10050850958306092432647691)
              ·
                refine ⟨15076276437459138648971537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10050850958306092432647691 15076276437459138648971537)
                ·
                  refine ⟨11307207328094353986728653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15076276437459138648971537 11307207328094353986728653)
                  ·
                    refine ⟨4240202748035382745023245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11307207328094353986728653 4240202748035382745023245)
                    ·
                      refine ⟨1590076030513268529383717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4240202748035382745023245 1590076030513268529383717)
                      ·
                        rfl

theorem cell23_3096662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3].length) (baseStart_3096662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3096662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3096662 prefixEnd_3096662 := by exact prefixLift 3096662
  have htrace : WordTrace (prefixWord ++ tailWord_3096662) baseStart_3096662 baseEnd_3096662 := by
    simpa [prefixWord, tailWord_3096662, baseEnd_3096662] using wordTrace_append hprefix tailTrace_3096662
  have hstable : (prefixWord ++ tailWord_3096662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3096662).length < 2 ^ (prefixWord ++ tailWord_3096662).sum := by decide
  have hdescent : baseEnd_3096662 < baseStart_3096662 := by decide
  rcases family_descends (prefixWord ++ tailWord_3096662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3096668 : List Nat := [2, 2, 4, 1, 1, 2, 1, 2, 1, 3, 4]
def baseStart_3096668 : Nat := 118140960795 + 3096668 * 2 ^ 59
def prefixEnd_3096668 : Nat := 4983230072969 + 3 ^ 40 * 3096668 * 2
def baseEnd_3096668 : Nat := 1590079111397195505908689

theorem tailTrace_3096668 : CollatzResearch.WordTrace tailWord_3096668 prefixEnd_3096668 1590079111397195505908689 := by
  unfold tailWord_3096668
  simp only [CollatzResearch.WordTrace]
  refine ⟨56472380372654089817057329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75296507163538786422743105 56472380372654089817057329)
  ·
    refine ⟨42354285279490567362792997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56472380372654089817057329 42354285279490567362792997)
    ·
      refine ⟨7941428489904481380523687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42354285279490567362792997 7941428489904481380523687)
      ·
        refine ⟨11912142734856722070785531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7941428489904481380523687 11912142734856722070785531)
        ·
          refine ⟨17868214102285083106178297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11912142734856722070785531 17868214102285083106178297)
          ·
            refine ⟨13401160576713812329633723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17868214102285083106178297 13401160576713812329633723)
            ·
              refine ⟨20101740865070718494450585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13401160576713812329633723 20101740865070718494450585)
              ·
                refine ⟨15076305648803038870837939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20101740865070718494450585 15076305648803038870837939)
                ·
                  refine ⟨22614458473204558306256909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15076305648803038870837939 22614458473204558306256909)
                  ·
                    refine ⟨8480421927451709364846341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22614458473204558306256909 8480421927451709364846341)
                    ·
                      refine ⟨1590079111397195505908689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8480421927451709364846341 1590079111397195505908689)
                      ·
                        rfl

theorem cell23_3096668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 2, 1, 3, 4].length) (baseStart_3096668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3096668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3096668 prefixEnd_3096668 := by exact prefixLift 3096668
  have htrace : WordTrace (prefixWord ++ tailWord_3096668) baseStart_3096668 baseEnd_3096668 := by
    simpa [prefixWord, tailWord_3096668, baseEnd_3096668] using wordTrace_append hprefix tailTrace_3096668
  have hstable : (prefixWord ++ tailWord_3096668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3096668).length < 2 ^ (prefixWord ++ tailWord_3096668).sum := by decide
  have hdescent : baseEnd_3096668 < baseStart_3096668 := by decide
  rcases family_descends (prefixWord ++ tailWord_3096668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3096681 : List Nat := [1, 2, 1, 1, 1, 5, 1, 1, 2, 4, 4]
def baseStart_3096681 : Nat := 118140960795 + 3096681 * 2 ^ 59
def prefixEnd_3096681 : Nat := 4983230072969 + 3 ^ 40 * 3096681 * 2
def baseEnd_3096681 : Nat := 1590085786645703955046129

theorem tailTrace_3096681 : CollatzResearch.WordTrace tailWord_3096681 prefixEnd_3096681 1590085786645703955046129 := by
  unfold tailWord_3096681
  simp only [CollatzResearch.WordTrace]
  refine ⟨112945234894261082854337897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75296823262840721902891931 112945234894261082854337897)
  ·
    refine ⟨84708926170695812140753423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112945234894261082854337897 84708926170695812140753423)
    ·
      refine ⟨127063389256043718211130135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84708926170695812140753423 127063389256043718211130135)
      ·
        refine ⟨190595083884065577316695203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127063389256043718211130135 190595083884065577316695203)
        ·
          refine ⟨285892625826098365975042805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190595083884065577316695203 285892625826098365975042805)
          ·
            refine ⟨26802433671196721810160263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 285892625826098365975042805 26802433671196721810160263)
            ·
              refine ⟨40203650506795082715240395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26802433671196721810160263 40203650506795082715240395)
              ·
                refine ⟨60305475760192624072860593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40203650506795082715240395 60305475760192624072860593)
                ·
                  refine ⟨45229106820144468054645445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60305475760192624072860593 45229106820144468054645445)
                  ·
                    refine ⟨8480457528777087760246021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45229106820144468054645445 8480457528777087760246021)
                    ·
                      refine ⟨1590085786645703955046129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8480457528777087760246021 1590085786645703955046129)
                      ·
                        rfl

theorem cell23_3096681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 1, 2, 4, 4].length) (baseStart_3096681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3096681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3096681 prefixEnd_3096681 := by exact prefixLift 3096681
  have htrace : WordTrace (prefixWord ++ tailWord_3096681) baseStart_3096681 baseEnd_3096681 := by
    simpa [prefixWord, tailWord_3096681, baseEnd_3096681] using wordTrace_append hprefix tailTrace_3096681
  have hstable : (prefixWord ++ tailWord_3096681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3096681).length < 2 ^ (prefixWord ++ tailWord_3096681).sum := by decide
  have hdescent : baseEnd_3096681 < baseStart_3096681 := by decide
  rcases family_descends (prefixWord ++ tailWord_3096681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3096688 : List Nat := [2, 1, 1, 1, 5, 2, 2, 1, 1, 4, 3]
def baseStart_3096688 : Nat := 118140960795 + 3096688 * 2 ^ 59
def prefixEnd_3096688 : Nat := 4983230072969 + 3 ^ 40 * 3096688 * 2
def baseEnd_3096688 : Nat := 1590089381010285427658597

theorem tailTrace_3096688 : CollatzResearch.WordTrace tailWord_3096688 prefixEnd_3096688 1590089381010285427658597 := by
  unfold tailWord_3096688
  simp only [CollatzResearch.WordTrace]
  refine ⟨56472745102617861524921359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75296993470157148699895145 56472745102617861524921359)
  ·
    refine ⟨84709117653926792287382039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56472745102617861524921359 84709117653926792287382039)
    ·
      refine ⟨127063676480890188431073059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84709117653926792287382039 127063676480890188431073059)
      ·
        refine ⟨190595514721335282646609589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127063676480890188431073059 190595514721335282646609589)
        ·
          refine ⟨17868329505125182748119649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 190595514721335282646609589 17868329505125182748119649)
          ·
            refine ⟨13401247128843887061089737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17868329505125182748119649 13401247128843887061089737)
            ·
              refine ⟨10050935346632915295817303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13401247128843887061089737 10050935346632915295817303)
              ·
                refine ⟨15076403019949372943725955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10050935346632915295817303 15076403019949372943725955)
                ·
                  refine ⟨22614604529924059415588933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15076403019949372943725955 22614604529924059415588933)
                  ·
                    refine ⟨4240238349360761140422925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22614604529924059415588933 4240238349360761140422925)
                    ·
                      refine ⟨1590089381010285427658597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4240238349360761140422925 1590089381010285427658597)
                      ·
                        rfl

theorem cell23_3096688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 1, 1, 4, 3].length) (baseStart_3096688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3096688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3096688 prefixEnd_3096688 := by exact prefixLift 3096688
  have htrace : WordTrace (prefixWord ++ tailWord_3096688) baseStart_3096688 baseEnd_3096688 := by
    simpa [prefixWord, tailWord_3096688, baseEnd_3096688] using wordTrace_append hprefix tailTrace_3096688
  have hstable : (prefixWord ++ tailWord_3096688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3096688).length < 2 ^ (prefixWord ++ tailWord_3096688).sum := by decide
  have hdescent : baseEnd_3096688 < baseStart_3096688 := by decide
  rcases family_descends (prefixWord ++ tailWord_3096688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3096708 : List Nat := [2, 3, 2, 1, 2, 1, 2, 4, 6]
def baseStart_3096708 : Nat := 118140960795 + 3096708 * 2 ^ 59
def prefixEnd_3096708 : Nat := 4983230072969 + 3 ^ 40 * 3096708 * 2
def baseEnd_3096708 : Nat := 176677738958152816600945

theorem tailTrace_3096708 : CollatzResearch.WordTrace tailWord_3096708 prefixEnd_3096708 176677738958152816600945 := by
  unfold tailWord_3096708
  simp only [CollatzResearch.WordTrace]
  refine ⟨56473109832581633232785389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75297479776775510977047185 56473109832581633232785389)
  ·
    refine ⟨21177416187218112462294521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56473109832581633232785389 21177416187218112462294521)
    ·
      refine ⟨15883062140413584346720891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21177416187218112462294521 15883062140413584346720891)
      ·
        refine ⟨23824593210620376520081337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15883062140413584346720891 23824593210620376520081337)
        ·
          refine ⟨17868444907965282390061003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23824593210620376520081337 17868444907965282390061003)
          ·
            refine ⟨26802667361947923585091505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17868444907965282390061003 26802667361947923585091505)
            ·
              refine ⟨20102000521460942688818629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26802667361947923585091505 20102000521460942688818629)
              ·
                refine ⟨3769125097773926754153493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20102000521460942688818629 3769125097773926754153493)
                ·
                  refine ⟨176677738958152816600945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3769125097773926754153493 176677738958152816600945)
                  ·
                    rfl

theorem cell23_3096708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 4, 6].length) (baseStart_3096708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3096708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3096708 prefixEnd_3096708 := by exact prefixLift 3096708
  have htrace : WordTrace (prefixWord ++ tailWord_3096708) baseStart_3096708 baseEnd_3096708 := by
    simpa [prefixWord, tailWord_3096708, baseEnd_3096708] using wordTrace_append hprefix tailTrace_3096708
  have hstable : (prefixWord ++ tailWord_3096708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3096708).length < 2 ^ (prefixWord ++ tailWord_3096708).sum := by decide
  have hdescent : baseEnd_3096708 < baseStart_3096708 := by decide
  rcases family_descends (prefixWord ++ tailWord_3096708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3096711 : List Nat := [1, 1, 4, 2, 1, 1, 2, 1, 1, 1, 8]
def baseStart_3096711 : Nat := 118140960795 + 3096711 * 2 ^ 59
def prefixEnd_3096711 : Nat := 4983230072969 + 3 ^ 40 * 3096711 * 2
def baseEnd_3096711 : Nat := 1590101191065338837670991

theorem tailTrace_3096711 : CollatzResearch.WordTrace tailWord_3096711 prefixEnd_3096711 1590101191065338837670991 := by
  unfold tailWord_3096711
  simp only [CollatzResearch.WordTrace]
  refine ⟨112946329084152397977929987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75297552722768265318619991 112946329084152397977929987)
  ·
    refine ⟨169419493626228596966894981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112946329084152397977929987 169419493626228596966894981)
    ·
      refine ⟨31766155054917861931292809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 169419493626228596966894981 31766155054917861931292809)
      ·
        refine ⟨23824616291188396448469607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31766155054917861931292809 23824616291188396448469607)
        ·
          refine ⟨35736924436782594672704411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23824616291188396448469607 35736924436782594672704411)
          ·
            refine ⟨53605386655173892009056617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35736924436782594672704411 53605386655173892009056617)
            ·
              refine ⟨40204039991380419006792463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53605386655173892009056617 40204039991380419006792463)
              ·
                refine ⟨60306059987070628510188695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40204039991380419006792463 60306059987070628510188695)
                ·
                  refine ⟨90459089980605942765283043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60306059987070628510188695 90459089980605942765283043)
                  ·
                    refine ⟨135688634970908914147924565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 90459089980605942765283043 135688634970908914147924565)
                    ·
                      refine ⟨1590101191065338837670991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 135688634970908914147924565 1590101191065338837670991)
                      ·
                        rfl

theorem cell23_3096711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 1, 1, 1, 8].length) (baseStart_3096711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3096711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3096711 prefixEnd_3096711 := by exact prefixLift 3096711
  have htrace : WordTrace (prefixWord ++ tailWord_3096711) baseStart_3096711 baseEnd_3096711 := by
    simpa [prefixWord, tailWord_3096711, baseEnd_3096711] using wordTrace_append hprefix tailTrace_3096711
  have hstable : (prefixWord ++ tailWord_3096711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3096711).length < 2 ^ (prefixWord ++ tailWord_3096711).sum := by decide
  have hdescent : baseEnd_3096711 < baseStart_3096711 := by decide
  rcases family_descends (prefixWord ++ tailWord_3096711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3096712 : List Nat := [2, 1, 3, 4, 1, 3, 1, 1, 3, 4]
def baseStart_3096712 : Nat := 118140960795 + 3096712 * 2 ^ 59
def prefixEnd_3096712 : Nat := 4983230072969 + 3 ^ 40 * 3096712 * 2
def baseEnd_3096712 : Nat := 530033901515331111252829

theorem tailTrace_3096712 : CollatzResearch.WordTrace tailWord_3096712 prefixEnd_3096712 530033901515331111252829 := by
  unfold tailWord_3096712
  simp only [CollatzResearch.WordTrace]
  refine ⟨56473182778574387574358195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75297577038099183432477593 56473182778574387574358195)
  ·
    refine ⟨84709774167861581361537293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56473182778574387574358195 84709774167861581361537293)
    ·
      refine ⟨31766165312948093010576485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84709774167861581361537293 31766165312948093010576485)
      ·
        refine ⟨5956155996177767439483091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31766165312948093010576485 5956155996177767439483091)
        ·
          refine ⟨8934233994266651159224637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5956155996177767439483091 8934233994266651159224637)
          ·
            refine ⟨3350337747849994184709239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8934233994266651159224637 3350337747849994184709239)
            ·
              refine ⟨5025506621774991277063859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3350337747849994184709239 5025506621774991277063859)
              ·
                refine ⟨7538259932662486915595789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5025506621774991277063859 7538259932662486915595789)
                ·
                  refine ⟨2826847474748432593348421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7538259932662486915595789 2826847474748432593348421)
                  ·
                    refine ⟨530033901515331111252829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2826847474748432593348421 530033901515331111252829)
                    ·
                      rfl

theorem cell23_3096712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 1, 1, 3, 4].length) (baseStart_3096712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3096712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3096712 prefixEnd_3096712 := by exact prefixLift 3096712
  have htrace : WordTrace (prefixWord ++ tailWord_3096712) baseStart_3096712 baseEnd_3096712 := by
    simpa [prefixWord, tailWord_3096712, baseEnd_3096712] using wordTrace_append hprefix tailTrace_3096712
  have hstable : (prefixWord ++ tailWord_3096712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3096712).length < 2 ^ (prefixWord ++ tailWord_3096712).sum := by decide
  have hdescent : baseEnd_3096712 < baseStart_3096712 := by decide
  rcases family_descends (prefixWord ++ tailWord_3096712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3096778 : List Nat := [3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 5]
def baseStart_3096778 : Nat := 118140960795 + 3096778 * 2 ^ 59
def prefixEnd_3096778 : Nat := 4983230072969 + 3 ^ 40 * 3096778 * 2
def baseEnd_3096778 : Nat := 1590135594269190075533183

theorem tailTrace_3096778 : CollatzResearch.WordTrace tailWord_3096778 prefixEnd_3096778 1590135594269190075533183 := by
  unfold tailWord_3096778
  simp only [CollatzResearch.WordTrace]
  refine ⟨28237193193727417105154747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75299181849939778947079325 28237193193727417105154747)
  ·
    refine ⟨42355789790591125657732121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28237193193727417105154747 42355789790591125657732121)
    ·
      refine ⟨31766842342943344243299091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42355789790591125657732121 31766842342943344243299091)
      ·
        refine ⟨47650263514415016364948637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31766842342943344243299091 47650263514415016364948637)
        ·
          refine ⟨17868848817905631136855739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47650263514415016364948637 17868848817905631136855739)
          ·
            refine ⟨26803273226858446705283609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17868848817905631136855739 26803273226858446705283609)
            ·
              refine ⟨20102454920143835028962707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26803273226858446705283609 20102454920143835028962707)
              ·
                refine ⟨30153682380215752543444061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20102454920143835028962707 30153682380215752543444061)
                ·
                  refine ⟨11307630892580907203791523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30153682380215752543444061 11307630892580907203791523)
                  ·
                    refine ⟨16961446338871360805687285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11307630892580907203791523 16961446338871360805687285)
                    ·
                      refine ⟨1590135594269190075533183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16961446338871360805687285 1590135594269190075533183)
                      ·
                        rfl

theorem cell23_3096778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 5].length) (baseStart_3096778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3096778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3096778 prefixEnd_3096778 := by exact prefixLift 3096778
  have htrace : WordTrace (prefixWord ++ tailWord_3096778) baseStart_3096778 baseEnd_3096778 := by
    simpa [prefixWord, tailWord_3096778, baseEnd_3096778] using wordTrace_append hprefix tailTrace_3096778
  have hstable : (prefixWord ++ tailWord_3096778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3096778).length < 2 ^ (prefixWord ++ tailWord_3096778).sum := by decide
  have hdescent : baseEnd_3096778 < baseStart_3096778 := by decide
  rcases family_descends (prefixWord ++ tailWord_3096778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3096785 : List Nat := [1, 2, 2, 1, 2, 2, 4, 3, 2, 4]
def baseStart_3096785 : Nat := 118140960795 + 3096785 * 2 ^ 59
def prefixEnd_3096785 : Nat := 4983230072969 + 3 ^ 40 * 3096785 * 2
def baseEnd_3096785 : Nat := 530046396211257182715217

theorem tailTrace_3096785 : CollatzResearch.WordTrace tailWord_3096785 prefixEnd_3096785 530046396211257182715217 := by
  unfold tailWord_3096785
  simp only [CollatzResearch.WordTrace]
  refine ⟨112949028085884308616123809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75299352057256205744082539 112949028085884308616123809)
  ·
    refine ⟨84711771064413231462092857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112949028085884308616123809 84711771064413231462092857)
    ·
      refine ⟨63533828298309923596569643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84711771064413231462092857 63533828298309923596569643)
      ·
        refine ⟨95300742447464885394854465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63533828298309923596569643 95300742447464885394854465)
        ·
          refine ⟨71475556835598664046140849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95300742447464885394854465 71475556835598664046140849)
          ·
            refine ⟨53606667626698998034605637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71475556835598664046140849 53606667626698998034605637)
            ·
              refine ⟨10051250180006062131488557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53606667626698998034605637 10051250180006062131488557)
              ·
                refine ⟨3769218817502273299308209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10051250180006062131488557 3769218817502273299308209)
                ·
                  refine ⟨2826914113126704974481157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3769218817502273299308209 2826914113126704974481157)
                  ·
                    refine ⟨530046396211257182715217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2826914113126704974481157 530046396211257182715217)
                    ·
                      rfl

theorem cell23_3096785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 3, 2, 4].length) (baseStart_3096785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3096785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3096785 prefixEnd_3096785 := by exact prefixLift 3096785
  have htrace : WordTrace (prefixWord ++ tailWord_3096785) baseStart_3096785 baseEnd_3096785 := by
    simpa [prefixWord, tailWord_3096785, baseEnd_3096785] using wordTrace_append hprefix tailTrace_3096785
  have hstable : (prefixWord ++ tailWord_3096785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3096785).length < 2 ^ (prefixWord ++ tailWord_3096785).sum := by decide
  have hdescent : baseEnd_3096785 < baseStart_3096785 := by decide
  rcases family_descends (prefixWord ++ tailWord_3096785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3096792 : List Nat := [2, 1, 2, 2, 4, 1, 1, 1, 5, 2, 2]
def baseStart_3096792 : Nat := 118140960795 + 3096792 * 2 ^ 59
def prefixEnd_3096792 : Nat := 4983230072969 + 3 ^ 40 * 3096792 * 2
def baseEnd_3096792 : Nat := 1590142782998353020758119

theorem tailTrace_3096792 : CollatzResearch.WordTrace tailWord_3096792 prefixEnd_3096792 1590142782998353020758119 := by
  unfold tailWord_3096792
  simp only [CollatzResearch.WordTrace]
  refine ⟨56474641698429474405814315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75299522264572632541085753 56474641698429474405814315)
  ·
    refine ⟨84711962547644211608721473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56474641698429474405814315 84711962547644211608721473)
    ·
      refine ⟨63533971910733158706541105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84711962547644211608721473 63533971910733158706541105)
      ·
        refine ⟨47650478933049869029905829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63533971910733158706541105 47650478933049869029905829)
        ·
          refine ⟨8934464799946850443107343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47650478933049869029905829 8934464799946850443107343)
          ·
            refine ⟨13401697199920275664661015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8934464799946850443107343 13401697199920275664661015)
            ·
              refine ⟨20102545799880413496991523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13401697199920275664661015 20102545799880413496991523)
              ·
                refine ⟨30153818699820620245487285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20102545799880413496991523 30153818699820620245487285)
                ·
                  refine ⟨2826920503108183148014433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30153818699820620245487285 2826920503108183148014433)
                  ·
                    refine ⟨2120190377331137361010825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2826920503108183148014433 2120190377331137361010825)
                    ·
                      refine ⟨1590142782998353020758119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2120190377331137361010825 1590142782998353020758119)
                      ·
                        rfl

theorem cell23_3096792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 1, 5, 2, 2].length) (baseStart_3096792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3096792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3096792 prefixEnd_3096792 := by exact prefixLift 3096792
  have htrace : WordTrace (prefixWord ++ tailWord_3096792) baseStart_3096792 baseEnd_3096792 := by
    simpa [prefixWord, tailWord_3096792, baseEnd_3096792] using wordTrace_append hprefix tailTrace_3096792
  have hstable : (prefixWord ++ tailWord_3096792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3096792).length < 2 ^ (prefixWord ++ tailWord_3096792).sum := by decide
  have hdescent : baseEnd_3096792 < baseStart_3096792 := by decide
  rcases family_descends (prefixWord ++ tailWord_3096792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3096805 : List Nat := [1, 3, 1, 4, 2, 1, 2, 2, 1, 2, 4]
def baseStart_3096805 : Nat := 118140960795 + 3096805 * 2 ^ 59
def prefixEnd_3096805 : Nat := 4983230072969 + 3 ^ 40 * 3096805 * 2
def baseEnd_3096805 : Nat := 1590149458246861469895559

theorem tailTrace_3096805 : CollatzResearch.WordTrace tailWord_3096805 prefixEnd_3096805 1590149458246861469895559 := by
  unfold tailWord_3096805
  simp only [CollatzResearch.WordTrace]
  refine ⟨112949757545811852031851869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75299838363874568021234579 112949757545811852031851869)
  ·
    refine ⟨42356159079679444511944451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112949757545811852031851869 42356159079679444511944451)
    ·
      refine ⟨63534238619519166767916677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42356159079679444511944451 63534238619519166767916677)
      ·
        refine ⟨11912669741159843768984377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63534238619519166767916677 11912669741159843768984377)
        ·
          refine ⟨8934502305869882826738283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11912669741159843768984377 8934502305869882826738283)
          ·
            refine ⟨13401753458804824240107425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8934502305869882826738283 13401753458804824240107425)
            ·
              refine ⟨10051315094103618180080569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13401753458804824240107425 10051315094103618180080569)
              ·
                refine ⟨7538486320577713635060427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10051315094103618180080569 7538486320577713635060427)
                ·
                  refine ⟨11307729480866570452590641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7538486320577713635060427 11307729480866570452590641)
                  ·
                    refine ⟨8480797110649927839442981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11307729480866570452590641 8480797110649927839442981)
                    ·
                      refine ⟨1590149458246861469895559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8480797110649927839442981 1590149458246861469895559)
                      ·
                        rfl

theorem cell23_3096805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 2, 1, 2, 4].length) (baseStart_3096805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3096805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3096805 prefixEnd_3096805 := by exact prefixLift 3096805
  have htrace : WordTrace (prefixWord ++ tailWord_3096805) baseStart_3096805 baseEnd_3096805 := by
    simpa [prefixWord, tailWord_3096805, baseEnd_3096805] using wordTrace_append hprefix tailTrace_3096805
  have hstable : (prefixWord ++ tailWord_3096805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3096805).length < 2 ^ (prefixWord ++ tailWord_3096805).sum := by decide
  have hdescent : baseEnd_3096805 < baseStart_3096805 := by decide
  rcases family_descends (prefixWord ++ tailWord_3096805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3096839 : List Nat := [1, 1, 4, 5, 1, 2, 1, 1, 1, 2, 4]
def baseStart_3096839 : Nat := 118140960795 + 3096839 * 2 ^ 59
def prefixEnd_3096839 : Nat := 4983230072969 + 3 ^ 40 * 3096839 * 2
def baseEnd_3096839 : Nat := 1590166916589114336870403

theorem tailTrace_3096839 : CollatzResearch.WordTrace tailWord_3096839 prefixEnd_3096839 1590166916589114336870403 := by
  unfold tailWord_3096839
  simp only [CollatzResearch.WordTrace]
  refine ⟨112950997627688675838589571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75300665085125783892393047 112950997627688675838589571)
  ·
    refine ⟨169426496441533013757884357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112950997627688675838589571 169426496441533013757884357)
    ·
      refine ⟨31767468082787440079603317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 169426496441533013757884357 31767468082787440079603317)
      ·
        refine ⟨2978200132761322507462811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 31767468082787440079603317 2978200132761322507462811)
        ·
          refine ⟨4467300199141983761194217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2978200132761322507462811 4467300199141983761194217)
          ·
            refine ⟨3350475149356487820895663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4467300199141983761194217 3350475149356487820895663)
            ·
              refine ⟨5025712724034731731343495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3350475149356487820895663 5025712724034731731343495)
              ·
                refine ⟨7538569086052097597015243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5025712724034731731343495 7538569086052097597015243)
                ·
                  refine ⟨11307853629078146395522865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7538569086052097597015243 11307853629078146395522865)
                  ·
                    refine ⟨8480890221808609796642149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11307853629078146395522865 8480890221808609796642149)
                    ·
                      refine ⟨1590166916589114336870403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8480890221808609796642149 1590166916589114336870403)
                      ·
                        rfl

theorem cell23_3096839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_3096839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3096839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3096839 prefixEnd_3096839 := by exact prefixLift 3096839
  have htrace : WordTrace (prefixWord ++ tailWord_3096839) baseStart_3096839 baseEnd_3096839 := by
    simpa [prefixWord, tailWord_3096839, baseEnd_3096839] using wordTrace_append hprefix tailTrace_3096839
  have hstable : (prefixWord ++ tailWord_3096839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3096839).length < 2 ^ (prefixWord ++ tailWord_3096839).sum := by decide
  have hdescent : baseEnd_3096839 < baseStart_3096839 := by decide
  rcases family_descends (prefixWord ++ tailWord_3096839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3096842 : List Nat := [3, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3]
def baseStart_3096842 : Nat := 118140960795 + 3096842 * 2 ^ 59
def prefixEnd_3096842 : Nat := 4983230072969 + 3 ^ 40 * 3096842 * 2
def baseEnd_3096842 : Nat := 1590168457031077825132889

theorem tailTrace_3096842 : CollatzResearch.WordTrace tailWord_3096842 prefixEnd_3096842 1590168457031077825132889 := by
  unfold tailWord_3096842
  simp only [CollatzResearch.WordTrace]
  refine ⟨28237776761669451837737195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75300738031118538233965853 28237776761669451837737195)
  ·
    refine ⟨42356665142504177756605793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28237776761669451837737195 42356665142504177756605793)
    ·
      refine ⟨31767498856878133317454345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42356665142504177756605793 31767498856878133317454345)
      ·
        refine ⟨23825624142658599988090759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31767498856878133317454345 23825624142658599988090759)
        ·
          refine ⟨35738436213987899982136139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23825624142658599988090759 35738436213987899982136139)
          ·
            refine ⟨53607654320981849973204209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35738436213987899982136139 53607654320981849973204209)
            ·
              refine ⟨40205740740736387479903157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53607654320981849973204209 40205740740736387479903157)
              ·
                refine ⟨3769288194444036326240921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40205740740736387479903157 3769288194444036326240921)
                ·
                  refine ⟨2826966145833027244680691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3769288194444036326240921 2826966145833027244680691)
                  ·
                    refine ⟨4240449218749540867021037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2826966145833027244680691 4240449218749540867021037)
                    ·
                      refine ⟨1590168457031077825132889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4240449218749540867021037 1590168457031077825132889)
                      ·
                        rfl

theorem cell23_3096842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3].length) (baseStart_3096842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3096842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3096842 prefixEnd_3096842 := by exact prefixLift 3096842
  have htrace : WordTrace (prefixWord ++ tailWord_3096842) baseStart_3096842 baseEnd_3096842 := by
    simpa [prefixWord, tailWord_3096842, baseEnd_3096842] using wordTrace_append hprefix tailTrace_3096842
  have hstable : (prefixWord ++ tailWord_3096842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3096842).length < 2 ^ (prefixWord ++ tailWord_3096842).sum := by decide
  have hdescent : baseEnd_3096842 < baseStart_3096842 := by decide
  rcases family_descends (prefixWord ++ tailWord_3096842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3096885 : List Nat := [1, 3, 3, 1, 2, 1, 2, 1, 2, 4, 3]
def baseStart_3096885 : Nat := 118140960795 + 3096885 * 2 ^ 59
def prefixEnd_3096885 : Nat := 4983230072969 + 3 ^ 40 * 3096885 * 2
def baseEnd_3096885 : Nat := 1590190536699221156895191

theorem tailTrace_3096885 : CollatzResearch.WordTrace tailWord_3096885 prefixEnd_3096885 1590190536699221156895191 := by
  unfold tailWord_3096885
  simp only [CollatzResearch.WordTrace]
  refine ⟨112952675385522025694764109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75301783590348017129842739 112952675385522025694764109)
  ·
    refine ⟨42357253269570759635536541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112952675385522025694764109 42357253269570759635536541)
    ·
      refine ⟨15883969976089034863326203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42357253269570759635536541 15883969976089034863326203)
      ·
        refine ⟨23825954964133552294989305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15883969976089034863326203 23825954964133552294989305)
        ·
          refine ⟨17869466223100164221241979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23825954964133552294989305 17869466223100164221241979)
          ·
            refine ⟨26804199334650246331862969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17869466223100164221241979 26804199334650246331862969)
            ·
              refine ⟨20103149500987684748897227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26804199334650246331862969 20103149500987684748897227)
              ·
                refine ⟨30154724251481527123345841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20103149500987684748897227 30154724251481527123345841)
                ·
                  refine ⟨22616043188611145342509381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30154724251481527123345841 22616043188611145342509381)
                  ·
                    refine ⟨4240508097864589751720509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22616043188611145342509381 4240508097864589751720509)
                    ·
                      refine ⟨1590190536699221156895191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4240508097864589751720509 1590190536699221156895191)
                      ·
                        rfl

theorem cell23_3096885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 1, 2, 4, 3].length) (baseStart_3096885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3096885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3096885 prefixEnd_3096885 := by exact prefixLift 3096885
  have htrace : WordTrace (prefixWord ++ tailWord_3096885) baseStart_3096885 baseEnd_3096885 := by
    simpa [prefixWord, tailWord_3096885, baseEnd_3096885] using wordTrace_append hprefix tailTrace_3096885
  have hstable : (prefixWord ++ tailWord_3096885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3096885).length < 2 ^ (prefixWord ++ tailWord_3096885).sum := by decide
  have hdescent : baseEnd_3096885 < baseStart_3096885 := by decide
  rcases family_descends (prefixWord ++ tailWord_3096885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3096972 : List Nat := [2, 2, 1, 2, 1, 4, 3, 1, 2, 1, 4]
def baseStart_3096972 : Nat := 118140960795 + 3096972 * 2 ^ 59
def prefixEnd_3096972 : Nat := 4983230072969 + 3 ^ 40 * 3096972 * 2
def baseEnd_3096972 : Nat := 1590235209516162316507291

theorem tailTrace_3096972 : CollatzResearch.WordTrace tailWord_3096972 prefixEnd_3096972 1590235209516162316507291 := by
  unfold tailWord_3096972
  simp only [CollatzResearch.WordTrace]
  refine ⟨56477924268103419776590585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75303899024137893035454113 56477924268103419776590585)
  ·
    refine ⟨42358443201077564832442939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56477924268103419776590585 42358443201077564832442939)
    ·
      refine ⟨63537664801616347248664409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42358443201077564832442939 63537664801616347248664409)
      ·
        refine ⟨47653248601212260436498307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63537664801616347248664409 47653248601212260436498307)
        ·
          refine ⟨71479872901818390654747461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47653248601212260436498307 71479872901818390654747461)
          ·
            refine ⟨13402476169090948247765149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71479872901818390654747461 13402476169090948247765149)
            ·
              refine ⟨5025928563409105592911931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13402476169090948247765149 5025928563409105592911931)
              ·
                refine ⟨7538892845113658389367897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5025928563409105592911931 7538892845113658389367897)
                ·
                  refine ⟨5654169633835243792025923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7538892845113658389367897 5654169633835243792025923)
                  ·
                    refine ⟨8481254450752865688038885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5654169633835243792025923 8481254450752865688038885)
                    ·
                      refine ⟨1590235209516162316507291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8481254450752865688038885 1590235209516162316507291)
                      ·
                        rfl

theorem cell23_3096972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 3, 1, 2, 1, 4].length) (baseStart_3096972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3096972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3096972 prefixEnd_3096972 := by exact prefixLift 3096972
  have htrace : WordTrace (prefixWord ++ tailWord_3096972) baseStart_3096972 baseEnd_3096972 := by
    simpa [prefixWord, tailWord_3096972, baseEnd_3096972] using wordTrace_append hprefix tailTrace_3096972
  have hstable : (prefixWord ++ tailWord_3096972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3096972).length < 2 ^ (prefixWord ++ tailWord_3096972).sum := by decide
  have hdescent : baseEnd_3096972 < baseStart_3096972 := by decide
  rcases family_descends (prefixWord ++ tailWord_3096972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3096995 : List Nat := [1, 1, 1, 4, 1, 5, 1, 1, 8]
def baseStart_3096995 : Nat := 118140960795 + 3096995 * 2 ^ 59
def prefixEnd_3096995 : Nat := 4983230072969 + 3 ^ 40 * 3096995 * 2
def baseEnd_3096995 : Nat := 176694113285690636279965

theorem tailTrace_3096995 : CollatzResearch.WordTrace tailWord_3096995 prefixEnd_3096995 176694113285690636279965 := by
  unfold tailWord_3096995
  simp only [CollatzResearch.WordTrace]
  refine ⟨112956687415123514481268439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75304458276749009654178959 112956687415123514481268439)
  ·
    refine ⟨169435031122685271721902659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112956687415123514481268439 169435031122685271721902659)
    ·
      refine ⟨254152546684027907582853989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169435031122685271721902659 254152546684027907582853989)
      ·
        refine ⟨47653602503255232671785123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 254152546684027907582853989 47653602503255232671785123)
        ·
          refine ⟨71480403754882849007677685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47653602503255232671785123 71480403754882849007677685)
          ·
            refine ⟨6701287852020267094469783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 71480403754882849007677685 6701287852020267094469783)
            ·
              refine ⟨10051931778030400641704675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6701287852020267094469783 10051931778030400641704675)
              ·
                refine ⟨15077897667045600962557013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10051931778030400641704675 15077897667045600962557013)
                ·
                  refine ⟨176694113285690636279965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15077897667045600962557013 176694113285690636279965)
                  ·
                    rfl

theorem cell23_3096995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 1, 8].length) (baseStart_3096995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3096995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3096995 prefixEnd_3096995 := by exact prefixLift 3096995
  have htrace : WordTrace (prefixWord ++ tailWord_3096995) baseStart_3096995 baseEnd_3096995 := by
    simpa [prefixWord, tailWord_3096995, baseEnd_3096995] using wordTrace_append hprefix tailTrace_3096995
  have hstable : (prefixWord ++ tailWord_3096995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3096995).length < 2 ^ (prefixWord ++ tailWord_3096995).sum := by decide
  have hdescent : baseEnd_3096995 < baseStart_3096995 := by decide
  rcases family_descends (prefixWord ++ tailWord_3096995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3096999 : List Nat := [1, 1, 6, 1, 1, 3, 2, 1, 3, 4]
def baseStart_3096999 : Nat := 118140960795 + 3096999 * 2 ^ 59
def prefixEnd_3096999 : Nat := 4983230072969 + 3 ^ 40 * 3096999 * 2
def baseEnd_3096999 : Nat := 530083024497944570289889

theorem tailTrace_3096999 : CollatzResearch.WordTrace tailWord_3096999 prefixEnd_3096999 530083024497944570289889 := by
  unfold tailWord_3096999
  simp only [CollatzResearch.WordTrace]
  refine ⟨112956833307109023164414051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75304555538072682109609367 112956833307109023164414051)
  ·
    refine ⟨169435249960663534746621077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112956833307109023164414051 169435249960663534746621077)
    ·
      refine ⟨7942277341906103191247863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 169435249960663534746621077 7942277341906103191247863)
      ·
        refine ⟨11913416012859154786871795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7942277341906103191247863 11913416012859154786871795)
        ·
          refine ⟨17870124019288732180307693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11913416012859154786871795 17870124019288732180307693)
          ·
            refine ⟨6701296507233274567615385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17870124019288732180307693 6701296507233274567615385)
            ·
              refine ⟨5025972380424955925711539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6701296507233274567615385 5025972380424955925711539)
              ·
                refine ⟨7538958570637433888567309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5025972380424955925711539 7538958570637433888567309)
                ·
                  refine ⟨2827109463989037708212741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7538958570637433888567309 2827109463989037708212741)
                  ·
                    refine ⟨530083024497944570289889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2827109463989037708212741 530083024497944570289889)
                    ·
                      rfl

theorem cell23_3096999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 2, 1, 3, 4].length) (baseStart_3096999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3096999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3096999 prefixEnd_3096999 := by exact prefixLift 3096999
  have htrace : WordTrace (prefixWord ++ tailWord_3096999) baseStart_3096999 baseEnd_3096999 := by
    simpa [prefixWord, tailWord_3096999, baseEnd_3096999] using wordTrace_append hprefix tailTrace_3096999
  have hstable : (prefixWord ++ tailWord_3096999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3096999).length < 2 ^ (prefixWord ++ tailWord_3096999).sum := by decide
  have hdescent : baseEnd_3096999 < baseStart_3096999 := by decide
  rcases family_descends (prefixWord ++ tailWord_3096999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3097049 : List Nat := [1, 2, 1, 2, 4, 1, 3, 2, 2, 3, 2]
def baseStart_3097049 : Nat := 118140960795 + 3097049 * 2 ^ 59
def prefixEnd_3097049 : Nat := 4983230072969 + 3 ^ 40 * 3097049 * 2
def baseEnd_3097049 : Nat := 1590274747526558515244437

theorem tailTrace_3097049 : CollatzResearch.WordTrace tailWord_3097049 prefixEnd_3097049 1590274747526558515244437 := by
  unfold tailWord_3097049
  simp only [CollatzResearch.WordTrace]
  refine ⟨112958656956927881703734201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75305771304618587802489467 112958656956927881703734201)
  ·
    refine ⟨84718992717695911277800651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112958656956927881703734201 84718992717695911277800651)
    ·
      refine ⟨127078489076543866916700977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84718992717695911277800651 127078489076543866916700977)
      ·
        refine ⟨95308866807407900187525733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127078489076543866916700977 95308866807407900187525733)
        ·
          refine ⟨17870412526388981285161075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 95308866807407900187525733 17870412526388981285161075)
          ·
            refine ⟨26805618789583471927741613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17870412526388981285161075 26805618789583471927741613)
            ·
              refine ⟨10052107046093801972903105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26805618789583471927741613 10052107046093801972903105)
              ·
                refine ⟨7539080284570351479677329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10052107046093801972903105 7539080284570351479677329)
                ·
                  refine ⟨5654310213427763609757997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7539080284570351479677329 5654310213427763609757997)
                  ·
                    refine ⟨2120366330035411353659249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5654310213427763609757997 2120366330035411353659249)
                    ·
                      refine ⟨1590274747526558515244437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2120366330035411353659249 1590274747526558515244437)
                      ·
                        rfl

theorem cell23_3097049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 2, 2, 3, 2].length) (baseStart_3097049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3097049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3097049 prefixEnd_3097049 := by exact prefixLift 3097049
  have htrace : WordTrace (prefixWord ++ tailWord_3097049) baseStart_3097049 baseEnd_3097049 := by
    simpa [prefixWord, tailWord_3097049, baseEnd_3097049] using wordTrace_append hprefix tailTrace_3097049
  have hstable : (prefixWord ++ tailWord_3097049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3097049).length < 2 ^ (prefixWord ++ tailWord_3097049).sum := by decide
  have hdescent : baseEnd_3097049 < baseStart_3097049 := by decide
  rcases family_descends (prefixWord ++ tailWord_3097049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3097065 : List Nat := [1, 2, 1, 1, 1, 2, 1, 5, 3, 1, 5]
def baseStart_3097065 : Nat := 118140960795 + 3097065 * 2 ^ 59
def prefixEnd_3097065 : Nat := 4983230072969 + 3 ^ 40 * 3097065 * 2
def baseEnd_3097065 : Nat := 1590282963217030452644363

theorem tailTrace_3097065 : CollatzResearch.WordTrace tailWord_3097065 prefixEnd_3097065 1590282963217030452644363 := by
  unfold tailWord_3097065
  simp only [CollatzResearch.WordTrace]
  refine ⟨112959240524869916436316649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75306160349913277624211099 112959240524869916436316649)
  ·
    refine ⟨84719430393652437327237487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112959240524869916436316649 84719430393652437327237487)
    ·
      refine ⟨127079145590478655990856231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84719430393652437327237487 127079145590478655990856231)
      ·
        refine ⟨190618718385717983986284347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127079145590478655990856231 190618718385717983986284347)
        ·
          refine ⟨285928077578576975979426521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190618718385717983986284347 285928077578576975979426521)
          ·
            refine ⟨214446058183932731984569891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 285928077578576975979426521 214446058183932731984569891)
            ·
              refine ⟨321669087275899097976854837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 214446058183932731984569891 321669087275899097976854837)
              ·
                refine ⟨30156476932115540435330141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 321669087275899097976854837 30156476932115540435330141)
                ·
                  refine ⟨11308678849543327663248803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30156476932115540435330141 11308678849543327663248803)
                  ·
                    refine ⟨16963018274314991494873205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11308678849543327663248803 16963018274314991494873205)
                    ·
                      refine ⟨1590282963217030452644363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16963018274314991494873205 1590282963217030452644363)
                      ·
                        rfl

theorem cell23_3097065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 5, 3, 1, 5].length) (baseStart_3097065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3097065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3097065 prefixEnd_3097065 := by exact prefixLift 3097065
  have htrace : WordTrace (prefixWord ++ tailWord_3097065) baseStart_3097065 baseEnd_3097065 := by
    simpa [prefixWord, tailWord_3097065, baseEnd_3097065] using wordTrace_append hprefix tailTrace_3097065
  have hstable : (prefixWord ++ tailWord_3097065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3097065).length < 2 ^ (prefixWord ++ tailWord_3097065).sum := by decide
  have hdescent : baseEnd_3097065 < baseStart_3097065 := by decide
  rcases family_descends (prefixWord ++ tailWord_3097065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3097075 : List Nat := [1, 1, 1, 2, 2, 2, 3, 3, 1, 1, 6]
def baseStart_3097075 : Nat := 118140960795 + 3097075 * 2 ^ 59
def prefixEnd_3097075 : Nat := 4983230072969 + 3 ^ 40 * 3097075 * 2
def baseEnd_3097075 : Nat := 1590288098023575413519317

theorem tailTrace_3097075 : CollatzResearch.WordTrace tailWord_3097075 prefixEnd_3097075 1590288098023575413519317 := by
  unfold tailWord_3097075
  simp only [CollatzResearch.WordTrace]
  refine ⟨112959605254833688144180679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75306403503222458762787119 112959605254833688144180679)
  ·
    refine ⟨169439407882250532216271019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112959605254833688144180679 169439407882250532216271019)
    ·
      refine ⟨254159111823375798324406529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169439407882250532216271019 254159111823375798324406529)
      ·
        refine ⟨190619333867531848743304897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 254159111823375798324406529 190619333867531848743304897)
        ·
          refine ⟨142964500400648886557478673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 190619333867531848743304897 142964500400648886557478673)
          ·
            refine ⟨107223375300486664918109005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142964500400648886557478673 107223375300486664918109005)
            ·
              refine ⟨40208765737682499344290877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 107223375300486664918109005 40208765737682499344290877)
              ·
                refine ⟨15078287151630937254109079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40208765737682499344290877 15078287151630937254109079)
                ·
                  refine ⟨22617430727446405881163619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15078287151630937254109079 22617430727446405881163619)
                  ·
                    refine ⟨33926146091169608821745429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22617430727446405881163619 33926146091169608821745429)
                    ·
                      refine ⟨1590288098023575413519317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33926146091169608821745429 1590288098023575413519317)
                      ·
                        rfl

theorem cell23_3097075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 3, 1, 1, 6].length) (baseStart_3097075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3097075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3097075 prefixEnd_3097075 := by exact prefixLift 3097075
  have htrace : WordTrace (prefixWord ++ tailWord_3097075) baseStart_3097075 baseEnd_3097075 := by
    simpa [prefixWord, tailWord_3097075, baseEnd_3097075] using wordTrace_append hprefix tailTrace_3097075
  have hstable : (prefixWord ++ tailWord_3097075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3097075).length < 2 ^ (prefixWord ++ tailWord_3097075).sum := by decide
  have hdescent : baseEnd_3097075 < baseStart_3097075 := by decide
  rcases family_descends (prefixWord ++ tailWord_3097075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3097085 : List Nat := [1, 4, 1, 1, 1, 3, 1, 11]
def baseStart_3097085 : Nat := 118140960795 + 3097085 * 2 ^ 59
def prefixEnd_3097085 : Nat := 4983230072969 + 3 ^ 40 * 3097085 * 2
def baseEnd_3097085 : Nat := 58899749364078532384973

theorem tailTrace_3097085 : CollatzResearch.WordTrace tailWord_3097085 prefixEnd_3097085 58899749364078532384973 := by
  unfold tailWord_3097085
  simp only [CollatzResearch.WordTrace]
  refine ⟨112959969984797459852044709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75306646656531639901363139 112959969984797459852044709)
  ·
    refine ⟨21179994372149523722258383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 112959969984797459852044709 21179994372149523722258383)
    ·
      refine ⟨31769991558224285583387575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21179994372149523722258383 31769991558224285583387575)
      ·
        refine ⟨47654987337336428375081363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31769991558224285583387575 47654987337336428375081363)
        ·
          refine ⟨71482481006004642562622045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47654987337336428375081363 71482481006004642562622045)
          ·
            refine ⟨26805930377251740960983267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71482481006004642562622045 26805930377251740960983267)
            ·
              refine ⟨40208895565877611441474901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26805930377251740960983267 40208895565877611441474901)
              ·
                refine ⟨58899749364078532384973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 40208895565877611441474901 58899749364078532384973)
                ·
                  rfl

theorem cell23_3097085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 11].length) (baseStart_3097085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3097085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3097085 prefixEnd_3097085 := by exact prefixLift 3097085
  have htrace : WordTrace (prefixWord ++ tailWord_3097085) baseStart_3097085 baseEnd_3097085 := by
    simpa [prefixWord, tailWord_3097085, baseEnd_3097085] using wordTrace_append hprefix tailTrace_3097085
  have hstable : (prefixWord ++ tailWord_3097085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3097085).length < 2 ^ (prefixWord ++ tailWord_3097085).sum := by decide
  have hdescent : baseEnd_3097085 < baseStart_3097085 := by decide
  rcases family_descends (prefixWord ++ tailWord_3097085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3097099 : List Nat := [1, 1, 1, 1, 7, 3, 1, 1, 1, 1, 5]
def baseStart_3097099 : Nat := 118140960795 + 3097099 * 2 ^ 59
def prefixEnd_3097099 : Nat := 4983230072969 + 3 ^ 40 * 3097099 * 2
def baseEnd_3097099 : Nat := 1590300421559283319619207

theorem tailTrace_3097099 : CollatzResearch.WordTrace tailWord_3097099 prefixEnd_3097099 1590300421559283319619207 := by
  unfold tailWord_3097099
  simp only [CollatzResearch.WordTrace]
  refine ⟨112960480606746740243054351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75306987071164493495369567 112960480606746740243054351)
  ·
    refine ⟨169440720910120110364581527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112960480606746740243054351 169440720910120110364581527)
    ·
      refine ⟨254161081365180165546872291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169440720910120110364581527 254161081365180165546872291)
      ·
        refine ⟨381241622047770248320308437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254161081365180165546872291 381241622047770248320308437)
        ·
          refine ⟨8935350516744615195007229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 381241622047770248320308437 8935350516744615195007229)
          ·
            refine ⟨3350756443779230698127711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8935350516744615195007229 3350756443779230698127711)
            ·
              refine ⟨5026134665668846047191567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3350756443779230698127711 5026134665668846047191567)
              ·
                refine ⟨7539201998503269070787351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5026134665668846047191567 7539201998503269070787351)
                ·
                  refine ⟨11308802997754903606181027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7539201998503269070787351 11308802997754903606181027)
                  ·
                    refine ⟨16963204496632355409271541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11308802997754903606181027 16963204496632355409271541)
                    ·
                      refine ⟨1590300421559283319619207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16963204496632355409271541 1590300421559283319619207)
                      ·
                        rfl

theorem cell23_3097099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 1, 1, 1, 1, 5].length) (baseStart_3097099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3097099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3097099 prefixEnd_3097099 := by exact prefixLift 3097099
  have htrace : WordTrace (prefixWord ++ tailWord_3097099) baseStart_3097099 baseEnd_3097099 := by
    simpa [prefixWord, tailWord_3097099, baseEnd_3097099] using wordTrace_append hprefix tailTrace_3097099
  have hstable : (prefixWord ++ tailWord_3097099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3097099).length < 2 ^ (prefixWord ++ tailWord_3097099).sum := by decide
  have hdescent : baseEnd_3097099 < baseStart_3097099 := by decide
  rcases family_descends (prefixWord ++ tailWord_3097099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3097105 : List Nat := [1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 6]
def baseStart_3097105 : Nat := 118140960795 + 3097105 * 2 ^ 59
def prefixEnd_3097105 : Nat := 4983230072969 + 3 ^ 40 * 3097105 * 2
def baseEnd_3097105 : Nat := 1590303502443210296144179

theorem tailTrace_3097105 : CollatzResearch.WordTrace tailWord_3097105 prefixEnd_3097105 1590303502443210296144179 := by
  unfold tailWord_3097105
  simp only [CollatzResearch.WordTrace]
  refine ⟨112960699444725003267772769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75307132963150002178515179 112960699444725003267772769)
  ·
    refine ⟨84720524583543752450829577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112960699444725003267772769 84720524583543752450829577)
    ·
      refine ⟨63540393437657814338122183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84720524583543752450829577 63540393437657814338122183)
      ·
        refine ⟨95310590156486721507183275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63540393437657814338122183 95310590156486721507183275)
        ·
          refine ⟨142965885234730082260774913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95310590156486721507183275 142965885234730082260774913)
          ·
            refine ⟨107224413926047561695581185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142965885234730082260774913 107224413926047561695581185)
            ·
              refine ⟨80418310444535671271685889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107224413926047561695581185 80418310444535671271685889)
              ·
                refine ⟨60313732833401753453764417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80418310444535671271685889 60313732833401753453764417)
                ·
                  refine ⟨45235299625051315090323313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60313732833401753453764417 45235299625051315090323313)
                  ·
                    refine ⟨33926474718788486317742485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45235299625051315090323313 33926474718788486317742485)
                    ·
                      refine ⟨1590303502443210296144179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33926474718788486317742485 1590303502443210296144179)
                      ·
                        rfl

theorem cell23_3097105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 6].length) (baseStart_3097105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3097105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3097105 prefixEnd_3097105 := by exact prefixLift 3097105
  have htrace : WordTrace (prefixWord ++ tailWord_3097105) baseStart_3097105 baseEnd_3097105 := by
    simpa [prefixWord, tailWord_3097105, baseEnd_3097105] using wordTrace_append hprefix tailTrace_3097105
  have hstable : (prefixWord ++ tailWord_3097105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3097105).length < 2 ^ (prefixWord ++ tailWord_3097105).sum := by decide
  have hdescent : baseEnd_3097105 < baseStart_3097105 := by decide
  rcases family_descends (prefixWord ++ tailWord_3097105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3097139 : List Nat := [1, 1, 1, 2, 4, 2, 1, 3, 3, 3, 2]
def baseStart_3097139 : Nat := 118140960795 + 3097139 * 2 ^ 59
def prefixEnd_3097139 : Nat := 4983230072969 + 3 ^ 40 * 3097139 * 2
def baseEnd_3097139 : Nat := 1590320960785463163119023

theorem tailTrace_3097139 : CollatzResearch.WordTrace tailWord_3097139 prefixEnd_3097139 1590320960785463163119023 := by
  unfold tailWord_3097139
  simp only [CollatzResearch.WordTrace]
  refine ⟨112961939526601827074510471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75307959684401218049673647 112961939526601827074510471)
  ·
    refine ⟨169442909289902740611765707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112961939526601827074510471 169442909289902740611765707)
    ·
      refine ⟨254164363934854110917648561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169442909289902740611765707 254164363934854110917648561)
      ·
        refine ⟨190623272951140583188236421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 254164363934854110917648561 190623272951140583188236421)
        ·
          refine ⟨35741863678338859347794329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 190623272951140583188236421 35741863678338859347794329)
          ·
            refine ⟨26806397758754144510845747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35741863678338859347794329 26806397758754144510845747)
            ·
              refine ⟨40209596638131216766268621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26806397758754144510845747 40209596638131216766268621)
              ·
                refine ⟨15078598739299206287350733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40209596638131216766268621 15078598739299206287350733)
                ·
                  refine ⟨5654474527237202357756525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15078598739299206287350733 5654474527237202357756525)
                  ·
                    refine ⟨2120427947713950884158697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5654474527237202357756525 2120427947713950884158697)
                    ·
                      refine ⟨1590320960785463163119023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2120427947713950884158697 1590320960785463163119023)
                      ·
                        rfl

theorem cell23_3097139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 3, 3, 3, 2].length) (baseStart_3097139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3097139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3097139 prefixEnd_3097139 := by exact prefixLift 3097139
  have htrace : WordTrace (prefixWord ++ tailWord_3097139) baseStart_3097139 baseEnd_3097139 := by
    simpa [prefixWord, tailWord_3097139, baseEnd_3097139] using wordTrace_append hprefix tailTrace_3097139
  have hstable : (prefixWord ++ tailWord_3097139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3097139).length < 2 ^ (prefixWord ++ tailWord_3097139).sum := by decide
  have hdescent : baseEnd_3097139 < baseStart_3097139 := by decide
  rcases family_descends (prefixWord ++ tailWord_3097139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3097162 : List Nat := [3, 1, 2, 1, 1, 4, 1, 2, 2, 6]
def baseStart_3097162 : Nat := 118140960795 + 3097162 * 2 ^ 59
def prefixEnd_3097162 : Nat := 4983230072969 + 3 ^ 40 * 3097162 * 2
def baseEnd_3097162 : Nat := 530110923613505524377139

theorem tailTrace_3097162 : CollatzResearch.WordTrace tailWord_3097162 prefixEnd_3097162 530110923613505524377139 := by
  unfold tailWord_3097162
  simp only [CollatzResearch.WordTrace]
  refine ⟨28240694601379625500649435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75308518937012334668398493 28240694601379625500649435)
  ·
    refine ⟨42361041902069438250974153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28240694601379625500649435 42361041902069438250974153)
    ·
      refine ⟨31770781426552078688230615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42361041902069438250974153 31770781426552078688230615)
      ·
        refine ⟨47656172139828118032345923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31770781426552078688230615 47656172139828118032345923)
        ·
          refine ⟨71484258209742177048518885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47656172139828118032345923 71484258209742177048518885)
          ·
            refine ⟨13403298414326658196597291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71484258209742177048518885 13403298414326658196597291)
            ·
              refine ⟨20104947621489987294895937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13403298414326658196597291 20104947621489987294895937)
              ·
                refine ⟨15078710716117490471171953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20104947621489987294895937 15078710716117490471171953)
                ·
                  refine ⟨11309033037088117853378965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15078710716117490471171953 11309033037088117853378965)
                  ·
                    refine ⟨530110923613505524377139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11309033037088117853378965 530110923613505524377139)
                    ·
                      rfl

theorem cell23_3097162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 2, 2, 6].length) (baseStart_3097162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3097162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3097162 prefixEnd_3097162 := by exact prefixLift 3097162
  have htrace : WordTrace (prefixWord ++ tailWord_3097162) baseStart_3097162 baseEnd_3097162 := by
    simpa [prefixWord, tailWord_3097162, baseEnd_3097162] using wordTrace_append hprefix tailTrace_3097162
  have hstable : (prefixWord ++ tailWord_3097162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3097162).length < 2 ^ (prefixWord ++ tailWord_3097162).sum := by decide
  have hdescent : baseEnd_3097162 < baseStart_3097162 := by decide
  rcases family_descends (prefixWord ++ tailWord_3097162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3097180 : List Nat := [2, 2, 4, 1, 3, 1, 3, 1, 2, 1, 3]
def baseStart_3097180 : Nat := 118140960795 + 3097180 * 2 ^ 59
def prefixEnd_3097180 : Nat := 4983230072969 + 3 ^ 40 * 3097180 * 2
def baseEnd_3097180 : Nat := 1590342013492297502706335

theorem tailTrace_3097180 : CollatzResearch.WordTrace tailWord_3097180 prefixEnd_3097180 1590342013492297502706335 := by
  unfold tailWord_3097180
  simp only [CollatzResearch.WordTrace]
  refine ⟨56481717459726645538376497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75308956612968860717835329 56481717459726645538376497)
  ·
    refine ⟨42361288094794984153782373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56481717459726645538376497 42361288094794984153782373)
    ·
      refine ⟨7942741517774059528834195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42361288094794984153782373 7942741517774059528834195)
      ·
        refine ⟨11914112276661089293251293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7942741517774059528834195 11914112276661089293251293)
        ·
          refine ⟨4467792103747908484969235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11914112276661089293251293 4467792103747908484969235)
          ·
            refine ⟨6701688155621862727453853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4467792103747908484969235 6701688155621862727453853)
            ·
              refine ⟨2513133058358198522795195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6701688155621862727453853 2513133058358198522795195)
              ·
                refine ⟨3769699587537297784192793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2513133058358198522795195 3769699587537297784192793)
                ·
                  refine ⟨2827274690652973338144595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3769699587537297784192793 2827274690652973338144595)
                  ·
                    refine ⟨4240912035979460007216893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2827274690652973338144595 4240912035979460007216893)
                    ·
                      refine ⟨1590342013492297502706335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4240912035979460007216893 1590342013492297502706335)
                      ·
                        rfl

theorem cell23_3097180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 3, 1, 2, 1, 3].length) (baseStart_3097180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3097180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3097180 prefixEnd_3097180 := by exact prefixLift 3097180
  have htrace : WordTrace (prefixWord ++ tailWord_3097180) baseStart_3097180 baseEnd_3097180 := by
    simpa [prefixWord, tailWord_3097180, baseEnd_3097180] using wordTrace_append hprefix tailTrace_3097180
  have hstable : (prefixWord ++ tailWord_3097180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3097180).length < 2 ^ (prefixWord ++ tailWord_3097180).sum := by decide
  have hdescent : baseEnd_3097180 < baseStart_3097180 := by decide
  rcases family_descends (prefixWord ++ tailWord_3097180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3097206 : List Nat := [5, 1, 1, 2, 3, 1, 1, 1, 2, 1, 5]
def baseStart_3097206 : Nat := 118140960795 + 3097206 * 2 ^ 59
def prefixEnd_3097206 : Nat := 4983230072969 + 3 ^ 40 * 3097206 * 2
def baseEnd_3097206 : Nat := 1590355363989314400981215

theorem tailTrace_3097206 : CollatzResearch.WordTrace tailWord_3097206 prefixEnd_3097206 1590355363989314400981215 := by
  unfold tailWord_3097206
  simp only [CollatzResearch.WordTrace]
  refine ⟨7060273951084943594824967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 75309588811572731678132981 7060273951084943594824967)
  ·
    refine ⟨10590410926627415392237451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7060273951084943594824967 10590410926627415392237451)
    ·
      refine ⟨15885616389941123088356177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10590410926627415392237451 15885616389941123088356177)
      ·
        refine ⟨11914212292455842316267133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15885616389941123088356177 11914212292455842316267133)
        ·
          refine ⟨4467829609670940868600175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11914212292455842316267133 4467829609670940868600175)
          ·
            refine ⟨6701744414506411302900263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4467829609670940868600175 6701744414506411302900263)
            ·
              refine ⟨10052616621759616954350395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6701744414506411302900263 10052616621759616954350395)
              ·
                refine ⟨15078924932639425431525593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10052616621759616954350395 15078924932639425431525593)
                ·
                  refine ⟨11309193699479569073644195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15078924932639425431525593 11309193699479569073644195)
                  ·
                    refine ⟨16963790549219353610466293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11309193699479569073644195 16963790549219353610466293)
                    ·
                      refine ⟨1590355363989314400981215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16963790549219353610466293 1590355363989314400981215)
                      ·
                        rfl

theorem cell23_3097206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 1, 2, 1, 5].length) (baseStart_3097206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3097206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3097206 prefixEnd_3097206 := by exact prefixLift 3097206
  have htrace : WordTrace (prefixWord ++ tailWord_3097206) baseStart_3097206 baseEnd_3097206 := by
    simpa [prefixWord, tailWord_3097206, baseEnd_3097206] using wordTrace_append hprefix tailTrace_3097206
  have hstable : (prefixWord ++ tailWord_3097206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3097206).length < 2 ^ (prefixWord ++ tailWord_3097206).sum := by decide
  have hdescent : baseEnd_3097206 < baseStart_3097206 := by decide
  rcases family_descends (prefixWord ++ tailWord_3097206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3097226 : List Nat := [3, 1, 2, 3, 3, 2, 1, 1, 7]
def baseStart_3097226 : Nat := 118140960795 + 3097226 * 2 ^ 59
def prefixEnd_3097226 : Nat := 4983230072969 + 3 ^ 40 * 3097226 * 2
def baseEnd_3097226 : Nat := 176707292622489369192347

theorem tailTrace_3097226 : CollatzResearch.WordTrace tailWord_3097226 prefixEnd_3097226 176707292622489369192347 := by
  unfold tailWord_3097226
  simp only [CollatzResearch.WordTrace]
  refine ⟨28241278169321660233231883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75310075118191093955285021 28241278169321660233231883)
  ·
    refine ⟨42361917253982490349847825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28241278169321660233231883 42361917253982490349847825)
    ·
      refine ⟨31771437940486867762385869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42361917253982490349847825 31771437940486867762385869)
      ·
        refine ⟨11914289227682575410894701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31771437940486867762385869 11914289227682575410894701)
        ·
          refine ⟨4467858460380965779085513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11914289227682575410894701 4467858460380965779085513)
          ·
            refine ⟨3350893845285724334314135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4467858460380965779085513 3350893845285724334314135)
            ·
              refine ⟨5026340767928586501471203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3350893845285724334314135 5026340767928586501471203)
              ·
                refine ⟨7539511151892879752206805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5026340767928586501471203 7539511151892879752206805)
                ·
                  refine ⟨176707292622489369192347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7539511151892879752206805 176707292622489369192347)
                  ·
                    rfl

theorem cell23_3097226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 1, 1, 7].length) (baseStart_3097226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3097226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3097226 prefixEnd_3097226 := by exact prefixLift 3097226
  have htrace : WordTrace (prefixWord ++ tailWord_3097226) baseStart_3097226 baseEnd_3097226 := by
    simpa [prefixWord, tailWord_3097226, baseEnd_3097226] using wordTrace_append hprefix tailTrace_3097226
  have hstable : (prefixWord ++ tailWord_3097226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3097226).length < 2 ^ (prefixWord ++ tailWord_3097226).sum := by decide
  have hdescent : baseEnd_3097226 < baseStart_3097226 := by decide
  rcases family_descends (prefixWord ++ tailWord_3097226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3097276 : List Nat := [2, 2, 2, 3, 1, 1, 2, 2, 2, 4, 2]
def baseStart_3097276 : Nat := 118140960795 + 3097276 * 2 ^ 59
def prefixEnd_3097276 : Nat := 4983230072969 + 3 ^ 40 * 3097276 * 2
def baseEnd_3097276 : Nat := 1590391307635129127105893

theorem tailTrace_3097276 : CollatzResearch.WordTrace tailWord_3097276 prefixEnd_3097276 1590391307635129127105893 := by
  unfold tailWord_3097276
  simp only [CollatzResearch.WordTrace]
  refine ⟨56483468163552749736123841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75311290884736999648165121 56483468163552749736123841)
  ·
    refine ⟨42362601122664562302092881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56483468163552749736123841 42362601122664562302092881)
    ·
      refine ⟨31771950841998421726569661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42362601122664562302092881 31771950841998421726569661)
      ·
        refine ⟨11914481565749408147463623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31771950841998421726569661 11914481565749408147463623)
        ·
          refine ⟨17871722348624112221195435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11914481565749408147463623 17871722348624112221195435)
          ·
            refine ⟨26807583522936168331793153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17871722348624112221195435 26807583522936168331793153)
            ·
              refine ⟨20105687642202126248844865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26807583522936168331793153 20105687642202126248844865)
              ·
                refine ⟨15079265731651594686633649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20105687642202126248844865 15079265731651594686633649)
                ·
                  refine ⟨11309449298738696014975237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15079265731651594686633649 11309449298738696014975237)
                  ·
                    refine ⟨2120521743513505502807857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11309449298738696014975237 2120521743513505502807857)
                    ·
                      refine ⟨1590391307635129127105893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2120521743513505502807857 1590391307635129127105893)
                      ·
                        rfl

theorem cell23_3097276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 2, 2, 4, 2].length) (baseStart_3097276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3097276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3097276 prefixEnd_3097276 := by exact prefixLift 3097276
  have htrace : WordTrace (prefixWord ++ tailWord_3097276) baseStart_3097276 baseEnd_3097276 := by
    simpa [prefixWord, tailWord_3097276, baseEnd_3097276] using wordTrace_append hprefix tailTrace_3097276
  have hstable : (prefixWord ++ tailWord_3097276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3097276).length < 2 ^ (prefixWord ++ tailWord_3097276).sum := by decide
  have hdescent : baseEnd_3097276 < baseStart_3097276 := by decide
  rcases family_descends (prefixWord ++ tailWord_3097276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3097313 : List Nat := [1, 2, 3, 1, 4, 3, 1, 1, 2, 2, 3]
def baseStart_3097313 : Nat := 118140960795 + 3097313 * 2 ^ 59
def prefixEnd_3097313 : Nat := 4983230072969 + 3 ^ 40 * 3097313 * 2
def baseEnd_3097313 : Nat := 1590410306419345482343223

theorem tailTrace_3097313 : CollatzResearch.WordTrace tailWord_3097313 prefixEnd_3097313 1590410306419345482343223 := by
  unfold tailWord_3097313
  simp only [CollatzResearch.WordTrace]
  refine ⟨112968285827971454791344593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75312190551980969860896395 112968285827971454791344593)
  ·
    refine ⟨84726214370978591093508445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112968285827971454791344593 84726214370978591093508445)
    ·
      refine ⟨31772330389116971660065667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84726214370978591093508445 31772330389116971660065667)
      ·
        refine ⟨47658495583675457490098501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31772330389116971660065667 47658495583675457490098501)
        ·
          refine ⟨8935967921939148279393469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47658495583675457490098501 8935967921939148279393469)
          ·
            refine ⟨3350987970727180604772551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8935967921939148279393469 3350987970727180604772551)
            ·
              refine ⟨5026481956090770907158827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3350987970727180604772551 5026481956090770907158827)
              ·
                refine ⟨7539722934136156360738241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5026481956090770907158827 7539722934136156360738241)
                ·
                  refine ⟨5654792200602117270553681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7539722934136156360738241 5654792200602117270553681)
                  ·
                    refine ⟨4241094150451587952915261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5654792200602117270553681 4241094150451587952915261)
                    ·
                      refine ⟨1590410306419345482343223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4241094150451587952915261 1590410306419345482343223)
                      ·
                        rfl

theorem cell23_3097313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 1, 1, 2, 2, 3].length) (baseStart_3097313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3097313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3097313 prefixEnd_3097313 := by exact prefixLift 3097313
  have htrace : WordTrace (prefixWord ++ tailWord_3097313) baseStart_3097313 baseEnd_3097313 := by
    simpa [prefixWord, tailWord_3097313, baseEnd_3097313] using wordTrace_append hprefix tailTrace_3097313
  have hstable : (prefixWord ++ tailWord_3097313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3097313).length < 2 ^ (prefixWord ++ tailWord_3097313).sum := by decide
  have hdescent : baseEnd_3097313 < baseStart_3097313 := by decide
  rcases family_descends (prefixWord ++ tailWord_3097313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3097320 : List Nat := [2, 1, 4, 1, 4, 1, 2, 3, 1, 4]
def baseStart_3097320 : Nat := 118140960795 + 3097320 * 2 ^ 59
def prefixEnd_3097320 : Nat := 4983230072969 + 3 ^ 40 * 3097320 * 2
def baseEnd_3097320 : Nat := 530137966927975651651897

theorem tailTrace_3097320 : CollatzResearch.WordTrace tailWord_3097320 prefixEnd_3097320 530137966927975651651897 := by
  unfold tailWord_3097320
  simp only [CollatzResearch.WordTrace]
  refine ⟨56484270569473047493424707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75312360759297396657899609 56484270569473047493424707)
  ·
    refine ⟨84726405854209571240137061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56484270569473047493424707 84726405854209571240137061)
    ·
      refine ⟨15886201097664294607525699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 84726405854209571240137061 15886201097664294607525699)
      ·
        refine ⟨23829301646496441911288549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15886201097664294607525699 23829301646496441911288549)
        ·
          refine ⟨4467994058718082858366603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23829301646496441911288549 4467994058718082858366603)
          ·
            refine ⟨6701991088077124287549905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4467994058718082858366603 6701991088077124287549905)
            ·
              refine ⟨5026493316057843215662429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6701991088077124287549905 5026493316057843215662429)
              ·
                refine ⟨1884934993521691205873411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5026493316057843215662429 1884934993521691205873411)
                ·
                  refine ⟨2827402490282536808810117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1884934993521691205873411 2827402490282536808810117)
                  ·
                    refine ⟨530137966927975651651897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2827402490282536808810117 530137966927975651651897)
                    ·
                      rfl

theorem cell23_3097320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 2, 3, 1, 4].length) (baseStart_3097320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3097320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3097320 prefixEnd_3097320 := by exact prefixLift 3097320
  have htrace : WordTrace (prefixWord ++ tailWord_3097320) baseStart_3097320 baseEnd_3097320 := by
    simpa [prefixWord, tailWord_3097320, baseEnd_3097320] using wordTrace_append hprefix tailTrace_3097320
  have hstable : (prefixWord ++ tailWord_3097320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3097320).length < 2 ^ (prefixWord ++ tailWord_3097320).sum := by decide
  have hdescent : baseEnd_3097320 < baseStart_3097320 := by decide
  rcases family_descends (prefixWord ++ tailWord_3097320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3097336 : List Nat := [2, 1, 2, 1, 1, 2, 4, 1, 4, 3, 2]
def baseStart_3097336 : Nat := 118140960795 + 3097336 * 2 ^ 59
def prefixEnd_3097336 : Nat := 4983230072969 + 3 ^ 40 * 3097336 * 2
def baseEnd_3097336 : Nat := 1590422116474398892355617

theorem tailTrace_3097336 : CollatzResearch.WordTrace tailWord_3097336 prefixEnd_3097336 1590422116474398892355617 := by
  unfold tailWord_3097336
  simp only [CollatzResearch.WordTrace]
  refine ⟨56484562353444064859715931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75312749804592086479621241 56484562353444064859715931)
  ·
    refine ⟨84726843530166097289573897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56484562353444064859715931 84726843530166097289573897)
    ·
      refine ⟨63545132647624572967180423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84726843530166097289573897 63545132647624572967180423)
      ·
        refine ⟨95317698971436859450770635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63545132647624572967180423 95317698971436859450770635)
        ·
          refine ⟨142976548457155289176155953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95317698971436859450770635 142976548457155289176155953)
          ·
            refine ⟨107232411342866466882116965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142976548457155289176155953 107232411342866466882116965)
            ·
              refine ⟨20106077126787462540396931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 107232411342866466882116965 20106077126787462540396931)
              ·
                refine ⟨30159115690181193810595397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20106077126787462540396931 30159115690181193810595397)
                ·
                  refine ⟨5654834191908973839486637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30159115690181193810595397 5654834191908973839486637)
                  ·
                    refine ⟨2120562821965865189807489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5654834191908973839486637 2120562821965865189807489)
                    ·
                      refine ⟨1590422116474398892355617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2120562821965865189807489 1590422116474398892355617)
                      ·
                        rfl

theorem cell23_3097336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 1, 4, 3, 2].length) (baseStart_3097336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3097336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3097336 prefixEnd_3097336 := by exact prefixLift 3097336
  have htrace : WordTrace (prefixWord ++ tailWord_3097336) baseStart_3097336 baseEnd_3097336 := by
    simpa [prefixWord, tailWord_3097336, baseEnd_3097336] using wordTrace_append hprefix tailTrace_3097336
  have hstable : (prefixWord ++ tailWord_3097336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3097336).length < 2 ^ (prefixWord ++ tailWord_3097336).sum := by decide
  have hdescent : baseEnd_3097336 < baseStart_3097336 := by decide
  rcases family_descends (prefixWord ++ tailWord_3097336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3097349 : List Nat := [1, 3, 1, 1, 2, 1, 1, 3, 5, 1, 4]
def baseStart_3097349 : Nat := 118140960795 + 3097349 * 2 ^ 59
def prefixEnd_3097349 : Nat := 4983230072969 + 3 ^ 40 * 3097349 * 2
def baseEnd_3097349 : Nat := 1590428791722907341493057

theorem tailTrace_3097349 : CollatzResearch.WordTrace tailWord_3097349 prefixEnd_3097349 1590428791722907341493057 := by
  unfold tailWord_3097349
  simp only [CollatzResearch.WordTrace]
  refine ⟨112969598855841032939655101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75313065903894021959770067 112969598855841032939655101)
  ·
    refine ⟨42363599570940387352370663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112969598855841032939655101 42363599570940387352370663)
    ·
      refine ⟨63545399356410581028555995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42363599570940387352370663 63545399356410581028555995)
      ·
        refine ⟨95318099034615871542833993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63545399356410581028555995 95318099034615871542833993)
        ·
          refine ⟨71488574275961903657125495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95318099034615871542833993 71488574275961903657125495)
          ·
            refine ⟨107232861413942855485688243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71488574275961903657125495 107232861413942855485688243)
            ·
              refine ⟨160849292120914283228532365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107232861413942855485688243 160849292120914283228532365)
              ·
                refine ⟨60318484545342856210699637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 160849292120914283228532365 60318484545342856210699637)
                ·
                  refine ⟨5654857926125892769753091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 60318484545342856210699637 5654857926125892769753091)
                  ·
                    refine ⟨8482286889188839154629637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5654857926125892769753091 8482286889188839154629637)
                    ·
                      refine ⟨1590428791722907341493057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8482286889188839154629637 1590428791722907341493057)
                      ·
                        rfl

theorem cell23_3097349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 3, 5, 1, 4].length) (baseStart_3097349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3097349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3097349 prefixEnd_3097349 := by exact prefixLift 3097349
  have htrace : WordTrace (prefixWord ++ tailWord_3097349) baseStart_3097349 baseEnd_3097349 := by
    simpa [prefixWord, tailWord_3097349, baseEnd_3097349] using wordTrace_append hprefix tailTrace_3097349
  have hstable : (prefixWord ++ tailWord_3097349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3097349).length < 2 ^ (prefixWord ++ tailWord_3097349).sum := by decide
  have hdescent : baseEnd_3097349 < baseStart_3097349 := by decide
  rcases family_descends (prefixWord ++ tailWord_3097349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3097376 : List Nat := [2, 1, 1, 5, 1, 2, 1, 2, 4, 4]
def baseStart_3097376 : Nat := 118140960795 + 3097376 * 2 ^ 59
def prefixEnd_3097376 : Nat := 4983230072969 + 3 ^ 40 * 3097376 * 2
def baseEnd_3097376 : Nat := 530147551900192911951811

theorem tailTrace_3097376 : CollatzResearch.WordTrace tailWord_3097376 prefixEnd_3097376 530147551900192911951811 := by
  unfold tailWord_3097376
  simp only [CollatzResearch.WordTrace]
  refine ⟨56485291813371608275443991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75313722417828811033925321 56485291813371608275443991)
  ·
    refine ⟨84727937720057412413165987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56485291813371608275443991 84727937720057412413165987)
    ·
      refine ⟨127091906580086118619748981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84727937720057412413165987 127091906580086118619748981)
      ·
        refine ⟨11914866241883073620601467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 127091906580086118619748981 11914866241883073620601467)
        ·
          refine ⟨17872299362824610430902201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11914866241883073620601467 17872299362824610430902201)
          ·
            refine ⟨13404224522118457823176651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17872299362824610430902201 13404224522118457823176651)
            ·
              refine ⟨20106336783177686734764977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13404224522118457823176651 20106336783177686734764977)
              ·
                refine ⟨15079752587383265051073733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20106336783177686734764977 15079752587383265051073733)
                ·
                  refine ⟨2827453610134362197076325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15079752587383265051073733 2827453610134362197076325)
                  ·
                    refine ⟨530147551900192911951811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2827453610134362197076325 530147551900192911951811)
                    ·
                      rfl

theorem cell23_3097376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 2, 4, 4].length) (baseStart_3097376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3097376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3097376 prefixEnd_3097376 := by exact prefixLift 3097376
  have htrace : WordTrace (prefixWord ++ tailWord_3097376) baseStart_3097376 baseEnd_3097376 := by
    simpa [prefixWord, tailWord_3097376, baseEnd_3097376] using wordTrace_append hprefix tailTrace_3097376
  have hstable : (prefixWord ++ tailWord_3097376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3097376).length < 2 ^ (prefixWord ++ tailWord_3097376).sum := by decide
  have hdescent : baseEnd_3097376 < baseStart_3097376 := by decide
  rcases family_descends (prefixWord ++ tailWord_3097376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3097379 : List Nat := [1, 1, 1, 4, 2, 1, 1, 3, 3, 2, 4]
def baseStart_3097379 : Nat := 118140960795 + 3097379 * 2 ^ 59
def prefixEnd_3097379 : Nat := 4983230072969 + 3 ^ 40 * 3097379 * 2
def baseEnd_3097379 : Nat := 1590444196142542224117919

theorem tailTrace_3097379 : CollatzResearch.WordTrace tailWord_3097379 prefixEnd_3097379 1590444196142542224117919 := by
  unfold tailWord_3097379
  simp only [CollatzResearch.WordTrace]
  refine ⟨112970693045732348063247191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75313795363821565375498127 112970693045732348063247191)
  ·
    refine ⟨169456039568598522094870787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112970693045732348063247191 169456039568598522094870787)
    ·
      refine ⟨254184059352897783142306181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169456039568598522094870787 254184059352897783142306181)
      ·
        refine ⟨47659511128668334339182409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 254184059352897783142306181 47659511128668334339182409)
        ·
          refine ⟨35744633346501250754386807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47659511128668334339182409 35744633346501250754386807)
          ·
            refine ⟨53616950019751876131580211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35744633346501250754386807 53616950019751876131580211)
            ·
              refine ⟨80425425029627814197370317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53616950019751876131580211 80425425029627814197370317)
              ·
                refine ⟨30159534386110430324013869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80425425029627814197370317 30159534386110430324013869)
                ·
                  refine ⟨11309825394791411371505201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30159534386110430324013869 11309825394791411371505201)
                  ·
                    refine ⟨8482369046093558528628901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11309825394791411371505201 8482369046093558528628901)
                    ·
                      refine ⟨1590444196142542224117919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8482369046093558528628901 1590444196142542224117919)
                      ·
                        rfl

theorem cell23_3097379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 3, 3, 2, 4].length) (baseStart_3097379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3097379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3097379 prefixEnd_3097379 := by exact prefixLift 3097379
  have htrace : WordTrace (prefixWord ++ tailWord_3097379) baseStart_3097379 baseEnd_3097379 := by
    simpa [prefixWord, tailWord_3097379, baseEnd_3097379] using wordTrace_append hprefix tailTrace_3097379
  have hstable : (prefixWord ++ tailWord_3097379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3097379).length < 2 ^ (prefixWord ++ tailWord_3097379).sum := by decide
  have hdescent : baseEnd_3097379 < baseStart_3097379 := by decide
  rcases family_descends (prefixWord ++ tailWord_3097379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3097414 : List Nat := [6, 1, 1, 2, 3, 1, 1, 2, 1, 5]
def baseStart_3097414 : Nat := 118140960795 + 3097414 * 2 ^ 59
def prefixEnd_3097414 : Nat := 4983230072969 + 3 ^ 40 * 3097414 * 2
def baseEnd_3097414 : Nat := 530154055988483195726753

theorem tailTrace_3097414 : CollatzResearch.WordTrace tailWord_3097414 prefixEnd_3097414 530154055988483195726753 := by
  unfold tailWord_3097414
  simp only [CollatzResearch.WordTrace]
  refine ⟨3530374050018923407524103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 75314646400403699360514197 3530374050018923407524103)
  ·
    refine ⟨5295561075028385111286155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3530374050018923407524103 5295561075028385111286155)
    ·
      refine ⟨7943341612542577666929233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5295561075028385111286155 7943341612542577666929233)
      ·
        refine ⟨5957506209406933250196925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7943341612542577666929233 5957506209406933250196925)
        ·
          refine ⟨2234064828527599968823847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5957506209406933250196925 2234064828527599968823847)
          ·
            refine ⟨3351097242791399953235771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2234064828527599968823847 3351097242791399953235771)
            ·
              refine ⟨5026645864187099929853657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3351097242791399953235771 5026645864187099929853657)
              ·
                refine ⟨3769984398140324947390243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5026645864187099929853657 3769984398140324947390243)
                ·
                  refine ⟨5654976597210487421085365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3769984398140324947390243 5654976597210487421085365)
                  ·
                    refine ⟨530154055988483195726753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5654976597210487421085365 530154055988483195726753)
                    ·
                      rfl

theorem cell23_3097414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 1, 2, 1, 5].length) (baseStart_3097414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3097414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3097414 prefixEnd_3097414 := by exact prefixLift 3097414
  have htrace : WordTrace (prefixWord ++ tailWord_3097414) baseStart_3097414 baseEnd_3097414 := by
    simpa [prefixWord, tailWord_3097414, baseEnd_3097414] using wordTrace_append hprefix tailTrace_3097414
  have hstable : (prefixWord ++ tailWord_3097414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3097414).length < 2 ^ (prefixWord ++ tailWord_3097414).sum := by decide
  have hdescent : baseEnd_3097414 < baseStart_3097414 := by decide
  rcases family_descends (prefixWord ++ tailWord_3097414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3097416 : List Nat := [2, 1, 3, 1, 1, 3, 2, 3, 1, 3, 3]
def baseStart_3097416 : Nat := 118140960795 + 3097416 * 2 ^ 59
def prefixEnd_3097416 : Nat := 4983230072969 + 3 ^ 40 * 3097416 * 2
def baseEnd_3097416 : Nat := 1590463194926758579355249

theorem tailTrace_3097416 : CollatzResearch.WordTrace tailWord_3097416 prefixEnd_3097416 1590463194926758579355249 := by
  unfold tailWord_3097416
  simp only [CollatzResearch.WordTrace]
  refine ⟨56486021273299151691172051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75314695031065535588229401 56486021273299151691172051)
  ·
    refine ⟨84729031909948727536758077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56486021273299151691172051 84729031909948727536758077)
    ·
      refine ⟨31773386966230772826284279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84729031909948727536758077 31773386966230772826284279)
      ·
        refine ⟨47660080449346159239426419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31773386966230772826284279 47660080449346159239426419)
        ·
          refine ⟨71490120674019238859139629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47660080449346159239426419 71490120674019238859139629)
          ·
            refine ⟨26808795252757214572177361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71490120674019238859139629 26808795252757214572177361)
            ·
              refine ⟨20106596439567910929133021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26808795252757214572177361 20106596439567910929133021)
              ·
                refine ⟨7539973664837966598424883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20106596439567910929133021 7539973664837966598424883)
                ·
                  refine ⟨11309960497256949897637325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7539973664837966598424883 11309960497256949897637325)
                  ·
                    refine ⟨4241235186471356211613997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11309960497256949897637325 4241235186471356211613997)
                    ·
                      refine ⟨1590463194926758579355249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4241235186471356211613997 1590463194926758579355249)
                      ·
                        rfl

theorem cell23_3097416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 3, 1, 3, 3].length) (baseStart_3097416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3097416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3097416 prefixEnd_3097416 := by exact prefixLift 3097416
  have htrace : WordTrace (prefixWord ++ tailWord_3097416) baseStart_3097416 baseEnd_3097416 := by
    simpa [prefixWord, tailWord_3097416, baseEnd_3097416] using wordTrace_append hprefix tailTrace_3097416
  have hstable : (prefixWord ++ tailWord_3097416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3097416).length < 2 ^ (prefixWord ++ tailWord_3097416).sum := by decide
  have hdescent : baseEnd_3097416 < baseStart_3097416 := by decide
  rcases family_descends (prefixWord ++ tailWord_3097416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3097420 : List Nat := [2, 2, 1, 3, 3, 3, 1, 2, 1, 2, 3]
def baseStart_3097420 : Nat := 118140960795 + 3097420 * 2 ^ 59
def prefixEnd_3097420 : Nat := 4983230072969 + 3 ^ 40 * 3097420 * 2
def baseEnd_3097420 : Nat := 1590465248849376563705231

theorem tailTrace_3097420 : CollatzResearch.WordTrace tailWord_3097420 prefixEnd_3097420 1590465248849376563705231 := by
  unfold tailWord_3097420
  simp only [CollatzResearch.WordTrace]
  refine ⟨56486094219291906032744857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75314792292389208043659809 56486094219291906032744857)
  ·
    refine ⟨42364570664468929524558643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56486094219291906032744857 42364570664468929524558643)
    ·
      refine ⟨63546855996703394286837965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42364570664468929524558643 63546855996703394286837965)
      ·
        refine ⟨23830070998763772857564237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63546855996703394286837965 23830070998763772857564237)
        ·
          refine ⟨8936276624536414821586589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23830070998763772857564237 8936276624536414821586589)
          ·
            refine ⟨3351103734201155558094971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8936276624536414821586589 3351103734201155558094971)
            ·
              refine ⟨5026655601301733337142457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3351103734201155558094971 5026655601301733337142457)
              ·
                refine ⟨3769991700976300002856843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5026655601301733337142457 3769991700976300002856843)
                ·
                  refine ⟨5654987551464450004285265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3769991700976300002856843 5654987551464450004285265)
                  ·
                    refine ⟨4241240663598337503213949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5654987551464450004285265 4241240663598337503213949)
                    ·
                      refine ⟨1590465248849376563705231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4241240663598337503213949 1590465248849376563705231)
                      ·
                        rfl

theorem cell23_3097420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 1, 2, 1, 2, 3].length) (baseStart_3097420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3097420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3097420 prefixEnd_3097420 := by exact prefixLift 3097420
  have htrace : WordTrace (prefixWord ++ tailWord_3097420) baseStart_3097420 baseEnd_3097420 := by
    simpa [prefixWord, tailWord_3097420, baseEnd_3097420] using wordTrace_append hprefix tailTrace_3097420
  have hstable : (prefixWord ++ tailWord_3097420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3097420).length < 2 ^ (prefixWord ++ tailWord_3097420).sum := by decide
  have hdescent : baseEnd_3097420 < baseStart_3097420 := by decide
  rcases family_descends (prefixWord ++ tailWord_3097420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3097459 : List Nat := [1, 1, 1, 2, 2, 1, 4, 2, 1, 3, 5]
def baseStart_3097459 : Nat := 118140960795 + 3097459 * 2 ^ 59
def prefixEnd_3097459 : Nat := 4983230072969 + 3 ^ 40 * 3097459 * 2
def baseEnd_3097459 : Nat := 1590485274594901911117551

theorem tailTrace_3097459 : CollatzResearch.WordTrace tailWord_3097459 prefixEnd_3097459 1590485274594901911117551 := by
  unfold tailWord_3097459
  simp only [CollatzResearch.WordTrace]
  refine ⟨112973610885442521726159431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75315740590295014484106287 112973610885442521726159431)
  ·
    refine ⟨169460416328163782589239147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112973610885442521726159431 169460416328163782589239147)
    ·
      refine ⟨254190624492245673883858721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169460416328163782589239147 254190624492245673883858721)
      ·
        refine ⟨190642968369184255412894041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 254190624492245673883858721 190642968369184255412894041)
        ·
          refine ⟨142982226276888191559670531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 190642968369184255412894041 142982226276888191559670531)
          ·
            refine ⟨214473339415332287339505797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142982226276888191559670531 214473339415332287339505797)
            ·
              refine ⟨40213751140374803876157337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 214473339415332287339505797 40213751140374803876157337)
              ·
                refine ⟨30160313355281102907118003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40213751140374803876157337 30160313355281102907118003)
                ·
                  refine ⟨45240470032921654360677005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30160313355281102907118003 45240470032921654360677005)
                  ·
                    refine ⟨16965176262345620385253877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45240470032921654360677005 16965176262345620385253877)
                    ·
                      refine ⟨1590485274594901911117551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16965176262345620385253877 1590485274594901911117551)
                      ·
                        rfl

theorem cell23_3097459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 2, 1, 3, 5].length) (baseStart_3097459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3097459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3097459 prefixEnd_3097459 := by exact prefixLift 3097459
  have htrace : WordTrace (prefixWord ++ tailWord_3097459) baseStart_3097459 baseEnd_3097459 := by
    simpa [prefixWord, tailWord_3097459, baseEnd_3097459] using wordTrace_append hprefix tailTrace_3097459
  have hstable : (prefixWord ++ tailWord_3097459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3097459).length < 2 ^ (prefixWord ++ tailWord_3097459).sum := by decide
  have hdescent : baseEnd_3097459 < baseStart_3097459 := by decide
  rcases family_descends (prefixWord ++ tailWord_3097459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3097476 : List Nat := [2, 3, 2, 1, 1, 1, 1, 1, 4, 4, 3]
def baseStart_3097476 : Nat := 118140960795 + 3097476 * 2 ^ 59
def prefixEnd_3097476 : Nat := 4983230072969 + 3 ^ 40 * 3097476 * 2
def baseEnd_3097476 : Nat := 1590494003766028344604973

theorem tailTrace_3097476 : CollatzResearch.WordTrace tailWord_3097476 prefixEnd_3097476 1590494003766028344604973 := by
  unfold tailWord_3097476
  simp only [CollatzResearch.WordTrace]
  refine ⟨56487115463190466814764141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75316153950920622419685521 56487115463190466814764141)
  ·
    refine ⟨21182668298696425055536553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56487115463190466814764141 21182668298696425055536553)
    ·
      refine ⟨15887001224022318791652415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21182668298696425055536553 15887001224022318791652415)
      ·
        refine ⟨23830501836033478187478623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15887001224022318791652415 23830501836033478187478623)
        ·
          refine ⟨35745752754050217281217935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23830501836033478187478623 35745752754050217281217935)
          ·
            refine ⟨53618629131075325921826903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35745752754050217281217935 53618629131075325921826903)
            ·
              refine ⟨80427943696612988882740355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53618629131075325921826903 80427943696612988882740355)
              ·
                refine ⟨120641915544919483324110533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80427943696612988882740355 120641915544919483324110533)
                ·
                  refine ⟨22620359164672403123270725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 120641915544919483324110533 22620359164672403123270725)
                  ·
                    refine ⟨4241317343376075585613261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22620359164672403123270725 4241317343376075585613261)
                    ·
                      refine ⟨1590494003766028344604973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4241317343376075585613261 1590494003766028344604973)
                      ·
                        rfl

theorem cell23_3097476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 1, 4, 4, 3].length) (baseStart_3097476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3097476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3097476 prefixEnd_3097476 := by exact prefixLift 3097476
  have htrace : WordTrace (prefixWord ++ tailWord_3097476) baseStart_3097476 baseEnd_3097476 := by
    simpa [prefixWord, tailWord_3097476, baseEnd_3097476] using wordTrace_append hprefix tailTrace_3097476
  have hstable : (prefixWord ++ tailWord_3097476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3097476).length < 2 ^ (prefixWord ++ tailWord_3097476).sum := by decide
  have hdescent : baseEnd_3097476 < baseStart_3097476 := by decide
  rcases family_descends (prefixWord ++ tailWord_3097476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3097489 : List Nat := [1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 7]
def baseStart_3097489 : Nat := 118140960795 + 3097489 * 2 ^ 59
def prefixEnd_3097489 : Nat := 4983230072969 + 3 ^ 40 * 3097489 * 2
def baseEnd_3097489 : Nat := 1590500679014536793742413

theorem tailTrace_3097489 : CollatzResearch.WordTrace tailWord_3097489 prefixEnd_3097489 1590500679014536793742413 := by
  unfold tailWord_3097489
  simp only [CollatzResearch.WordTrace]
  refine ⟨112974705075333836849751521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75316470050222557899834347 112974705075333836849751521)
  ·
    refine ⟨84731028806500377637313641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112974705075333836849751521 84731028806500377637313641)
    ·
      refine ⟨63548271604875283227985231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84731028806500377637313641 63548271604875283227985231)
      ·
        refine ⟨95322407407312924841977847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63548271604875283227985231 95322407407312924841977847)
        ·
          refine ⟨142983611110969387262966771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95322407407312924841977847 142983611110969387262966771)
          ·
            refine ⟨214475416666454080894450157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142983611110969387262966771 214475416666454080894450157)
            ·
              refine ⟨80428281249920280335418809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 214475416666454080894450157 80428281249920280335418809)
              ·
                refine ⟨60321210937440210251564107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80428281249920280335418809 60321210937440210251564107)
                ·
                  refine ⟨90481816406160315377346161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60321210937440210251564107 90481816406160315377346161)
                  ·
                    refine ⟨67861362304620236533009621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 90481816406160315377346161 67861362304620236533009621)
                    ·
                      refine ⟨1590500679014536793742413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 67861362304620236533009621 1590500679014536793742413)
                      ·
                        rfl

theorem cell23_3097489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 7].length) (baseStart_3097489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3097489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3097489 prefixEnd_3097489 := by exact prefixLift 3097489
  have htrace : WordTrace (prefixWord ++ tailWord_3097489) baseStart_3097489 baseEnd_3097489 := by
    simpa [prefixWord, tailWord_3097489, baseEnd_3097489] using wordTrace_append hprefix tailTrace_3097489
  have hstable : (prefixWord ++ tailWord_3097489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3097489).length < 2 ^ (prefixWord ++ tailWord_3097489).sum := by decide
  have hdescent : baseEnd_3097489 < baseStart_3097489 := by decide
  rcases family_descends (prefixWord ++ tailWord_3097489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3097524 : List Nat := [2, 5, 2, 1, 1, 3, 1, 1, 1, 4, 2]
def baseStart_3097524 : Nat := 118140960795 + 3097524 * 2 ^ 59
def prefixEnd_3097524 : Nat := 4983230072969 + 3 ^ 40 * 3097524 * 2
def baseEnd_3097524 : Nat := 1590518650837444156804753

theorem tailTrace_3097524 : CollatzResearch.WordTrace tailWord_3097524 prefixEnd_3097524 1590518650837444156804753 := by
  unfold tailWord_3097524
  simp only [CollatzResearch.WordTrace]
  refine ⟨56487990815103518913637813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75317321086804691884850417 56487990815103518913637813)
  ·
    refine ⟨5295749138915954898153545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 56487990815103518913637813 5295749138915954898153545)
    ·
      refine ⟨3971811854186966173615159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5295749138915954898153545 3971811854186966173615159)
      ·
        refine ⟨5957717781280449260422739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3971811854186966173615159 5957717781280449260422739)
        ·
          refine ⟨8936576671920673890634109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5957717781280449260422739 8936576671920673890634109)
          ·
            refine ⟨3351216251970252708987791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8936576671920673890634109 3351216251970252708987791)
            ·
              refine ⟨5026824377955379063481687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3351216251970252708987791 5026824377955379063481687)
              ·
                refine ⟨7540236566933068595222531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5026824377955379063481687 7540236566933068595222531)
                ·
                  refine ⟨11310354850399602892833797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7540236566933068595222531 11310354850399602892833797)
                  ·
                    refine ⟨2120691534449925542406337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11310354850399602892833797 2120691534449925542406337)
                    ·
                      refine ⟨1590518650837444156804753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2120691534449925542406337 1590518650837444156804753)
                      ·
                        rfl

theorem cell23_3097524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 1, 1, 1, 4, 2].length) (baseStart_3097524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3097524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3097524 prefixEnd_3097524 := by exact prefixLift 3097524
  have htrace : WordTrace (prefixWord ++ tailWord_3097524) baseStart_3097524 baseEnd_3097524 := by
    simpa [prefixWord, tailWord_3097524, baseEnd_3097524] using wordTrace_append hprefix tailTrace_3097524
  have hstable : (prefixWord ++ tailWord_3097524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3097524).length < 2 ^ (prefixWord ++ tailWord_3097524).sum := by decide
  have hdescent : baseEnd_3097524 < baseStart_3097524 := by decide
  rcases family_descends (prefixWord ++ tailWord_3097524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3097570 : List Nat := [3, 3, 3, 1, 1, 2, 1, 1, 1, 2, 5]
def baseStart_3097570 : Nat := 118140960795 + 3097570 * 2 ^ 59
def prefixEnd_3097570 : Nat := 4983230072969 + 3 ^ 40 * 3097570 * 2
def baseEnd_3097570 : Nat := 1590542270947550976829541

theorem tailTrace_3097570 : CollatzResearch.WordTrace tailWord_3097570 prefixEnd_3097570 1590542270947550976829541 := by
  unfold tailWord_3097570
  simp only [CollatzResearch.WordTrace]
  refine ⟨28244414847010096920862541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75318439592026925122300109 28244414847010096920862541)
  ·
    refine ⟨10591655567628786345323453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28244414847010096920862541 10591655567628786345323453)
    ·
      refine ⟨3971870837860794879496295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10591655567628786345323453 3971870837860794879496295)
      ·
        refine ⟨5957806256791192319244443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3971870837860794879496295 5957806256791192319244443)
        ·
          refine ⟨8936709385186788478866665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5957806256791192319244443 8936709385186788478866665)
          ·
            refine ⟨6702532038890091359149999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8936709385186788478866665 6702532038890091359149999)
            ·
              refine ⟨10053798058335137038724999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6702532038890091359149999 10053798058335137038724999)
              ·
                refine ⟨15080697087502705558087499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10053798058335137038724999 15080697087502705558087499)
                ·
                  refine ⟨22621045631254058337131249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15080697087502705558087499 22621045631254058337131249)
                  ·
                    refine ⟨16965784223440543752848437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22621045631254058337131249 16965784223440543752848437)
                    ·
                      refine ⟨1590542270947550976829541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16965784223440543752848437 1590542270947550976829541)
                      ·
                        rfl

theorem cell23_3097570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_3097570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3097570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3097570 prefixEnd_3097570 := by exact prefixLift 3097570
  have htrace : WordTrace (prefixWord ++ tailWord_3097570) baseStart_3097570 baseEnd_3097570 := by
    simpa [prefixWord, tailWord_3097570, baseEnd_3097570] using wordTrace_append hprefix tailTrace_3097570
  have hstable : (prefixWord ++ tailWord_3097570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3097570).length < 2 ^ (prefixWord ++ tailWord_3097570).sum := by decide
  have hdescent : baseEnd_3097570 < baseStart_3097570 := by decide
  rcases family_descends (prefixWord ++ tailWord_3097570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3097576 : List Nat := [2, 1, 4, 1, 1, 1, 2, 2, 2, 1, 6]
def baseStart_3097576 : Nat := 118140960795 + 3097576 * 2 ^ 59
def prefixEnd_3097576 : Nat := 4983230072969 + 3 ^ 40 * 3097576 * 2
def baseEnd_3097576 : Nat := 1590545351831477953354513

theorem tailTrace_3097576 : CollatzResearch.WordTrace tailWord_3097576 prefixEnd_3097576 1590545351831477953354513 := by
  unfold tailWord_3097576
  simp only [CollatzResearch.WordTrace]
  refine ⟨56488939113009325354084291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75318585484012433805445721 56488939113009325354084291)
  ·
    refine ⟨84733408669513988031126437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56488939113009325354084291 84733408669513988031126437)
    ·
      refine ⟨15887514125533872755836207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 84733408669513988031126437 15887514125533872755836207)
      ·
        refine ⟨23831271188300809133754311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15887514125533872755836207 23831271188300809133754311)
        ·
          refine ⟨35746906782451213700631467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23831271188300809133754311 35746906782451213700631467)
          ·
            refine ⟨53620360173676820550947201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35746906782451213700631467 53620360173676820550947201)
            ·
              refine ⟨40215270130257615413210401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53620360173676820550947201 40215270130257615413210401)
              ·
                refine ⟨30161452597693211559907801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40215270130257615413210401 30161452597693211559907801)
                ·
                  refine ⟨22621089448269908669930851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30161452597693211559907801 22621089448269908669930851)
                  ·
                    refine ⟨33931634172404863004896277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22621089448269908669930851 33931634172404863004896277)
                    ·
                      refine ⟨1590545351831477953354513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33931634172404863004896277 1590545351831477953354513)
                      ·
                        rfl

theorem cell23_3097576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 2, 2, 1, 6].length) (baseStart_3097576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3097576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3097576 prefixEnd_3097576 := by exact prefixLift 3097576
  have htrace : WordTrace (prefixWord ++ tailWord_3097576) baseStart_3097576 baseEnd_3097576 := by
    simpa [prefixWord, tailWord_3097576, baseEnd_3097576] using wordTrace_append hprefix tailTrace_3097576
  have hstable : (prefixWord ++ tailWord_3097576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3097576).length < 2 ^ (prefixWord ++ tailWord_3097576).sum := by decide
  have hdescent : baseEnd_3097576 < baseStart_3097576 := by decide
  rcases family_descends (prefixWord ++ tailWord_3097576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
