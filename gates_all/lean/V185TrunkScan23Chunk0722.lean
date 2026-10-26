import V185TrunkScan23Chunk0721

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4269044 : List Nat := [2, 6, 2, 1, 2, 1, 1, 3, 5]
def baseStart_4269044 : Nat := 118140960795 + 4269044 * 2 ^ 59
def prefixEnd_4269044 : Nat := 4983230072969 + 3 ^ 40 * 4269044 * 2
def baseEnd_4269044 : Nat := 243563500799188953268559

theorem tailTrace_4269044 : CollatzResearch.WordTrace tailWord_4269044 prefixEnd_4269044 243563500799188953268559 := by
  unfold tailWord_4269044
  simp only [CollatzResearch.WordTrace]
  refine ⟨77852413172995078757059093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103803217563993438342745457 77852413172995078757059093)
  ·
    refine ⟨3649331867484144316737145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 77852413172995078757059093 3649331867484144316737145)
    ·
      refine ⟨2736998900613108237552859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3649331867484144316737145 2736998900613108237552859)
      ·
        refine ⟨4105498350919662356329289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2736998900613108237552859 4105498350919662356329289)
        ·
          refine ⟨3079123763189746767246967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4105498350919662356329289 3079123763189746767246967)
          ·
            refine ⟨4618685644784620150870451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3079123763189746767246967 4618685644784620150870451)
            ·
              refine ⟨6928028467176930226305677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4618685644784620150870451 6928028467176930226305677)
              ·
                refine ⟨2598010675191348834864629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6928028467176930226305677 2598010675191348834864629)
                ·
                  refine ⟨243563500799188953268559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2598010675191348834864629 243563500799188953268559)
                  ·
                    rfl

theorem cell23_4269044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 1, 3, 5].length) (baseStart_4269044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4269044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4269044 prefixEnd_4269044 := by exact prefixLift 4269044
  have htrace : WordTrace (prefixWord ++ tailWord_4269044) baseStart_4269044 baseEnd_4269044 := by
    simpa [prefixWord, tailWord_4269044, baseEnd_4269044] using wordTrace_append hprefix tailTrace_4269044
  have hstable : (prefixWord ++ tailWord_4269044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4269044).length < 2 ^ (prefixWord ++ tailWord_4269044).sum := by decide
  have hdescent : baseEnd_4269044 < baseStart_4269044 := by decide
  rcases family_descends (prefixWord ++ tailWord_4269044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4269152 : List Nat := [2, 1, 1, 3, 2, 2, 1, 2, 2, 7]
def baseStart_4269152 : Nat := 118140960795 + 4269152 * 2 ^ 59
def prefixEnd_4269152 : Nat := 4983230072969 + 3 ^ 40 * 4269152 * 2
def baseEnd_4269152 : Nat := 730708987701128718955511

theorem tailTrace_4269152 : CollatzResearch.WordTrace tailWord_4269152 prefixEnd_4269152 730708987701128718955511 := by
  unfold tailWord_4269152
  simp only [CollatzResearch.WordTrace]
  refine ⟨77854382714799445979524855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103805843619732594639366473 77854382714799445979524855)
  ·
    refine ⟨116781574072199168969287283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77854382714799445979524855 116781574072199168969287283)
    ·
      refine ⟨175172361108298753453930925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116781574072199168969287283 175172361108298753453930925)
      ·
        refine ⟨65689635415612032545224097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 175172361108298753453930925 65689635415612032545224097)
        ·
          refine ⟨49267226561709024408918073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65689635415612032545224097 49267226561709024408918073)
          ·
            refine ⟨36950419921281768306688555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49267226561709024408918073 36950419921281768306688555)
            ·
              refine ⟨55425629881922652460032833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36950419921281768306688555 55425629881922652460032833)
              ·
                refine ⟨41569222411441989345024625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55425629881922652460032833 41569222411441989345024625)
                ·
                  refine ⟨31176916808581492008768469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41569222411441989345024625 31176916808581492008768469)
                  ·
                    refine ⟨730708987701128718955511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31176916808581492008768469 730708987701128718955511)
                    ·
                      rfl

theorem cell23_4269152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 2, 2, 7].length) (baseStart_4269152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4269152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4269152 prefixEnd_4269152 := by exact prefixLift 4269152
  have htrace : WordTrace (prefixWord ++ tailWord_4269152) baseStart_4269152 baseEnd_4269152 := by
    simpa [prefixWord, tailWord_4269152, baseEnd_4269152] using wordTrace_append hprefix tailTrace_4269152
  have hstable : (prefixWord ++ tailWord_4269152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4269152).length < 2 ^ (prefixWord ++ tailWord_4269152).sum := by decide
  have hdescent : baseEnd_4269152 < baseStart_4269152 := by decide
  rcases family_descends (prefixWord ++ tailWord_4269152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4269166 : List Nat := [4, 1, 2, 2, 1, 2, 2, 2, 1, 3, 3]
def baseStart_4269166 : Nat := 118140960795 + 4269166 * 2 ^ 59
def prefixEnd_4269166 : Nat := 4983230072969 + 3 ^ 40 * 4269166 * 2
def baseEnd_4269166 : Nat := 2192134151832549102091469

theorem tailTrace_4269166 : CollatzResearch.WordTrace tailWord_4269166 prefixEnd_4269166 2192134151832549102091469 := by
  unfold tailWord_4269166
  simp only [CollatzResearch.WordTrace]
  refine ⟨19463659506443521543757419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 103806184034365448233372901 19463659506443521543757419)
  ·
    refine ⟨29195489259665282315636129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19463659506443521543757419 29195489259665282315636129)
    ·
      refine ⟨21896616944748961736727097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29195489259665282315636129 21896616944748961736727097)
      ·
        refine ⟨16422462708561721302545323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21896616944748961736727097 16422462708561721302545323)
        ·
          refine ⟨24633694062842581953817985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16422462708561721302545323 24633694062842581953817985)
          ·
            refine ⟨18475270547131936465363489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24633694062842581953817985 18475270547131936465363489)
            ·
              refine ⟨13856452910348952349022617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18475270547131936465363489 13856452910348952349022617)
              ·
                refine ⟨10392339682761714261766963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13856452910348952349022617 10392339682761714261766963)
                ·
                  refine ⟨15588509524142571392650445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10392339682761714261766963 15588509524142571392650445)
                  ·
                    refine ⟨5845691071553464272243917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15588509524142571392650445 5845691071553464272243917)
                    ·
                      refine ⟨2192134151832549102091469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5845691071553464272243917 2192134151832549102091469)
                      ·
                        rfl

theorem cell23_4269166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 2, 1, 3, 3].length) (baseStart_4269166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4269166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4269166 prefixEnd_4269166 := by exact prefixLift 4269166
  have htrace : WordTrace (prefixWord ++ tailWord_4269166) baseStart_4269166 baseEnd_4269166 := by
    simpa [prefixWord, tailWord_4269166, baseEnd_4269166] using wordTrace_append hprefix tailTrace_4269166
  have hstable : (prefixWord ++ tailWord_4269166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4269166).length < 2 ^ (prefixWord ++ tailWord_4269166).sum := by decide
  have hdescent : baseEnd_4269166 < baseStart_4269166 := by decide
  rcases family_descends (prefixWord ++ tailWord_4269166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4269210 : List Nat := [3, 1, 1, 5, 1, 2, 2, 2, 1, 3, 2]
def baseStart_4269210 : Nat := 118140960795 + 4269210 * 2 ^ 59
def prefixEnd_4269210 : Nat := 4983230072969 + 3 ^ 40 * 4269210 * 2
def baseEnd_4269210 : Nat := 2192156744981346929941267

theorem tailTrace_4269210 : CollatzResearch.WordTrace tailWord_4269210 prefixEnd_4269210 2192156744981346929941267 := by
  unfold tailWord_4269210
  simp only [CollatzResearch.WordTrace]
  refine ⟨38927720215847191966165271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103807253908925845243107389 38927720215847191966165271)
  ·
    refine ⟨58391580323770787949247907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38927720215847191966165271 58391580323770787949247907)
    ·
      refine ⟨87587370485656181923871861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58391580323770787949247907 87587370485656181923871861)
      ·
        refine ⟨8211315983030267055362987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 87587370485656181923871861 8211315983030267055362987)
        ·
          refine ⟨12316973974545400583044481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8211315983030267055362987 12316973974545400583044481)
          ·
            refine ⟨9237730480909050437283361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12316973974545400583044481 9237730480909050437283361)
            ·
              refine ⟨6928297860681787827962521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9237730480909050437283361 6928297860681787827962521)
              ·
                refine ⟨5196223395511340870971891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6928297860681787827962521 5196223395511340870971891)
                ·
                  refine ⟨7794335093267011306457837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5196223395511340870971891 7794335093267011306457837)
                  ·
                    refine ⟨2922875659975129239921689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7794335093267011306457837 2922875659975129239921689)
                    ·
                      refine ⟨2192156744981346929941267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2922875659975129239921689 2192156744981346929941267)
                      ·
                        rfl

theorem cell23_4269210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 2, 2, 1, 3, 2].length) (baseStart_4269210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4269210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4269210 prefixEnd_4269210 := by exact prefixLift 4269210
  have htrace : WordTrace (prefixWord ++ tailWord_4269210) baseStart_4269210 baseEnd_4269210 := by
    simpa [prefixWord, tailWord_4269210, baseEnd_4269210] using wordTrace_append hprefix tailTrace_4269210
  have hstable : (prefixWord ++ tailWord_4269210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4269210).length < 2 ^ (prefixWord ++ tailWord_4269210).sum := by decide
  have hdescent : baseEnd_4269210 < baseStart_4269210 := by decide
  rcases family_descends (prefixWord ++ tailWord_4269210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4269226 : List Nat := [3, 1, 5, 1, 1, 1, 1, 1, 1, 3, 5]
def baseStart_4269226 : Nat := 118140960795 + 4269226 * 2 ^ 59
def prefixEnd_4269226 : Nat := 4983230072969 + 3 ^ 40 * 4269226 * 2
def baseEnd_4269226 : Nat := 2192164960671818867341193

theorem tailTrace_4269226 : CollatzResearch.WordTrace tailWord_4269226 prefixEnd_4269226 2192164960671818867341193 := by
  unfold tailWord_4269226
  simp only [CollatzResearch.WordTrace]
  refine ⟨38927866107832700649310883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103807642954220535064829021 38927866107832700649310883)
  ·
    refine ⟨58391799161749050973966325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38927866107832700649310883 58391799161749050973966325)
    ·
      refine ⟨5474231171413973528809343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 58391799161749050973966325 5474231171413973528809343)
      ·
        refine ⟨8211346757120960293214015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5474231171413973528809343 8211346757120960293214015)
        ·
          refine ⟨12317020135681440439821023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8211346757120960293214015 12317020135681440439821023)
          ·
            refine ⟨18475530203522160659731535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12317020135681440439821023 18475530203522160659731535)
            ·
              refine ⟨27713295305283240989597303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18475530203522160659731535 27713295305283240989597303)
              ·
                refine ⟨41569942957924861484395955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27713295305283240989597303 41569942957924861484395955)
                ·
                  refine ⟨62354914436887292226593933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41569942957924861484395955 62354914436887292226593933)
                  ·
                    refine ⟨23383092913832734584972725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 62354914436887292226593933 23383092913832734584972725)
                    ·
                      refine ⟨2192164960671818867341193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23383092913832734584972725 2192164960671818867341193)
                      ·
                        rfl

theorem cell23_4269226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_4269226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4269226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4269226 prefixEnd_4269226 := by exact prefixLift 4269226
  have htrace : WordTrace (prefixWord ++ tailWord_4269226) baseStart_4269226 baseEnd_4269226 := by
    simpa [prefixWord, tailWord_4269226, baseEnd_4269226] using wordTrace_append hprefix tailTrace_4269226
  have hstable : (prefixWord ++ tailWord_4269226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4269226).length < 2 ^ (prefixWord ++ tailWord_4269226).sum := by decide
  have hdescent : baseEnd_4269226 < baseStart_4269226 := by decide
  rcases family_descends (prefixWord ++ tailWord_4269226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4269246 : List Nat := [4, 2, 1, 1, 3, 1, 3, 1, 7]
def baseStart_4269246 : Nat := 118140960795 + 4269246 * 2 ^ 59
def prefixEnd_4269246 : Nat := 4983230072969 + 3 ^ 40 * 4269246 * 2
def baseEnd_4269246 : Nat := 243575025587212087676789

theorem tailTrace_4269246 : CollatzResearch.WordTrace tailWord_4269246 prefixEnd_4269246 243575025587212087676789 := by
  unfold tailWord_4269246
  simp only [CollatzResearch.WordTrace]
  refine ⟨19464024236407293251621449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 103808129260838897341981061 19464024236407293251621449)
  ·
    refine ⟨14598018177305469938716087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19464024236407293251621449 14598018177305469938716087)
    ·
      refine ⟨21897027265958204908074131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14598018177305469938716087 21897027265958204908074131)
      ·
        refine ⟨32845540898937307362111197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21897027265958204908074131 32845540898937307362111197)
        ·
          refine ⟨12317077837101490260791699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32845540898937307362111197 12317077837101490260791699)
          ·
            refine ⟨18475616755652235391187549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12317077837101490260791699 18475616755652235391187549)
            ·
              refine ⟨6928356283369588271695331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18475616755652235391187549 6928356283369588271695331)
              ·
                refine ⟨10392534425054382407542997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6928356283369588271695331 10392534425054382407542997)
                ·
                  refine ⟨243575025587212087676789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10392534425054382407542997 243575025587212087676789)
                  ·
                    rfl

theorem cell23_4269246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 3, 1, 7].length) (baseStart_4269246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4269246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4269246 prefixEnd_4269246 := by exact prefixLift 4269246
  have htrace : WordTrace (prefixWord ++ tailWord_4269246) baseStart_4269246 baseEnd_4269246 := by
    simpa [prefixWord, tailWord_4269246, baseEnd_4269246] using wordTrace_append hprefix tailTrace_4269246
  have hstable : (prefixWord ++ tailWord_4269246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4269246).length < 2 ^ (prefixWord ++ tailWord_4269246).sum := by decide
  have hdescent : baseEnd_4269246 < baseStart_4269246 := by decide
  rcases family_descends (prefixWord ++ tailWord_4269246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4269261 : List Nat := [1, 6, 2, 2, 2, 1, 1, 2, 1, 3, 2]
def baseStart_4269261 : Nat := 118140960795 + 4269261 * 2 ^ 59
def prefixEnd_4269261 : Nat := 4983230072969 + 3 ^ 40 * 4269261 * 2
def baseEnd_4269261 : Nat := 2192182932494726230403533

theorem tailTrace_4269261 : CollatzResearch.WordTrace tailWord_4269261 prefixEnd_4269261 2192182932494726230403533 := by
  unfold tailWord_4269261
  simp only [CollatzResearch.WordTrace]
  refine ⟨155712740986204003574767637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103808493990802669049845091 155712740986204003574767637)
  ·
    refine ⟨7299034733728312667567233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 155712740986204003574767637 7299034733728312667567233)
    ·
      refine ⟨5474276050296234500675425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7299034733728312667567233 5474276050296234500675425)
      ·
        refine ⟨4105707037722175875506569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5474276050296234500675425 4105707037722175875506569)
        ·
          refine ⟨3079280278291631906629927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4105707037722175875506569 3079280278291631906629927)
          ·
            refine ⟨4618920417437447859944891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3079280278291631906629927 4618920417437447859944891)
            ·
              refine ⟨6928380626156171789917337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4618920417437447859944891 6928380626156171789917337)
              ·
                refine ⟨5196285469617128842438003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6928380626156171789917337 5196285469617128842438003)
                ·
                  refine ⟨7794428204425693263657005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5196285469617128842438003 7794428204425693263657005)
                  ·
                    refine ⟨2922910576659634973871377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7794428204425693263657005 2922910576659634973871377)
                    ·
                      refine ⟨2192182932494726230403533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2922910576659634973871377 2192182932494726230403533)
                      ·
                        rfl

theorem cell23_4269261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 1, 2, 1, 3, 2].length) (baseStart_4269261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4269261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4269261 prefixEnd_4269261 := by exact prefixLift 4269261
  have htrace : WordTrace (prefixWord ++ tailWord_4269261) baseStart_4269261 baseEnd_4269261 := by
    simpa [prefixWord, tailWord_4269261, baseEnd_4269261] using wordTrace_append hprefix tailTrace_4269261
  have hstable : (prefixWord ++ tailWord_4269261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4269261).length < 2 ^ (prefixWord ++ tailWord_4269261).sum := by decide
  have hdescent : baseEnd_4269261 < baseStart_4269261 := by decide
  rcases family_descends (prefixWord ++ tailWord_4269261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4269279 : List Nat := [1, 1, 2, 3, 2, 1, 2, 3, 1, 3, 4]
def baseStart_4269279 : Nat := 118140960795 + 4269279 * 2 ^ 59
def prefixEnd_4269279 : Nat := 4983230072969 + 3 ^ 40 * 4269279 * 2
def baseEnd_4269279 : Nat := 2192192175146507159978449

theorem tailTrace_4269279 : CollatzResearch.WordTrace tailWord_4269279 prefixEnd_4269279 2192192175146507159978449 := by
  unfold tailWord_4269279
  simp only [CollatzResearch.WordTrace]
  refine ⟨155713397500138792648922891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103808931666759195099281927 155713397500138792648922891)
  ·
    refine ⟨233570096250208188973384337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155713397500138792648922891 233570096250208188973384337)
    ·
      refine ⟨175177572187656141730038253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 233570096250208188973384337 175177572187656141730038253)
      ·
        refine ⟨65691589570371053148764345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 175177572187656141730038253 65691589570371053148764345)
        ·
          refine ⟨49268692177778289861573259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65691589570371053148764345 49268692177778289861573259)
          ·
            refine ⟨73903038266667434792359889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49268692177778289861573259 73903038266667434792359889)
            ·
              refine ⟨55427278700000576094269917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73903038266667434792359889 55427278700000576094269917)
              ·
                refine ⟨20785229512500216035351219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55427278700000576094269917 20785229512500216035351219)
                ·
                  refine ⟨31177844268750324053026829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20785229512500216035351219 31177844268750324053026829)
                  ·
                    refine ⟨11691691600781371519885061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 31177844268750324053026829 11691691600781371519885061)
                    ·
                      refine ⟨2192192175146507159978449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11691691600781371519885061 2192192175146507159978449)
                      ·
                        rfl

theorem cell23_4269279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 3, 1, 3, 4].length) (baseStart_4269279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4269279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4269279 prefixEnd_4269279 := by exact prefixLift 4269279
  have htrace : WordTrace (prefixWord ++ tailWord_4269279) baseStart_4269279 baseEnd_4269279 := by
    simpa [prefixWord, tailWord_4269279, baseEnd_4269279] using wordTrace_append hprefix tailTrace_4269279
  have hstable : (prefixWord ++ tailWord_4269279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4269279).length < 2 ^ (prefixWord ++ tailWord_4269279).sum := by decide
  have hdescent : baseEnd_4269279 < baseStart_4269279 := by decide
  rcases family_descends (prefixWord ++ tailWord_4269279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4269306 : List Nat := [3, 1, 1, 1, 1, 4, 2, 3, 3, 4]
def baseStart_4269306 : Nat := 118140960795 + 4269306 * 2 ^ 59
def prefixEnd_4269306 : Nat := 4983230072969 + 3 ^ 40 * 4269306 * 2
def baseEnd_4269306 : Nat := 730735346374726184780275

theorem tailTrace_4269306 : CollatzResearch.WordTrace tailWord_4269306 prefixEnd_4269306 730735346374726184780275 := by
  unfold tailWord_4269306
  simp only [CollatzResearch.WordTrace]
  refine ⟨38928595567760244065038943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103809588180693984173437181 38928595567760244065038943)
  ·
    refine ⟨58392893351640366097558415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38928595567760244065038943 58392893351640366097558415)
    ·
      refine ⟨87589340027460549146337623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58392893351640366097558415 87589340027460549146337623)
      ·
        refine ⟨131384010041190823719506435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87589340027460549146337623 131384010041190823719506435)
        ·
          refine ⟨197076015061786235579259653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131384010041190823719506435 197076015061786235579259653)
          ·
            refine ⟨36951752824084919171111185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 197076015061786235579259653 36951752824084919171111185)
            ·
              refine ⟨27713814618063689378333389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36951752824084919171111185 27713814618063689378333389)
              ·
                refine ⟨10392680481773883516875021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27713814618063689378333389 10392680481773883516875021)
                ·
                  refine ⟨3897255180665206318828133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10392680481773883516875021 3897255180665206318828133)
                  ·
                    refine ⟨730735346374726184780275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3897255180665206318828133 730735346374726184780275)
                    ·
                      rfl

theorem cell23_4269306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 3, 3, 4].length) (baseStart_4269306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4269306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4269306 prefixEnd_4269306 := by exact prefixLift 4269306
  have htrace : WordTrace (prefixWord ++ tailWord_4269306) baseStart_4269306 baseEnd_4269306 := by
    simpa [prefixWord, tailWord_4269306, baseEnd_4269306] using wordTrace_append hprefix tailTrace_4269306
  have hstable : (prefixWord ++ tailWord_4269306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4269306).length < 2 ^ (prefixWord ++ tailWord_4269306).sum := by decide
  have hdescent : baseEnd_4269306 < baseStart_4269306 := by decide
  rcases family_descends (prefixWord ++ tailWord_4269306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4269309 : List Nat := [1, 4, 1, 1, 1, 1, 1, 1, 4, 4, 4]
def baseStart_4269309 : Nat := 118140960795 + 4269309 * 2 ^ 59
def prefixEnd_4269309 : Nat := 4983230072969 + 3 ^ 40 * 4269309 * 2
def baseEnd_4269309 : Nat := 2192207579566142042603311

theorem tailTrace_4269309 : CollatzResearch.WordTrace tailWord_4269309 prefixEnd_4269309 2192207579566142042603311 := by
  unfold tailWord_4269309
  simp only [CollatzResearch.WordTrace]
  refine ⟨155714491690030107772514981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103809661126686738515009987 155714491690030107772514981)
  ·
    refine ⟨29196467191880645207346559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 155714491690030107772514981 29196467191880645207346559)
    ·
      refine ⟨43794700787820967811019839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29196467191880645207346559 43794700787820967811019839)
      ·
        refine ⟨65692051181731451716529759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43794700787820967811019839 65692051181731451716529759)
        ·
          refine ⟨98538076772597177574794639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65692051181731451716529759 98538076772597177574794639)
          ·
            refine ⟨147807115158895766362191959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98538076772597177574794639 147807115158895766362191959)
            ·
              refine ⟨221710672738343649543287939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 147807115158895766362191959 221710672738343649543287939)
              ·
                refine ⟨332566009107515474314931909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 221710672738343649543287939 332566009107515474314931909)
                ·
                  refine ⟨62356126707659151434049733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 332566009107515474314931909 62356126707659151434049733)
                  ·
                    refine ⟨11691773757686090893884325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 62356126707659151434049733 11691773757686090893884325)
                    ·
                      refine ⟨2192207579566142042603311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11691773757686090893884325 2192207579566142042603311)
                      ·
                        rfl

theorem cell23_4269309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 4, 4, 4].length) (baseStart_4269309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4269309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4269309 prefixEnd_4269309 := by exact prefixLift 4269309
  have htrace : WordTrace (prefixWord ++ tailWord_4269309) baseStart_4269309 baseEnd_4269309 := by
    simpa [prefixWord, tailWord_4269309, baseEnd_4269309] using wordTrace_append hprefix tailTrace_4269309
  have hstable : (prefixWord ++ tailWord_4269309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4269309).length < 2 ^ (prefixWord ++ tailWord_4269309).sum := by decide
  have hdescent : baseEnd_4269309 < baseStart_4269309 := by decide
  rcases family_descends (prefixWord ++ tailWord_4269309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4269313 : List Nat := [1, 2, 4, 1, 1, 4, 1, 1, 2, 4, 2]
def baseStart_4269313 : Nat := 118140960795 + 4269313 * 2 ^ 59
def prefixEnd_4269313 : Nat := 4983230072969 + 3 ^ 40 * 4269313 * 2
def baseEnd_4269313 : Nat := 2192209633488760026953293

theorem tailTrace_4269313 : CollatzResearch.WordTrace tailWord_4269313 prefixEnd_4269313 2192209633488760026953293 := by
  unfold tailWord_4269313
  simp only [CollatzResearch.WordTrace]
  refine ⟨155714637582015616455660593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103809758388010410970440395 155714637582015616455660593)
  ·
    refine ⟨116785978186511712341745445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155714637582015616455660593 116785978186511712341745445)
    ·
      refine ⟨21897370909970946064077271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 116785978186511712341745445 21897370909970946064077271)
      ·
        refine ⟨32846056364956419096115907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21897370909970946064077271 32846056364956419096115907)
        ·
          refine ⟨49269084547434628644173861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32846056364956419096115907 49269084547434628644173861)
          ·
            refine ⟨9237953352643992870782599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49269084547434628644173861 9237953352643992870782599)
            ·
              refine ⟨13856930028965989306173899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9237953352643992870782599 13856930028965989306173899)
              ·
                refine ⟨20785395043448983959260849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13856930028965989306173899 20785395043448983959260849)
                ·
                  refine ⟨15589046282586737969445637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20785395043448983959260849 15589046282586737969445637)
                  ·
                    refine ⟨2922946177985013369271057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15589046282586737969445637 2922946177985013369271057)
                    ·
                      refine ⟨2192209633488760026953293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2922946177985013369271057 2192209633488760026953293)
                      ·
                        rfl

theorem cell23_4269313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 1, 2, 4, 2].length) (baseStart_4269313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4269313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4269313 prefixEnd_4269313 := by exact prefixLift 4269313
  have htrace : WordTrace (prefixWord ++ tailWord_4269313) baseStart_4269313 baseEnd_4269313 := by
    simpa [prefixWord, tailWord_4269313, baseEnd_4269313] using wordTrace_append hprefix tailTrace_4269313
  have hstable : (prefixWord ++ tailWord_4269313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4269313).length < 2 ^ (prefixWord ++ tailWord_4269313).sum := by decide
  have hdescent : baseEnd_4269313 < baseStart_4269313 := by decide
  rcases family_descends (prefixWord ++ tailWord_4269313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4269330 : List Nat := [3, 2, 4, 2, 1, 1, 1, 1, 1, 3, 4]
def baseStart_4269330 : Nat := 118140960795 + 4269330 * 2 ^ 59
def prefixEnd_4269330 : Nat := 4983230072969 + 3 ^ 40 * 4269330 * 2
def baseEnd_4269330 : Nat := 2192218362659886460440715

theorem tailTrace_4269330 : CollatzResearch.WordTrace tailWord_4269330 prefixEnd_4269330 2192218362659886460440715 := by
  unfold tailWord_4269330
  simp only [CollatzResearch.WordTrace]
  refine ⟨38928814405738507089757361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103810171748636018906019629 38928814405738507089757361)
  ·
    refine ⟨29196610804303880317318021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38928814405738507089757361 29196610804303880317318021)
    ·
      refine ⟨5474364525806977559497129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29196610804303880317318021 5474364525806977559497129)
      ·
        refine ⟨4105773394355233169622847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5474364525806977559497129 4105773394355233169622847)
        ·
          refine ⟨6158660091532849754434271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4105773394355233169622847 6158660091532849754434271)
          ·
            refine ⟨9237990137299274631651407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6158660091532849754434271 9237990137299274631651407)
            ·
              refine ⟨13856985205948911947477111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9237990137299274631651407 13856985205948911947477111)
              ·
                refine ⟨20785477808923367921215667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13856985205948911947477111 20785477808923367921215667)
                ·
                  refine ⟨31178216713385051881823501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20785477808923367921215667 31178216713385051881823501)
                  ·
                    refine ⟨11691831267519394455683813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 31178216713385051881823501 11691831267519394455683813)
                    ·
                      refine ⟨2192218362659886460440715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11691831267519394455683813 2192218362659886460440715)
                      ·
                        rfl

theorem cell23_4269330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_4269330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4269330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4269330 prefixEnd_4269330 := by exact prefixLift 4269330
  have htrace : WordTrace (prefixWord ++ tailWord_4269330) baseStart_4269330 baseEnd_4269330 := by
    simpa [prefixWord, tailWord_4269330, baseEnd_4269330] using wordTrace_append hprefix tailTrace_4269330
  have hstable : (prefixWord ++ tailWord_4269330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4269330).length < 2 ^ (prefixWord ++ tailWord_4269330).sum := by decide
  have hdescent : baseEnd_4269330 < baseStart_4269330 := by decide
  rcases family_descends (prefixWord ++ tailWord_4269330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4269357 : List Nat := [1, 5, 3, 1, 1, 1, 2, 4, 1, 4]
def baseStart_4269357 : Nat := 118140960795 + 4269357 * 2 ^ 59
def prefixEnd_4269357 : Nat := 4983230072969 + 3 ^ 40 * 4269357 * 2
def baseEnd_4269357 : Nat := 730744075545852618267697

theorem tailTrace_4269357 : CollatzResearch.WordTrace tailWord_4269357 prefixEnd_4269357 730744075545852618267697 := by
  unfold tailWord_4269357
  simp only [CollatzResearch.WordTrace]
  refine ⟨155716242393856211970262325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103810828262570807980174883 155716242393856211970262325)
  ·
    refine ⟨14598397724424019872212093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 155716242393856211970262325 14598397724424019872212093)
    ·
      refine ⟨5474399146659007452079535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14598397724424019872212093 5474399146659007452079535)
      ·
        refine ⟨8211598719988511178119303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5474399146659007452079535 8211598719988511178119303)
        ·
          refine ⟨12317398079982766767178955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8211598719988511178119303 12317398079982766767178955)
          ·
            refine ⟨18476097119974150150768433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12317398079982766767178955 18476097119974150150768433)
            ·
              refine ⟨13857072839980612613076325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18476097119974150150768433 13857072839980612613076325)
              ·
                refine ⟨2598201157496364864951811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13857072839980612613076325 2598201157496364864951811)
                ·
                  refine ⟨3897301736244547297427717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2598201157496364864951811 3897301736244547297427717)
                  ·
                    refine ⟨730744075545852618267697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3897301736244547297427717 730744075545852618267697)
                    ·
                      rfl

theorem cell23_4269357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 4, 1, 4].length) (baseStart_4269357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4269357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4269357 prefixEnd_4269357 := by exact prefixLift 4269357
  have htrace : WordTrace (prefixWord ++ tailWord_4269357) baseStart_4269357 baseEnd_4269357 := by
    simpa [prefixWord, tailWord_4269357, baseEnd_4269357] using wordTrace_append hprefix tailTrace_4269357
  have hstable : (prefixWord ++ tailWord_4269357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4269357).length < 2 ^ (prefixWord ++ tailWord_4269357).sum := by decide
  have hdescent : baseEnd_4269357 < baseStart_4269357 := by decide
  rcases family_descends (prefixWord ++ tailWord_4269357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4269363 : List Nat := [1, 1, 1, 2, 5, 2, 1, 3, 3, 1, 3]
def baseStart_4269363 : Nat := 118140960795 + 4269363 * 2 ^ 59
def prefixEnd_4269363 : Nat := 4983230072969 + 3 ^ 40 * 4269363 * 2
def baseEnd_4269363 : Nat := 2192235307521484831328063

theorem tailTrace_4269363 : CollatzResearch.WordTrace tailWord_4269363 prefixEnd_4269363 2192235307521484831328063 := by
  unfold tailWord_4269363
  simp only [CollatzResearch.WordTrace]
  refine ⟨155716461231834474994980743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103810974154556316663320495 155716461231834474994980743)
  ·
    refine ⟨233574691847751712492471115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155716461231834474994980743 233574691847751712492471115)
    ·
      refine ⟨350362037771627568738706673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 233574691847751712492471115 350362037771627568738706673)
      ·
        refine ⟨262771528328720676554030005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 350362037771627568738706673 262771528328720676554030005)
        ·
          refine ⟨24634830780817563426940313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 262771528328720676554030005 24634830780817563426940313)
          ·
            refine ⟨18476123085613172570205235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24634830780817563426940313 18476123085613172570205235)
            ·
              refine ⟨27714184628419758855307853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18476123085613172570205235 27714184628419758855307853)
              ·
                refine ⟨10392819235657409570740445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27714184628419758855307853 10392819235657409570740445)
                ·
                  refine ⟨3897307213371528589027667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10392819235657409570740445 3897307213371528589027667)
                  ·
                    refine ⟨5845960820057292883541501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3897307213371528589027667 5845960820057292883541501)
                    ·
                      refine ⟨2192235307521484831328063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5845960820057292883541501 2192235307521484831328063)
                      ·
                        rfl

theorem cell23_4269363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 3, 3, 1, 3].length) (baseStart_4269363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4269363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4269363 prefixEnd_4269363 := by exact prefixLift 4269363
  have htrace : WordTrace (prefixWord ++ tailWord_4269363) baseStart_4269363 baseEnd_4269363 := by
    simpa [prefixWord, tailWord_4269363, baseEnd_4269363] using wordTrace_append hprefix tailTrace_4269363
  have hstable : (prefixWord ++ tailWord_4269363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4269363).length < 2 ^ (prefixWord ++ tailWord_4269363).sum := by decide
  have hdescent : baseEnd_4269363 < baseStart_4269363 := by decide
  rcases family_descends (prefixWord ++ tailWord_4269363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4269383 : List Nat := [1, 1, 4, 1, 2, 4, 2, 2, 1, 5]
def baseStart_4269383 : Nat := 118140960795 + 4269383 * 2 ^ 59
def prefixEnd_4269383 : Nat := 4983230072969 + 3 ^ 40 * 4269383 * 2
def baseEnd_4269383 : Nat := 730748525711524917692657

theorem tailTrace_4269383 : CollatzResearch.WordTrace tailWord_4269383 prefixEnd_4269383 730748525711524917692657 := by
  unfold tailWord_4269383
  simp only [CollatzResearch.WordTrace]
  refine ⟨155717190691762018410708803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103811460461174678940472535 155717190691762018410708803)
  ·
    refine ⟨233575786037643027616063205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155717190691762018410708803 233575786037643027616063205)
    ·
      refine ⟨43795459882058067678011851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 233575786037643027616063205 43795459882058067678011851)
      ·
        refine ⟨65693189823087101517017777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43795459882058067678011851 65693189823087101517017777)
        ·
          refine ⟨49269892367315326137763333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65693189823087101517017777 49269892367315326137763333)
          ·
            refine ⟨9238104818871623650830625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49269892367315326137763333 9238104818871623650830625)
            ·
              refine ⟨6928578614153717738122969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9238104818871623650830625 6928578614153717738122969)
              ·
                refine ⟨5196433960615288303592227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6928578614153717738122969 5196433960615288303592227)
                ·
                  refine ⟨7794650940922932455388341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5196433960615288303592227 7794650940922932455388341)
                  ·
                    refine ⟨730748525711524917692657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7794650940922932455388341 730748525711524917692657)
                    ·
                      rfl

theorem cell23_4269383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 2, 2, 1, 5].length) (baseStart_4269383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4269383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4269383 prefixEnd_4269383 := by exact prefixLift 4269383
  have htrace : WordTrace (prefixWord ++ tailWord_4269383) baseStart_4269383 baseEnd_4269383 := by
    simpa [prefixWord, tailWord_4269383, baseEnd_4269383] using wordTrace_append hprefix tailTrace_4269383
  have hstable : (prefixWord ++ tailWord_4269383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4269383).length < 2 ^ (prefixWord ++ tailWord_4269383).sum := by decide
  have hdescent : baseEnd_4269383 < baseStart_4269383 := by decide
  rcases family_descends (prefixWord ++ tailWord_4269383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4269386 : List Nat := [3, 1, 2, 1, 1, 1, 1, 5, 3, 1, 4]
def baseStart_4269386 : Nat := 118140960795 + 4269386 * 2 ^ 59
def prefixEnd_4269386 : Nat := 4983230072969 + 3 ^ 40 * 4269386 * 2
def baseEnd_4269386 : Nat := 2192247117576538241340457

theorem tailTrace_4269386 : CollatzResearch.WordTrace tailWord_4269386 prefixEnd_4269386 2192247117576538241340457 := by
  unfold tailWord_4269386
  simp only [CollatzResearch.WordTrace]
  refine ⟨38929325027687787480767003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103811533407167433282045341 38929325027687787480767003)
  ·
    refine ⟨58393987541531681221150505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38929325027687787480767003 58393987541531681221150505)
    ·
      refine ⟨43795490656148760915862879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58393987541531681221150505 43795490656148760915862879)
      ·
        refine ⟨65693235984223141373794319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43795490656148760915862879 65693235984223141373794319)
        ·
          refine ⟨98539853976334712060691479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65693235984223141373794319 98539853976334712060691479)
          ·
            refine ⟨147809780964502068091037219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98539853976334712060691479 147809780964502068091037219)
            ·
              refine ⟨221714671446753102136555829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 147809780964502068091037219 221714671446753102136555829)
              ·
                refine ⟨20785750448133103325302109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 221714671446753102136555829 20785750448133103325302109)
                ·
                  refine ⟨7794656418049913746988291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20785750448133103325302109 7794656418049913746988291)
                  ·
                    refine ⟨11691984627074870620482437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7794656418049913746988291 11691984627074870620482437)
                    ·
                      refine ⟨2192247117576538241340457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11691984627074870620482437 2192247117576538241340457)
                      ·
                        rfl

theorem cell23_4269386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 5, 3, 1, 4].length) (baseStart_4269386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4269386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4269386 prefixEnd_4269386 := by exact prefixLift 4269386
  have htrace : WordTrace (prefixWord ++ tailWord_4269386) baseStart_4269386 baseEnd_4269386 := by
    simpa [prefixWord, tailWord_4269386, baseEnd_4269386] using wordTrace_append hprefix tailTrace_4269386
  have hstable : (prefixWord ++ tailWord_4269386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4269386).length < 2 ^ (prefixWord ++ tailWord_4269386).sum := by decide
  have hdescent : baseEnd_4269386 < baseStart_4269386 := by decide
  rcases family_descends (prefixWord ++ tailWord_4269386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4269396 : List Nat := [2, 4, 1, 1, 2, 1, 2, 1, 3, 6]
def baseStart_4269396 : Nat := 118140960795 + 4269396 * 2 ^ 59
def prefixEnd_4269396 : Nat := 4983230072969 + 3 ^ 40 * 4269396 * 2
def baseEnd_4269396 : Nat := 730750750794361067405137

theorem tailTrace_4269396 : CollatzResearch.WordTrace tailWord_4269396 prefixEnd_4269396 730750750794361067405137 := by
  unfold tailWord_4269396
  simp only [CollatzResearch.WordTrace]
  refine ⟨77858832420357460815466021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103811776560476614420621361 77858832420357460815466021)
  ·
    refine ⟨14598531078817023902899879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 77858832420357460815466021 14598531078817023902899879)
    ·
      refine ⟨21897796618225535854349819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14598531078817023902899879 21897796618225535854349819)
      ·
        refine ⟨32846694927338303781524729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21897796618225535854349819 32846694927338303781524729)
        ·
          refine ⟨24635021195503727836143547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32846694927338303781524729 24635021195503727836143547)
          ·
            refine ⟨36952531793255591754215321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24635021195503727836143547 36952531793255591754215321)
            ·
              refine ⟨27714398844941693815661491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36952531793255591754215321 27714398844941693815661491)
              ·
                refine ⟨41571598267412540723492237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27714398844941693815661491 41571598267412540723492237)
                ·
                  refine ⟨15589349350279702771309589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41571598267412540723492237 15589349350279702771309589)
                  ·
                    refine ⟨730750750794361067405137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15589349350279702771309589 730750750794361067405137)
                    ·
                      rfl

theorem cell23_4269396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 1, 3, 6].length) (baseStart_4269396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4269396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4269396 prefixEnd_4269396 := by exact prefixLift 4269396
  have htrace : WordTrace (prefixWord ++ tailWord_4269396) baseStart_4269396 baseEnd_4269396 := by
    simpa [prefixWord, tailWord_4269396, baseEnd_4269396] using wordTrace_append hprefix tailTrace_4269396
  have hstable : (prefixWord ++ tailWord_4269396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4269396).length < 2 ^ (prefixWord ++ tailWord_4269396).sum := by decide
  have hdescent : baseEnd_4269396 < baseStart_4269396 := by decide
  rcases family_descends (prefixWord ++ tailWord_4269396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4269397 : List Nat := [1, 3, 2, 2, 3, 1, 3, 3, 1, 1, 3]
def baseStart_4269397 : Nat := 118140960795 + 4269397 * 2 ^ 59
def prefixEnd_4269397 : Nat := 4983230072969 + 3 ^ 40 * 4269397 * 2
def baseEnd_4269397 : Nat := 2192252765863737698302907

theorem tailTrace_4269397 : CollatzResearch.WordTrace tailWord_4269397 prefixEnd_4269397 2192252765863737698302907 := by
  unfold tailWord_4269397
  simp only [CollatzResearch.WordTrace]
  refine ⟨155717701313711298801718445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103811800875807532534478963 155717701313711298801718445)
  ·
    refine ⟨58394137992641737050644417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 155717701313711298801718445 58394137992641737050644417)
    ·
      refine ⟨43795603494481302787983313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58394137992641737050644417 43795603494481302787983313)
      ·
        refine ⟨32846702620860977090987485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43795603494481302787983313 32846702620860977090987485)
        ·
          refine ⟨12317513482822866409120307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32846702620860977090987485 12317513482822866409120307)
          ·
            refine ⟨18476270224234299613680461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12317513482822866409120307 18476270224234299613680461)
            ·
              refine ⟨6928601334087862355130173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18476270224234299613680461 6928601334087862355130173)
              ·
                refine ⟨2598225500282948383173815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6928601334087862355130173 2598225500282948383173815)
                ·
                  refine ⟨3897338250424422574760723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2598225500282948383173815 3897338250424422574760723)
                  ·
                    refine ⟨5846007375636633862141085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3897338250424422574760723 5846007375636633862141085)
                    ·
                      refine ⟨2192252765863737698302907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5846007375636633862141085 2192252765863737698302907)
                      ·
                        rfl

theorem cell23_4269397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 3, 3, 1, 1, 3].length) (baseStart_4269397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4269397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4269397 prefixEnd_4269397 := by exact prefixLift 4269397
  have htrace : WordTrace (prefixWord ++ tailWord_4269397) baseStart_4269397 baseEnd_4269397 := by
    simpa [prefixWord, tailWord_4269397, baseEnd_4269397] using wordTrace_append hprefix tailTrace_4269397
  have hstable : (prefixWord ++ tailWord_4269397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4269397).length < 2 ^ (prefixWord ++ tailWord_4269397).sum := by decide
  have hdescent : baseEnd_4269397 < baseStart_4269397 := by decide
  rcases family_descends (prefixWord ++ tailWord_4269397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4269413 : List Nat := [1, 3, 1, 3, 1, 2, 2, 4, 2, 4]
def baseStart_4269413 : Nat := 118140960795 + 4269413 * 2 ^ 59
def prefixEnd_4269413 : Nat := 4983230072969 + 3 ^ 40 * 4269413 * 2
def baseEnd_4269413 : Nat := 730753660518069878567611

theorem tailTrace_4269413 : CollatzResearch.WordTrace tailWord_4269413 prefixEnd_4269413 730753660518069878567611 := by
  unfold tailWord_4269413
  simp only [CollatzResearch.WordTrace]
  refine ⟨155718284881653333534300893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103812189921102222356200595 155718284881653333534300893)
  ·
    refine ⟨58394356830620000075362835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 155718284881653333534300893 58394356830620000075362835)
    ·
      refine ⟨87591535245930000113044253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58394356830620000075362835 87591535245930000113044253)
      ·
        refine ⟨32846825717223750042391595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87591535245930000113044253 32846825717223750042391595)
        ·
          refine ⟨49270238575835625063587393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32846825717223750042391595 49270238575835625063587393)
          ·
            refine ⟨36952678931876718797690545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49270238575835625063587393 36952678931876718797690545)
            ·
              refine ⟨27714509198907539098267909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36952678931876718797690545 27714509198907539098267909)
              ·
                refine ⟨5196470474795163580925233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27714509198907539098267909 5196470474795163580925233)
                ·
                  refine ⟨3897352856096372685693925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5196470474795163580925233 3897352856096372685693925)
                  ·
                    refine ⟨730753660518069878567611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3897352856096372685693925 730753660518069878567611)
                    ·
                      rfl

theorem cell23_4269413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 4, 2, 4].length) (baseStart_4269413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4269413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4269413 prefixEnd_4269413 := by exact prefixLift 4269413
  have htrace : WordTrace (prefixWord ++ tailWord_4269413) baseStart_4269413 baseEnd_4269413 := by
    simpa [prefixWord, tailWord_4269413, baseEnd_4269413] using wordTrace_append hprefix tailTrace_4269413
  have hstable : (prefixWord ++ tailWord_4269413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4269413).length < 2 ^ (prefixWord ++ tailWord_4269413).sum := by decide
  have hdescent : baseEnd_4269413 < baseStart_4269413 := by decide
  rcases family_descends (prefixWord ++ tailWord_4269413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4269419 : List Nat := [1, 1, 1, 1, 2, 2, 2, 1, 1, 4, 7]
def baseStart_4269419 : Nat := 118140960795 + 4269419 * 2 ^ 59
def prefixEnd_4269419 : Nat := 4983230072969 + 3 ^ 40 * 4269419 * 2
def baseEnd_4269419 : Nat := 2192264062438136612227805

theorem tailTrace_4269419 : CollatzResearch.WordTrace tailWord_4269419 prefixEnd_4269419 2192264062438136612227805 := by
  unfold tailWord_4269419
  simp only [CollatzResearch.WordTrace]
  refine ⟨155718503719631596559019311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103812335813087731039346207 155718503719631596559019311)
  ·
    refine ⟨233577755579447394838528967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155718503719631596559019311 233577755579447394838528967)
    ·
      refine ⟨350366633369171092257793451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 233577755579447394838528967 350366633369171092257793451)
      ·
        refine ⟨525549950053756638386690177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 350366633369171092257793451 525549950053756638386690177)
        ·
          refine ⟨394162462540317478790017633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 525549950053756638386690177 394162462540317478790017633)
          ·
            refine ⟨295621846905238109092513225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 394162462540317478790017633 295621846905238109092513225)
            ·
              refine ⟨221716385178928581819384919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 295621846905238109092513225 221716385178928581819384919)
              ·
                refine ⟨332574577768392872729077379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 221716385178928581819384919 332574577768392872729077379)
                ·
                  refine ⟨498861866652589309093616069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 332574577768392872729077379 498861866652589309093616069)
                  ·
                    refine ⟨93536599997360495455053013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 498861866652589309093616069 93536599997360495455053013)
                    ·
                      refine ⟨2192264062438136612227805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 93536599997360495455053013 2192264062438136612227805)
                      ·
                        rfl

theorem cell23_4269419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 4, 7].length) (baseStart_4269419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4269419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4269419 prefixEnd_4269419 := by exact prefixLift 4269419
  have htrace : WordTrace (prefixWord ++ tailWord_4269419) baseStart_4269419 baseEnd_4269419 := by
    simpa [prefixWord, tailWord_4269419, baseEnd_4269419] using wordTrace_append hprefix tailTrace_4269419
  have hstable : (prefixWord ++ tailWord_4269419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4269419).length < 2 ^ (prefixWord ++ tailWord_4269419).sum := by decide
  have hdescent : baseEnd_4269419 < baseStart_4269419 := by decide
  rcases family_descends (prefixWord ++ tailWord_4269419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4269426 : List Nat := [3, 2, 1, 2, 1, 2, 4, 8]
def baseStart_4269426 : Nat := 118140960795 + 4269426 * 2 ^ 59
def prefixEnd_4269426 : Nat := 4983230072969 + 3 ^ 40 * 4269426 * 2
def baseEnd_4269426 : Nat := 81195098400100669808899

theorem tailTrace_4269426 : CollatzResearch.WordTrace tailWord_4269426 prefixEnd_4269426 81195098400100669808899 := by
  unfold tailWord_4269426
  simp only [CollatzResearch.WordTrace]
  refine ⟨38929689757651559188631033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103812506020404157836349421 38929689757651559188631033)
  ·
    refine ⟨29197267318238669391473275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38929689757651559188631033 29197267318238669391473275)
    ·
      refine ⟨43795900977358004087209913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29197267318238669391473275 43795900977358004087209913)
      ·
        refine ⟨32846925733018503065407435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43795900977358004087209913 32846925733018503065407435)
        ·
          refine ⟨49270388599527754598111153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32846925733018503065407435 49270388599527754598111153)
          ·
            refine ⟨36952791449645815948583365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49270388599527754598111153 36952791449645815948583365)
            ·
              refine ⟨6928648396808590490359381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36952791449645815948583365 6928648396808590490359381)
              ·
                refine ⟨81195098400100669808899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6928648396808590490359381 81195098400100669808899)
                ·
                  rfl

theorem cell23_4269426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 4, 8].length) (baseStart_4269426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4269426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4269426 prefixEnd_4269426 := by exact prefixLift 4269426
  have htrace : WordTrace (prefixWord ++ tailWord_4269426) baseStart_4269426 baseEnd_4269426 := by
    simpa [prefixWord, tailWord_4269426, baseEnd_4269426] using wordTrace_append hprefix tailTrace_4269426
  have hstable : (prefixWord ++ tailWord_4269426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4269426).length < 2 ^ (prefixWord ++ tailWord_4269426).sum := by decide
  have hdescent : baseEnd_4269426 < baseStart_4269426 := by decide
  rcases family_descends (prefixWord ++ tailWord_4269426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4269471 : List Nat := [1, 1, 2, 5, 1, 4, 2, 2, 1, 2, 2]
def baseStart_4269471 : Nat := 118140960795 + 4269471 * 2 ^ 59
def prefixEnd_4269471 : Nat := 4983230072969 + 3 ^ 40 * 4269471 * 2
def baseEnd_4269471 : Nat := 2192290763432170408777567

theorem tailTrace_4269471 : CollatzResearch.WordTrace tailWord_4269471 prefixEnd_4269471 2192290763432170408777567 := by
  unfold tailWord_4269471
  simp only [CollatzResearch.WordTrace]
  refine ⟨155720400315443209439912267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103813600210295472959941511 155720400315443209439912267)
  ·
    refine ⟨233580600473164814159868401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155720400315443209439912267 233580600473164814159868401)
    ·
      refine ⟨175185450354873610619901301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 233580600473164814159868401 175185450354873610619901301)
      ·
        refine ⟨16423635970769400995615747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 175185450354873610619901301 16423635970769400995615747)
        ·
          refine ⟨24635453956154101493423621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16423635970769400995615747 24635453956154101493423621)
          ·
            refine ⟨4619147616778894030016929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24635453956154101493423621 4619147616778894030016929)
            ·
              refine ⟨3464360712584170522512697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4619147616778894030016929 3464360712584170522512697)
              ·
                refine ⟨2598270534438127891884523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3464360712584170522512697 2598270534438127891884523)
                ·
                  refine ⟨3897405801657191837826785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2598270534438127891884523 3897405801657191837826785)
                  ·
                    refine ⟨2923054351242893878370089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3897405801657191837826785 2923054351242893878370089)
                    ·
                      refine ⟨2192290763432170408777567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2923054351242893878370089 2192290763432170408777567)
                      ·
                        rfl

theorem cell23_4269471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 2, 2, 1, 2, 2].length) (baseStart_4269471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4269471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4269471 prefixEnd_4269471 := by exact prefixLift 4269471
  have htrace : WordTrace (prefixWord ++ tailWord_4269471) baseStart_4269471 baseEnd_4269471 := by
    simpa [prefixWord, tailWord_4269471, baseEnd_4269471] using wordTrace_append hprefix tailTrace_4269471
  have hstable : (prefixWord ++ tailWord_4269471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4269471).length < 2 ^ (prefixWord ++ tailWord_4269471).sum := by decide
  have hdescent : baseEnd_4269471 < baseStart_4269471 := by decide
  rcases family_descends (prefixWord ++ tailWord_4269471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4269496 : List Nat := [2, 1, 2, 1, 2, 2, 2, 1, 4, 1, 5]
def baseStart_4269496 : Nat := 118140960795 + 4269496 * 2 ^ 59
def prefixEnd_4269496 : Nat := 4983230072969 + 3 ^ 40 * 4269496 * 2
def baseEnd_4269496 : Nat := 2192303600448532810964951

theorem tailTrace_4269496 : CollatzResearch.WordTrace tailWord_4269496 prefixEnd_4269496 2192303600448532810964951 := by
  unfold tailWord_4269496
  simp only [CollatzResearch.WordTrace]
  refine ⟨77860656070176319354786171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103814208093568425806381561 77860656070176319354786171)
  ·
    refine ⟨116790984105264479032179257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77860656070176319354786171 116790984105264479032179257)
    ·
      refine ⟨87593238078948359274134443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116790984105264479032179257 87593238078948359274134443)
      ·
        refine ⟨131389857118422538911201665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87593238078948359274134443 131389857118422538911201665)
        ·
          refine ⟨98542392838816904183401249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 131389857118422538911201665 98542392838816904183401249)
          ·
            refine ⟨73906794629112678137550937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98542392838816904183401249 73906794629112678137550937)
            ·
              refine ⟨55430095971834508603163203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73906794629112678137550937 55430095971834508603163203)
              ·
                refine ⟨83145143957751762904744805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55430095971834508603163203 83145143957751762904744805)
                ·
                  refine ⟨15589714492078455544639651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 83145143957751762904744805 15589714492078455544639651)
                  ·
                    refine ⟨23384571738117683316959477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15589714492078455544639651 23384571738117683316959477)
                    ·
                      refine ⟨2192303600448532810964951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23384571738117683316959477 2192303600448532810964951)
                      ·
                        rfl

theorem cell23_4269496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 4, 1, 5].length) (baseStart_4269496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4269496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4269496 prefixEnd_4269496 := by exact prefixLift 4269496
  have htrace : WordTrace (prefixWord ++ tailWord_4269496) baseStart_4269496 baseEnd_4269496 := by
    simpa [prefixWord, tailWord_4269496, baseEnd_4269496] using wordTrace_append hprefix tailTrace_4269496
  have hstable : (prefixWord ++ tailWord_4269496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4269496).length < 2 ^ (prefixWord ++ tailWord_4269496).sum := by decide
  have hdescent : baseEnd_4269496 < baseStart_4269496 := by decide
  rcases family_descends (prefixWord ++ tailWord_4269496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4269514 : List Nat := [3, 1, 2, 1, 2, 5, 2, 1, 1, 3, 2]
def baseStart_4269514 : Nat := 118140960795 + 4269514 * 2 ^ 59
def prefixEnd_4269514 : Nat := 4983230072969 + 3 ^ 40 * 4269514 * 2
def baseEnd_4269514 : Nat := 2192312843100313740539869

theorem tailTrace_4269514 : CollatzResearch.WordTrace tailWord_4269514 prefixEnd_4269514 2192312843100313740539869 := by
  unfold tailWord_4269514
  simp only [CollatzResearch.WordTrace]
  refine ⟨38930492163571856945931899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103814645769524951855818397 38930492163571856945931899)
  ·
    refine ⟨58395738245357785418897849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38930492163571856945931899 58395738245357785418897849)
    ·
      refine ⟨43796803684018339064173387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58395738245357785418897849 43796803684018339064173387)
      ·
        refine ⟨65695205526027508596260081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43796803684018339064173387 65695205526027508596260081)
        ·
          refine ⟨49271404144520631447195061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65695205526027508596260081 49271404144520631447195061)
          ·
            refine ⟨4619194138548809198174537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 49271404144520631447195061 4619194138548809198174537)
            ·
              refine ⟨3464395603911606898630903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4619194138548809198174537 3464395603911606898630903)
              ·
                refine ⟨5196593405867410347946355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3464395603911606898630903 5196593405867410347946355)
                ·
                  refine ⟨7794890108801115521919533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5196593405867410347946355 7794890108801115521919533)
                  ·
                    refine ⟨2923083790800418320719825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7794890108801115521919533 2923083790800418320719825)
                    ·
                      refine ⟨2192312843100313740539869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2923083790800418320719825 2192312843100313740539869)
                      ·
                        rfl

theorem cell23_4269514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 2, 1, 1, 3, 2].length) (baseStart_4269514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4269514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4269514 prefixEnd_4269514 := by exact prefixLift 4269514
  have htrace : WordTrace (prefixWord ++ tailWord_4269514) baseStart_4269514 baseEnd_4269514 := by
    simpa [prefixWord, tailWord_4269514, baseEnd_4269514] using wordTrace_append hprefix tailTrace_4269514
  have hstable : (prefixWord ++ tailWord_4269514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4269514).length < 2 ^ (prefixWord ++ tailWord_4269514).sum := by decide
  have hdescent : baseEnd_4269514 < baseStart_4269514 := by decide
  rcases family_descends (prefixWord ++ tailWord_4269514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4269533 : List Nat := [1, 4, 3, 1, 1, 2, 1, 3, 7]
def baseStart_4269533 : Nat := 118140960795 + 4269533 * 2 ^ 59
def prefixEnd_4269533 : Nat := 4983230072969 + 3 ^ 40 * 4269533 * 2
def baseEnd_4269533 : Nat := 243591399914749907355809

theorem tailTrace_4269533 : CollatzResearch.WordTrace tailWord_4269533 prefixEnd_4269533 243591399914749907355809 := by
  unfold tailWord_4269533
  simp only [CollatzResearch.WordTrace]
  refine ⟨155722661641218594028669253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103815107760812396019112835 155722661641218594028669253)
  ·
    refine ⟨29197999057728486380375485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 155722661641218594028669253 29197999057728486380375485)
    ·
      refine ⟨10949249646648182392640807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29197999057728486380375485 10949249646648182392640807)
      ·
        refine ⟨16423874469972273588961211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10949249646648182392640807 16423874469972273588961211)
        ·
          refine ⟨24635811704958410383441817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16423874469972273588961211 24635811704958410383441817)
          ·
            refine ⟨18476858778718807787581363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24635811704958410383441817 18476858778718807787581363)
            ·
              refine ⟨27715288168078211681372045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18476858778718807787581363 27715288168078211681372045)
              ·
                refine ⟨10393233063029329380514517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27715288168078211681372045 10393233063029329380514517)
                ·
                  refine ⟨243591399914749907355809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10393233063029329380514517 243591399914749907355809)
                  ·
                    rfl

theorem cell23_4269533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 3, 7].length) (baseStart_4269533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4269533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4269533 prefixEnd_4269533 := by exact prefixLift 4269533
  have htrace : WordTrace (prefixWord ++ tailWord_4269533) baseStart_4269533 baseEnd_4269533 := by
    simpa [prefixWord, tailWord_4269533, baseEnd_4269533] using wordTrace_append hprefix tailTrace_4269533
  have hstable : (prefixWord ++ tailWord_4269533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4269533).length < 2 ^ (prefixWord ++ tailWord_4269533).sum := by decide
  have hdescent : baseEnd_4269533 < baseStart_4269533 := by decide
  rcases family_descends (prefixWord ++ tailWord_4269533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4269544 : List Nat := [2, 1, 4, 1, 1, 2, 5, 1, 2, 2, 2]
def baseStart_4269544 : Nat := 118140960795 + 4269544 * 2 ^ 59
def prefixEnd_4269544 : Nat := 4983230072969 + 3 ^ 40 * 4269544 * 2
def baseEnd_4269544 : Nat := 2192328247519948623164731

theorem tailTrace_4269544 : CollatzResearch.WordTrace tailWord_4269544 prefixEnd_4269544 2192328247519948623164731 := by
  unfold tailWord_4269544
  simp only [CollatzResearch.WordTrace]
  refine ⟨77861531422089371453659843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103815375229452495271546457 77861531422089371453659843)
  ·
    refine ⟨116792297133134057180489765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77861531422089371453659843 116792297133134057180489765)
    ·
      refine ⟨21898555712462635721341831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 116792297133134057180489765 21898555712462635721341831)
      ·
        refine ⟨32847833568693953582012747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21898555712462635721341831 32847833568693953582012747)
        ·
          refine ⟨49271750353040930373019121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32847833568693953582012747 49271750353040930373019121)
          ·
            refine ⟨36953812764780697779764341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49271750353040930373019121 36953812764780697779764341)
            ·
              refine ⟨3464419946698190416852907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36953812764780697779764341 3464419946698190416852907)
              ·
                refine ⟨5196629920047285625279361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3464419946698190416852907 5196629920047285625279361)
                ·
                  refine ⟨3897472440035464218959521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5196629920047285625279361 3897472440035464218959521)
                  ·
                    refine ⟨2923104330026598164219641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3897472440035464218959521 2923104330026598164219641)
                    ·
                      refine ⟨2192328247519948623164731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2923104330026598164219641 2192328247519948623164731)
                      ·
                        rfl

theorem cell23_4269544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 5, 1, 2, 2, 2].length) (baseStart_4269544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4269544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4269544 prefixEnd_4269544 := by exact prefixLift 4269544
  have htrace : WordTrace (prefixWord ++ tailWord_4269544) baseStart_4269544 baseEnd_4269544 := by
    simpa [prefixWord, tailWord_4269544, baseEnd_4269544] using wordTrace_append hprefix tailTrace_4269544
  have hstable : (prefixWord ++ tailWord_4269544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4269544).length < 2 ^ (prefixWord ++ tailWord_4269544).sum := by decide
  have hdescent : baseEnd_4269544 < baseStart_4269544 := by decide
  rcases family_descends (prefixWord ++ tailWord_4269544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4269580 : List Nat := [2, 2, 1, 2, 5, 1, 1, 2, 2, 5]
def baseStart_4269580 : Nat := 118140960795 + 4269580 * 2 ^ 59
def prefixEnd_4269580 : Nat := 4983230072969 + 3 ^ 40 * 4269580 * 2
def baseEnd_4269580 : Nat := 730782244274503494104855

theorem tailTrace_4269580 : CollatzResearch.WordTrace tailWord_4269580 prefixEnd_4269580 730782244274503494104855 := by
  unfold tailWord_4269580
  simp only [CollatzResearch.WordTrace]
  refine ⟨77862187936024160527815097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103816250581365547370420129 77862187936024160527815097)
  ·
    refine ⟨58396640952018120395861323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77862187936024160527815097 58396640952018120395861323)
    ·
      refine ⟨87594961428027180593791985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58396640952018120395861323 87594961428027180593791985)
      ·
        refine ⟨65696221071020385445343989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87594961428027180593791985 65696221071020385445343989)
        ·
          refine ⟨6159020725408161135500999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 65696221071020385445343989 6159020725408161135500999)
          ·
            refine ⟨9238531088112241703251499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6159020725408161135500999 9238531088112241703251499)
            ·
              refine ⟨13857796632168362554877249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9238531088112241703251499 13857796632168362554877249)
              ·
                refine ⟨10393347474126271916157937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13857796632168362554877249 10393347474126271916157937)
                ·
                  refine ⟨7795010605594703937118453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10393347474126271916157937 7795010605594703937118453)
                  ·
                    refine ⟨730782244274503494104855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7795010605594703937118453 730782244274503494104855)
                    ·
                      rfl

theorem cell23_4269580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 2, 2, 5].length) (baseStart_4269580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4269580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4269580 prefixEnd_4269580 := by exact prefixLift 4269580
  have htrace : WordTrace (prefixWord ++ tailWord_4269580) baseStart_4269580 baseEnd_4269580 := by
    simpa [prefixWord, tailWord_4269580, baseEnd_4269580] using wordTrace_append hprefix tailTrace_4269580
  have hstable : (prefixWord ++ tailWord_4269580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4269580).length < 2 ^ (prefixWord ++ tailWord_4269580).sum := by decide
  have hdescent : baseEnd_4269580 < baseStart_4269580 := by decide
  rcases family_descends (prefixWord ++ tailWord_4269580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4269610 : List Nat := [3, 1, 4, 1, 1, 1, 2, 1, 5, 4]
def baseStart_4269610 : Nat := 118140960795 + 4269610 * 2 ^ 59
def prefixEnd_4269610 : Nat := 4983230072969 + 3 ^ 40 * 4269610 * 2
def baseEnd_4269610 : Nat := 730787379081048454979809

theorem tailTrace_4269610 : CollatzResearch.WordTrace tailWord_4269610 prefixEnd_4269610 730787379081048454979809 := by
  unfold tailWord_4269610
  simp only [CollatzResearch.WordTrace]
  refine ⟨38931367515484909044805571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103816980041293090786148189 38931367515484909044805571)
  ·
    refine ⟨58397051273227363567208357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38931367515484909044805571 58397051273227363567208357)
    ·
      refine ⟨10949447113730130668851567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58397051273227363567208357 10949447113730130668851567)
      ·
        refine ⟨16424170670595196003277351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10949447113730130668851567 16424170670595196003277351)
        ·
          refine ⟨24636256005892794004916027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16424170670595196003277351 24636256005892794004916027)
          ·
            refine ⟨36954384008839191007374041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24636256005892794004916027 36954384008839191007374041)
            ·
              refine ⟨27715788006629393255530531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36954384008839191007374041 27715788006629393255530531)
              ·
                refine ⟨41573682009944089883295797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27715788006629393255530531 41573682009944089883295797)
                ·
                  refine ⟨3897532688432258426558981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 41573682009944089883295797 3897532688432258426558981)
                  ·
                    refine ⟨730787379081048454979809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3897532688432258426558981 730787379081048454979809)
                    ·
                      rfl

theorem cell23_4269610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 1, 5, 4].length) (baseStart_4269610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4269610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4269610 prefixEnd_4269610 := by exact prefixLift 4269610
  have htrace : WordTrace (prefixWord ++ tailWord_4269610) baseStart_4269610 baseEnd_4269610 := by
    simpa [prefixWord, tailWord_4269610, baseEnd_4269610] using wordTrace_append hprefix tailTrace_4269610
  have hstable : (prefixWord ++ tailWord_4269610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4269610).length < 2 ^ (prefixWord ++ tailWord_4269610).sum := by decide
  have hdescent : baseEnd_4269610 < baseStart_4269610 := by decide
  rcases family_descends (prefixWord ++ tailWord_4269610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4269644 : List Nat := [2, 2, 1, 3, 1, 3, 4, 2, 1, 4]
def baseStart_4269644 : Nat := 118140960795 + 4269644 * 2 ^ 59
def prefixEnd_4269644 : Nat := 4983230072969 + 3 ^ 40 * 4269644 * 2
def baseEnd_4269644 : Nat := 730793198528466077304757

theorem tailTrace_4269644 : CollatzResearch.WordTrace tailWord_4269644 prefixEnd_4269644 730793198528466077304757 := by
  unfold tailWord_4269644
  simp only [CollatzResearch.WordTrace]
  refine ⟨77863355071908229992979993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103817806762544306657306657 77863355071908229992979993)
  ·
    refine ⟨58397516303931172494734995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77863355071908229992979993 58397516303931172494734995)
    ·
      refine ⟨87596274455896758742102493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58397516303931172494734995 87596274455896758742102493)
      ·
        refine ⟨32848602920961284528288435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87596274455896758742102493 32848602920961284528288435)
        ·
          refine ⟨49272904381441926792432653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32848602920961284528288435 49272904381441926792432653)
          ·
            refine ⟨18477339143040722547162245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49272904381441926792432653 18477339143040722547162245)
            ·
              refine ⟨3464501089320135477592921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18477339143040722547162245 3464501089320135477592921)
              ·
                refine ⟨2598375816990101608194691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3464501089320135477592921 2598375816990101608194691)
                ·
                  refine ⟨3897563725485152412292037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2598375816990101608194691 3897563725485152412292037)
                  ·
                    refine ⟨730793198528466077304757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3897563725485152412292037 730793198528466077304757)
                    ·
                      rfl

theorem cell23_4269644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 4, 2, 1, 4].length) (baseStart_4269644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4269644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4269644 prefixEnd_4269644 := by exact prefixLift 4269644
  have htrace : WordTrace (prefixWord ++ tailWord_4269644) baseStart_4269644 baseEnd_4269644 := by
    simpa [prefixWord, tailWord_4269644, baseEnd_4269644] using wordTrace_append hprefix tailTrace_4269644
  have hstable : (prefixWord ++ tailWord_4269644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4269644).length < 2 ^ (prefixWord ++ tailWord_4269644).sum := by decide
  have hdescent : baseEnd_4269644 < baseStart_4269644 := by decide
  rcases family_descends (prefixWord ++ tailWord_4269644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4269667 : List Nat := [1, 1, 1, 5, 1, 4, 1, 2, 3, 1, 3]
def baseStart_4269667 : Nat := 118140960795 + 4269667 * 2 ^ 59
def prefixEnd_4269667 : Nat := 4983230072969 + 3 ^ 40 * 4269667 * 2
def baseEnd_4269667 : Nat := 2192391405640451641926665

theorem tailTrace_4269667 : CollatzResearch.WordTrace tailWord_4269667 prefixEnd_4269667 2192391405640451641926665 := by
  unfold tailWord_4269667
  simp only [CollatzResearch.WordTrace]
  refine ⟨155727549022733134914047255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103818366015155423276031503 155727549022733134914047255)
  ·
    refine ⟨233591323534099702371070883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155727549022733134914047255 233591323534099702371070883)
    ·
      refine ⟨350386985301149553556606325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 233591323534099702371070883 350386985301149553556606325)
      ·
        refine ⟨32848779871982770645931843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 350386985301149553556606325 32848779871982770645931843)
        ·
          refine ⟨49273169807974155968897765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32848779871982770645931843 49273169807974155968897765)
          ·
            refine ⟨9238719338995154244168331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49273169807974155968897765 9238719338995154244168331)
            ·
              refine ⟨13858079008492731366252497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9238719338995154244168331 13858079008492731366252497)
              ·
                refine ⟨10393559256369548524689373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13858079008492731366252497 10393559256369548524689373)
                ·
                  refine ⟨3897584721138580696758515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10393559256369548524689373 3897584721138580696758515)
                  ·
                    refine ⟨5846377081707871045137773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3897584721138580696758515 5846377081707871045137773)
                    ·
                      refine ⟨2192391405640451641926665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5846377081707871045137773 2192391405640451641926665)
                      ·
                        rfl

theorem cell23_4269667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 2, 3, 1, 3].length) (baseStart_4269667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4269667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4269667 prefixEnd_4269667 := by exact prefixLift 4269667
  have htrace : WordTrace (prefixWord ++ tailWord_4269667) baseStart_4269667 baseEnd_4269667 := by
    simpa [prefixWord, tailWord_4269667, baseEnd_4269667] using wordTrace_append hprefix tailTrace_4269667
  have hstable : (prefixWord ++ tailWord_4269667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4269667).length < 2 ^ (prefixWord ++ tailWord_4269667).sum := by decide
  have hdescent : baseEnd_4269667 < baseStart_4269667 := by decide
  rcases family_descends (prefixWord ++ tailWord_4269667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4269710 : List Nat := [4, 1, 1, 3, 1, 2, 1, 1, 3, 1, 5]
def baseStart_4269710 : Nat := 118140960795 + 4269710 * 2 ^ 59
def prefixEnd_4269710 : Nat := 4983230072969 + 3 ^ 40 * 4269710 * 2
def baseEnd_4269710 : Nat := 2192413485308594973688967

theorem tailTrace_4269710 : CollatzResearch.WordTrace tailWord_4269710 prefixEnd_4269710 2192413485308594973688967 := by
  unfold tailWord_4269710
  simp only [CollatzResearch.WordTrace]
  refine ⟨19466139670197169157232823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 103819411574384902171908389 19466139670197169157232823)
  ·
    refine ⟨29199209505295753735849235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19466139670197169157232823 29199209505295753735849235)
    ·
      refine ⟨43798814257943630603773853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29199209505295753735849235 43798814257943630603773853)
      ·
        refine ⟨16424555346728861476415195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43798814257943630603773853 16424555346728861476415195)
        ·
          refine ⟨24636833020093292214622793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16424555346728861476415195 24636833020093292214622793)
          ·
            refine ⟨18477624765069969160967095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24636833020093292214622793 18477624765069969160967095)
            ·
              refine ⟨27716437147604953741450643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18477624765069969160967095 27716437147604953741450643)
              ·
                refine ⟨41574655721407430612175965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27716437147604953741450643 41574655721407430612175965)
                ·
                  refine ⟨15590495895527786479565987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41574655721407430612175965 15590495895527786479565987)
                  ·
                    refine ⟨23385743843291679719348981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15590495895527786479565987 23385743843291679719348981)
                    ·
                      refine ⟨2192413485308594973688967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23385743843291679719348981 2192413485308594973688967)
                      ·
                        rfl

theorem cell23_4269710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 1, 3, 1, 5].length) (baseStart_4269710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4269710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4269710 prefixEnd_4269710 := by exact prefixLift 4269710
  have htrace : WordTrace (prefixWord ++ tailWord_4269710) baseStart_4269710 baseEnd_4269710 := by
    simpa [prefixWord, tailWord_4269710, baseEnd_4269710] using wordTrace_append hprefix tailTrace_4269710
  have hstable : (prefixWord ++ tailWord_4269710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4269710).length < 2 ^ (prefixWord ++ tailWord_4269710).sum := by decide
  have hdescent : baseEnd_4269710 < baseStart_4269710 := by decide
  rcases family_descends (prefixWord ++ tailWord_4269710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4269720 : List Nat := [2, 1, 2, 4, 1, 3, 1, 1, 1, 1, 6]
def baseStart_4269720 : Nat := 118140960795 + 4269720 * 2 ^ 59
def prefixEnd_4269720 : Nat := 4983230072969 + 3 ^ 40 * 4269720 * 2
def baseEnd_4269720 : Nat := 2192418620115139934563921

theorem tailTrace_4269720 : CollatzResearch.WordTrace tailWord_4269720 prefixEnd_4269720 2192418620115139934563921 := by
  unfold tailWord_4269720
  simp only [CollatzResearch.WordTrace]
  refine ⟨77864741045770562482863307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103819654727694083310484409 77864741045770562482863307)
  ·
    refine ⟨116797111568655843724294961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77864741045770562482863307 116797111568655843724294961)
    ·
      refine ⟨87597833676491882793221221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116797111568655843724294961 87597833676491882793221221)
      ·
        refine ⟨16424593814342228023728979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 87597833676491882793221221 16424593814342228023728979)
        ·
          refine ⟨24636890721513342035593469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16424593814342228023728979 24636890721513342035593469)
          ·
            refine ⟨9238834020567503263347551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24636890721513342035593469 9238834020567503263347551)
            ·
              refine ⟨13858251030851254895021327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9238834020567503263347551 13858251030851254895021327)
              ·
                refine ⟨20787376546276882342531991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13858251030851254895021327 20787376546276882342531991)
                ·
                  refine ⟨31181064819415323513797987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20787376546276882342531991 31181064819415323513797987)
                  ·
                    refine ⟨46771597229122985270696981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31181064819415323513797987 46771597229122985270696981)
                    ·
                      refine ⟨2192418620115139934563921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 46771597229122985270696981 2192418620115139934563921)
                      ·
                        rfl

theorem cell23_4269720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 1, 1, 1, 6].length) (baseStart_4269720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4269720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4269720 prefixEnd_4269720 := by exact prefixLift 4269720
  have htrace : WordTrace (prefixWord ++ tailWord_4269720) baseStart_4269720 baseEnd_4269720 := by
    simpa [prefixWord, tailWord_4269720, baseEnd_4269720] using wordTrace_append hprefix tailTrace_4269720
  have hstable : (prefixWord ++ tailWord_4269720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4269720).length < 2 ^ (prefixWord ++ tailWord_4269720).sum := by decide
  have hdescent : baseEnd_4269720 < baseStart_4269720 := by decide
  rcases family_descends (prefixWord ++ tailWord_4269720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4269724 : List Nat := [2, 2, 3, 2, 3, 1, 2, 2, 1, 1, 4]
def baseStart_4269724 : Nat := 118140960795 + 4269724 * 2 ^ 59
def prefixEnd_4269724 : Nat := 4983230072969 + 3 ^ 40 * 4269724 * 2
def baseEnd_4269724 : Nat := 2192420674037757918913903

theorem tailTrace_4269724 : CollatzResearch.WordTrace tailWord_4269724 prefixEnd_4269724 2192420674037757918913903 := by
  unfold tailWord_4269724
  simp only [CollatzResearch.WordTrace]
  refine ⟨77864813991763316824436113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103819751989017755765914817 77864813991763316824436113)
  ·
    refine ⟨58398610493822487618327085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77864813991763316824436113 58398610493822487618327085)
    ·
      refine ⟨21899478935183432856872657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58398610493822487618327085 21899478935183432856872657)
      ·
        refine ⟨16424609201387574642654493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21899478935183432856872657 16424609201387574642654493)
        ·
          refine ⟨6159228450520340490995435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16424609201387574642654493 6159228450520340490995435)
          ·
            refine ⟨9238842675780510736493153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6159228450520340490995435 9238842675780510736493153)
            ·
              refine ⟨6929132006835383052369865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9238842675780510736493153 6929132006835383052369865)
              ·
                refine ⟨5196849005126537289277399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6929132006835383052369865 5196849005126537289277399)
                ·
                  refine ⟨7795273507689805933916099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5196849005126537289277399 7795273507689805933916099)
                  ·
                    refine ⟨11692910261534708900874149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7795273507689805933916099 11692910261534708900874149)
                    ·
                      refine ⟨2192420674037757918913903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11692910261534708900874149 2192420674037757918913903)
                      ·
                        rfl

theorem cell23_4269724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 2, 2, 1, 1, 4].length) (baseStart_4269724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4269724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4269724 prefixEnd_4269724 := by exact prefixLift 4269724
  have htrace : WordTrace (prefixWord ++ tailWord_4269724) baseStart_4269724 baseEnd_4269724 := by
    simpa [prefixWord, tailWord_4269724, baseEnd_4269724] using wordTrace_append hprefix tailTrace_4269724
  have hstable : (prefixWord ++ tailWord_4269724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4269724).length < 2 ^ (prefixWord ++ tailWord_4269724).sum := by decide
  have hdescent : baseEnd_4269724 < baseStart_4269724 := by decide
  rcases family_descends (prefixWord ++ tailWord_4269724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4269757 : List Nat := [1, 4, 1, 2, 1, 2, 1, 3, 4, 1, 3]
def baseStart_4269757 : Nat := 118140960795 + 4269757 * 2 ^ 59
def prefixEnd_4269757 : Nat := 4983230072969 + 3 ^ 40 * 4269757 * 2
def baseEnd_4269757 : Nat := 2192437618899356289801251

theorem tailTrace_4269757 : CollatzResearch.WordTrace tailWord_4269757 prefixEnd_4269757 2192437618899356289801251 := by
  unfold tailWord_4269757
  simp only [CollatzResearch.WordTrace]
  refine ⟨155730831592407080284823525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103820554394938053523215683 155730831592407080284823525)
  ·
    refine ⟨29199530923576327553404411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 155730831592407080284823525 29199530923576327553404411)
    ·
      refine ⟨43799296385364491330106617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29199530923576327553404411 43799296385364491330106617)
      ·
        refine ⟨32849472289023368497579963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43799296385364491330106617 32849472289023368497579963)
        ·
          refine ⟨49274208433535052746369945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32849472289023368497579963 49274208433535052746369945)
          ·
            refine ⟨36955656325151289559777459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49274208433535052746369945 36955656325151289559777459)
            ·
              refine ⟨55433484487726934339666189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36955656325151289559777459 55433484487726934339666189)
              ·
                refine ⟨20787556682897600377374821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55433484487726934339666189 20787556682897600377374821)
                ·
                  refine ⟨3897666878043300070757779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20787556682897600377374821 3897666878043300070757779)
                  ·
                    refine ⟨5846500317064950106136669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3897666878043300070757779 5846500317064950106136669)
                    ·
                      refine ⟨2192437618899356289801251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5846500317064950106136669 2192437618899356289801251)
                      ·
                        rfl

theorem cell23_4269757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 3, 4, 1, 3].length) (baseStart_4269757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4269757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4269757 prefixEnd_4269757 := by exact prefixLift 4269757
  have htrace : WordTrace (prefixWord ++ tailWord_4269757) baseStart_4269757 baseEnd_4269757 := by
    simpa [prefixWord, tailWord_4269757, baseEnd_4269757] using wordTrace_append hprefix tailTrace_4269757
  have hstable : (prefixWord ++ tailWord_4269757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4269757).length < 2 ^ (prefixWord ++ tailWord_4269757).sum := by decide
  have hdescent : baseEnd_4269757 < baseStart_4269757 := by decide
  rcases family_descends (prefixWord ++ tailWord_4269757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4269767 : List Nat := [1, 1, 4, 1, 1, 1, 4, 2, 3, 3, 2]
def baseStart_4269767 : Nat := 118140960795 + 4269767 * 2 ^ 59
def prefixEnd_4269767 : Nat := 4983230072969 + 3 ^ 40 * 4269767 * 2
def baseEnd_4269767 : Nat := 2192442753705901250676205

theorem tailTrace_4269767 : CollatzResearch.WordTrace tailWord_4269767 prefixEnd_4269767 2192442753705901250676205 := by
  unfold tailWord_4269767
  simp only [CollatzResearch.WordTrace]
  refine ⟨155731196322370851992687555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103820797548247234661791703 155731196322370851992687555)
  ·
    refine ⟨233596794483556277989031333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155731196322370851992687555 233596794483556277989031333)
    ·
      refine ⟨43799398965666802122943375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 233596794483556277989031333 43799398965666802122943375)
      ·
        refine ⟨65699098448500203184415063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43799398965666802122943375 65699098448500203184415063)
        ·
          refine ⟨98548647672750304776622595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65699098448500203184415063 98548647672750304776622595)
          ·
            refine ⟨147822971509125457164933893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98548647672750304776622595 147822971509125457164933893)
            ·
              refine ⟨27716807157961023218425105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 147822971509125457164933893 27716807157961023218425105)
              ·
                refine ⟨20787605368470767413818829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27716807157961023218425105 20787605368470767413818829)
                ·
                  refine ⟨7795352013176537780182061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20787605368470767413818829 7795352013176537780182061)
                  ·
                    refine ⟨2923257004941201667568273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7795352013176537780182061 2923257004941201667568273)
                    ·
                      refine ⟨2192442753705901250676205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2923257004941201667568273 2192442753705901250676205)
                      ·
                        rfl

theorem cell23_4269767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 2, 3, 3, 2].length) (baseStart_4269767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4269767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4269767 prefixEnd_4269767 := by exact prefixLift 4269767
  have htrace : WordTrace (prefixWord ++ tailWord_4269767) baseStart_4269767 baseEnd_4269767 := by
    simpa [prefixWord, tailWord_4269767, baseEnd_4269767] using wordTrace_append hprefix tailTrace_4269767
  have hstable : (prefixWord ++ tailWord_4269767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4269767).length < 2 ^ (prefixWord ++ tailWord_4269767).sum := by decide
  have hdescent : baseEnd_4269767 < baseStart_4269767 := by decide
  rcases family_descends (prefixWord ++ tailWord_4269767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4269774 : List Nat := [4, 1, 1, 1, 3, 1, 3, 3, 2, 1, 3]
def baseStart_4269774 : Nat := 118140960795 + 4269774 * 2 ^ 59
def prefixEnd_4269774 : Nat := 4983230072969 + 3 ^ 40 * 4269774 * 2
def baseEnd_4269774 : Nat := 2192446348070482723288673

theorem tailTrace_4269774 : CollatzResearch.WordTrace tailWord_4269774 prefixEnd_4269774 2192446348070482723288673 := by
  unfold tailWord_4269774
  simp only [CollatzResearch.WordTrace]
  refine ⟨19466431454168186523524047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 103820967755563661458794917 19466431454168186523524047)
  ·
    refine ⟨29199647181252279785286071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19466431454168186523524047 29199647181252279785286071)
    ·
      refine ⟨43799470771878419677929107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29199647181252279785286071 43799470771878419677929107)
      ·
        refine ⟨65699206157817629516893661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43799470771878419677929107 65699206157817629516893661)
        ·
          refine ⟨24637202309181611068835123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65699206157817629516893661 24637202309181611068835123)
          ·
            refine ⟨36955803463772416603252685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24637202309181611068835123 36955803463772416603252685)
            ·
              refine ⟨13858426298914656226219757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36955803463772416603252685 13858426298914656226219757)
              ·
                refine ⟨5196909862092996084832409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13858426298914656226219757 5196909862092996084832409)
                ·
                  refine ⟨3897682396569747063624307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5196909862092996084832409 3897682396569747063624307)
                  ·
                    refine ⟨5846523594854620595436461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3897682396569747063624307 5846523594854620595436461)
                    ·
                      refine ⟨2192446348070482723288673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5846523594854620595436461 2192446348070482723288673)
                      ·
                        rfl

theorem cell23_4269774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 3, 2, 1, 3].length) (baseStart_4269774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4269774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4269774 prefixEnd_4269774 := by exact prefixLift 4269774
  have htrace : WordTrace (prefixWord ++ tailWord_4269774) baseStart_4269774 baseEnd_4269774 := by
    simpa [prefixWord, tailWord_4269774, baseEnd_4269774] using wordTrace_append hprefix tailTrace_4269774
  have hstable : (prefixWord ++ tailWord_4269774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4269774).length < 2 ^ (prefixWord ++ tailWord_4269774).sum := by decide
  have hdescent : baseEnd_4269774 < baseStart_4269774 := by decide
  rcases family_descends (prefixWord ++ tailWord_4269774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4269820 : List Nat := [2, 2, 2, 1, 3, 1, 2, 3, 7]
def baseStart_4269820 : Nat := 118140960795 + 4269820 * 2 ^ 59
def prefixEnd_4269820 : Nat := 4983230072969 + 3 ^ 40 * 4269820 * 2
def baseEnd_4269820 : Nat := 243607774242287727034829

theorem tailTrace_4269820 : CollatzResearch.WordTrace tailWord_4269820 prefixEnd_4269820 243607774242287727034829 := by
  unfold tailWord_4269820
  simp only [CollatzResearch.WordTrace]
  refine ⟨77866564695589421022183457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103822086260785894696244609 77866564695589421022183457)
  ·
    refine ⟨58399923521692065766637593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77866564695589421022183457 58399923521692065766637593)
    ·
      refine ⟨43799942641269049324978195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58399923521692065766637593 43799942641269049324978195)
      ·
        refine ⟨65699913961903573987467293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43799942641269049324978195 65699913961903573987467293)
        ·
          refine ⟨24637467735713840245300235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65699913961903573987467293 24637467735713840245300235)
          ·
            refine ⟨36956201603570760367950353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24637467735713840245300235 36956201603570760367950353)
            ·
              refine ⟨27717151202678070275962765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36956201603570760367950353 27717151202678070275962765)
              ·
                refine ⟨10393931701004276353486037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27717151202678070275962765 10393931701004276353486037)
                ·
                  refine ⟨243607774242287727034829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10393931701004276353486037 243607774242287727034829)
                  ·
                    rfl

theorem cell23_4269820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 3, 7].length) (baseStart_4269820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4269820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4269820 prefixEnd_4269820 := by exact prefixLift 4269820
  have htrace : WordTrace (prefixWord ++ tailWord_4269820) baseStart_4269820 baseEnd_4269820 := by
    simpa [prefixWord, tailWord_4269820, baseEnd_4269820] using wordTrace_append hprefix tailTrace_4269820
  have hstable : (prefixWord ++ tailWord_4269820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4269820).length < 2 ^ (prefixWord ++ tailWord_4269820).sum := by decide
  have hdescent : baseEnd_4269820 < baseStart_4269820 := by decide
  rcases family_descends (prefixWord ++ tailWord_4269820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4269831 : List Nat := [1, 1, 4, 4, 2, 1, 2, 1, 1, 4, 2]
def baseStart_4269831 : Nat := 118140960795 + 4269831 * 2 ^ 59
def prefixEnd_4269831 : Nat := 4983230072969 + 3 ^ 40 * 4269831 * 2
def baseEnd_4269831 : Nat := 2192475616467789000275911

theorem tailTrace_4269831 : CollatzResearch.WordTrace tailWord_4269831 prefixEnd_4269831 2192475616467789000275911 := by
  unfold tailWord_4269831
  simp only [CollatzResearch.WordTrace]
  refine ⟨155733530594138990923017347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103822353729425993948678231 155733530594138990923017347)
  ·
    refine ⟨233600295891208486384526021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155733530594138990923017347 233600295891208486384526021)
    ·
      refine ⟨43800055479601591197098629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 233600295891208486384526021 43800055479601591197098629)
      ·
        refine ⟨8212510402425298349455993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43800055479601591197098629 8212510402425298349455993)
        ·
          refine ⟨6159382801818973762091995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8212510402425298349455993 6159382801818973762091995)
          ·
            refine ⟨9239074202728460643137993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6159382801818973762091995 9239074202728460643137993)
            ·
              refine ⟨6929305652046345482353495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9239074202728460643137993 6929305652046345482353495)
              ·
                refine ⟨10393958478069518223530243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6929305652046345482353495 10393958478069518223530243)
                ·
                  refine ⟨15590937717104277335295365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10393958478069518223530243 15590937717104277335295365)
                  ·
                    refine ⟨2923300821957052000367881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15590937717104277335295365 2923300821957052000367881)
                    ·
                      refine ⟨2192475616467789000275911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2923300821957052000367881 2192475616467789000275911)
                      ·
                        rfl

theorem cell23_4269831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 2, 1, 1, 4, 2].length) (baseStart_4269831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4269831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4269831 prefixEnd_4269831 := by exact prefixLift 4269831
  have htrace : WordTrace (prefixWord ++ tailWord_4269831) baseStart_4269831 baseEnd_4269831 := by
    simpa [prefixWord, tailWord_4269831, baseEnd_4269831] using wordTrace_append hprefix tailTrace_4269831
  have hstable : (prefixWord ++ tailWord_4269831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4269831).length < 2 ^ (prefixWord ++ tailWord_4269831).sum := by decide
  have hdescent : baseEnd_4269831 < baseStart_4269831 := by decide
  rcases family_descends (prefixWord ++ tailWord_4269831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4269897 : List Nat := [1, 2, 1, 1, 2, 4, 1, 4, 3, 4]
def baseStart_4269897 : Nat := 118140960795 + 4269897 * 2 ^ 59
def prefixEnd_4269897 : Nat := 4983230072969 + 3 ^ 40 * 4269897 * 2
def baseEnd_4269897 : Nat := 730836502063661914016869

theorem tailTrace_4269897 : CollatzResearch.WordTrace tailWord_4269897 prefixEnd_4269897 730836502063661914016869 := by
  unfold tailWord_4269897
  simp only [CollatzResearch.WordTrace]
  refine ⟨155735937811899884194919945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103823958541266589463279963 155735937811899884194919945)
  ·
    refine ⟨116801953358924913146189959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155735937811899884194919945 116801953358924913146189959)
    ·
      refine ⟨175202930038387369719284939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116801953358924913146189959 175202930038387369719284939)
      ·
        refine ⟨262804395057581054578927409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175202930038387369719284939 262804395057581054578927409)
        ·
          refine ⟨197103296293185790934195557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 262804395057581054578927409 197103296293185790934195557)
          ·
            refine ⟨36956868054972335800161667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 197103296293185790934195557 36956868054972335800161667)
            ·
              refine ⟨55435302082458503700242501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36956868054972335800161667 55435302082458503700242501)
              ·
                refine ⟨10394119140460969443795469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 55435302082458503700242501 10394119140460969443795469)
                ·
                  refine ⟨3897794677672863541423301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10394119140460969443795469 3897794677672863541423301)
                  ·
                    refine ⟨730836502063661914016869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3897794677672863541423301 730836502063661914016869)
                    ·
                      rfl

theorem cell23_4269897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 4, 3, 4].length) (baseStart_4269897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4269897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4269897 prefixEnd_4269897 := by exact prefixLift 4269897
  have htrace : WordTrace (prefixWord ++ tailWord_4269897) baseStart_4269897 baseEnd_4269897 := by
    simpa [prefixWord, tailWord_4269897, baseEnd_4269897] using wordTrace_append hprefix tailTrace_4269897
  have hstable : (prefixWord ++ tailWord_4269897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4269897).length < 2 ^ (prefixWord ++ tailWord_4269897).sum := by decide
  have hdescent : baseEnd_4269897 < baseStart_4269897 := by decide
  rcases family_descends (prefixWord ++ tailWord_4269897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4269927 : List Nat := [1, 1, 5, 1, 2, 1, 2, 4, 6]
def baseStart_4269927 : Nat := 118140960795 + 4269927 * 2 ^ 59
def prefixEnd_4269927 : Nat := 4983230072969 + 3 ^ 40 * 4269927 * 2
def baseEnd_4269927 : Nat := 243613878956735624963941

theorem tailTrace_4269927 : CollatzResearch.WordTrace tailWord_4269927 prefixEnd_4269927 243613878956735624963941 := by
  unfold tailWord_4269927
  simp only [CollatzResearch.WordTrace]
  refine ⟨155737032001791199318512035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103824688001194132879008023 155737032001791199318512035)
  ·
    refine ⟨233605548002686798977768053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155737032001791199318512035 233605548002686798977768053)
    ·
      refine ⟨21900520125251887404165755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 233605548002686798977768053 21900520125251887404165755)
      ·
        refine ⟨32850780187877831106248633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21900520125251887404165755 32850780187877831106248633)
        ·
          refine ⟨24638085140908373329686475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32850780187877831106248633 24638085140908373329686475)
          ·
            refine ⟨36957127711362559994529713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24638085140908373329686475 36957127711362559994529713)
            ·
              refine ⟨27717845783521919995897285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36957127711362559994529713 27717845783521919995897285)
              ·
                refine ⟨5197096084410359999230741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27717845783521919995897285 5197096084410359999230741)
                ·
                  refine ⟨243613878956735624963941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5197096084410359999230741 243613878956735624963941)
                  ·
                    rfl

theorem cell23_4269927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 4, 6].length) (baseStart_4269927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4269927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4269927 prefixEnd_4269927 := by exact prefixLift 4269927
  have htrace : WordTrace (prefixWord ++ tailWord_4269927) baseStart_4269927 baseEnd_4269927 := by
    simpa [prefixWord, tailWord_4269927, baseEnd_4269927] using wordTrace_append hprefix tailTrace_4269927
  have hstable : (prefixWord ++ tailWord_4269927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4269927).length < 2 ^ (prefixWord ++ tailWord_4269927).sum := by decide
  have hdescent : baseEnd_4269927 < baseStart_4269927 := by decide
  rcases family_descends (prefixWord ++ tailWord_4269927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4269957 : List Nat := [1, 3, 1, 1, 3, 2, 3, 1, 3, 5]
def baseStart_4269957 : Nat := 118140960795 + 4269957 * 2 ^ 59
def prefixEnd_4269957 : Nat := 4983230072969 + 3 ^ 40 * 4269957 * 2
def baseEnd_4269957 : Nat := 730846771676751835766777

theorem tailTrace_4269957 : CollatzResearch.WordTrace tailWord_4269957 prefixEnd_4269957 730846771676751835766777 := by
  unfold tailWord_4269957
  simp only [CollatzResearch.WordTrace]
  refine ⟨155738126191682514442104125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103825417461121676294736083 155738126191682514442104125)
  ·
    refine ⟨58401797321880942915789047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 155738126191682514442104125 58401797321880942915789047)
    ·
      refine ⟨87602695982821414373683571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58401797321880942915789047 87602695982821414373683571)
      ·
        refine ⟨131404043974232121560525357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87602695982821414373683571 131404043974232121560525357)
        ·
          refine ⟨49276516490337045585197009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 131404043974232121560525357 49276516490337045585197009)
          ·
            refine ⟨36957387367752784188897757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49276516490337045585197009 36957387367752784188897757)
            ·
              refine ⟨13859020262907294070836659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36957387367752784188897757 13859020262907294070836659)
              ·
                refine ⟨20788530394360941106254989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13859020262907294070836659 20788530394360941106254989)
                ·
                  refine ⟨7795698897885352914845621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20788530394360941106254989 7795698897885352914845621)
                  ·
                    refine ⟨730846771676751835766777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7795698897885352914845621 730846771676751835766777)
                    ·
                      rfl

theorem cell23_4269957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 1, 3, 5].length) (baseStart_4269957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4269957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4269957 prefixEnd_4269957 := by exact prefixLift 4269957
  have htrace : WordTrace (prefixWord ++ tailWord_4269957) baseStart_4269957 baseEnd_4269957 := by
    simpa [prefixWord, tailWord_4269957, baseEnd_4269957] using wordTrace_append hprefix tailTrace_4269957
  have hstable : (prefixWord ++ tailWord_4269957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4269957).length < 2 ^ (prefixWord ++ tailWord_4269957).sum := by decide
  have hdescent : baseEnd_4269957 < baseStart_4269957 := by decide
  rcases family_descends (prefixWord ++ tailWord_4269957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4269981 : List Nat := [1, 4, 2, 1, 2, 2, 2, 2, 2, 3, 2]
def baseStart_4269981 : Nat := 118140960795 + 4269981 * 2 ^ 59
def prefixEnd_4269981 : Nat := 4983230072969 + 3 ^ 40 * 4269981 * 2
def baseEnd_4269981 : Nat := 2192552638565963413400221

theorem tailTrace_4269981 : CollatzResearch.WordTrace tailWord_4269981 prefixEnd_4269981 2192552638565963413400221 := by
  unfold tailWord_4269981
  simp only [CollatzResearch.WordTrace]
  refine ⟨155739001543595566540977797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103826001029063711027318531 155739001543595566540977797)
  ·
    refine ⟨29201062789424168726433337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 155739001543595566540977797 29201062789424168726433337)
    ·
      refine ⟨21900797092068126544825003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29201062789424168726433337 21900797092068126544825003)
      ·
        refine ⟨32851195638102189817237505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21900797092068126544825003 32851195638102189817237505)
        ·
          refine ⟨24638396728576642362928129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32851195638102189817237505 24638396728576642362928129)
          ·
            refine ⟨18478797546432481772196097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24638396728576642362928129 18478797546432481772196097)
            ·
              refine ⟨13859098159824361329147073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18478797546432481772196097 13859098159824361329147073)
              ·
                refine ⟨10394323619868270996860305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13859098159824361329147073 10394323619868270996860305)
                ·
                  refine ⟨7795742714901203247645229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10394323619868270996860305 7795742714901203247645229)
                  ·
                    refine ⟨2923403518087951217866961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7795742714901203247645229 2923403518087951217866961)
                    ·
                      refine ⟨2192552638565963413400221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2923403518087951217866961 2192552638565963413400221)
                      ·
                        rfl

theorem cell23_4269981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 2, 2, 3, 2].length) (baseStart_4269981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4269981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4269981 prefixEnd_4269981 := by exact prefixLift 4269981
  have htrace : WordTrace (prefixWord ++ tailWord_4269981) baseStart_4269981 baseEnd_4269981 := by
    simpa [prefixWord, tailWord_4269981, baseEnd_4269981] using wordTrace_append hprefix tailTrace_4269981
  have hstable : (prefixWord ++ tailWord_4269981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4269981).length < 2 ^ (prefixWord ++ tailWord_4269981).sum := by decide
  have hdescent : baseEnd_4269981 < baseStart_4269981 := by decide
  rcases family_descends (prefixWord ++ tailWord_4269981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4269988 : List Nat := [2, 3, 1, 2, 1, 4, 1, 4, 1, 1, 3]
def baseStart_4269988 : Nat := 118140960795 + 4269988 * 2 ^ 59
def prefixEnd_4269988 : Nat := 4983230072969 + 3 ^ 40 * 4269988 * 2
def baseEnd_4269988 : Nat := 2192556232930544886012689

theorem tailTrace_4269988 : CollatzResearch.WordTrace tailWord_4269988 prefixEnd_4269988 2192556232930544886012689 := by
  unfold tailWord_4269988
  simp only [CollatzResearch.WordTrace]
  refine ⟨77869628427285103368241309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103826171236380137824321745 77869628427285103368241309)
  ·
    refine ⟨29201110660231913763090491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77869628427285103368241309 29201110660231913763090491)
    ·
      refine ⟨43801665990347870644635737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29201110660231913763090491 43801665990347870644635737)
      ·
        refine ⟨32851249492760902983476803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43801665990347870644635737 32851249492760902983476803)
        ·
          refine ⟨49276874239141354475215205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32851249492760902983476803 49276874239141354475215205)
          ·
            refine ⟨9239413919839003964102851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49276874239141354475215205 9239413919839003964102851)
            ·
              refine ⟨13859120879758505946154277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9239413919839003964102851 13859120879758505946154277)
              ·
                refine ⟨2598585164954719864903927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13859120879758505946154277 2598585164954719864903927)
                ·
                  refine ⟨3897877747432079797355891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2598585164954719864903927 3897877747432079797355891)
                  ·
                    refine ⟨5846816621148119696033837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3897877747432079797355891 5846816621148119696033837)
                    ·
                      refine ⟨2192556232930544886012689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5846816621148119696033837 2192556232930544886012689)
                      ·
                        rfl

theorem cell23_4269988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 4, 1, 1, 3].length) (baseStart_4269988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4269988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4269988 prefixEnd_4269988 := by exact prefixLift 4269988
  have htrace : WordTrace (prefixWord ++ tailWord_4269988) baseStart_4269988 baseEnd_4269988 := by
    simpa [prefixWord, tailWord_4269988, baseEnd_4269988] using wordTrace_append hprefix tailTrace_4269988
  have hstable : (prefixWord ++ tailWord_4269988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4269988).length < 2 ^ (prefixWord ++ tailWord_4269988).sum := by decide
  have hdescent : baseEnd_4269988 < baseStart_4269988 := by decide
  rcases family_descends (prefixWord ++ tailWord_4269988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4270024 : List Nat := [2, 1, 3, 1, 4, 1, 2, 2, 1, 2, 4]
def baseStart_4270024 : Nat := 118140960795 + 4270024 * 2 ^ 59
def prefixEnd_4270024 : Nat := 4983230072969 + 3 ^ 40 * 4270024 * 2
def baseEnd_4270024 : Nat := 2192574718234106745162523

theorem tailTrace_4270024 : CollatzResearch.WordTrace tailWord_4270024 prefixEnd_4270024 2192574718234106745162523 := by
  unfold tailWord_4270024
  simp only [CollatzResearch.WordTrace]
  refine ⟨77870284941219892442396563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103827046588293189923195417 77870284941219892442396563)
  ·
    refine ⟨116805427411829838663594845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77870284941219892442396563 116805427411829838663594845)
    ·
      refine ⟨43802035279436189498848067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 116805427411829838663594845 43802035279436189498848067)
      ·
        refine ⟨65703052919154284248272101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43802035279436189498848067 65703052919154284248272101)
        ·
          refine ⟨12319322422341428296551019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 65703052919154284248272101 12319322422341428296551019)
          ·
            refine ⟨18478983633512142444826529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12319322422341428296551019 18478983633512142444826529)
            ·
              refine ⟨13859237725134106833619897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18478983633512142444826529 13859237725134106833619897)
              ·
                refine ⟨10394428293850580125214923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13859237725134106833619897 10394428293850580125214923)
                ·
                  refine ⟨15591642440775870187822385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10394428293850580125214923 15591642440775870187822385)
                  ·
                    refine ⟨11693731830581902640866789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15591642440775870187822385 11693731830581902640866789)
                    ·
                      refine ⟨2192574718234106745162523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11693731830581902640866789 2192574718234106745162523)
                      ·
                        rfl

theorem cell23_4270024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 2, 1, 2, 4].length) (baseStart_4270024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4270024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4270024 prefixEnd_4270024 := by exact prefixLift 4270024
  have htrace : WordTrace (prefixWord ++ tailWord_4270024) baseStart_4270024 baseEnd_4270024 := by
    simpa [prefixWord, tailWord_4270024, baseEnd_4270024] using wordTrace_append hprefix tailTrace_4270024
  have hstable : (prefixWord ++ tailWord_4270024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4270024).length < 2 ^ (prefixWord ++ tailWord_4270024).sum := by decide
  have hdescent : baseEnd_4270024 < baseStart_4270024 := by decide
  rcases family_descends (prefixWord ++ tailWord_4270024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4270028 : List Nat := [2, 2, 1, 4, 1, 4, 2, 1, 1, 1, 4]
def baseStart_4270028 : Nat := 118140960795 + 4270028 * 2 ^ 59
def prefixEnd_4270028 : Nat := 4983230072969 + 3 ^ 40 * 4270028 * 2
def baseEnd_4270028 : Nat := 2192576772156724729512505

theorem tailTrace_4270028 : CollatzResearch.WordTrace tailWord_4270028 prefixEnd_4270028 2192576772156724729512505 := by
  unfold tailWord_4270028
  simp only [CollatzResearch.WordTrace]
  refine ⟨77870357887212646783969369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103827143849616862378625825 77870357887212646783969369)
  ·
    refine ⟨58402768415409485087977027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77870357887212646783969369 58402768415409485087977027)
    ·
      refine ⟨87604152623114227631965541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58402768415409485087977027 87604152623114227631965541)
      ·
        refine ⟨16425778616833917680993539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 87604152623114227631965541 16425778616833917680993539)
        ·
          refine ⟨24638667925250876521490309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16425778616833917680993539 24638667925250876521490309)
          ·
            refine ⟨4619750235984539347779433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24638667925250876521490309 4619750235984539347779433)
            ·
              refine ⟨3464812676988404510834575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4619750235984539347779433 3464812676988404510834575)
              ·
                refine ⟨5197219015482606766251863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3464812676988404510834575 5197219015482606766251863)
                ·
                  refine ⟨7795828523223910149377795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5197219015482606766251863 7795828523223910149377795)
                  ·
                    refine ⟨11693742784835865224066693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7795828523223910149377795 11693742784835865224066693)
                    ·
                      refine ⟨2192576772156724729512505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11693742784835865224066693 2192576772156724729512505)
                      ·
                        rfl

theorem cell23_4270028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 2, 1, 1, 1, 4].length) (baseStart_4270028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4270028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4270028 prefixEnd_4270028 := by exact prefixLift 4270028
  have htrace : WordTrace (prefixWord ++ tailWord_4270028) baseStart_4270028 baseEnd_4270028 := by
    simpa [prefixWord, tailWord_4270028, baseEnd_4270028] using wordTrace_append hprefix tailTrace_4270028
  have hstable : (prefixWord ++ tailWord_4270028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4270028).length < 2 ^ (prefixWord ++ tailWord_4270028).sum := by decide
  have hdescent : baseEnd_4270028 < baseStart_4270028 := by decide
  rcases family_descends (prefixWord ++ tailWord_4270028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4270034 : List Nat := [3, 2, 2, 3, 2, 1, 10]
def baseStart_4270034 : Nat := 118140960795 + 4270034 * 2 ^ 59
def prefixEnd_4270034 : Nat := 4983230072969 + 3 ^ 40 * 4270034 * 2
def baseEnd_4270034 : Nat := 27068887074575946988117

theorem tailTrace_4270034 : CollatzResearch.WordTrace tailWord_4270034 prefixEnd_4270034 27068887074575946988117 := by
  unfold tailWord_4270034
  simp only [CollatzResearch.WordTrace]
  refine ⟨38935233653100889148164289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103827289741602371061771437 38935233653100889148164289)
  ·
    refine ⟨29201425239825666861123217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38935233653100889148164289 29201425239825666861123217)
    ·
      refine ⟨21901068929869250145842413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29201425239825666861123217 21901068929869250145842413)
      ·
        refine ⟨8212900848700968804690905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21901068929869250145842413 8212900848700968804690905)
        ·
          refine ⟨6159675636525726603518179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8212900848700968804690905 6159675636525726603518179)
          ·
            refine ⟨9239513454788589905277269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6159675636525726603518179 9239513454788589905277269)
            ·
              refine ⟨27068887074575946988117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 9239513454788589905277269 27068887074575946988117)
              ·
                rfl

theorem cell23_4270034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 10].length) (baseStart_4270034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4270034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4270034 prefixEnd_4270034 := by exact prefixLift 4270034
  have htrace : WordTrace (prefixWord ++ tailWord_4270034) baseStart_4270034 baseEnd_4270034 := by
    simpa [prefixWord, tailWord_4270034, baseEnd_4270034] using wordTrace_append hprefix tailTrace_4270034
  have hstable : (prefixWord ++ tailWord_4270034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4270034).length < 2 ^ (prefixWord ++ tailWord_4270034).sum := by decide
  have hdescent : baseEnd_4270034 < baseStart_4270034 := by decide
  rcases family_descends (prefixWord ++ tailWord_4270034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4270038 : List Nat := [5, 2, 1, 1, 3, 1, 1, 1, 4, 4]
def baseStart_4270038 : Nat := 118140960795 + 4270038 * 2 ^ 59
def prefixEnd_4270038 : Nat := 4983230072969 + 3 ^ 40 * 4270038 * 2
def baseEnd_4270038 : Nat := 730860635654423230129153

theorem tailTrace_4270038 : CollatzResearch.WordTrace tailWord_4270038 prefixEnd_4270038 730860635654423230129153 := by
  unfold tailWord_4270038
  simp only [CollatzResearch.WordTrace]
  refine ⟨9733817531524316579737673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 103827387002926043517201845 9733817531524316579737673)
  ·
    refine ⟨7300363148643237434803255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9733817531524316579737673 7300363148643237434803255)
    ·
      refine ⟨10950544722964856152204883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7300363148643237434803255 10950544722964856152204883)
      ·
        refine ⟨16425817084447284228307325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10950544722964856152204883 16425817084447284228307325)
        ·
          refine ⟨6159681406667731585615247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16425817084447284228307325 6159681406667731585615247)
          ·
            refine ⟨9239522110001597378422871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6159681406667731585615247 9239522110001597378422871)
            ·
              refine ⟨13859283165002396067634307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9239522110001597378422871 13859283165002396067634307)
              ·
                refine ⟨20788924747503594101451461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13859283165002396067634307 20788924747503594101451461)
                ·
                  refine ⟨3897923390156923894022149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20788924747503594101451461 3897923390156923894022149)
                  ·
                    refine ⟨730860635654423230129153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3897923390156923894022149 730860635654423230129153)
                    ·
                      rfl

theorem cell23_4270038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 1, 4, 4].length) (baseStart_4270038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4270038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4270038 prefixEnd_4270038 := by exact prefixLift 4270038
  have htrace : WordTrace (prefixWord ++ tailWord_4270038) baseStart_4270038 baseEnd_4270038 := by
    simpa [prefixWord, tailWord_4270038, baseEnd_4270038] using wordTrace_append hprefix tailTrace_4270038
  have hstable : (prefixWord ++ tailWord_4270038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4270038).length < 2 ^ (prefixWord ++ tailWord_4270038).sum := by decide
  have hdescent : baseEnd_4270038 < baseStart_4270038 := by decide
  rcases family_descends (prefixWord ++ tailWord_4270038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4270045 : List Nat := [1, 4, 3, 1, 3, 1, 2, 1, 3, 2, 2]
def baseStart_4270045 : Nat := 118140960795 + 4270045 * 2 ^ 59
def prefixEnd_4270045 : Nat := 4983230072969 + 3 ^ 40 * 4270045 * 2
def baseEnd_4270045 : Nat := 2192585501327851162999927

theorem tailTrace_4270045 : CollatzResearch.WordTrace tailWord_4270045 prefixEnd_4270045 2192585501327851162999927 := by
  unfold tailWord_4270045
  simp only [CollatzResearch.WordTrace]
  refine ⟨155741335815363705471307589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103827557210242470314205059 155741335815363705471307589)
  ·
    refine ⟨29201500465380694775870173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 155741335815363705471307589 29201500465380694775870173)
    ·
      refine ⟨10950562674517760540951315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29201500465380694775870173 10950562674517760540951315)
      ·
        refine ⟨16425844011776640811426973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10950562674517760540951315 16425844011776640811426973)
        ·
          refine ⟨6159691504416240304285115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16425844011776640811426973 6159691504416240304285115)
          ·
            refine ⟨9239537256624360456427673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6159691504416240304285115 9239537256624360456427673)
            ·
              refine ⟨6929652942468270342320755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9239537256624360456427673 6929652942468270342320755)
              ·
                refine ⟨10394479413702405513481133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6929652942468270342320755 10394479413702405513481133)
                ·
                  refine ⟨3897929780138402067555425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10394479413702405513481133 3897929780138402067555425)
                  ·
                    refine ⟨2923447335103801550666569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3897929780138402067555425 2923447335103801550666569)
                    ·
                      refine ⟨2192585501327851162999927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2923447335103801550666569 2192585501327851162999927)
                      ·
                        rfl

theorem cell23_4270045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 2, 1, 3, 2, 2].length) (baseStart_4270045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4270045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4270045 prefixEnd_4270045 := by exact prefixLift 4270045
  have htrace : WordTrace (prefixWord ++ tailWord_4270045) baseStart_4270045 baseEnd_4270045 := by
    simpa [prefixWord, tailWord_4270045, baseEnd_4270045] using wordTrace_append hprefix tailTrace_4270045
  have hstable : (prefixWord ++ tailWord_4270045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4270045).length < 2 ^ (prefixWord ++ tailWord_4270045).sum := by decide
  have hdescent : baseEnd_4270045 < baseStart_4270045 := by decide
  rcases family_descends (prefixWord ++ tailWord_4270045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4270067 : List Nat := [1, 1, 1, 2, 2, 2, 1, 4, 2, 3, 4]
def baseStart_4270067 : Nat := 118140960795 + 4270067 * 2 ^ 59
def prefixEnd_4270067 : Nat := 4983230072969 + 3 ^ 40 * 4270067 * 2
def baseEnd_4270067 : Nat := 2192596797902250076924825

theorem tailTrace_4270067 : CollatzResearch.WordTrace tailWord_4270067 prefixEnd_4270067 2192596797902250076924825 := by
  unfold tailWord_4270067
  simp only [CollatzResearch.WordTrace]
  refine ⟨155742138221284003228608455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103828092147522668819072303 155742138221284003228608455)
  ·
    refine ⟨233613207331926004842912683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155742138221284003228608455 233613207331926004842912683)
    ·
      refine ⟨350419810997889007264369025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 233613207331926004842912683 350419810997889007264369025)
      ·
        refine ⟨262814858248416755448276769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 350419810997889007264369025 262814858248416755448276769)
        ·
          refine ⟨197111143686312566586207577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 262814858248416755448276769 197111143686312566586207577)
          ·
            refine ⟨147833357764734424939655683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 197111143686312566586207577 147833357764734424939655683)
            ·
              refine ⟨221750036647101637409483525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 147833357764734424939655683 221750036647101637409483525)
              ·
                refine ⟨41578131871331557014278161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 221750036647101637409483525 41578131871331557014278161)
                ·
                  refine ⟨31183598903498667760708621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41578131871331557014278161 31183598903498667760708621)
                  ·
                    refine ⟨11693849588812000410265733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 31183598903498667760708621 11693849588812000410265733)
                    ·
                      refine ⟨2192596797902250076924825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11693849588812000410265733 2192596797902250076924825)
                      ·
                        rfl

theorem cell23_4270067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 4, 2, 3, 4].length) (baseStart_4270067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4270067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4270067 prefixEnd_4270067 := by exact prefixLift 4270067
  have htrace : WordTrace (prefixWord ++ tailWord_4270067) baseStart_4270067 baseEnd_4270067 := by
    simpa [prefixWord, tailWord_4270067, baseEnd_4270067] using wordTrace_append hprefix tailTrace_4270067
  have hstable : (prefixWord ++ tailWord_4270067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4270067).length < 2 ^ (prefixWord ++ tailWord_4270067).sum := by decide
  have hdescent : baseEnd_4270067 < baseStart_4270067 := by decide
  rcases family_descends (prefixWord ++ tailWord_4270067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4270077 : List Nat := [1, 4, 1, 1, 1, 2, 2, 2, 1, 8]
def baseStart_4270077 : Nat := 118140960795 + 4270077 * 2 ^ 59
def prefixEnd_4270077 : Nat := 4983230072969 + 3 ^ 40 * 4270077 * 2
def baseEnd_4270077 : Nat := 730867310902931679266593

theorem tailTrace_4270077 : CollatzResearch.WordTrace tailWord_4270077 prefixEnd_4270077 730867310902931679266593 := by
  unfold tailWord_4270077
  simp only [CollatzResearch.WordTrace]
  refine ⟨155742502951247774936472485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103828335300831849957648323 155742502951247774936472485)
  ·
    refine ⟨29201719303358957800588591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 155742502951247774936472485 29201719303358957800588591)
    ·
      refine ⟨43802578955038436700882887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29201719303358957800588591 43802578955038436700882887)
      ·
        refine ⟨65703868432557655051324331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43802578955038436700882887 65703868432557655051324331)
        ·
          refine ⟨98555802648836482576986497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65703868432557655051324331 98555802648836482576986497)
          ·
            refine ⟨73916851986627361932739873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98555802648836482576986497 73916851986627361932739873)
            ·
              refine ⟨55437638989970521449554905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73916851986627361932739873 55437638989970521449554905)
              ·
                refine ⟨41578229242477891087166179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55437638989970521449554905 41578229242477891087166179)
                ·
                  refine ⟨62367343863716836630749269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41578229242477891087166179 62367343863716836630749269)
                  ·
                    refine ⟨730867310902931679266593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 62367343863716836630749269 730867310902931679266593)
                    ·
                      rfl

theorem cell23_4270077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 2, 1, 8].length) (baseStart_4270077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4270077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4270077 prefixEnd_4270077 := by exact prefixLift 4270077
  have htrace : WordTrace (prefixWord ++ tailWord_4270077) baseStart_4270077 baseEnd_4270077 := by
    simpa [prefixWord, tailWord_4270077, baseEnd_4270077] using wordTrace_append hprefix tailTrace_4270077
  have hstable : (prefixWord ++ tailWord_4270077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4270077).length < 2 ^ (prefixWord ++ tailWord_4270077).sum := by decide
  have hdescent : baseEnd_4270077 < baseStart_4270077 := by decide
  rcases family_descends (prefixWord ++ tailWord_4270077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4270078 : List Nat := [4, 2, 2, 2, 1, 1, 1, 2, 4, 1, 3]
def baseStart_4270078 : Nat := 118140960795 + 4270078 * 2 ^ 59
def prefixEnd_4270078 : Nat := 4983230072969 + 3 ^ 40 * 4270078 * 2
def baseEnd_4270078 : Nat := 2192602446189449533887275

theorem tailTrace_4270078 : CollatzResearch.WordTrace tailWord_4270078 prefixEnd_4270078 2192602446189449533887275 := by
  unfold tailWord_4270078
  simp only [CollatzResearch.WordTrace]
  refine ⟨19467817428030519013407361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 103828359616162768071505925 19467817428030519013407361)
  ·
    refine ⟨14600863071022889260055521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19467817428030519013407361 14600863071022889260055521)
    ·
      refine ⟨10950647303267166945041641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14600863071022889260055521 10950647303267166945041641)
      ·
        refine ⟨8212985477450375208781231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10950647303267166945041641 8212985477450375208781231)
        ·
          refine ⟨12319478216175562813171847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8212985477450375208781231 12319478216175562813171847)
          ·
            refine ⟨18479217324263344219757771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12319478216175562813171847 18479217324263344219757771)
            ·
              refine ⟨27718825986395016329636657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18479217324263344219757771 27718825986395016329636657)
              ·
                refine ⟨20789119489796262247227493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27718825986395016329636657 20789119489796262247227493)
                ·
                  refine ⟨3897959904336799171355155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20789119489796262247227493 3897959904336799171355155)
                  ·
                    refine ⟨5846939856505198757032733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3897959904336799171355155 5846939856505198757032733)
                    ·
                      refine ⟨2192602446189449533887275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5846939856505198757032733 2192602446189449533887275)
                      ·
                        rfl

theorem cell23_4270078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 2, 4, 1, 3].length) (baseStart_4270078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4270078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4270078 prefixEnd_4270078 := by exact prefixLift 4270078
  have htrace : WordTrace (prefixWord ++ tailWord_4270078) baseStart_4270078 baseEnd_4270078 := by
    simpa [prefixWord, tailWord_4270078, baseEnd_4270078] using wordTrace_append hprefix tailTrace_4270078
  have hstable : (prefixWord ++ tailWord_4270078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4270078).length < 2 ^ (prefixWord ++ tailWord_4270078).sum := by decide
  have hdescent : baseEnd_4270078 < baseStart_4270078 := by decide
  rcases family_descends (prefixWord ++ tailWord_4270078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4270104 : List Nat := [2, 1, 2, 3, 2, 1, 2, 1, 2, 4, 3]
def baseStart_4270104 : Nat := 118140960795 + 4270104 * 2 ^ 59
def prefixEnd_4270104 : Nat := 4983230072969 + 3 ^ 40 * 4270104 * 2
def baseEnd_4270104 : Nat := 2192615796686466432162155

theorem tailTrace_4270104 : CollatzResearch.WordTrace tailWord_4270104 prefixEnd_4270104 2192615796686466432162155 := by
  unfold tailWord_4270104
  simp only [CollatzResearch.WordTrace]
  refine ⟨77871743861074979273852683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103828991814766639031803577 77871743861074979273852683)
  ·
    refine ⟨116807615791612468910779025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77871743861074979273852683 116807615791612468910779025)
    ·
      refine ⟨87605711843709351683084269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116807615791612468910779025 87605711843709351683084269)
      ·
        refine ⟨32852141941391006881156601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87605711843709351683084269 32852141941391006881156601)
        ·
          refine ⟨24639106456043255160867451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32852141941391006881156601 24639106456043255160867451)
          ·
            refine ⟨36958659684064882741301177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24639106456043255160867451 36958659684064882741301177)
            ·
              refine ⟨27718994763048662055975883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36958659684064882741301177 27718994763048662055975883)
              ·
                refine ⟨41578492144572993083963825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27718994763048662055975883 41578492144572993083963825)
                ·
                  refine ⟨31183869108429744812972869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41578492144572993083963825 31183869108429744812972869)
                  ·
                    refine ⟨5846975457830577152432413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 31183869108429744812972869 5846975457830577152432413)
                    ·
                      refine ⟨2192615796686466432162155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5846975457830577152432413 2192615796686466432162155)
                      ·
                        rfl

theorem cell23_4270104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 1, 2, 4, 3].length) (baseStart_4270104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4270104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4270104 prefixEnd_4270104 := by exact prefixLift 4270104
  have htrace : WordTrace (prefixWord ++ tailWord_4270104) baseStart_4270104 baseEnd_4270104 := by
    simpa [prefixWord, tailWord_4270104, baseEnd_4270104] using wordTrace_append hprefix tailTrace_4270104
  have hstable : (prefixWord ++ tailWord_4270104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4270104).length < 2 ^ (prefixWord ++ tailWord_4270104).sum := by decide
  have hdescent : baseEnd_4270104 < baseStart_4270104 := by decide
  rcases family_descends (prefixWord ++ tailWord_4270104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4270107 : List Nat := [1, 1, 1, 1, 1, 1, 3, 7, 7]
def baseStart_4270107 : Nat := 118140960795 + 4270107 * 2 ^ 59
def prefixEnd_4270107 : Nat := 4983230072969 + 3 ^ 40 * 4270107 * 2
def baseEnd_4270107 : Nat := 243624148569825546713849

theorem tailTrace_4270107 : CollatzResearch.WordTrace tailWord_4270107 prefixEnd_4270107 243624148569825546713849 := by
  unfold tailWord_4270107
  simp only [CollatzResearch.WordTrace]
  refine ⟨155743597141139090060064575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103829064760759393373376383 155743597141139090060064575)
  ·
    refine ⟨233615395711708635090096863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155743597141139090060064575 233615395711708635090096863)
    ·
      refine ⟨350423093567562952635145295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 233615395711708635090096863 350423093567562952635145295)
      ·
        refine ⟨525634640351344428952717943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 350423093567562952635145295 525634640351344428952717943)
        ·
          refine ⟨788451960527016643429076915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 525634640351344428952717943 788451960527016643429076915)
          ·
            refine ⟨1182677940790524965143615373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 788451960527016643429076915 1182677940790524965143615373)
            ·
              refine ⟨443504227796446861928855765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1182677940790524965143615373 443504227796446861928855765)
              ·
                refine ⟨10394630338979223326457557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 443504227796446861928855765 10394630338979223326457557)
                ·
                  refine ⟨243624148569825546713849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10394630338979223326457557 243624148569825546713849)
                  ·
                    rfl

theorem cell23_4270107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 7, 7].length) (baseStart_4270107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4270107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4270107 prefixEnd_4270107 := by exact prefixLift 4270107
  have htrace : WordTrace (prefixWord ++ tailWord_4270107) baseStart_4270107 baseEnd_4270107 := by
    simpa [prefixWord, tailWord_4270107, baseEnd_4270107] using wordTrace_append hprefix tailTrace_4270107
  have hstable : (prefixWord ++ tailWord_4270107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4270107).length < 2 ^ (prefixWord ++ tailWord_4270107).sum := by decide
  have hdescent : baseEnd_4270107 < baseStart_4270107 := by decide
  rcases family_descends (prefixWord ++ tailWord_4270107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4270114 : List Nat := [3, 3, 1, 1, 1, 2, 2, 1, 1, 4, 4]
def baseStart_4270114 : Nat := 118140960795 + 4270114 * 2 ^ 59
def prefixEnd_4270114 : Nat := 4983230072969 + 3 ^ 40 * 4270114 * 2
def baseEnd_4270114 : Nat := 2192620931493011393037109

theorem tailTrace_4270114 : CollatzResearch.WordTrace tailWord_4270114 prefixEnd_4270114 2192620931493011393037109 := by
  unfold tailWord_4270114
  simp only [CollatzResearch.WordTrace]
  refine ⟨38935963113028432563892349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103829234968075820170379597 38935963113028432563892349)
  ·
    refine ⟨14600986167385662211459631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38935963113028432563892349 14600986167385662211459631)
    ·
      refine ⟨21901479251078493317189447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14600986167385662211459631 21901479251078493317189447)
      ·
        refine ⟨32852218876617739975784171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21901479251078493317189447 32852218876617739975784171)
        ·
          refine ⟨49278328314926609963676257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32852218876617739975784171 49278328314926609963676257)
          ·
            refine ⟨36958746236194957472757193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49278328314926609963676257 36958746236194957472757193)
            ·
              refine ⟨27719059677146218104567895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36958746236194957472757193 27719059677146218104567895)
              ·
                refine ⟨41578589515719327156851843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27719059677146218104567895 41578589515719327156851843)
                ·
                  refine ⟨62367884273578990735277765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41578589515719327156851843 62367884273578990735277765)
                  ·
                    refine ⟨11693978301296060762864581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 62367884273578990735277765 11693978301296060762864581)
                    ·
                      refine ⟨2192620931493011393037109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11693978301296060762864581 2192620931493011393037109)
                      ·
                        rfl

theorem cell23_4270114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 1, 1, 4, 4].length) (baseStart_4270114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4270114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4270114 prefixEnd_4270114 := by exact prefixLift 4270114
  have htrace : WordTrace (prefixWord ++ tailWord_4270114) baseStart_4270114 baseEnd_4270114 := by
    simpa [prefixWord, tailWord_4270114, baseEnd_4270114] using wordTrace_append hprefix tailTrace_4270114
  have hstable : (prefixWord ++ tailWord_4270114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4270114).length < 2 ^ (prefixWord ++ tailWord_4270114).sum := by decide
  have hdescent : baseEnd_4270114 < baseStart_4270114 := by decide
  rcases family_descends (prefixWord ++ tailWord_4270114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4270141 : List Nat := [1, 4, 1, 3, 1, 1, 2, 5, 5]
def baseStart_4270141 : Nat := 118140960795 + 4270141 * 2 ^ 59
def prefixEnd_4270141 : Nat := 4983230072969 + 3 ^ 40 * 4270141 * 2
def baseEnd_4270141 : Nat := 243626088385631420822165

theorem tailTrace_4270141 : CollatzResearch.WordTrace tailWord_4270141 prefixEnd_4270141 243626088385631420822165 := by
  unfold tailWord_4270141
  simp only [CollatzResearch.WordTrace]
  refine ⟨155744837223015913866802277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103829891482010609244534851 155744837223015913866802277)
  ·
    refine ⟨29202156979315483850025427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 155744837223015913866802277 29202156979315483850025427)
    ·
      refine ⟨43803235468973225775038141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29202156979315483850025427 43803235468973225775038141)
      ·
        refine ⟨16426213300864959665639303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43803235468973225775038141 16426213300864959665639303)
        ·
          refine ⟨24639319951297439498458955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16426213300864959665639303 24639319951297439498458955)
          ·
            refine ⟨36958979926946159247688433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24639319951297439498458955 36958979926946159247688433)
            ·
              refine ⟨27719234945209619435766325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36958979926946159247688433 27719234945209619435766325)
              ·
                refine ⟨2598678276113401822103093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27719234945209619435766325 2598678276113401822103093)
                ·
                  refine ⟨243626088385631420822165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2598678276113401822103093 243626088385631420822165)
                  ·
                    rfl

theorem cell23_4270141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 5, 5].length) (baseStart_4270141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4270141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4270141 prefixEnd_4270141 := by exact prefixLift 4270141
  have htrace : WordTrace (prefixWord ++ tailWord_4270141) baseStart_4270141 baseEnd_4270141 := by
    simpa [prefixWord, tailWord_4270141, baseEnd_4270141] using wordTrace_append hprefix tailTrace_4270141
  have hstable : (prefixWord ++ tailWord_4270141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4270141).length < 2 ^ (prefixWord ++ tailWord_4270141).sum := by decide
  have hdescent : baseEnd_4270141 < baseStart_4270141 := by decide
  rcases family_descends (prefixWord ++ tailWord_4270141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4270158 : List Nat := [4, 1, 1, 1, 1, 4, 4, 2, 5]
def baseStart_4270158 : Nat := 118140960795 + 4270158 * 2 ^ 59
def prefixEnd_4270158 : Nat := 4983230072969 + 3 ^ 40 * 4270158 * 2
def baseEnd_4270158 : Nat := 243627058293534357876323

theorem tailTrace_4270158 : CollatzResearch.WordTrace tailWord_4270158 prefixEnd_4270158 243627058293534357876323 := by
  unfold tailWord_4270158
  simp only [CollatzResearch.WordTrace]
  refine ⟨19468182157994290721271391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 103830304842636217180114085 19468182157994290721271391)
  ·
    refine ⟨29202273236991436081907087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19468182157994290721271391 29202273236991436081907087)
    ·
      refine ⟨43803409855487154122860631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29202273236991436081907087 43803409855487154122860631)
      ·
        refine ⟨65705114783230731184290947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43803409855487154122860631 65705114783230731184290947)
        ·
          refine ⟨98557672174846096776436421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65705114783230731184290947 98557672174846096776436421)
          ·
            refine ⟨18479563532783643145581829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 98557672174846096776436421 18479563532783643145581829)
            ·
              refine ⟨3464918162396933089796593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18479563532783643145581829 3464918162396933089796593)
              ·
                refine ⟨2598688621797699817347445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3464918162396933089796593 2598688621797699817347445)
                ·
                  refine ⟨243627058293534357876323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2598688621797699817347445 243627058293534357876323)
                  ·
                    rfl

theorem cell23_4270158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 4, 2, 5].length) (baseStart_4270158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4270158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4270158 prefixEnd_4270158 := by exact prefixLift 4270158
  have htrace : WordTrace (prefixWord ++ tailWord_4270158) baseStart_4270158 baseEnd_4270158 := by
    simpa [prefixWord, tailWord_4270158, baseEnd_4270158] using wordTrace_append hprefix tailTrace_4270158
  have hstable : (prefixWord ++ tailWord_4270158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4270158).length < 2 ^ (prefixWord ++ tailWord_4270158).sum := by decide
  have hdescent : baseEnd_4270158 < baseStart_4270158 := by decide
  rcases family_descends (prefixWord ++ tailWord_4270158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4270191 : List Nat := [1, 1, 2, 1, 3, 4, 3, 1, 2, 1, 4]
def baseStart_4270191 : Nat := 118140960795 + 4270191 * 2 ^ 59
def prefixEnd_4270191 : Nat := 4983230072969 + 3 ^ 40 * 4270191 * 2
def baseEnd_4270191 : Nat := 2192660469503407591774255

theorem tailTrace_4270191 : CollatzResearch.WordTrace tailWord_4270191 prefixEnd_4270191 2192660469503407591774255 := by
  unfold tailWord_4270191
  simp only [CollatzResearch.WordTrace]
  refine ⟨155746660872834772406122427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103831107248556514937414951 155746660872834772406122427)
  ·
    refine ⟨233619991309252158609183641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155746660872834772406122427 233619991309252158609183641)
    ·
      refine ⟨175214993481939118956887731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 233619991309252158609183641 175214993481939118956887731)
      ·
        refine ⟨262822490222908678435331597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175214993481939118956887731 262822490222908678435331597)
        ·
          refine ⟨98558433833590754413249349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 262822490222908678435331597 98558433833590754413249349)
          ·
            refine ⟨18479706343798266452484253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 98558433833590754413249349 18479706343798266452484253)
            ·
              refine ⟨6929889878924349919681595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18479706343798266452484253 6929889878924349919681595)
              ·
                refine ⟨10394834818386524879522393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6929889878924349919681595 10394834818386524879522393)
                ·
                  refine ⟨7796126113789893659641795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10394834818386524879522393 7796126113789893659641795)
                  ·
                    refine ⟨11694189170684840489462693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7796126113789893659641795 11694189170684840489462693)
                    ·
                      refine ⟨2192660469503407591774255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11694189170684840489462693 2192660469503407591774255)
                      ·
                        rfl

theorem cell23_4270191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 3, 1, 2, 1, 4].length) (baseStart_4270191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4270191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4270191 prefixEnd_4270191 := by exact prefixLift 4270191
  have htrace : WordTrace (prefixWord ++ tailWord_4270191) baseStart_4270191 baseEnd_4270191 := by
    simpa [prefixWord, tailWord_4270191, baseEnd_4270191] using wordTrace_append hprefix tailTrace_4270191
  have hstable : (prefixWord ++ tailWord_4270191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4270191).length < 2 ^ (prefixWord ++ tailWord_4270191).sum := by decide
  have hdescent : baseEnd_4270191 < baseStart_4270191 := by decide
  rcases family_descends (prefixWord ++ tailWord_4270191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4270204 : List Nat := [2, 2, 2, 1, 1, 4, 1, 1, 2, 1, 6]
def baseStart_4270204 : Nat := 118140960795 + 4270204 * 2 ^ 59
def prefixEnd_4270204 : Nat := 4983230072969 + 3 ^ 40 * 4270204 * 2
def baseEnd_4270204 : Nat := 2192667144751916040911695

theorem tailTrace_4270204 : CollatzResearch.WordTrace tailWord_4270204 prefixEnd_4270204 2192667144751916040911695 := by
  unfold tailWord_4270204
  simp only [CollatzResearch.WordTrace]
  refine ⟨77873567510893837813172833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103831423347858450417563777 77873567510893837813172833)
  ·
    refine ⟨58405175633170378359879625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77873567510893837813172833 58405175633170378359879625)
    ·
      refine ⟨43803881724877783769909719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58405175633170378359879625 43803881724877783769909719)
      ·
        refine ⟨65705822587316675654864579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43803881724877783769909719 65705822587316675654864579)
        ·
          refine ⟨98558733880975013482296869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65705822587316675654864579 98558733880975013482296869)
          ·
            refine ⟨18479762602682815027930663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 98558733880975013482296869 18479762602682815027930663)
            ·
              refine ⟨27719643904024222541895995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18479762602682815027930663 27719643904024222541895995)
              ·
                refine ⟨41579465856036333812843993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27719643904024222541895995 41579465856036333812843993)
                ·
                  refine ⟨31184599392027250359632995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41579465856036333812843993 31184599392027250359632995)
                  ·
                    refine ⟨46776899088040875539449493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31184599392027250359632995 46776899088040875539449493)
                    ·
                      refine ⟨2192667144751916040911695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 46776899088040875539449493 2192667144751916040911695)
                      ·
                        rfl

theorem cell23_4270204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 1, 2, 1, 6].length) (baseStart_4270204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4270204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4270204 prefixEnd_4270204 := by exact prefixLift 4270204
  have htrace : WordTrace (prefixWord ++ tailWord_4270204) baseStart_4270204 baseEnd_4270204 := by
    simpa [prefixWord, tailWord_4270204, baseEnd_4270204] using wordTrace_append hprefix tailTrace_4270204
  have hstable : (prefixWord ++ tailWord_4270204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4270204).length < 2 ^ (prefixWord ++ tailWord_4270204).sum := by decide
  have hdescent : baseEnd_4270204 < baseStart_4270204 := by decide
  rcases family_descends (prefixWord ++ tailWord_4270204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4270218 : List Nat := [3, 1, 2, 3, 1, 3, 2, 1, 3, 4]
def baseStart_4270218 : Nat := 118140960795 + 4270218 * 2 ^ 59
def prefixEnd_4270218 : Nat := 4983230072969 + 3 ^ 40 * 4270218 * 2
def baseEnd_4270218 : Nat := 730891444493692995378877

theorem tailTrace_4270218 : CollatzResearch.WordTrace tailWord_4270218 prefixEnd_4270218 730891444493692995378877 := by
  unfold tailWord_4270218
  simp only [CollatzResearch.WordTrace]
  refine ⟨38936911410934239004338827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103831763762491304011570205 38936911410934239004338827)
  ·
    refine ⟨58405367116401358506508241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38936911410934239004338827 58405367116401358506508241)
    ·
      refine ⟨43804025337301018879881181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58405367116401358506508241 43804025337301018879881181)
      ·
        refine ⟨16426509501487882079955443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43804025337301018879881181 16426509501487882079955443)
        ·
          refine ⟨24639764252231823119933165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16426509501487882079955443 24639764252231823119933165)
          ·
            refine ⟨9239911594586933669974937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24639764252231823119933165 9239911594586933669974937)
            ·
              refine ⟨6929933695940200252481203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9239911594586933669974937 6929933695940200252481203)
              ·
                refine ⟨10394900543910300378721805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6929933695940200252481203 10394900543910300378721805)
                ·
                  refine ⟨3898087703966362642020677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10394900543910300378721805 3898087703966362642020677)
                  ·
                    refine ⟨730891444493692995378877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3898087703966362642020677 730891444493692995378877)
                    ·
                      rfl

theorem cell23_4270218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 2, 1, 3, 4].length) (baseStart_4270218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4270218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4270218 prefixEnd_4270218 := by exact prefixLift 4270218
  have htrace : WordTrace (prefixWord ++ tailWord_4270218) baseStart_4270218 baseEnd_4270218 := by
    simpa [prefixWord, tailWord_4270218, baseEnd_4270218] using wordTrace_append hprefix tailTrace_4270218
  have hstable : (prefixWord ++ tailWord_4270218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4270218).length < 2 ^ (prefixWord ++ tailWord_4270218).sum := by decide
  have hdescent : baseEnd_4270218 < baseStart_4270218 := by decide
  rcases family_descends (prefixWord ++ tailWord_4270218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4270281 : List Nat := [1, 2, 1, 1, 2, 1, 1, 4, 2, 6, 2]
def baseStart_4270281 : Nat := 118140960795 + 4270281 * 2 ^ 59
def prefixEnd_4270281 : Nat := 4983230072969 + 3 ^ 40 * 4270281 * 2
def baseEnd_4270281 : Nat := 2192706682762312239648841

theorem tailTrace_4270281 : CollatzResearch.WordTrace tailWord_4270281 prefixEnd_4270281 2192706682762312239648841 := by
  unfold tailWord_4270281
  simp only [CollatzResearch.WordTrace]
  refine ⟨155749943442508717776898697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103833295628339145184599131 155749943442508717776898697)
  ·
    refine ⟨116812457581881538332674023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155749943442508717776898697 116812457581881538332674023)
    ·
      refine ⟨175218686372822307499011035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116812457581881538332674023 175218686372822307499011035)
      ·
        refine ⟨262828029559233461248516553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175218686372822307499011035 262828029559233461248516553)
        ·
          refine ⟨197121022169425095936387415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 262828029559233461248516553 197121022169425095936387415)
          ·
            refine ⟨295681533254137643904581123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 197121022169425095936387415 295681533254137643904581123)
            ·
              refine ⟨443522299881206465856871685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 295681533254137643904581123 443522299881206465856871685)
              ·
                refine ⟨83160431227726212348163441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 443522299881206465856871685 83160431227726212348163441)
                ·
                  refine ⟨62370323420794659261122581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 83160431227726212348163441 62370323420794659261122581)
                  ·
                    refine ⟨2923608910349749652865121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 62370323420794659261122581 2923608910349749652865121)
                    ·
                      refine ⟨2192706682762312239648841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2923608910349749652865121 2192706682762312239648841)
                      ·
                        rfl

theorem cell23_4270281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 4, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 4, 2, 6, 2].length) (baseStart_4270281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4270281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4270281 prefixEnd_4270281 := by exact prefixLift 4270281
  have htrace : WordTrace (prefixWord ++ tailWord_4270281) baseStart_4270281 baseEnd_4270281 := by
    simpa [prefixWord, tailWord_4270281, baseEnd_4270281] using wordTrace_append hprefix tailTrace_4270281
  have hstable : (prefixWord ++ tailWord_4270281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4270281).length < 2 ^ (prefixWord ++ tailWord_4270281).sum := by decide
  have hdescent : baseEnd_4270281 < baseStart_4270281 := by decide
  rcases family_descends (prefixWord ++ tailWord_4270281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4270298 : List Nat := [3, 1, 1, 2, 2, 1, 5, 2, 1, 1, 4]
def baseStart_4270298 : Nat := 118140960795 + 4270298 * 2 ^ 59
def prefixEnd_4270298 : Nat := 4983230072969 + 3 ^ 40 * 4270298 * 2
def baseEnd_4270298 : Nat := 2192715411933438673136263

theorem tailTrace_4270298 : CollatzResearch.WordTrace tailWord_4270298 prefixEnd_4270298 2192715411933438673136263 := by
  unfold tailWord_4270298
  simp only [CollatzResearch.WordTrace]
  refine ⟨38937640870861782420066887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103833708988964753120178365 38937640870861782420066887)
  ·
    refine ⟨58406461306292673630100331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38937640870861782420066887 58406461306292673630100331)
    ·
      refine ⟨87609691959439010445150497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58406461306292673630100331 87609691959439010445150497)
      ·
        refine ⟨65707268969579257833862873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87609691959439010445150497 65707268969579257833862873)
        ·
          refine ⟨49280451727184443375397155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65707268969579257833862873 49280451727184443375397155)
          ·
            refine ⟨73920677590776665063095733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49280451727184443375397155 73920677590776665063095733)
            ·
              refine ⟨6930063524135312349665225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 73920677590776665063095733 6930063524135312349665225)
              ·
                refine ⟨5197547643101484262248919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6930063524135312349665225 5197547643101484262248919)
                ·
                  refine ⟨7796321464652226393373379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5197547643101484262248919 7796321464652226393373379)
                  ·
                    refine ⟨11694482196978339590060069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7796321464652226393373379 11694482196978339590060069)
                    ·
                      refine ⟨2192715411933438673136263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11694482196978339590060069 2192715411933438673136263)
                      ·
                        rfl

theorem cell23_4270298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 5, 2, 1, 1, 4].length) (baseStart_4270298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4270298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4270298 prefixEnd_4270298 := by exact prefixLift 4270298
  have htrace : WordTrace (prefixWord ++ tailWord_4270298) baseStart_4270298 baseEnd_4270298 := by
    simpa [prefixWord, tailWord_4270298, baseEnd_4270298] using wordTrace_append hprefix tailTrace_4270298
  have hstable : (prefixWord ++ tailWord_4270298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4270298).length < 2 ^ (prefixWord ++ tailWord_4270298).sum := by decide
  have hdescent : baseEnd_4270298 < baseStart_4270298 := by decide
  rcases family_descends (prefixWord ++ tailWord_4270298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4270304 : List Nat := [2, 1, 1, 3, 1, 3, 1, 11]
def baseStart_4270304 : Nat := 118140960795 + 4270304 * 2 ^ 59
def prefixEnd_4270304 : Nat := 4983230072969 + 3 ^ 40 * 4270304 * 2
def baseEnd_4270304 : Nat := 81211796030272801839305

theorem tailTrace_4270304 : CollatzResearch.WordTrace tailWord_4270304 prefixEnd_4270304 81211796030272801839305 := by
  unfold tailWord_4270304
  simp only [CollatzResearch.WordTrace]
  refine ⟨77875391160712696352492983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103833854880950261803323977 77875391160712696352492983)
  ·
    refine ⟨116813086741069044528739475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77875391160712696352492983 116813086741069044528739475)
    ·
      refine ⟨175219630111603566793109213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116813086741069044528739475 175219630111603566793109213)
      ·
        refine ⟨65707361291851337547415955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 175219630111603566793109213 65707361291851337547415955)
        ·
          refine ⟨98561041937777006321123933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65707361291851337547415955 98561041937777006321123933)
          ·
            refine ⟨36960390726666377370421475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 98561041937777006321123933 36960390726666377370421475)
            ·
              refine ⟨55440586089999566055632213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36960390726666377370421475 55440586089999566055632213)
              ·
                refine ⟨81211796030272801839305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 55440586089999566055632213 81211796030272801839305)
                ·
                  rfl

theorem cell23_4270304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 11].length) (baseStart_4270304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4270304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4270304 prefixEnd_4270304 := by exact prefixLift 4270304
  have htrace : WordTrace (prefixWord ++ tailWord_4270304) baseStart_4270304 baseEnd_4270304 := by
    simpa [prefixWord, tailWord_4270304, baseEnd_4270304] using wordTrace_append hprefix tailTrace_4270304
  have hstable : (prefixWord ++ tailWord_4270304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4270304).length < 2 ^ (prefixWord ++ tailWord_4270304).sum := by decide
  have hdescent : baseEnd_4270304 < baseStart_4270304 := by decide
  rcases family_descends (prefixWord ++ tailWord_4270304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4270338 : List Nat := [3, 4, 1, 1, 2, 1, 3, 8]
def baseStart_4270338 : Nat := 118140960795 + 4270338 * 2 ^ 59
def prefixEnd_4270338 : Nat := 4983230072969 + 3 ^ 40 * 4270338 * 2
def baseEnd_4270338 : Nat := 81212442635541426542077

theorem tailTrace_4270338 : CollatzResearch.WordTrace tailWord_4270338 prefixEnd_4270338 81212442635541426542077 := by
  unfold tailWord_4270338
  simp only [CollatzResearch.WordTrace]
  refine ⟨38938005600825554127930917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103834681602201477674482445 38938005600825554127930917)
  ·
    refine ⟨7300876050154791398987047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38938005600825554127930917 7300876050154791398987047)
    ·
      refine ⟨10951314075232187098480571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7300876050154791398987047 10951314075232187098480571)
      ·
        refine ⟨16426971112848280647720857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10951314075232187098480571 16426971112848280647720857)
        ·
          refine ⟨12320228334636210485790643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16426971112848280647720857 12320228334636210485790643)
          ·
            refine ⟨18480342501954315728685965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12320228334636210485790643 18480342501954315728685965)
            ·
              refine ⟨6930128438232868398257237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18480342501954315728685965 6930128438232868398257237)
              ·
                refine ⟨81212442635541426542077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6930128438232868398257237 81212442635541426542077)
                ·
                  rfl

theorem cell23_4270338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 3, 8].length) (baseStart_4270338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4270338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4270338 prefixEnd_4270338 := by exact prefixLift 4270338
  have htrace : WordTrace (prefixWord ++ tailWord_4270338) baseStart_4270338 baseEnd_4270338 := by
    simpa [prefixWord, tailWord_4270338, baseEnd_4270338] using wordTrace_append hprefix tailTrace_4270338
  have hstable : (prefixWord ++ tailWord_4270338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4270338).length < 2 ^ (prefixWord ++ tailWord_4270338).sum := by decide
  have hdescent : baseEnd_4270338 < baseStart_4270338 := by decide
  rcases family_descends (prefixWord ++ tailWord_4270338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4270348 : List Nat := [2, 2, 1, 2, 2, 2, 4, 1, 1, 3, 3]
def baseStart_4270348 : Nat := 118140960795 + 4270348 * 2 ^ 59
def prefixEnd_4270348 : Nat := 4983230072969 + 3 ^ 40 * 4270348 * 2
def baseEnd_4270348 : Nat := 2192741085966163477511033

theorem tailTrace_4270348 : CollatzResearch.WordTrace tailWord_4270348 prefixEnd_4270348 2192741085966163477511033 := by
  unfold tailWord_4270348
  simp only [CollatzResearch.WordTrace]
  refine ⟨77876193566632994109793849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103834924755510658813058465 77876193566632994109793849)
  ·
    refine ⟨58407145174974745582345387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77876193566632994109793849 58407145174974745582345387)
    ·
      refine ⟨87610717762462118373518081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58407145174974745582345387 87610717762462118373518081)
      ·
        refine ⟨65708038321846588780138561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87610717762462118373518081 65708038321846588780138561)
        ·
          refine ⟨49281028741384941585103921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65708038321846588780138561 49281028741384941585103921)
          ·
            refine ⟨36960771556038706188827941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49281028741384941585103921 36960771556038706188827941)
            ·
              refine ⟨6930144666757257410405239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36960771556038706188827941 6930144666757257410405239)
              ·
                refine ⟨10395217000135886115607859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6930144666757257410405239 10395217000135886115607859)
                ·
                  refine ⟨15592825500203829173411789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10395217000135886115607859 15592825500203829173411789)
                  ·
                    refine ⟨5847309562576435940029421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15592825500203829173411789 5847309562576435940029421)
                    ·
                      refine ⟨2192741085966163477511033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5847309562576435940029421 2192741085966163477511033)
                      ·
                        rfl

theorem cell23_4270348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 4, 1, 1, 3, 3].length) (baseStart_4270348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4270348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4270348 prefixEnd_4270348 := by exact prefixLift 4270348
  have htrace : WordTrace (prefixWord ++ tailWord_4270348) baseStart_4270348 baseEnd_4270348 := by
    simpa [prefixWord, tailWord_4270348, baseEnd_4270348] using wordTrace_append hprefix tailTrace_4270348
  have hstable : (prefixWord ++ tailWord_4270348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4270348).length < 2 ^ (prefixWord ++ tailWord_4270348).sum := by decide
  have hdescent : baseEnd_4270348 < baseStart_4270348 := by decide
  rcases family_descends (prefixWord ++ tailWord_4270348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4270366 : List Nat := [4, 3, 2, 1, 1, 1, 1, 5, 1, 2, 2]
def baseStart_4270366 : Nat := 118140960795 + 4270366 * 2 ^ 59
def prefixEnd_4270366 : Nat := 4983230072969 + 3 ^ 40 * 4270366 * 2
def baseEnd_4270366 : Nat := 2192750328617944407085951

theorem tailTrace_4270366 : CollatzResearch.WordTrace tailWord_4270366 prefixEnd_4270366 2192750328617944407085951 := by
  unfold tailWord_4270366
  simp only [CollatzResearch.WordTrace]
  refine ⟨19469130455900097161717869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 103835362431467184862495301 19469130455900097161717869)
  ·
    refine ⟨7300923920962536435644201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19469130455900097161717869 7300923920962536435644201)
    ·
      refine ⟨5475692940721902326733151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7300923920962536435644201 5475692940721902326733151)
      ·
        refine ⟨8213539411082853490099727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5475692940721902326733151 8213539411082853490099727)
        ·
          refine ⟨12320309116624280235149591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8213539411082853490099727 12320309116624280235149591)
          ·
            refine ⟨18480463674936420352724387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12320309116624280235149591 18480463674936420352724387)
            ·
              refine ⟨27720695512404630529086581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18480463674936420352724387 27720695512404630529086581)
              ·
                refine ⟨2598815204287934112101867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27720695512404630529086581 2598815204287934112101867)
                ·
                  refine ⟨3898222806431901168152801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2598815204287934112101867 3898222806431901168152801)
                  ·
                    refine ⟨2923667104823925876114601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3898222806431901168152801 2923667104823925876114601)
                    ·
                      refine ⟨2192750328617944407085951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2923667104823925876114601 2192750328617944407085951)
                      ·
                        rfl

theorem cell23_4270366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 5, 1, 2, 2].length) (baseStart_4270366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4270366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4270366 prefixEnd_4270366 := by exact prefixLift 4270366
  have htrace : WordTrace (prefixWord ++ tailWord_4270366) baseStart_4270366 baseEnd_4270366 := by
    simpa [prefixWord, tailWord_4270366, baseEnd_4270366] using wordTrace_append hprefix tailTrace_4270366
  have hstable : (prefixWord ++ tailWord_4270366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4270366).length < 2 ^ (prefixWord ++ tailWord_4270366).sum := by decide
  have hdescent : baseEnd_4270366 < baseStart_4270366 := by decide
  rcases family_descends (prefixWord ++ tailWord_4270366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4270391 : List Nat := [1, 1, 3, 1, 2, 1, 1, 3, 1, 6, 3]
def baseStart_4270391 : Nat := 118140960795 + 4270391 * 2 ^ 59
def prefixEnd_4270391 : Nat := 4983230072969 + 3 ^ 40 * 4270391 * 2
def baseEnd_4270391 : Nat := 2192763165634306809273335

theorem tailTrace_4270391 : CollatzResearch.WordTrace tailWord_4270391 prefixEnd_4270391 2192763165634306809273335 := by
  unfold tailWord_4270391
  simp only [CollatzResearch.WordTrace]
  refine ⟨155753955472110206563403027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103835970314740137708935351 155753955472110206563403027)
  ·
    refine ⟨233630933208165309845104541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155753955472110206563403027 233630933208165309845104541)
    ·
      refine ⟨87611599953061991191914203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 233630933208165309845104541 87611599953061991191914203)
      ·
        refine ⟨131417399929592986787871305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87611599953061991191914203 131417399929592986787871305)
        ·
          refine ⟨98563049947194740090903479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 131417399929592986787871305 98563049947194740090903479)
          ·
            refine ⟨147844574920792110136355219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98563049947194740090903479 147844574920792110136355219)
            ·
              refine ⟨221766862381188165204532829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 147844574920792110136355219 221766862381188165204532829)
              ·
                refine ⟨83162573392945561951699811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 221766862381188165204532829 83162573392945561951699811)
                ·
                  refine ⟨124743860089418342927549717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 83162573392945561951699811 124743860089418342927549717)
                  ·
                    refine ⟨5847368441691484824728893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 124743860089418342927549717 5847368441691484824728893)
                    ·
                      refine ⟨2192763165634306809273335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5847368441691484824728893 2192763165634306809273335)
                      ·
                        rfl

theorem cell23_4270391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 3, 1, 6, 3].length) (baseStart_4270391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4270391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4270391 prefixEnd_4270391 := by exact prefixLift 4270391
  have htrace : WordTrace (prefixWord ++ tailWord_4270391) baseStart_4270391 baseEnd_4270391 := by
    simpa [prefixWord, tailWord_4270391, baseEnd_4270391] using wordTrace_append hprefix tailTrace_4270391
  have hstable : (prefixWord ++ tailWord_4270391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4270391).length < 2 ^ (prefixWord ++ tailWord_4270391).sum := by decide
  have hdescent : baseEnd_4270391 < baseStart_4270391 := by decide
  rcases family_descends (prefixWord ++ tailWord_4270391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4270398 : List Nat := [4, 2, 1, 2, 1, 2, 2, 1, 2, 6]
def baseStart_4270398 : Nat := 118140960795 + 4270398 * 2 ^ 59
def prefixEnd_4270398 : Nat := 4983230072969 + 3 ^ 40 * 4270398 * 2
def baseEnd_4270398 : Nat := 730922253332962760628601

theorem tailTrace_4270398 : CollatzResearch.WordTrace tailWord_4270398 prefixEnd_4270398 730922253332962760628601 := by
  unfold tailWord_4270398
  simp only [CollatzResearch.WordTrace]
  refine ⟨19469276347885605844863481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 103836140522056564505938565 19469276347885605844863481)
  ·
    refine ⟨14601957260914204383647611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19469276347885605844863481 14601957260914204383647611)
    ·
      refine ⟨21902935891371306575471417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14601957260914204383647611 21902935891371306575471417)
      ·
        refine ⟨16427201918528479931603563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21902935891371306575471417 16427201918528479931603563)
        ·
          refine ⟨24640802877792719897405345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16427201918528479931603563 24640802877792719897405345)
          ·
            refine ⟨18480602158344539923054009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24640802877792719897405345 18480602158344539923054009)
            ·
              refine ⟨13860451618758404942290507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18480602158344539923054009 13860451618758404942290507)
              ·
                refine ⟨20790677428137607413435761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13860451618758404942290507 20790677428137607413435761)
                ·
                  refine ⟨15593008071103205560076821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20790677428137607413435761 15593008071103205560076821)
                  ·
                    refine ⟨730922253332962760628601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15593008071103205560076821 730922253332962760628601)
                    ·
                      rfl

theorem cell23_4270398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 1, 2, 6].length) (baseStart_4270398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4270398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4270398 prefixEnd_4270398 := by exact prefixLift 4270398
  have htrace : WordTrace (prefixWord ++ tailWord_4270398) baseStart_4270398 baseEnd_4270398 := by
    simpa [prefixWord, tailWord_4270398, baseEnd_4270398] using wordTrace_append hprefix tailTrace_4270398
  have hstable : (prefixWord ++ tailWord_4270398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4270398).length < 2 ^ (prefixWord ++ tailWord_4270398).sum := by decide
  have hdescent : baseEnd_4270398 < baseStart_4270398 := by decide
  rcases family_descends (prefixWord ++ tailWord_4270398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4270451 : List Nat := [1, 1, 1, 2, 2, 1, 2, 5, 1, 2, 5]
def baseStart_4270451 : Nat := 118140960795 + 4270451 * 2 ^ 59
def prefixEnd_4270451 : Nat := 4983230072969 + 3 ^ 40 * 4270451 * 2
def baseEnd_4270451 : Nat := 2192793974473576574523059

theorem tailTrace_4270451 : CollatzResearch.WordTrace tailWord_4270451 prefixEnd_4270451 2192793974473576574523059 := by
  unfold tailWord_4270451
  simp only [CollatzResearch.WordTrace]
  refine ⟨155756143851892836810587207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103837429234595224540391471 155756143851892836810587207)
  ·
    refine ⟨233634215777839255215880811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155756143851892836810587207 233634215777839255215880811)
    ·
      refine ⟨350451323666758882823821217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 233634215777839255215880811 350451323666758882823821217)
      ·
        refine ⟨262838492750069162117865913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 350451323666758882823821217 262838492750069162117865913)
        ·
          refine ⟨197128869562551871588399435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 262838492750069162117865913 197128869562551871588399435)
          ·
            refine ⟨295693304343827807382599153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 197128869562551871588399435 295693304343827807382599153)
            ·
              refine ⟨221769978257870855536949365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 295693304343827807382599153 221769978257870855536949365)
              ·
                refine ⟨20790935461675392706589003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 221769978257870855536949365 20790935461675392706589003)
                ·
                  refine ⟨31186403192513089059883505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20790935461675392706589003 31186403192513089059883505)
                  ·
                    refine ⟨23389802394384816794912629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31186403192513089059883505 23389802394384816794912629)
                    ·
                      refine ⟨2192793974473576574523059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23389802394384816794912629 2192793974473576574523059)
                      ·
                        rfl

theorem cell23_4270451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 5, 1, 2, 5].length) (baseStart_4270451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4270451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4270451 prefixEnd_4270451 := by exact prefixLift 4270451
  have htrace : WordTrace (prefixWord ++ tailWord_4270451) baseStart_4270451 baseEnd_4270451 := by
    simpa [prefixWord, tailWord_4270451, baseEnd_4270451] using wordTrace_append hprefix tailTrace_4270451
  have hstable : (prefixWord ++ tailWord_4270451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4270451).length < 2 ^ (prefixWord ++ tailWord_4270451).sum := by decide
  have hdescent : baseEnd_4270451 < baseStart_4270451 := by decide
  rcases family_descends (prefixWord ++ tailWord_4270451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4270481 : List Nat := [1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 5]
def baseStart_4270481 : Nat := 118140960795 + 4270481 * 2 ^ 59
def prefixEnd_4270481 : Nat := 4983230072969 + 3 ^ 40 * 4270481 * 2
def baseEnd_4270481 : Nat := 2192809378893211457147921

theorem tailTrace_4270481 : CollatzResearch.WordTrace tailWord_4270481 prefixEnd_4270481 2192809378893211457147921 := by
  unfold tailWord_4270481
  simp only [CollatzResearch.WordTrace]
  refine ⟨155757238041784151934179297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103838158694522767956119531 155757238041784151934179297)
  ·
    refine ⟨116817928531338113950634473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155757238041784151934179297 116817928531338113950634473)
    ·
      refine ⟨87613446398503585462975855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116817928531338113950634473 87613446398503585462975855)
      ·
        refine ⟨131420169597755378194463783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87613446398503585462975855 131420169597755378194463783)
        ·
          refine ⟨197130254396633067291695675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131420169597755378194463783 197130254396633067291695675)
          ·
            refine ⟨295695381594949600937543513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 197130254396633067291695675 295695381594949600937543513)
            ·
              refine ⟨221771536196212200703157635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 295695381594949600937543513 221771536196212200703157635)
              ·
                refine ⟨332657304294318301054736453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 221771536196212200703157635 332657304294318301054736453)
                ·
                  refine ⟨62373244555184681447763085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 332657304294318301054736453 62373244555184681447763085)
                  ·
                    refine ⟨23389966708194255542911157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 62373244555184681447763085 23389966708194255542911157)
                    ·
                      refine ⟨2192809378893211457147921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23389966708194255542911157 2192809378893211457147921)
                      ·
                        rfl

theorem cell23_4270481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 5].length) (baseStart_4270481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4270481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4270481 prefixEnd_4270481 := by exact prefixLift 4270481
  have htrace : WordTrace (prefixWord ++ tailWord_4270481) baseStart_4270481 baseEnd_4270481 := by
    simpa [prefixWord, tailWord_4270481, baseEnd_4270481] using wordTrace_append hprefix tailTrace_4270481
  have hstable : (prefixWord ++ tailWord_4270481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4270481).length < 2 ^ (prefixWord ++ tailWord_4270481).sum := by decide
  have hdescent : baseEnd_4270481 < baseStart_4270481 := by decide
  rcases family_descends (prefixWord ++ tailWord_4270481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4270495 : List Nat := [1, 1, 2, 5, 1, 1, 2, 2, 2, 4, 2]
def baseStart_4270495 : Nat := 118140960795 + 4270495 * 2 ^ 59
def prefixEnd_4270495 : Nat := 4983230072969 + 3 ^ 40 * 4270495 * 2
def baseEnd_4270495 : Nat := 2192816567622374402372857

theorem tailTrace_4270495 : CollatzResearch.WordTrace tailWord_4270495 prefixEnd_4270495 2192816567622374402372857 := by
  unfold tailWord_4270495
  simp only [CollatzResearch.WordTrace]
  refine ⟨155757748663733432325188939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103838499109155621550125959 155757748663733432325188939)
  ·
    refine ⟨233636622995600148487783409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155757748663733432325188939 233636622995600148487783409)
    ·
      refine ⟨175227467246700111365837557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 233636622995600148487783409 175227467246700111365837557)
      ·
        refine ⟨16427575054378135440547271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 175227467246700111365837557 16427575054378135440547271)
        ·
          refine ⟨24641362581567203160820907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16427575054378135440547271 24641362581567203160820907)
          ·
            refine ⟨36962043872350804741231361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24641362581567203160820907 36962043872350804741231361)
            ·
              refine ⟨27721532904263103555923521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36962043872350804741231361 27721532904263103555923521)
              ·
                refine ⟨20791149678197327666942641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27721532904263103555923521 20791149678197327666942641)
                ·
                  refine ⟨15593362258647995750206981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20791149678197327666942641 15593362258647995750206981)
                  ·
                    refine ⟨2923755423496499203163809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15593362258647995750206981 2923755423496499203163809)
                    ·
                      refine ⟨2192816567622374402372857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2923755423496499203163809 2192816567622374402372857)
                      ·
                        rfl

theorem cell23_4270495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 2, 2, 4, 2].length) (baseStart_4270495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4270495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4270495 prefixEnd_4270495 := by exact prefixLift 4270495
  have htrace : WordTrace (prefixWord ++ tailWord_4270495) baseStart_4270495 baseEnd_4270495 := by
    simpa [prefixWord, tailWord_4270495, baseEnd_4270495] using wordTrace_append hprefix tailTrace_4270495
  have hstable : (prefixWord ++ tailWord_4270495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4270495).length < 2 ^ (prefixWord ++ tailWord_4270495).sum := by decide
  have hdescent : baseEnd_4270495 < baseStart_4270495 := by decide
  rcases family_descends (prefixWord ++ tailWord_4270495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4270498 : List Nat := [3, 3, 1, 2, 1, 1, 1, 1, 2, 3, 5]
def baseStart_4270498 : Nat := 118140960795 + 4270498 * 2 ^ 59
def prefixEnd_4270498 : Nat := 4983230072969 + 3 ^ 40 * 4270498 * 2
def baseEnd_4270498 : Nat := 2192818108064337890635343

theorem tailTrace_4270498 : CollatzResearch.WordTrace tailWord_4270498 prefixEnd_4270498 2192818108064337890635343 := by
  unfold tailWord_4270498
  simp only [CollatzResearch.WordTrace]
  refine ⟨38939464520680640959387037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103838572055148375891698765 38939464520680640959387037)
  ·
    refine ⟨14602299195255240359770139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38939464520680640959387037 14602299195255240359770139)
    ·
      refine ⟨21903448792882860539655209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14602299195255240359770139 21903448792882860539655209)
      ·
        refine ⟨16427586594662145404741407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21903448792882860539655209 16427586594662145404741407)
        ·
          refine ⟨24641379891993218107112111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16427586594662145404741407 24641379891993218107112111)
          ·
            refine ⟨36962069837989827160668167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24641379891993218107112111 36962069837989827160668167)
            ·
              refine ⟨55443104756984740741002251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36962069837989827160668167 55443104756984740741002251)
              ·
                refine ⟨83164657135477111111503377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55443104756984740741002251 83164657135477111111503377)
                ·
                  refine ⟨62373492851607833333627533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 83164657135477111111503377 62373492851607833333627533)
                  ·
                    refine ⟨23390059819352937500110325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 62373492851607833333627533 23390059819352937500110325)
                    ·
                      refine ⟨2192818108064337890635343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23390059819352937500110325 2192818108064337890635343)
                      ·
                        rfl

theorem cell23_4270498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 1, 2, 3, 5].length) (baseStart_4270498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4270498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4270498 prefixEnd_4270498 := by exact prefixLift 4270498
  have htrace : WordTrace (prefixWord ++ tailWord_4270498) baseStart_4270498 baseEnd_4270498 := by
    simpa [prefixWord, tailWord_4270498, baseEnd_4270498] using wordTrace_append hprefix tailTrace_4270498
  have hstable : (prefixWord ++ tailWord_4270498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4270498).length < 2 ^ (prefixWord ++ tailWord_4270498).sum := by decide
  have hdescent : baseEnd_4270498 < baseStart_4270498 := by decide
  rcases family_descends (prefixWord ++ tailWord_4270498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4270529 : List Nat := [1, 2, 7, 1, 1, 1, 1, 1, 1, 3, 4]
def baseStart_4270529 : Nat := 118140960795 + 4270529 * 2 ^ 59
def prefixEnd_4270529 : Nat := 4983230072969 + 3 ^ 40 * 4270529 * 2
def baseEnd_4270529 : Nat := 2192834025964627269347701

theorem tailTrace_4270529 : CollatzResearch.WordTrace tailWord_4270529 prefixEnd_4270529 2192834025964627269347701 := by
  unfold tailWord_4270529
  simp only [CollatzResearch.WordTrace]
  refine ⟨155758988745610256131926641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103839325830406837421284427 155758988745610256131926641)
  ·
    refine ⟨116819241559207692098944981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155758988745610256131926641 116819241559207692098944981)
    ·
      refine ⟨2737950974043930283569023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 116819241559207692098944981 2737950974043930283569023)
      ·
        refine ⟨4106926461065895425353535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2737950974043930283569023 4106926461065895425353535)
        ·
          refine ⟨6160389691598843138030303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4106926461065895425353535 6160389691598843138030303)
          ·
            refine ⟨9240584537398264707045455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6160389691598843138030303 9240584537398264707045455)
            ·
              refine ⟨13860876806097397060568183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9240584537398264707045455 13860876806097397060568183)
              ·
                refine ⟨20791315209146095590852275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13860876806097397060568183 20791315209146095590852275)
                ·
                  refine ⟨31186972813719143386278413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20791315209146095590852275 31186972813719143386278413)
                  ·
                    refine ⟨11695114805144678769854405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 31186972813719143386278413 11695114805144678769854405)
                    ·
                      refine ⟨2192834025964627269347701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11695114805144678769854405 2192834025964627269347701)
                      ·
                        rfl

theorem cell23_4270529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_4270529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4270529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4270529 prefixEnd_4270529 := by exact prefixLift 4270529
  have htrace : WordTrace (prefixWord ++ tailWord_4270529) baseStart_4270529 baseEnd_4270529 := by
    simpa [prefixWord, tailWord_4270529, baseEnd_4270529] using wordTrace_append hprefix tailTrace_4270529
  have hstable : (prefixWord ++ tailWord_4270529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4270529).length < 2 ^ (prefixWord ++ tailWord_4270529).sum := by decide
  have hdescent : baseEnd_4270529 < baseStart_4270529 := by decide
  rcases family_descends (prefixWord ++ tailWord_4270529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4270532 : List Nat := [2, 3, 3, 2, 2, 1, 1, 1, 1, 4, 3]
def baseStart_4270532 : Nat := 118140960795 + 4270532 * 2 ^ 59
def prefixEnd_4270532 : Nat := 4983230072969 + 3 ^ 40 * 4270532 * 2
def baseEnd_4270532 : Nat := 2192835566406590757610187

theorem tailTrace_4270532 : CollatzResearch.WordTrace tailWord_4270532 prefixEnd_4270532 2192835566406590757610187 := by
  unfold tailWord_4270532
  simp only [CollatzResearch.WordTrace]
  refine ⟨77879549082299693822142925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103839398776399591762857233 77879549082299693822142925)
  ·
    refine ⟨29204830905862385183303597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77879549082299693822142925 29204830905862385183303597)
    ·
      refine ⟨10951811589698394443738849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29204830905862385183303597 10951811589698394443738849)
      ·
        refine ⟨8213858692273795832804137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10951811589698394443738849 8213858692273795832804137)
        ·
          refine ⟨6160394019205346874603103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8213858692273795832804137 6160394019205346874603103)
          ·
            refine ⟨9240591028808020311904655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6160394019205346874603103 9240591028808020311904655)
            ·
              refine ⟨13860886543212030467856983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9240591028808020311904655 13860886543212030467856983)
              ·
                refine ⟨20791329814818045701785475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13860886543212030467856983 20791329814818045701785475)
                ·
                  refine ⟨31186994722227068552678213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20791329814818045701785475 31186994722227068552678213)
                  ·
                    refine ⟨5847561510417575353627165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 31186994722227068552678213 5847561510417575353627165)
                    ·
                      refine ⟨2192835566406590757610187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5847561510417575353627165 2192835566406590757610187)
                      ·
                        rfl

theorem cell23_4270532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 1, 1, 4, 3].length) (baseStart_4270532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4270532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4270532 prefixEnd_4270532 := by exact prefixLift 4270532
  have htrace : WordTrace (prefixWord ++ tailWord_4270532) baseStart_4270532 baseEnd_4270532 := by
    simpa [prefixWord, tailWord_4270532, baseEnd_4270532] using wordTrace_append hprefix tailTrace_4270532
  have hstable : (prefixWord ++ tailWord_4270532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4270532).length < 2 ^ (prefixWord ++ tailWord_4270532).sum := by decide
  have hdescent : baseEnd_4270532 < baseStart_4270532 := by decide
  rcases family_descends (prefixWord ++ tailWord_4270532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4270582 : List Nat := [5, 1, 1, 1, 2, 1, 4, 2, 1, 5]
def baseStart_4270582 : Nat := 118140960795 + 4270582 * 2 ^ 59
def prefixEnd_4270582 : Nat := 4983230072969 + 3 ^ 40 * 4270582 * 2
def baseEnd_4270582 : Nat := 730953746813105187328319

theorem tailTrace_4270582 : CollatzResearch.WordTrace tailWord_4270582 prefixEnd_4270582 730953746813105187328319 := by
  unfold tailWord_4270582
  simp only [CollatzResearch.WordTrace]
  refine ⟨9735057613401140386475375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 103840614542945497455737333 9735057613401140386475375)
  ·
    refine ⟨14602586420101710579713063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9735057613401140386475375 14602586420101710579713063)
    ·
      refine ⟨21903879630152565869569595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14602586420101710579713063 21903879630152565869569595)
      ·
        refine ⟨32855819445228848804354393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21903879630152565869569595 32855819445228848804354393)
        ·
          refine ⟨24641864583921636603265795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32855819445228848804354393 24641864583921636603265795)
          ·
            refine ⟨36962796875882454904898693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24641864583921636603265795 36962796875882454904898693)
            ·
              refine ⟨6930524414227960294668505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36962796875882454904898693 6930524414227960294668505)
              ·
                refine ⟨5197893310670970221001379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6930524414227960294668505 5197893310670970221001379)
                ·
                  refine ⟨7796839966006455331502069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5197893310670970221001379 7796839966006455331502069)
                  ·
                    refine ⟨730953746813105187328319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7796839966006455331502069 730953746813105187328319)
                    ·
                      rfl

theorem cell23_4270582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 4, 2, 1, 5].length) (baseStart_4270582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4270582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4270582 prefixEnd_4270582 := by exact prefixLift 4270582
  have htrace : WordTrace (prefixWord ++ tailWord_4270582) baseStart_4270582 baseEnd_4270582 := by
    simpa [prefixWord, tailWord_4270582, baseEnd_4270582] using wordTrace_append hprefix tailTrace_4270582
  have hstable : (prefixWord ++ tailWord_4270582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4270582).length < 2 ^ (prefixWord ++ tailWord_4270582).sum := by decide
  have hdescent : baseEnd_4270582 < baseStart_4270582 := by decide
  rcases family_descends (prefixWord ++ tailWord_4270582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4270585 : List Nat := [1, 2, 1, 3, 1, 2, 3, 4, 1, 1, 4]
def baseStart_4270585 : Nat := 118140960795 + 4270585 * 2 ^ 59
def prefixEnd_4270585 : Nat := 4983230072969 + 3 ^ 40 * 4270585 * 2
def baseEnd_4270585 : Nat := 2192862780881279050247443

theorem tailTrace_4270585 : CollatzResearch.WordTrace tailWord_4270585 prefixEnd_4270585 2192862780881279050247443 := by
  unfold tailWord_4270585
  simp only [CollatzResearch.WordTrace]
  refine ⟨155761031233407377695965209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103840687488938251797310139 155761031233407377695965209)
  ·
    refine ⟨116820773425055533271973907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155761031233407377695965209 116820773425055533271973907)
    ·
      refine ⟨175231160137583299907960861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116820773425055533271973907 175231160137583299907960861)
      ·
        refine ⟨65711685051593737465485323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 175231160137583299907960861 65711685051593737465485323)
        ·
          refine ⟨98567527577390606198227985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65711685051593737465485323 98567527577390606198227985)
          ·
            refine ⟨73925645683042954648670989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98567527577390606198227985 73925645683042954648670989)
            ·
              refine ⟨27722117131141107993251621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 73925645683042954648670989 27722117131141107993251621)
              ·
                refine ⟨5197896962088957748734679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27722117131141107993251621 5197896962088957748734679)
                ·
                  refine ⟨7796845443133436623102019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5197896962088957748734679 7796845443133436623102019)
                  ·
                    refine ⟨11695268164700154934653029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7796845443133436623102019 11695268164700154934653029)
                    ·
                      refine ⟨2192862780881279050247443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11695268164700154934653029 2192862780881279050247443)
                      ·
                        rfl

theorem cell23_4270585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 4, 1, 1, 4].length) (baseStart_4270585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4270585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4270585 prefixEnd_4270585 := by exact prefixLift 4270585
  have htrace : WordTrace (prefixWord ++ tailWord_4270585) baseStart_4270585 baseEnd_4270585 := by
    simpa [prefixWord, tailWord_4270585, baseEnd_4270585] using wordTrace_append hprefix tailTrace_4270585
  have hstable : (prefixWord ++ tailWord_4270585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4270585).length < 2 ^ (prefixWord ++ tailWord_4270585).sum := by decide
  have hdescent : baseEnd_4270585 < baseStart_4270585 := by decide
  rcases family_descends (prefixWord ++ tailWord_4270585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4270588 : List Nat := [2, 2, 2, 1, 2, 1, 1, 1, 5, 1, 5]
def baseStart_4270588 : Nat := 118140960795 + 4270588 * 2 ^ 59
def prefixEnd_4270588 : Nat := 4983230072969 + 3 ^ 40 * 4270588 * 2
def baseEnd_4270588 : Nat := 2192864321323242538509929

theorem tailTrace_4270588 : CollatzResearch.WordTrace tailWord_4270588 prefixEnd_4270588 2192864321323242538509929 := by
  unfold tailWord_4270588
  simp only [CollatzResearch.WordTrace]
  refine ⟨77880570326198254604162209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103840760434931006138882945 77880570326198254604162209)
  ·
    refine ⟨58410427744648690953121657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77880570326198254604162209 58410427744648690953121657)
    ·
      refine ⟨43807820808486518214841243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58410427744648690953121657 43807820808486518214841243)
      ·
        refine ⟨65711731212729777322261865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43807820808486518214841243 65711731212729777322261865)
        ·
          refine ⟨49283798409547332991696399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65711731212729777322261865 49283798409547332991696399)
          ·
            refine ⟨73925697614320999487544599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49283798409547332991696399 73925697614320999487544599)
            ·
              refine ⟨110888546421481499231316899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73925697614320999487544599 110888546421481499231316899)
              ·
                refine ⟨166332819632222248846975349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 110888546421481499231316899 166332819632222248846975349)
                ·
                  refine ⟨15593701840520835829403939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 166332819632222248846975349 15593701840520835829403939)
                  ·
                    refine ⟨23390552760781253744105909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15593701840520835829403939 23390552760781253744105909)
                    ·
                      refine ⟨2192864321323242538509929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23390552760781253744105909 2192864321323242538509929)
                      ·
                        rfl

theorem cell23_4270588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 1, 5, 1, 5].length) (baseStart_4270588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4270588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4270588 prefixEnd_4270588 := by exact prefixLift 4270588
  have htrace : WordTrace (prefixWord ++ tailWord_4270588) baseStart_4270588 baseEnd_4270588 := by
    simpa [prefixWord, tailWord_4270588, baseEnd_4270588] using wordTrace_append hprefix tailTrace_4270588
  have hstable : (prefixWord ++ tailWord_4270588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4270588).length < 2 ^ (prefixWord ++ tailWord_4270588).sum := by decide
  have hdescent : baseEnd_4270588 < baseStart_4270588 := by decide
  rcases family_descends (prefixWord ++ tailWord_4270588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4270596 : List Nat := [2, 3, 2, 3, 1, 1, 3, 3, 1, 1, 3]
def baseStart_4270596 : Nat := 118140960795 + 4270596 * 2 ^ 59
def prefixEnd_4270596 : Nat := 4983230072969 + 3 ^ 40 * 4270596 * 2
def baseEnd_4270596 : Nat := 2192868429168478507209893

theorem tailTrace_4270596 : CollatzResearch.WordTrace tailWord_4270596 prefixEnd_4270596 2192868429168478507209893 := by
  unfold tailWord_4270596
  simp only [CollatzResearch.WordTrace]
  refine ⟨77880716218183763287307821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103840954957578351049743761 77880716218183763287307821)
  ·
    refine ⟨29205268581818911232740433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77880716218183763287307821 29205268581818911232740433)
    ·
      refine ⟨21903951436364183424555325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29205268581818911232740433 21903951436364183424555325)
      ·
        refine ⟨8213981788636568784208247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21903951436364183424555325 8213981788636568784208247)
        ·
          refine ⟨12320972682954853176312371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8213981788636568784208247 12320972682954853176312371)
          ·
            refine ⟨18481459024432279764468557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12320972682954853176312371 18481459024432279764468557)
            ·
              refine ⟨6930547134162104911675709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18481459024432279764468557 6930547134162104911675709)
              ·
                refine ⟨2598955175310789341878391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6930547134162104911675709 2598955175310789341878391)
                ·
                  refine ⟨3898432762966184012817587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2598955175310789341878391 3898432762966184012817587)
                  ·
                    refine ⟨5847649144449276019226381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3898432762966184012817587 5847649144449276019226381)
                    ·
                      refine ⟨2192868429168478507209893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5847649144449276019226381 2192868429168478507209893)
                      ·
                        rfl

theorem cell23_4270596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 3, 3, 1, 1, 3].length) (baseStart_4270596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4270596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4270596 prefixEnd_4270596 := by exact prefixLift 4270596
  have htrace : WordTrace (prefixWord ++ tailWord_4270596) baseStart_4270596 baseEnd_4270596 := by
    simpa [prefixWord, tailWord_4270596, baseEnd_4270596] using wordTrace_append hprefix tailTrace_4270596
  have hstable : (prefixWord ++ tailWord_4270596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4270596).length < 2 ^ (prefixWord ++ tailWord_4270596).sum := by decide
  have hdescent : baseEnd_4270596 < baseStart_4270596 := by decide
  rcases family_descends (prefixWord ++ tailWord_4270596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4270652 : List Nat := [2, 2, 2, 2, 3, 2, 1, 2, 1, 3, 3]
def baseStart_4270652 : Nat := 118140960795 + 4270652 * 2 ^ 59
def prefixEnd_4270652 : Nat := 4983230072969 + 3 ^ 40 * 4270652 * 2
def baseEnd_4270652 : Nat := 2192897184085130288109635

theorem tailTrace_4270652 : CollatzResearch.WordTrace tailWord_4270652 prefixEnd_4270652 2192897184085130288109635 := by
  unfold tailWord_4270652
  simp only [CollatzResearch.WordTrace]
  refine ⟨77881737462082324069327105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103842316616109765425769473 77881737462082324069327105)
  ·
    refine ⟨58411303096561743051995329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77881737462082324069327105 58411303096561743051995329)
    ·
      refine ⟨43808477322421307288996497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58411303096561743051995329 43808477322421307288996497)
      ·
        refine ⟨32856357991815980466747373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43808477322421307288996497 32856357991815980466747373)
        ·
          refine ⟨12321134246930992675030265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32856357991815980466747373 12321134246930992675030265)
          ·
            refine ⟨9240850685198244506272699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12321134246930992675030265 9240850685198244506272699)
            ·
              refine ⟨13861276027797366759409049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9240850685198244506272699 13861276027797366759409049)
              ·
                refine ⟨10395957020848025069556787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13861276027797366759409049 10395957020848025069556787)
                ·
                  refine ⟨15593935531272037604335181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10395957020848025069556787 15593935531272037604335181)
                  ·
                    refine ⟨5847725824227014101625693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15593935531272037604335181 5847725824227014101625693)
                    ·
                      refine ⟨2192897184085130288109635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5847725824227014101625693 2192897184085130288109635)
                      ·
                        rfl

theorem cell23_4270652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 2, 1, 3, 3].length) (baseStart_4270652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4270652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4270652 prefixEnd_4270652 := by exact prefixLift 4270652
  have htrace : WordTrace (prefixWord ++ tailWord_4270652) baseStart_4270652 baseEnd_4270652 := by
    simpa [prefixWord, tailWord_4270652, baseEnd_4270652] using wordTrace_append hprefix tailTrace_4270652
  have hstable : (prefixWord ++ tailWord_4270652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4270652).length < 2 ^ (prefixWord ++ tailWord_4270652).sum := by decide
  have hdescent : baseEnd_4270652 < baseStart_4270652 := by decide
  rcases family_descends (prefixWord ++ tailWord_4270652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4270675 : List Nat := [1, 1, 1, 2, 1, 1, 2, 1, 1, 10, 2]
def baseStart_4270675 : Nat := 118140960795 + 4270675 * 2 ^ 59
def prefixEnd_4270675 : Nat := 4983230072969 + 3 ^ 40 * 4270675 * 2
def baseEnd_4270675 : Nat := 2192908994140183698122029

theorem tailTrace_4270675 : CollatzResearch.WordTrace tailWord_4270675 prefixEnd_4270675 2192908994140183698122029 := by
  unfold tailWord_4270675
  simp only [CollatzResearch.WordTrace]
  refine ⟨155764313803081323066741479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103842875868720882044494319 155764313803081323066741479)
  ·
    refine ⟨233646470704621984600112219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155764313803081323066741479 233646470704621984600112219)
    ·
      refine ⟨350469706056932976900168329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 233646470704621984600112219 350469706056932976900168329)
      ·
        refine ⟨262852279542699732675126247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 350469706056932976900168329 262852279542699732675126247)
        ·
          refine ⟨394278419314049599012689371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 262852279542699732675126247 394278419314049599012689371)
          ·
            refine ⟨591417628971074398519034057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 394278419314049599012689371 591417628971074398519034057)
            ·
              refine ⟨443563221728305798889275543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 591417628971074398519034057 443563221728305798889275543)
              ·
                refine ⟨665344832592458698333913315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 443563221728305798889275543 665344832592458698333913315)
                ·
                  refine ⟨998017248888688047500869973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 665344832592458698333913315 998017248888688047500869973)
                  ·
                    refine ⟨2923878658853578264162705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 998017248888688047500869973 2923878658853578264162705)
                    ·
                      refine ⟨2192908994140183698122029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2923878658853578264162705 2192908994140183698122029)
                      ·
                        rfl

theorem cell23_4270675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 10, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 10, 2].length) (baseStart_4270675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4270675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4270675 prefixEnd_4270675 := by exact prefixLift 4270675
  have htrace : WordTrace (prefixWord ++ tailWord_4270675) baseStart_4270675 baseEnd_4270675 := by
    simpa [prefixWord, tailWord_4270675, baseEnd_4270675] using wordTrace_append hprefix tailTrace_4270675
  have hstable : (prefixWord ++ tailWord_4270675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4270675).length < 2 ^ (prefixWord ++ tailWord_4270675).sum := by decide
  have hdescent : baseEnd_4270675 < baseStart_4270675 := by decide
  rcases family_descends (prefixWord ++ tailWord_4270675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4270695 : List Nat := [1, 1, 5, 1, 1, 1, 1, 1, 4, 4, 3]
def baseStart_4270695 : Nat := 118140960795 + 4270695 * 2 ^ 59
def prefixEnd_4270695 : Nat := 4983230072969 + 3 ^ 40 * 4270695 * 2
def baseEnd_4270695 : Nat := 2192919263753273619871937

theorem tailTrace_4270695 : CollatzResearch.WordTrace tailWord_4270695 prefixEnd_4270695 2192919263753273619871937 := by
  unfold tailWord_4270695
  simp only [CollatzResearch.WordTrace]
  refine ⟨155765043263008866482469539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103843362175339244321646359 155765043263008866482469539)
  ·
    refine ⟨233647564894513299723704309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155765043263008866482469539 233647564894513299723704309)
    ·
      refine ⟨21904459208860621849097279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 233647564894513299723704309 21904459208860621849097279)
      ·
        refine ⟨32856688813290932773645919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21904459208860621849097279 32856688813290932773645919)
        ·
          refine ⟨49285033219936399160468879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32856688813290932773645919 49285033219936399160468879)
          ·
            refine ⟨73927549829904598740703319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49285033219936399160468879 73927549829904598740703319)
            ·
              refine ⟨110891324744856898111054979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73927549829904598740703319 110891324744856898111054979)
              ·
                refine ⟨166336987117285347166582469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 110891324744856898111054979 166336987117285347166582469)
                ·
                  refine ⟨31188185084491002593734213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 166336987117285347166582469 31188185084491002593734213)
                  ·
                    refine ⟨5847784703342062986325165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 31188185084491002593734213 5847784703342062986325165)
                    ·
                      refine ⟨2192919263753273619871937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5847784703342062986325165 2192919263753273619871937)
                      ·
                        rfl

theorem cell23_4270695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 4, 4, 3].length) (baseStart_4270695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4270695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4270695 prefixEnd_4270695 := by exact prefixLift 4270695
  have htrace : WordTrace (prefixWord ++ tailWord_4270695) baseStart_4270695 baseEnd_4270695 := by
    simpa [prefixWord, tailWord_4270695, baseEnd_4270695] using wordTrace_append hprefix tailTrace_4270695
  have hstable : (prefixWord ++ tailWord_4270695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4270695).length < 2 ^ (prefixWord ++ tailWord_4270695).sum := by decide
  have hdescent : baseEnd_4270695 < baseStart_4270695 := by decide
  rcases family_descends (prefixWord ++ tailWord_4270695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4270766 : List Nat := [4, 1, 4, 1, 1, 1, 3, 3, 5]
def baseStart_4270766 : Nat := 118140960795 + 4270766 * 2 ^ 59
def prefixEnd_4270766 : Nat := 4983230072969 + 3 ^ 40 * 4270766 * 2
def baseEnd_4270766 : Nat := 243661746764415871342679

theorem tailTrace_4270766 : CollatzResearch.WordTrace tailWord_4270766 prefixEnd_4270766 243661746764415871342679 := by
  unfold tailWord_4270766
  simp only [CollatzResearch.WordTrace]
  refine ⟨19470954105718955701038019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 103845088563834430405536101 19470954105718955701038019)
  ·
    refine ⟨29206431158578433551557029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19470954105718955701038019 29206431158578433551557029)
    ·
      refine ⟨5476205842233456290916943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29206431158578433551557029 5476205842233456290916943)
      ·
        refine ⟨8214308763350184436375415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5476205842233456290916943 8214308763350184436375415)
        ·
          refine ⟨12321463145025276654563123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8214308763350184436375415 12321463145025276654563123)
          ·
            refine ⟨18482194717537914981844685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12321463145025276654563123 18482194717537914981844685)
            ·
              refine ⟨6930823019076718118191757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18482194717537914981844685 6930823019076718118191757)
              ·
                refine ⟨2599058632153769294321909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6930823019076718118191757 2599058632153769294321909)
                ·
                  refine ⟨243661746764415871342679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2599058632153769294321909 243661746764415871342679)
                  ·
                    rfl

theorem cell23_4270766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 3, 3, 5].length) (baseStart_4270766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4270766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4270766 prefixEnd_4270766 := by exact prefixLift 4270766
  have htrace : WordTrace (prefixWord ++ tailWord_4270766) baseStart_4270766 baseEnd_4270766 := by
    simpa [prefixWord, tailWord_4270766, baseEnd_4270766] using wordTrace_append hprefix tailTrace_4270766
  have hstable : (prefixWord ++ tailWord_4270766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4270766).length < 2 ^ (prefixWord ++ tailWord_4270766).sum := by decide
  have hdescent : baseEnd_4270766 < baseStart_4270766 := by decide
  rcases family_descends (prefixWord ++ tailWord_4270766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4270819 : List Nat := [1, 1, 1, 7, 1, 1, 1, 3, 2, 2, 3]
def baseStart_4270819 : Nat := 118140960795 + 4270819 * 2 ^ 59
def prefixEnd_4270819 : Nat := 4983230072969 + 3 ^ 40 * 4270819 * 2
def baseEnd_4270819 : Nat := 2192982935354431134721367

theorem tailTrace_4270819 : CollatzResearch.WordTrace tailWord_4270819 prefixEnd_4270819 2192982935354431134721367 := by
  unfold tailWord_4270819
  simp only [CollatzResearch.WordTrace]
  refine ⟨155769565914559635659983511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103846377276373090439989007 155769565914559635659983511)
  ·
    refine ⟨233654348871839453489975267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155769565914559635659983511 233654348871839453489975267)
    ·
      refine ⟨350481523307759180234962901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 233654348871839453489975267 350481523307759180234962901)
      ·
        refine ⟨8214410702525605786756943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 350481523307759180234962901 8214410702525605786756943)
        ·
          refine ⟨12321616053788408680135415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8214410702525605786756943 12321616053788408680135415)
          ·
            refine ⟨18482424080682613020203123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12321616053788408680135415 18482424080682613020203123)
            ·
              refine ⟨27723636121023919530304685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18482424080682613020203123 27723636121023919530304685)
              ·
                refine ⟨10396363545383969823864257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27723636121023919530304685 10396363545383969823864257)
                ·
                  refine ⟨7797272659037977367898193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10396363545383969823864257 7797272659037977367898193)
                  ·
                    refine ⟨5847954494278483025923645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7797272659037977367898193 5847954494278483025923645)
                    ·
                      refine ⟨2192982935354431134721367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5847954494278483025923645 2192982935354431134721367)
                      ·
                        rfl

theorem cell23_4270819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 3, 2, 2, 3].length) (baseStart_4270819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4270819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4270819 prefixEnd_4270819 := by exact prefixLift 4270819
  have htrace : WordTrace (prefixWord ++ tailWord_4270819) baseStart_4270819 baseEnd_4270819 := by
    simpa [prefixWord, tailWord_4270819, baseEnd_4270819] using wordTrace_append hprefix tailTrace_4270819
  have hstable : (prefixWord ++ tailWord_4270819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4270819).length < 2 ^ (prefixWord ++ tailWord_4270819).sum := by decide
  have hdescent : baseEnd_4270819 < baseStart_4270819 := by decide
  rcases family_descends (prefixWord ++ tailWord_4270819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4270849 : List Nat := [1, 2, 4, 1, 1, 1, 1, 5, 3, 1, 3]
def baseStart_4270849 : Nat := 118140960795 + 4270849 * 2 ^ 59
def prefixEnd_4270849 : Nat := 4983230072969 + 3 ^ 40 * 4270849 * 2
def baseEnd_4270849 : Nat := 2192998339774066017346229

theorem tailTrace_4270849 : CollatzResearch.WordTrace tailWord_4270849 prefixEnd_4270849 2192998339774066017346229 := by
  unfold tailWord_4270849
  simp only [CollatzResearch.WordTrace]
  refine ⟨155770660104450950783575601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103847106736300633855717067 155770660104450950783575601)
  ·
    refine ⟨116827995078338213087681701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155770660104450950783575601 116827995078338213087681701)
    ·
      refine ⟨21905249077188414953940319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 116827995078338213087681701 21905249077188414953940319)
      ·
        refine ⟨32857873615782622430910479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21905249077188414953940319 32857873615782622430910479)
        ·
          refine ⟨49286810423673933646365719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32857873615782622430910479 49286810423673933646365719)
          ·
            refine ⟨73930215635510900469548579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49286810423673933646365719 73930215635510900469548579)
            ·
              refine ⟨110895323453266350704322869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73930215635510900469548579 110895323453266350704322869)
              ·
                refine ⟨10396436573743720378530269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 110895323453266350704322869 10396436573743720378530269)
                ·
                  refine ⟨3898663715153895141948851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10396436573743720378530269 3898663715153895141948851)
                  ·
                    refine ⟨5847995572730842712923277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3898663715153895141948851 5847995572730842712923277)
                    ·
                      refine ⟨2192998339774066017346229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5847995572730842712923277 2192998339774066017346229)
                      ·
                        rfl

theorem cell23_4270849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 5, 3, 1, 3].length) (baseStart_4270849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4270849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4270849 prefixEnd_4270849 := by exact prefixLift 4270849
  have htrace : WordTrace (prefixWord ++ tailWord_4270849) baseStart_4270849 baseEnd_4270849 := by
    simpa [prefixWord, tailWord_4270849, baseEnd_4270849] using wordTrace_append hprefix tailTrace_4270849
  have hstable : (prefixWord ++ tailWord_4270849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4270849).length < 2 ^ (prefixWord ++ tailWord_4270849).sum := by decide
  have hdescent : baseEnd_4270849 < baseStart_4270849 := by decide
  rcases family_descends (prefixWord ++ tailWord_4270849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4270852 : List Nat := [2, 3, 2, 2, 1, 1, 1, 1, 5, 5]
def baseStart_4270852 : Nat := 118140960795 + 4270852 * 2 ^ 59
def prefixEnd_4270852 : Nat := 4983230072969 + 3 ^ 40 * 4270852 * 2
def baseEnd_4270852 : Nat := 730999960072009835202905

theorem tailTrace_4270852 : CollatzResearch.WordTrace tailWord_4270852 prefixEnd_4270852 730999960072009835202905 := by
  unfold tailWord_4270852
  simp only [CollatzResearch.WordTrace]
  refine ⟨77885384761720041147967405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103847179682293388197289873 77885384761720041147967405)
  ·
    refine ⟨29207019285645015430487777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77885384761720041147967405 29207019285645015430487777)
    ·
      refine ⟨21905264464233761572865833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29207019285645015430487777 21905264464233761572865833)
      ·
        refine ⟨16428948348175321179649375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21905264464233761572865833 16428948348175321179649375)
        ·
          refine ⟨24643422522262981769474063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16428948348175321179649375 24643422522262981769474063)
          ·
            refine ⟨36965133783394472654211095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24643422522262981769474063 36965133783394472654211095)
            ·
              refine ⟨55447700675091708981316643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36965133783394472654211095 55447700675091708981316643)
              ·
                refine ⟨83171551012637563471974965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55447700675091708981316643 83171551012637563471974965)
                ·
                  refine ⟨7797332907434771575497653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 83171551012637563471974965 7797332907434771575497653)
                  ·
                    refine ⟨730999960072009835202905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7797332907434771575497653 730999960072009835202905)
                    ·
                      rfl

theorem cell23_4270852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 1, 5, 5].length) (baseStart_4270852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4270852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4270852 prefixEnd_4270852 := by exact prefixLift 4270852
  have htrace : WordTrace (prefixWord ++ tailWord_4270852) baseStart_4270852 baseEnd_4270852 := by
    simpa [prefixWord, tailWord_4270852, baseEnd_4270852] using wordTrace_append hprefix tailTrace_4270852
  have hstable : (prefixWord ++ tailWord_4270852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4270852).length < 2 ^ (prefixWord ++ tailWord_4270852).sum := by decide
  have hdescent : baseEnd_4270852 < baseStart_4270852 := by decide
  rcases family_descends (prefixWord ++ tailWord_4270852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4270875 : List Nat := [1, 1, 1, 1, 1, 1, 4, 1, 2, 5, 5]
def baseStart_4270875 : Nat := 118140960795 + 4270875 * 2 ^ 59
def prefixEnd_4270875 : Nat := 4983230072969 + 3 ^ 40 * 4270875 * 2
def baseEnd_4270875 : Nat := 2193011690271082915621109

theorem tailTrace_4270875 : CollatzResearch.WordTrace tailWord_4270875 prefixEnd_4270875 2193011690271082915621109 := by
  unfold tailWord_4270875
  simp only [CollatzResearch.WordTrace]
  refine ⟨155771608402356757224022079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103847738934904504816014719 155771608402356757224022079)
  ·
    refine ⟨233657412603535135836033119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155771608402356757224022079 233657412603535135836033119)
    ·
      refine ⟨350486118905302703754049679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 233657412603535135836033119 350486118905302703754049679)
      ·
        refine ⟨525729178357954055631074519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 350486118905302703754049679 525729178357954055631074519)
        ·
          refine ⟨788593767536931083446611779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 525729178357954055631074519 788593767536931083446611779)
          ·
            refine ⟨1182890651305396625169917669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 788593767536931083446611779 1182890651305396625169917669)
            ·
              refine ⟨221791997119761867219359563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1182890651305396625169917669 221791997119761867219359563)
              ·
                refine ⟨332687995679642800829039345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 221791997119761867219359563 332687995679642800829039345)
                ·
                  refine ⟨249515996759732100621779509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 332687995679642800829039345 249515996759732100621779509)
                  ·
                    refine ⟨23392124696224884433291829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 249515996759732100621779509 23392124696224884433291829)
                    ·
                      refine ⟨2193011690271082915621109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23392124696224884433291829 2193011690271082915621109)
                      ·
                        rfl

theorem cell23_4270875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 2, 5, 5].length) (baseStart_4270875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4270875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4270875 prefixEnd_4270875 := by exact prefixLift 4270875
  have htrace : WordTrace (prefixWord ++ tailWord_4270875) baseStart_4270875 baseEnd_4270875 := by
    simpa [prefixWord, tailWord_4270875, baseEnd_4270875] using wordTrace_append hprefix tailTrace_4270875
  have hstable : (prefixWord ++ tailWord_4270875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4270875).length < 2 ^ (prefixWord ++ tailWord_4270875).sum := by decide
  have hdescent : baseEnd_4270875 < baseStart_4270875 := by decide
  rcases family_descends (prefixWord ++ tailWord_4270875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4270876 : List Nat := [2, 2, 3, 1, 1, 3, 3, 1, 2, 3, 2]
def baseStart_4270876 : Nat := 118140960795 + 4270876 * 2 ^ 59
def prefixEnd_4270876 : Nat := 4983230072969 + 3 ^ 40 * 4270876 * 2
def baseEnd_4270876 : Nat := 2193012203751737411708605

theorem tailTrace_4270876 : CollatzResearch.WordTrace tailWord_4270876 prefixEnd_4270876 2193012203751737411708605 := by
  unfold tailWord_4270876
  simp only [CollatzResearch.WordTrace]
  refine ⟨77885822437676567197404241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103847763250235422929872321 77885822437676567197404241)
  ·
    refine ⟨58414366828257425398053181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77885822437676567197404241 58414366828257425398053181)
    ·
      refine ⟨21905387560596534524269943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58414366828257425398053181 21905387560596534524269943)
      ·
        refine ⟨32858081340894801786404915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21905387560596534524269943 32858081340894801786404915)
        ·
          refine ⟨49287122011342202679607373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32858081340894801786404915 49287122011342202679607373)
          ·
            refine ⟨18482670754253326004852765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49287122011342202679607373 18482670754253326004852765)
            ·
              refine ⟨6931001532844997251819787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18482670754253326004852765 6931001532844997251819787)
              ·
                refine ⟨10396502299267495877729681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6931001532844997251819787 10396502299267495877729681)
                ·
                  refine ⟨7797376724450621908297261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10396502299267495877729681 7797376724450621908297261)
                  ·
                    refine ⟨2924016271668983215611473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7797376724450621908297261 2924016271668983215611473)
                    ·
                      refine ⟨2193012203751737411708605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2924016271668983215611473 2193012203751737411708605)
                      ·
                        rfl

theorem cell23_4270876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 3, 1, 2, 3, 2].length) (baseStart_4270876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4270876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4270876 prefixEnd_4270876 := by exact prefixLift 4270876
  have htrace : WordTrace (prefixWord ++ tailWord_4270876) baseStart_4270876 baseEnd_4270876 := by
    simpa [prefixWord, tailWord_4270876, baseEnd_4270876] using wordTrace_append hprefix tailTrace_4270876
  have hstable : (prefixWord ++ tailWord_4270876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4270876).length < 2 ^ (prefixWord ++ tailWord_4270876).sum := by decide
  have hdescent : baseEnd_4270876 < baseStart_4270876 := by decide
  rcases family_descends (prefixWord ++ tailWord_4270876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4270892 : List Nat := [2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 5]
def baseStart_4270892 : Nat := 118140960795 + 4270892 * 2 ^ 59
def prefixEnd_4270892 : Nat := 4983230072969 + 3 ^ 40 * 4270892 * 2
def baseEnd_4270892 : Nat := 2193020419442209349108531

theorem tailTrace_4270892 : CollatzResearch.WordTrace tailWord_4270892 prefixEnd_4270892 2193020419442209349108531 := by
  unfold tailWord_4270892
  simp only [CollatzResearch.WordTrace]
  refine ⟨77886114221647584563695465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103848152295530112751593953 77886114221647584563695465)
  ·
    refine ⟨58414585666235688422771599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77886114221647584563695465 58414585666235688422771599)
    ·
      refine ⟨87621878499353532634157399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58414585666235688422771599 87621878499353532634157399)
      ·
        refine ⟨131432817749030298951236099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87621878499353532634157399 131432817749030298951236099)
        ·
          refine ⟨197149226623545448426854149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131432817749030298951236099 197149226623545448426854149)
          ·
            refine ⟨36965479991914771580035153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 197149226623545448426854149 36965479991914771580035153)
            ·
              refine ⟨27724109993936078685026365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36965479991914771580035153 27724109993936078685026365)
              ·
                refine ⟨10396541247726029506884887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27724109993936078685026365 10396541247726029506884887)
                ·
                  refine ⟨15594811871589044260327331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10396541247726029506884887 15594811871589044260327331)
                  ·
                    refine ⟨23392217807383566390490997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15594811871589044260327331 23392217807383566390490997)
                    ·
                      refine ⟨2193020419442209349108531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23392217807383566390490997 2193020419442209349108531)
                      ·
                        rfl

theorem cell23_4270892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 5].length) (baseStart_4270892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4270892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4270892 prefixEnd_4270892 := by exact prefixLift 4270892
  have htrace : WordTrace (prefixWord ++ tailWord_4270892) baseStart_4270892 baseEnd_4270892 := by
    simpa [prefixWord, tailWord_4270892, baseEnd_4270892] using wordTrace_append hprefix tailTrace_4270892
  have hstable : (prefixWord ++ tailWord_4270892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4270892).length < 2 ^ (prefixWord ++ tailWord_4270892).sum := by decide
  have hdescent : baseEnd_4270892 < baseStart_4270892 := by decide
  rcases family_descends (prefixWord ++ tailWord_4270892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4270899 : List Nat := [1, 1, 1, 2, 6, 2, 1, 1, 4, 4]
def baseStart_4270899 : Nat := 118140960795 + 4270899 * 2 ^ 59
def prefixEnd_4270899 : Nat := 4983230072969 + 3 ^ 40 * 4270899 * 2
def baseEnd_4270899 : Nat := 731008004602263607240333

theorem tailTrace_4270899 : CollatzResearch.WordTrace tailWord_4270899 prefixEnd_4270899 731008004602263607240333 := by
  unfold tailWord_4270899
  simp only [CollatzResearch.WordTrace]
  refine ⟨155772483754269809322895751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103848322502846539548597167 155772483754269809322895751)
  ·
    refine ⟨233658725631404713984343627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155772483754269809322895751 233658725631404713984343627)
    ·
      refine ⟨350488088447107070976515441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 233658725631404713984343627 350488088447107070976515441)
      ·
        refine ⟨262866066335330303232386581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 350488088447107070976515441 262866066335330303232386581)
        ·
          refine ⟨12321846859468607964018121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 262866066335330303232386581 12321846859468607964018121)
          ·
            refine ⟨9241385144601455973013591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12321846859468607964018121 9241385144601455973013591)
            ·
              refine ⟨13862077716902183959520387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9241385144601455973013591 13862077716902183959520387)
              ·
                refine ⟨20793116575353275939280581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13862077716902183959520387 20793116575353275939280581)
                ·
                  refine ⟨3898709357878739238615109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20793116575353275939280581 3898709357878739238615109)
                  ·
                    refine ⟨731008004602263607240333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3898709357878739238615109 731008004602263607240333)
                    ·
                      rfl

theorem cell23_4270899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 1, 4, 4].length) (baseStart_4270899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4270899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4270899 prefixEnd_4270899 := by exact prefixLift 4270899
  have htrace : WordTrace (prefixWord ++ tailWord_4270899) baseStart_4270899 baseEnd_4270899 := by
    simpa [prefixWord, tailWord_4270899, baseEnd_4270899] using wordTrace_append hprefix tailTrace_4270899
  have hstable : (prefixWord ++ tailWord_4270899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4270899).length < 2 ^ (prefixWord ++ tailWord_4270899).sum := by decide
  have hdescent : baseEnd_4270899 < baseStart_4270899 := by decide
  rcases family_descends (prefixWord ++ tailWord_4270899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4270946 : List Nat := [3, 3, 2, 1, 4, 1, 9]
def baseStart_4270946 : Nat := 118140960795 + 4270946 * 2 ^ 59
def prefixEnd_4270946 : Nat := 4983230072969 + 3 ^ 40 * 4270946 * 2
def baseEnd_4270946 : Nat := 27074668486389532565843

theorem tailTrace_4270946 : CollatzResearch.WordTrace tailWord_4270946 prefixEnd_4270946 27074668486389532565843 := by
  unfold tailWord_4270946
  simp only [CollatzResearch.WordTrace]
  refine ⟨38943549496274884087464173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103849465323399690899904461 38943549496274884087464173)
  ·
    refine ⟨14603831061103081532799065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38943549496274884087464173 14603831061103081532799065)
    ·
      refine ⟨10952873295827311149599299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14603831061103081532799065 10952873295827311149599299)
      ·
        refine ⟨16429309943740966724398949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10952873295827311149599299 16429309943740966724398949)
        ·
          refine ⟨3080495614451431260824803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16429309943740966724398949 3080495614451431260824803)
          ·
            refine ⟨4620743421677146891237205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3080495614451431260824803 4620743421677146891237205)
            ·
              refine ⟨27074668486389532565843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4620743421677146891237205 27074668486389532565843)
              ·
                rfl

theorem cell23_4270946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 9].length) (baseStart_4270946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4270946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4270946 prefixEnd_4270946 := by exact prefixLift 4270946
  have htrace : WordTrace (prefixWord ++ tailWord_4270946) baseStart_4270946 baseEnd_4270946 := by
    simpa [prefixWord, tailWord_4270946, baseEnd_4270946] using wordTrace_append hprefix tailTrace_4270946
  have hstable : (prefixWord ++ tailWord_4270946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4270946).length < 2 ^ (prefixWord ++ tailWord_4270946).sum := by decide
  have hdescent : baseEnd_4270946 < baseStart_4270946 := by decide
  rcases family_descends (prefixWord ++ tailWord_4270946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4270956 : List Nat := [2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 3]
def baseStart_4270956 : Nat := 118140960795 + 4270956 * 2 ^ 59
def prefixEnd_4270956 : Nat := 4983230072969 + 3 ^ 40 * 4270956 * 2
def baseEnd_4270956 : Nat := 2193053282204097098708237

theorem tailTrace_4270956 : CollatzResearch.WordTrace tailWord_4270956 prefixEnd_4270956 2193053282204097098708237 := by
  unfold tailWord_4270956
  simp only [CollatzResearch.WordTrace]
  refine ⟨77887281357531654028860361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103849708476708872038480481 77887281357531654028860361)
  ·
    refine ⟨58415461018148740521645271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77887281357531654028860361 58415461018148740521645271)
    ·
      refine ⟨87623191527223110782467907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58415461018148740521645271 87623191527223110782467907)
      ·
        refine ⟨131434787290834666173701861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87623191527223110782467907 131434787290834666173701861)
        ·
          refine ⟨24644022617031499907569099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 131434787290834666173701861 24644022617031499907569099)
          ·
            refine ⟨36966033925547249861353649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24644022617031499907569099 36966033925547249861353649)
            ·
              refine ⟨27724525444160437396015237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36966033925547249861353649 27724525444160437396015237)
              ·
                refine ⟨5198348520780082011752857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27724525444160437396015237 5198348520780082011752857)
                ·
                  refine ⟨3898761390585061508814643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5198348520780082011752857 3898761390585061508814643)
                  ·
                    refine ⟨5848142085877592263221965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3898761390585061508814643 5848142085877592263221965)
                    ·
                      refine ⟨2193053282204097098708237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5848142085877592263221965 2193053282204097098708237)
                      ·
                        rfl

theorem cell23_4270956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 3].length) (baseStart_4270956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4270956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4270956 prefixEnd_4270956 := by exact prefixLift 4270956
  have htrace : WordTrace (prefixWord ++ tailWord_4270956) baseStart_4270956 baseEnd_4270956 := by
    simpa [prefixWord, tailWord_4270956, baseEnd_4270956] using wordTrace_append hprefix tailTrace_4270956
  have hstable : (prefixWord ++ tailWord_4270956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4270956).length < 2 ^ (prefixWord ++ tailWord_4270956).sum := by decide
  have hdescent : baseEnd_4270956 < baseStart_4270956 := by decide
  rcases family_descends (prefixWord ++ tailWord_4270956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4270972 : List Nat := [2, 2, 2, 1, 1, 1, 1, 5, 2, 6]
def baseStart_4270972 : Nat := 118140960795 + 4270972 * 2 ^ 59
def prefixEnd_4270972 : Nat := 4983230072969 + 3 ^ 40 * 4270972 * 2
def baseEnd_4270972 : Nat := 731020499298189678702721

theorem tailTrace_4270972 : CollatzResearch.WordTrace tailWord_4270972 prefixEnd_4270972 731020499298189678702721 := by
  unfold tailWord_4270972
  simp only [CollatzResearch.WordTrace]
  refine ⟨77887573141502671395151585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103850097522003561860202113 77887573141502671395151585)
  ·
    refine ⟨58415679856127003546363689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77887573141502671395151585 58415679856127003546363689)
    ·
      refine ⟨43811759892095252659772767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58415679856127003546363689 43811759892095252659772767)
      ·
        refine ⟨65717639838142878989659151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43811759892095252659772767 65717639838142878989659151)
        ·
          refine ⟨98576459757214318484488727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65717639838142878989659151 98576459757214318484488727)
          ·
            refine ⟨147864689635821477726733091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98576459757214318484488727 147864689635821477726733091)
            ·
              refine ⟨221797034453732216590099637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 147864689635821477726733091 221797034453732216590099637)
              ·
                refine ⟨20793471980037395305321841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 221797034453732216590099637 20793471980037395305321841)
                ·
                  refine ⟨15595103985028046478991381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20793471980037395305321841 15595103985028046478991381)
                  ·
                    refine ⟨731020499298189678702721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15595103985028046478991381 731020499298189678702721)
                    ·
                      rfl

theorem cell23_4270972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 5, 2, 6].length) (baseStart_4270972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4270972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4270972 prefixEnd_4270972 := by exact prefixLift 4270972
  have htrace : WordTrace (prefixWord ++ tailWord_4270972) baseStart_4270972 baseEnd_4270972 := by
    simpa [prefixWord, tailWord_4270972, baseEnd_4270972] using wordTrace_append hprefix tailTrace_4270972
  have hstable : (prefixWord ++ tailWord_4270972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4270972).length < 2 ^ (prefixWord ++ tailWord_4270972).sum := by decide
  have hdescent : baseEnd_4270972 < baseStart_4270972 := by decide
  rcases family_descends (prefixWord ++ tailWord_4270972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4270973 : List Nat := [1, 4, 1, 1, 2, 1, 6, 1, 2, 1, 3]
def baseStart_4270973 : Nat := 118140960795 + 4270973 * 2 ^ 59
def prefixEnd_4270973 : Nat := 4983230072969 + 3 ^ 40 * 4270973 * 2
def baseEnd_4270973 : Nat := 2193062011375223532195659

theorem tailTrace_4270973 : CollatzResearch.WordTrace tailWord_4270973 prefixEnd_4270973 2193062011375223532195659 := by
  unfold tailWord_4270973
  simp only [CollatzResearch.WordTrace]
  refine ⟨155775182756001719961089573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103850121837334479974059715 155775182756001719961089573)
  ·
    refine ⟨29207846766750322492704295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 155775182756001719961089573 29207846766750322492704295)
    ·
      refine ⟨43811770150125483739056443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29207846766750322492704295 43811770150125483739056443)
      ·
        refine ⟨65717655225188225608584665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43811770150125483739056443 65717655225188225608584665)
        ·
          refine ⟨49288241418891169206438499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65717655225188225608584665 49288241418891169206438499)
          ·
            refine ⟨73932362128336753809657749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49288241418891169206438499 73932362128336753809657749)
            ·
              refine ⟨3465579474765785334827707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 73932362128336753809657749 3465579474765785334827707)
              ·
                refine ⟨5198369212148678002241561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3465579474765785334827707 5198369212148678002241561)
                ·
                  refine ⟨3898776909111508501681171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5198369212148678002241561 3898776909111508501681171)
                  ·
                    refine ⟨5848165363667262752521757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3898776909111508501681171 5848165363667262752521757)
                    ·
                      refine ⟨2193062011375223532195659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5848165363667262752521757 2193062011375223532195659)
                      ·
                        rfl

theorem cell23_4270973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 6, 1, 2, 1, 3].length) (baseStart_4270973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4270973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4270973 prefixEnd_4270973 := by exact prefixLift 4270973
  have htrace : WordTrace (prefixWord ++ tailWord_4270973) baseStart_4270973 baseEnd_4270973 := by
    simpa [prefixWord, tailWord_4270973, baseEnd_4270973] using wordTrace_append hprefix tailTrace_4270973
  have hstable : (prefixWord ++ tailWord_4270973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4270973).length < 2 ^ (prefixWord ++ tailWord_4270973).sum := by decide
  have hdescent : baseEnd_4270973 < baseStart_4270973 := by decide
  rcases family_descends (prefixWord ++ tailWord_4270973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4270983 : List Nat := [1, 1, 4, 2, 3, 1, 3, 2, 1, 3, 2]
def baseStart_4270983 : Nat := 118140960795 + 4270983 * 2 ^ 59
def prefixEnd_4270983 : Nat := 4983230072969 + 3 ^ 40 * 4270983 * 2
def baseEnd_4270983 : Nat := 2193067146181768493070613

theorem tailTrace_4270983 : CollatzResearch.WordTrace tailWord_4270983 prefixEnd_4270983 2193067146181768493070613 := by
  unfold tailWord_4270983
  simp only [CollatzResearch.WordTrace]
  refine ⟨155775547485965491668953603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103850364990643661112635735 155775547485965491668953603)
  ·
    refine ⟨233663321228948237503430405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155775547485965491668953603 233663321228948237503430405)
    ·
      refine ⟨43811872730427794531893201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 233663321228948237503430405 43811872730427794531893201)
      ·
        refine ⟨32858904547820845898919901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43811872730427794531893201 32858904547820845898919901)
        ·
          refine ⟨12322089205432817212094963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32858904547820845898919901 12322089205432817212094963)
          ·
            refine ⟨18483133808149225818142445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12322089205432817212094963 18483133808149225818142445)
            ·
              refine ⟨6931175178055959681803417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18483133808149225818142445 6931175178055959681803417)
              ·
                refine ⟨5198381383541969761352563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6931175178055959681803417 5198381383541969761352563)
                ·
                  refine ⟨7797572075312954642028845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5198381383541969761352563 7797572075312954642028845)
                  ·
                    refine ⟨2924089528242357990760817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7797572075312954642028845 2924089528242357990760817)
                    ·
                      refine ⟨2193067146181768493070613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2924089528242357990760817 2193067146181768493070613)
                      ·
                        rfl

theorem cell23_4270983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 3, 2, 1, 3, 2].length) (baseStart_4270983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4270983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4270983 prefixEnd_4270983 := by exact prefixLift 4270983
  have htrace : WordTrace (prefixWord ++ tailWord_4270983) baseStart_4270983 baseEnd_4270983 := by
    simpa [prefixWord, tailWord_4270983, baseEnd_4270983] using wordTrace_append hprefix tailTrace_4270983
  have hstable : (prefixWord ++ tailWord_4270983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4270983).length < 2 ^ (prefixWord ++ tailWord_4270983).sum := by decide
  have hdescent : baseEnd_4270983 < baseStart_4270983 := by decide
  rcases family_descends (prefixWord ++ tailWord_4270983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4271019 : List Nat := [1, 1, 1, 1, 2, 1, 1, 10, 5]
def baseStart_4271019 : Nat := 118140960795 + 4271019 * 2 ^ 59
def prefixEnd_4271019 : Nat := 4983230072969 + 3 ^ 40 * 4271019 * 2
def baseEnd_4271019 : Nat := 243676181276147816913383

theorem tailTrace_4271019 : CollatzResearch.WordTrace tailWord_4271019 prefixEnd_4271019 243676181276147816913383 := by
  unfold tailWord_4271019
  simp only [CollatzResearch.WordTrace]
  refine ⟨155776860513835069817264111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103851240342556713211509407 155776860513835069817264111)
  ·
    refine ⟨233665290770752604725896167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155776860513835069817264111 233665290770752604725896167)
    ·
      refine ⟨350497936156128907088844251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 233665290770752604725896167 350497936156128907088844251)
      ·
        refine ⟨525746904234193360633266377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 350497936156128907088844251 525746904234193360633266377)
        ·
          refine ⟨394310178175645020474949783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 525746904234193360633266377 394310178175645020474949783)
          ·
            refine ⟨591465267263467530712424675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 394310178175645020474949783 591465267263467530712424675)
            ·
              refine ⟨887197900895201296068637013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 591465267263467530712424675 887197900895201296068637013)
              ·
                refine ⟨2599212600278910047076085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 887197900895201296068637013 2599212600278910047076085)
                ·
                  refine ⟨243676181276147816913383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2599212600278910047076085 243676181276147816913383)
                  ·
                    rfl

theorem cell23_4271019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 10, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 10, 5].length) (baseStart_4271019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4271019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4271019 prefixEnd_4271019 := by exact prefixLift 4271019
  have htrace : WordTrace (prefixWord ++ tailWord_4271019) baseStart_4271019 baseEnd_4271019 := by
    simpa [prefixWord, tailWord_4271019, baseEnd_4271019] using wordTrace_append hprefix tailTrace_4271019
  have hstable : (prefixWord ++ tailWord_4271019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4271019).length < 2 ^ (prefixWord ++ tailWord_4271019).sum := by decide
  have hdescent : baseEnd_4271019 < baseStart_4271019 := by decide
  rcases family_descends (prefixWord ++ tailWord_4271019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4271130 : List Nat := [3, 1, 1, 3, 1, 2, 5, 2, 1, 4]
def baseStart_4271130 : Nat := 118140960795 + 4271130 * 2 ^ 59
def prefixEnd_4271130 : Nat := 4983230072969 + 3 ^ 40 * 4271130 * 2
def baseEnd_4271130 : Nat := 731047542612659805977479

theorem tailTrace_4271130 : CollatzResearch.WordTrace tailWord_4271130 prefixEnd_4271130 731047542612659805977479 := by
  unfold tailWord_4271130
  simp only [CollatzResearch.WordTrace]
  refine ⟨38945227254108233943638711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103853939344288623849703229 38945227254108233943638711)
  ·
    refine ⟨58417840881162350915458067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38945227254108233943638711 58417840881162350915458067)
    ·
      refine ⟨87626761321743526373187101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58417840881162350915458067 87626761321743526373187101)
      ·
        refine ⟨32860035495653822389945163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87626761321743526373187101 32860035495653822389945163)
        ·
          refine ⟨49290053243480733584917745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32860035495653822389945163 49290053243480733584917745)
          ·
            refine ⟨36967539932610550188688309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49290053243480733584917745 36967539932610550188688309)
            ·
              refine ⟨3465706868682239080189529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36967539932610550188688309 3465706868682239080189529)
              ·
                refine ⟨2599280151511679310142147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3465706868682239080189529 2599280151511679310142147)
                ·
                  refine ⟨3898920227267518965213221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2599280151511679310142147 3898920227267518965213221)
                  ·
                    refine ⟨731047542612659805977479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3898920227267518965213221 731047542612659805977479)
                    ·
                      rfl

theorem cell23_4271130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 5, 2, 1, 4].length) (baseStart_4271130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4271130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4271130 prefixEnd_4271130 := by exact prefixLift 4271130
  have htrace : WordTrace (prefixWord ++ tailWord_4271130) baseStart_4271130 baseEnd_4271130 := by
    simpa [prefixWord, tailWord_4271130, baseEnd_4271130] using wordTrace_append hprefix tailTrace_4271130
  have hstable : (prefixWord ++ tailWord_4271130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4271130).length < 2 ^ (prefixWord ++ tailWord_4271130).sum := by decide
  have hdescent : baseEnd_4271130 < baseStart_4271130 := by decide
  rcases family_descends (prefixWord ++ tailWord_4271130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4271143 : List Nat := [1, 1, 7, 1, 1, 2, 1, 3, 6]
def baseStart_4271143 : Nat := 118140960795 + 4271143 * 2 ^ 59
def prefixEnd_4271143 : Nat := 4983230072969 + 3 ^ 40 * 4271143 * 2
def baseEnd_4271143 : Nat := 243683255898498651896653

theorem tailTrace_4271143 : CollatzResearch.WordTrace tailWord_4271143 prefixEnd_4271143 243683255898498651896653 := by
  unfold tailWord_4271143
  simp only [CollatzResearch.WordTrace]
  refine ⟨155781383165385838994778083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103854255443590559329852055 155781383165385838994778083)
  ·
    refine ⟨233672074748078758492167125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155781383165385838994778083 233672074748078758492167125)
    ·
      refine ⟨5476689251908095902160167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 233672074748078758492167125 5476689251908095902160167)
      ·
        refine ⟨8215033877862143853240251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5476689251908095902160167 8215033877862143853240251)
        ·
          refine ⟨12322550816793215779860377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8215033877862143853240251 12322550816793215779860377)
          ·
            refine ⟨9241913112594911834895283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12322550816793215779860377 9241913112594911834895283)
            ·
              refine ⟨13862869668892367752342925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9241913112594911834895283 13862869668892367752342925)
              ·
                refine ⟨5198576125834637907128597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13862869668892367752342925 5198576125834637907128597)
                ·
                  refine ⟨243683255898498651896653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5198576125834637907128597 243683255898498651896653)
                  ·
                    rfl

theorem cell23_4271143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 3, 6].length) (baseStart_4271143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4271143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4271143 prefixEnd_4271143 := by exact prefixLift 4271143
  have htrace : WordTrace (prefixWord ++ tailWord_4271143) baseStart_4271143 baseEnd_4271143 := by
    simpa [prefixWord, tailWord_4271143, baseEnd_4271143] using wordTrace_append hprefix tailTrace_4271143
  have hstable : (prefixWord ++ tailWord_4271143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4271143).length < 2 ^ (prefixWord ++ tailWord_4271143).sum := by decide
  have hdescent : baseEnd_4271143 < baseStart_4271143 := by decide
  rcases family_descends (prefixWord ++ tailWord_4271143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4271196 : List Nat := [2, 2, 4, 1, 1, 1, 2, 1, 3, 1, 5]
def baseStart_4271196 : Nat := 118140960795 + 4271196 * 2 ^ 59
def prefixEnd_4271196 : Nat := 4983230072969 + 3 ^ 40 * 4271196 * 2
def baseEnd_4271196 : Nat := 2193176517561176159707133

theorem tailTrace_4271196 : CollatzResearch.WordTrace tailWord_4271196 prefixEnd_4271196 2193176517561176159707133 := by
  unfold tailWord_4271196
  simp only [CollatzResearch.WordTrace]
  refine ⟨77891658117096914523228721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103855544156129219364304961 77891658117096914523228721)
  ·
    refine ⟨58418743587822685892421541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77891658117096914523228721 58418743587822685892421541)
    ·
      refine ⟨10953514422716753604829039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58418743587822685892421541 10953514422716753604829039)
      ·
        refine ⟨16430271634075130407243559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10953514422716753604829039 16430271634075130407243559)
        ·
          refine ⟨24645407451112695610865339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16430271634075130407243559 24645407451112695610865339)
          ·
            refine ⟨36968111176669043416298009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24645407451112695610865339 36968111176669043416298009)
            ·
              refine ⟨27726083382501782562223507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36968111176669043416298009 27726083382501782562223507)
              ·
                refine ⟨41589125073752673843335261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27726083382501782562223507 41589125073752673843335261)
                ·
                  refine ⟨15595921902657252691250723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41589125073752673843335261 15595921902657252691250723)
                  ·
                    refine ⟨23393882853985879036876085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15595921902657252691250723 23393882853985879036876085)
                    ·
                      refine ⟨2193176517561176159707133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23393882853985879036876085 2193176517561176159707133)
                      ·
                        rfl

theorem cell23_4271196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 1, 3, 1, 5].length) (baseStart_4271196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4271196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4271196 prefixEnd_4271196 := by exact prefixLift 4271196
  have htrace : WordTrace (prefixWord ++ tailWord_4271196) baseStart_4271196 baseEnd_4271196 := by
    simpa [prefixWord, tailWord_4271196, baseEnd_4271196] using wordTrace_append hprefix tailTrace_4271196
  have hstable : (prefixWord ++ tailWord_4271196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4271196).length < 2 ^ (prefixWord ++ tailWord_4271196).sum := by decide
  have hdescent : baseEnd_4271196 < baseStart_4271196 := by decide
  rcases family_descends (prefixWord ++ tailWord_4271196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4271210 : List Nat := [3, 1, 3, 2, 2, 1, 1, 1, 5, 2, 2]
def baseStart_4271210 : Nat := 118140960795 + 4271210 * 2 ^ 59
def prefixEnd_4271210 : Nat := 4983230072969 + 3 ^ 40 * 4271210 * 2
def baseEnd_4271210 : Nat := 2193183706290339104932069

theorem tailTrace_4271210 : CollatzResearch.WordTrace tailWord_4271210 prefixEnd_4271210 2193183706290339104932069 := by
  unfold tailWord_4271210
  simp only [CollatzResearch.WordTrace]
  refine ⟨38945956714035777359366771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103855884570762072958311389 38945956714035777359366771)
  ·
    refine ⟨58418935071053666039050157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38945956714035777359366771 58418935071053666039050157)
    ·
      refine ⟨21907100651645124764643809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58418935071053666039050157 21907100651645124764643809)
      ·
        refine ⟨16430325488733843573482857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21907100651645124764643809 16430325488733843573482857)
        ·
          refine ⟨12322744116550382680112143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16430325488733843573482857 12322744116550382680112143)
          ·
            refine ⟨18484116174825574020168215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12322744116550382680112143 18484116174825574020168215)
            ·
              refine ⟨27726174262238361030252323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18484116174825574020168215 27726174262238361030252323)
              ·
                refine ⟨41589261393357541545378485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27726174262238361030252323 41589261393357541545378485)
                ·
                  refine ⟨3898993255627269519879233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 41589261393357541545378485 3898993255627269519879233)
                  ·
                    refine ⟨2924244941720452139909425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3898993255627269519879233 2924244941720452139909425)
                    ·
                      refine ⟨2193183706290339104932069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2924244941720452139909425 2193183706290339104932069)
                      ·
                        rfl

theorem cell23_4271210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 1, 5, 2, 2].length) (baseStart_4271210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4271210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4271210 prefixEnd_4271210 := by exact prefixLift 4271210
  have htrace : WordTrace (prefixWord ++ tailWord_4271210) baseStart_4271210 baseEnd_4271210 := by
    simpa [prefixWord, tailWord_4271210, baseEnd_4271210] using wordTrace_append hprefix tailTrace_4271210
  have hstable : (prefixWord ++ tailWord_4271210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4271210).length < 2 ^ (prefixWord ++ tailWord_4271210).sum := by decide
  have hdescent : baseEnd_4271210 < baseStart_4271210 := by decide
  rcases family_descends (prefixWord ++ tailWord_4271210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4271213 : List Nat := [1, 5, 1, 1, 2, 2, 2, 1, 3, 2, 3]
def baseStart_4271213 : Nat := 118140960795 + 4271213 * 2 ^ 59
def prefixEnd_4271213 : Nat := 4983230072969 + 3 ^ 40 * 4271213 * 2
def baseEnd_4271213 : Nat := 2193185246732302593194555

theorem tailTrace_4271213 : CollatzResearch.WordTrace tailWord_4271213 prefixEnd_4271213 2193185246732302593194555 := by
  unfold tailWord_4271213
  simp only [CollatzResearch.WordTrace]
  refine ⟨155783936275132240949826293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103855957516754827299884195 155783936275132240949826293)
  ·
    refine ⟨14604744025793647589046215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 155783936275132240949826293 14604744025793647589046215)
    ·
      refine ⟨21907116038690471383569323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14604744025793647589046215 21907116038690471383569323)
      ·
        refine ⟨32860674058035707075353985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21907116038690471383569323 32860674058035707075353985)
        ·
          refine ⟨24645505543526780306515489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32860674058035707075353985 24645505543526780306515489)
          ·
            refine ⟨18484129157645085229886617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24645505543526780306515489 18484129157645085229886617)
            ·
              refine ⟨13863096868233813922414963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18484129157645085229886617 13863096868233813922414963)
              ·
                refine ⟨20794645302350720883622445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13863096868233813922414963 20794645302350720883622445)
                ·
                  refine ⟨7797991988381520331358417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20794645302350720883622445 7797991988381520331358417)
                  ·
                    refine ⟨5848493991286140248518813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7797991988381520331358417 5848493991286140248518813)
                    ·
                      refine ⟨2193185246732302593194555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5848493991286140248518813 2193185246732302593194555)
                      ·
                        rfl

theorem cell23_4271213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 1, 3, 2, 3].length) (baseStart_4271213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4271213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4271213 prefixEnd_4271213 := by exact prefixLift 4271213
  have htrace : WordTrace (prefixWord ++ tailWord_4271213) baseStart_4271213 baseEnd_4271213 := by
    simpa [prefixWord, tailWord_4271213, baseEnd_4271213] using wordTrace_append hprefix tailTrace_4271213
  have hstable : (prefixWord ++ tailWord_4271213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4271213).length < 2 ^ (prefixWord ++ tailWord_4271213).sum := by decide
  have hdescent : baseEnd_4271213 < baseStart_4271213 := by decide
  rcases family_descends (prefixWord ++ tailWord_4271213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4271216 : List Nat := [2, 1, 1, 1, 5, 1, 5, 7]
def baseStart_4271216 : Nat := 118140960795 + 4271216 * 2 ^ 59
def prefixEnd_4271216 : Nat := 4983230072969 + 3 ^ 40 * 4271216 * 2
def baseEnd_4271216 : Nat := 81229140265713558572483

theorem tailTrace_4271216 : CollatzResearch.WordTrace tailWord_4271216 prefixEnd_4271216 81229140265713558572483 := by
  unfold tailWord_4271216
  simp only [CollatzResearch.WordTrace]
  refine ⟨77892022847060686231092751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103856030462747581641457001 77892022847060686231092751)
  ·
    refine ⟨116838034270591029346639127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77892022847060686231092751 116838034270591029346639127)
    ·
      refine ⟨175257051405886544019958691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116838034270591029346639127 175257051405886544019958691)
      ·
        refine ⟨262885577108829816029938037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175257051405886544019958691 262885577108829816029938037)
        ·
          refine ⟨24645522853952795252806691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 262885577108829816029938037 24645522853952795252806691)
          ·
            refine ⟨36968284280929192879210037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24645522853952795252806691 36968284280929192879210037)
            ·
              refine ⟨3465776651337111832425941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36968284280929192879210037 3465776651337111832425941)
              ·
                refine ⟨81229140265713558572483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3465776651337111832425941 81229140265713558572483)
                ·
                  rfl

theorem cell23_4271216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 5, 7].length) (baseStart_4271216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4271216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4271216 prefixEnd_4271216 := by exact prefixLift 4271216
  have htrace : WordTrace (prefixWord ++ tailWord_4271216) baseStart_4271216 baseEnd_4271216 := by
    simpa [prefixWord, tailWord_4271216, baseEnd_4271216] using wordTrace_append hprefix tailTrace_4271216
  have hstable : (prefixWord ++ tailWord_4271216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4271216).length < 2 ^ (prefixWord ++ tailWord_4271216).sum := by decide
  have hdescent : baseEnd_4271216 < baseStart_4271216 := by decide
  rcases family_descends (prefixWord ++ tailWord_4271216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4271237 : List Nat := [1, 3, 1, 1, 7, 1, 1, 2, 2, 4]
def baseStart_4271237 : Nat := 118140960795 + 4271237 * 2 ^ 59
def prefixEnd_4271237 : Nat := 4983230072969 + 3 ^ 40 * 4271237 * 2
def baseEnd_4271237 : Nat := 731065856756003499764815

theorem tailTrace_4271237 : CollatzResearch.WordTrace tailWord_4271237 prefixEnd_4271237 731065856756003499764815 := by
  unfold tailWord_4271237
  simp only [CollatzResearch.WordTrace]
  refine ⟨155784811627045293048699965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103856541084696862032466643 155784811627045293048699965)
  ·
    refine ⟨58419304360141984893262487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 155784811627045293048699965 58419304360141984893262487)
    ·
      refine ⟨87628956540212977339893731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58419304360141984893262487 87628956540212977339893731)
      ·
        refine ⟨131443434810319466009840597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87628956540212977339893731 131443434810319466009840597)
        ·
          refine ⟨3080705503366862484605639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 131443434810319466009840597 3080705503366862484605639)
          ·
            refine ⟨4621058255050293726908459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3080705503366862484605639 4621058255050293726908459)
            ·
              refine ⟨6931587382575440590362689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4621058255050293726908459 6931587382575440590362689)
              ·
                refine ⟨5198690536931580442772017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6931587382575440590362689 5198690536931580442772017)
                ·
                  refine ⟨3899017902698685332079013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5198690536931580442772017 3899017902698685332079013)
                  ·
                    refine ⟨731065856756003499764815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3899017902698685332079013 731065856756003499764815)
                    ·
                      rfl

theorem cell23_4271237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 1, 2, 2, 4].length) (baseStart_4271237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4271237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4271237 prefixEnd_4271237 := by exact prefixLift 4271237
  have htrace : WordTrace (prefixWord ++ tailWord_4271237) baseStart_4271237 baseEnd_4271237 := by
    simpa [prefixWord, tailWord_4271237, baseEnd_4271237] using wordTrace_append hprefix tailTrace_4271237
  have hstable : (prefixWord ++ tailWord_4271237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4271237).length < 2 ^ (prefixWord ++ tailWord_4271237).sum := by decide
  have hdescent : baseEnd_4271237 < baseStart_4271237 := by decide
  rcases family_descends (prefixWord ++ tailWord_4271237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4271253 : List Nat := [1, 3, 2, 1, 1, 1, 2, 4, 3, 3, 2]
def baseStart_4271253 : Nat := 118140960795 + 4271253 * 2 ^ 59
def prefixEnd_4271253 : Nat := 4983230072969 + 3 ^ 40 * 4271253 * 2
def baseEnd_4271253 : Nat := 2193205785958482436694371

theorem tailTrace_4271253 : CollatzResearch.WordTrace tailWord_4271253 prefixEnd_4271253 2193205785958482436694371 := by
  unfold tailWord_4271253
  simp only [CollatzResearch.WordTrace]
  refine ⟨155785395194987327781282413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103856930129991551854188275 155785395194987327781282413)
  ·
    refine ⟨58419523198120247917980905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 155785395194987327781282413 58419523198120247917980905)
    ·
      refine ⟨43814642398590185938485679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58419523198120247917980905 43814642398590185938485679)
      ·
        refine ⟨65721963597885278907728519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43814642398590185938485679 65721963597885278907728519)
        ·
          refine ⟨98582945396827918361592779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65721963597885278907728519 98582945396827918361592779)
          ·
            refine ⟨147874418095241877542389169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98582945396827918361592779 147874418095241877542389169)
            ·
              refine ⟨110905813571431408156791877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 147874418095241877542389169 110905813571431408156791877)
              ·
                refine ⟨20794840044643389029398477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 110905813571431408156791877 20794840044643389029398477)
                ·
                  refine ⟨7798065016741270886024429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20794840044643389029398477 7798065016741270886024429)
                  ·
                    refine ⟨2924274381277976582259161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7798065016741270886024429 2924274381277976582259161)
                    ·
                      refine ⟨2193205785958482436694371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2924274381277976582259161 2193205785958482436694371)
                      ·
                        rfl

theorem cell23_4271253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 4, 3, 3, 2].length) (baseStart_4271253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4271253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4271253 prefixEnd_4271253 := by exact prefixLift 4271253
  have htrace : WordTrace (prefixWord ++ tailWord_4271253) baseStart_4271253 baseEnd_4271253 := by
    simpa [prefixWord, tailWord_4271253, baseEnd_4271253] using wordTrace_append hprefix tailTrace_4271253
  have hstable : (prefixWord ++ tailWord_4271253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4271253).length < 2 ^ (prefixWord ++ tailWord_4271253).sum := by decide
  have hdescent : baseEnd_4271253 < baseStart_4271253 := by decide
  rcases family_descends (prefixWord ++ tailWord_4271253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4271260 : List Nat := [2, 2, 3, 2, 1, 4, 1, 1, 1, 3, 3]
def baseStart_4271260 : Nat := 118140960795 + 4271260 * 2 ^ 59
def prefixEnd_4271260 : Nat := 4983230072969 + 3 ^ 40 * 4271260 * 2
def baseEnd_4271260 : Nat := 2193209380323063909306839

theorem tailTrace_4271260 : CollatzResearch.WordTrace tailWord_4271260 prefixEnd_4271260 2193209380323063909306839 := by
  unfold tailWord_4271260
  simp only [CollatzResearch.WordTrace]
  refine ⟨77892825252980983988393617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103857100337307978651191489 77892825252980983988393617)
  ·
    refine ⟨58419618939735737991295213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77892825252980983988393617 58419618939735737991295213)
    ·
      refine ⟨21907357102400901746735705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58419618939735737991295213 21907357102400901746735705)
      ·
        refine ⟨16430517826800676310051779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21907357102400901746735705 16430517826800676310051779)
        ·
          refine ⟨24645776740201014465077669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16430517826800676310051779 24645776740201014465077669)
          ·
            refine ⟨4621083138787690212202063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24645776740201014465077669 4621083138787690212202063)
            ·
              refine ⟨6931624708181535318303095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4621083138787690212202063 6931624708181535318303095)
              ·
                refine ⟨10397437062272302977454643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6931624708181535318303095 10397437062272302977454643)
                ·
                  refine ⟨15596155593408454466181965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10397437062272302977454643 15596155593408454466181965)
                  ·
                    refine ⟨5848558347528170424818237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15596155593408454466181965 5848558347528170424818237)
                    ·
                      refine ⟨2193209380323063909306839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5848558347528170424818237 2193209380323063909306839)
                      ·
                        rfl

theorem cell23_4271260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 1, 1, 1, 3, 3].length) (baseStart_4271260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4271260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4271260 prefixEnd_4271260 := by exact prefixLift 4271260
  have htrace : WordTrace (prefixWord ++ tailWord_4271260) baseStart_4271260 baseEnd_4271260 := by
    simpa [prefixWord, tailWord_4271260, baseEnd_4271260] using wordTrace_append hprefix tailTrace_4271260
  have hstable : (prefixWord ++ tailWord_4271260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4271260).length < 2 ^ (prefixWord ++ tailWord_4271260).sum := by decide
  have hdescent : baseEnd_4271260 < baseStart_4271260 := by decide
  rcases family_descends (prefixWord ++ tailWord_4271260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4271283 : List Nat := [1, 1, 1, 2, 3, 2, 2, 4, 1, 4, 2]
def baseStart_4271283 : Nat := 118140960795 + 4271283 * 2 ^ 59
def prefixEnd_4271283 : Nat := 4983230072969 + 3 ^ 40 * 4271283 * 2
def baseEnd_4271283 : Nat := 2193221190378117319319233

theorem tailTrace_4271283 : CollatzResearch.WordTrace tailWord_4271283 prefixEnd_4271283 2193221190378117319319233 := by
  unfold tailWord_4271283
  simp only [CollatzResearch.WordTrace]
  refine ⟨155786489384878642904874503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103857659589919095269916335 155786489384878642904874503)
  ·
    refine ⟨233679734077317964357311755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155786489384878642904874503 233679734077317964357311755)
    ·
      refine ⟨350519601115976946535967633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 233679734077317964357311755 350519601115976946535967633)
      ·
        refine ⟨262889700836982709901975725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 350519601115976946535967633 262889700836982709901975725)
        ·
          refine ⟨98583637813868516213240897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 262889700836982709901975725 98583637813868516213240897)
          ·
            refine ⟨73937728360401387159930673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98583637813868516213240897 73937728360401387159930673)
            ·
              refine ⟨55453296270301040369948005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73937728360401387159930673 55453296270301040369948005)
              ·
                refine ⟨10397493050681445069365251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 55453296270301040369948005 10397493050681445069365251)
                ·
                  refine ⟨15596239576022167604047877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10397493050681445069365251 15596239576022167604047877)
                  ·
                    refine ⟨2924294920504156425758977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15596239576022167604047877 2924294920504156425758977)
                    ·
                      refine ⟨2193221190378117319319233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2924294920504156425758977 2193221190378117319319233)
                      ·
                        rfl

theorem cell23_4271283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 4, 1, 4, 2].length) (baseStart_4271283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4271283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4271283 prefixEnd_4271283 := by exact prefixLift 4271283
  have htrace : WordTrace (prefixWord ++ tailWord_4271283) baseStart_4271283 baseEnd_4271283 := by
    simpa [prefixWord, tailWord_4271283, baseEnd_4271283] using wordTrace_append hprefix tailTrace_4271283
  have hstable : (prefixWord ++ tailWord_4271283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4271283).length < 2 ^ (prefixWord ++ tailWord_4271283).sum := by decide
  have hdescent : baseEnd_4271283 < baseStart_4271283 := by decide
  rcases family_descends (prefixWord ++ tailWord_4271283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4271413 : List Nat := [1, 3, 3, 1, 2, 3, 1, 1, 8]
def baseStart_4271413 : Nat := 118140960795 + 4271413 * 2 ^ 59
def prefixEnd_4271413 : Nat := 4983230072969 + 3 ^ 40 * 4271413 * 2
def baseEnd_4271413 : Nat := 243698660318133534521515

theorem tailTrace_4271413 : CollatzResearch.WordTrace tailWord_4271413 prefixEnd_4271413 243698660318133534521515 := by
  unfold tailWord_4271413
  simp only [CollatzResearch.WordTrace]
  refine ⟨155791230874407675107106893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103860820582938450071404595 155791230874407675107106893)
  ·
    refine ⟨58421711577902878165165085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 155791230874407675107106893 58421711577902878165165085)
    ·
      refine ⟨21908141841713579311936907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58421711577902878165165085 21908141841713579311936907)
      ·
        refine ⟨32862212762570368967905361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21908141841713579311936907 32862212762570368967905361)
        ·
          refine ⟨24646659571927776725929021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32862212762570368967905361 24646659571927776725929021)
          ·
            refine ⟨9242497339472916272223383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24646659571927776725929021 9242497339472916272223383)
            ·
              refine ⟨13863746009209374408335075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9242497339472916272223383 13863746009209374408335075)
              ·
                refine ⟨20795619013814061612502613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13863746009209374408335075 20795619013814061612502613)
                ·
                  refine ⟨243698660318133534521515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20795619013814061612502613 243698660318133534521515)
                  ·
                    rfl

theorem cell23_4271413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 1, 8].length) (baseStart_4271413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4271413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4271413 prefixEnd_4271413 := by exact prefixLift 4271413
  have htrace : WordTrace (prefixWord ++ tailWord_4271413) baseStart_4271413 baseEnd_4271413 := by
    simpa [prefixWord, tailWord_4271413, baseEnd_4271413] using wordTrace_append hprefix tailTrace_4271413
  have hstable : (prefixWord ++ tailWord_4271413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4271413).length < 2 ^ (prefixWord ++ tailWord_4271413).sum := by decide
  have hdescent : baseEnd_4271413 < baseStart_4271413 := by decide
  rcases family_descends (prefixWord ++ tailWord_4271413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4271417 : List Nat := [1, 2, 1, 6, 2, 1, 2, 1, 3, 4]
def baseStart_4271417 : Nat := 118140960795 + 4271417 * 2 ^ 59
def prefixEnd_4271417 : Nat := 4983230072969 + 3 ^ 40 * 4271417 * 2
def baseEnd_4271417 : Nat := 731096665595273265014539

theorem tailTrace_4271417 : CollatzResearch.WordTrace tailWord_4271417 prefixEnd_4271417 731096665595273265014539 := by
  unfold tailWord_4271417
  simp only [CollatzResearch.WordTrace]
  refine ⟨155791376766393183790252505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103860917844262122526835003 155791376766393183790252505)
  ·
    refine ⟨116843532574794887842689379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155791376766393183790252505 116843532574794887842689379)
    ·
      refine ⟨175265298862192331764034069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116843532574794887842689379 175265298862192331764034069)
      ·
        refine ⟨8215560884165265551439097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 175265298862192331764034069 8215560884165265551439097)
        ·
          refine ⟨6161670663123949163579323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8215560884165265551439097 6161670663123949163579323)
          ·
            refine ⟨9242505994685923745368985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6161670663123949163579323 9242505994685923745368985)
            ·
              refine ⟨6931879496014442809026739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9242505994685923745368985 6931879496014442809026739)
              ·
                refine ⟨10397819244021664213540109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6931879496014442809026739 10397819244021664213540109)
                ·
                  refine ⟨3899182216508124080077541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10397819244021664213540109 3899182216508124080077541)
                  ·
                    refine ⟨731096665595273265014539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3899182216508124080077541 731096665595273265014539)
                    ·
                      rfl

theorem cell23_4271417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 2, 1, 3, 4].length) (baseStart_4271417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4271417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4271417 prefixEnd_4271417 := by exact prefixLift 4271417
  have htrace : WordTrace (prefixWord ++ tailWord_4271417) baseStart_4271417 baseEnd_4271417 := by
    simpa [prefixWord, tailWord_4271417, baseEnd_4271417] using wordTrace_append hprefix tailTrace_4271417
  have hstable : (prefixWord ++ tailWord_4271417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4271417).length < 2 ^ (prefixWord ++ tailWord_4271417).sum := by decide
  have hdescent : baseEnd_4271417 < baseStart_4271417 := by decide
  rcases family_descends (prefixWord ++ tailWord_4271417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4271440 : List Nat := [2, 1, 1, 1, 1, 5, 1, 4, 3, 1, 3]
def baseStart_4271440 : Nat := 118140960795 + 4271440 * 2 ^ 59
def prefixEnd_4271440 : Nat := 4983230072969 + 3 ^ 40 * 4271440 * 2
def baseEnd_4271440 : Nat := 2193301806840873205056011

theorem tailTrace_4271440 : CollatzResearch.WordTrace tailWord_4271440 prefixEnd_4271440 2193301806840873205056011 := by
  unfold tailWord_4271440
  simp only [CollatzResearch.WordTrace]
  refine ⟨77896107822654929359169887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103861477096873239145559849 77896107822654929359169887)
  ·
    refine ⟨116844161733982394038754831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77896107822654929359169887 116844161733982394038754831)
    ·
      refine ⟨175266242600973591058132247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116844161733982394038754831 175266242600973591058132247)
      ·
        refine ⟨262899363901460386587198371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175266242600973591058132247 262899363901460386587198371)
        ·
          refine ⟨394349045852190579880797557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 262899363901460386587198371 394349045852190579880797557)
          ·
            refine ⟨36970223048642866863824771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 394349045852190579880797557 36970223048642866863824771)
            ·
              refine ⟨55455334572964300295737157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36970223048642866863824771 55455334572964300295737157)
              ·
                refine ⟨10397875232430806305450717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 55455334572964300295737157 10397875232430806305450717)
                ·
                  refine ⟨3899203212161552364544019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10397875232430806305450717 3899203212161552364544019)
                  ·
                    refine ⟨5848804818242328546816029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3899203212161552364544019 5848804818242328546816029)
                    ·
                      refine ⟨2193301806840873205056011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5848804818242328546816029 2193301806840873205056011)
                      ·
                        rfl

theorem cell23_4271440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 4, 3, 1, 3].length) (baseStart_4271440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4271440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4271440 prefixEnd_4271440 := by exact prefixLift 4271440
  have htrace : WordTrace (prefixWord ++ tailWord_4271440) baseStart_4271440 baseEnd_4271440 := by
    simpa [prefixWord, tailWord_4271440, baseEnd_4271440] using wordTrace_append hprefix tailTrace_4271440
  have hstable : (prefixWord ++ tailWord_4271440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4271440).length < 2 ^ (prefixWord ++ tailWord_4271440).sum := by decide
  have hdescent : baseEnd_4271440 < baseStart_4271440 := by decide
  rcases family_descends (prefixWord ++ tailWord_4271440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4271450 : List Nat := [3, 1, 1, 2, 1, 2, 4, 1, 1, 5, 2]
def baseStart_4271450 : Nat := 118140960795 + 4271450 * 2 ^ 59
def prefixEnd_4271450 : Nat := 4983230072969 + 3 ^ 40 * 4271450 * 2
def baseEnd_4271450 : Nat := 2193306941647418165930965

theorem tailTrace_4271450 : CollatzResearch.WordTrace tailWord_4271450 prefixEnd_4271450 2193306941647418165930965 := by
  unfold tailWord_4271450
  simp only [CollatzResearch.WordTrace]
  refine ⟨38948145093818407606550951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103861720250182420284135869 38948145093818407606550951)
  ·
    refine ⟨58422217640727611409826427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38948145093818407606550951 58422217640727611409826427)
    ·
      refine ⟨87633326461091417114739641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58422217640727611409826427 87633326461091417114739641)
      ·
        refine ⟨65724994845818562836054731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87633326461091417114739641 65724994845818562836054731)
        ·
          refine ⟨98587492268727844254082097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65724994845818562836054731 98587492268727844254082097)
          ·
            refine ⟨73940619201545883190561573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98587492268727844254082097 73940619201545883190561573)
            ·
              refine ⟨13863866100289853098230295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 73940619201545883190561573 13863866100289853098230295)
              ·
                refine ⟨20795799150434779647345443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13863866100289853098230295 20795799150434779647345443)
                ·
                  refine ⟨31193698725652169471018165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20795799150434779647345443 31193698725652169471018165)
                  ·
                    refine ⟨2924409255529890887907953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31193698725652169471018165 2924409255529890887907953)
                    ·
                      refine ⟨2193306941647418165930965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2924409255529890887907953 2193306941647418165930965)
                      ·
                        rfl

theorem cell23_4271450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 1, 1, 5, 2].length) (baseStart_4271450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4271450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4271450 prefixEnd_4271450 := by exact prefixLift 4271450
  have htrace : WordTrace (prefixWord ++ tailWord_4271450) baseStart_4271450 baseEnd_4271450 := by
    simpa [prefixWord, tailWord_4271450, baseEnd_4271450] using wordTrace_append hprefix tailTrace_4271450
  have hstable : (prefixWord ++ tailWord_4271450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4271450).length < 2 ^ (prefixWord ++ tailWord_4271450).sum := by decide
  have hdescent : baseEnd_4271450 < baseStart_4271450 := by decide
  rcases family_descends (prefixWord ++ tailWord_4271450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4271460 : List Nat := [2, 3, 1, 1, 3, 2, 2, 3, 1, 5]
def baseStart_4271460 : Nat := 118140960795 + 4271460 * 2 ^ 59
def prefixEnd_4271460 : Nat := 4983230072969 + 3 ^ 40 * 4271460 * 2
def baseEnd_4271460 : Nat := 731104025484654375601973

theorem tailTrace_4271460 : CollatzResearch.WordTrace tailWord_4271460 prefixEnd_4271460 731104025484654375601973 := by
  unfold tailWord_4271460
  simp only [CollatzResearch.WordTrace]
  refine ⟨77896472552618701067033917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103861963403491601422711889 77896472552618701067033917)
  ·
    refine ⟨29211177207232012900137719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77896472552618701067033917 29211177207232012900137719)
    ·
      refine ⟨43816765810848019350206579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29211177207232012900137719 43816765810848019350206579)
      ·
        refine ⟨65725148716272029025309869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43816765810848019350206579 65725148716272029025309869)
        ·
          refine ⟨24646930768602010884491201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65725148716272029025309869 24646930768602010884491201)
          ·
            refine ⟨18485198076451508163368401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24646930768602010884491201 18485198076451508163368401)
            ·
              refine ⟨13863898557338631122526301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18485198076451508163368401 13863898557338631122526301)
              ·
                refine ⟨5198961959001986670947363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13863898557338631122526301 5198961959001986670947363)
                ·
                  refine ⟨7798442938502980006421045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5198961959001986670947363 7798442938502980006421045)
                  ·
                    refine ⟨731104025484654375601973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7798442938502980006421045 731104025484654375601973)
                    ·
                      rfl

theorem cell23_4271460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 3, 1, 5].length) (baseStart_4271460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4271460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4271460 prefixEnd_4271460 := by exact prefixLift 4271460
  have htrace : WordTrace (prefixWord ++ tailWord_4271460) baseStart_4271460 baseEnd_4271460 := by
    simpa [prefixWord, tailWord_4271460, baseEnd_4271460] using wordTrace_append hprefix tailTrace_4271460
  have hstable : (prefixWord ++ tailWord_4271460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4271460).length < 2 ^ (prefixWord ++ tailWord_4271460).sum := by decide
  have hdescent : baseEnd_4271460 < baseStart_4271460 := by decide
  rcases family_descends (prefixWord ++ tailWord_4271460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4271483 : List Nat := [1, 1, 1, 1, 1, 6, 1, 4, 1, 1, 5]
def baseStart_4271483 : Nat := 118140960795 + 4271483 * 2 ^ 59
def prefixEnd_4271483 : Nat := 4983230072969 + 3 ^ 40 * 4271483 * 2
def baseEnd_4271483 : Nat := 2193323886509016536818313

theorem tailTrace_4271483 : CollatzResearch.WordTrace tailWord_4271483 prefixEnd_4271483 2193323886509016536818313 := by
  unfold tailWord_4271483
  simp only [CollatzResearch.WordTrace]
  refine ⟨155793783984154077062155103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103862522656102718041436735 155793783984154077062155103)
  ·
    refine ⟨233690675976231115593232655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155793783984154077062155103 233690675976231115593232655)
    ·
      refine ⟨350536013964346673389848983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 233690675976231115593232655 350536013964346673389848983)
      ·
        refine ⟨525804020946520010084773475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 350536013964346673389848983 525804020946520010084773475)
        ·
          refine ⟨788706031419780015127160213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 525804020946520010084773475 788706031419780015127160213)
          ·
            refine ⟨36970595222802188209085635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 788706031419780015127160213 36970595222802188209085635)
            ·
              refine ⟨55455892834203282313628453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36970595222802188209085635 55455892834203282313628453)
              ·
                refine ⟨10397979906413115433805335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 55455892834203282313628453 10397979906413115433805335)
                ·
                  refine ⟨15596969859619673150708003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10397979906413115433805335 15596969859619673150708003)
                  ·
                    refine ⟨23395454789429509726062005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15596969859619673150708003 23395454789429509726062005)
                    ·
                      refine ⟨2193323886509016536818313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23395454789429509726062005 2193323886509016536818313)
                      ·
                        rfl

theorem cell23_4271483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 4, 1, 1, 5].length) (baseStart_4271483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4271483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4271483 prefixEnd_4271483 := by exact prefixLift 4271483
  have htrace : WordTrace (prefixWord ++ tailWord_4271483) baseStart_4271483 baseEnd_4271483 := by
    simpa [prefixWord, tailWord_4271483, baseEnd_4271483] using wordTrace_append hprefix tailTrace_4271483
  have hstable : (prefixWord ++ tailWord_4271483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4271483).length < 2 ^ (prefixWord ++ tailWord_4271483).sum := by decide
  have hdescent : baseEnd_4271483 < baseStart_4271483 := by decide
  rcases family_descends (prefixWord ++ tailWord_4271483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4271493 : List Nat := [1, 3, 1, 1, 3, 1, 4, 1, 1, 1, 6]
def baseStart_4271493 : Nat := 118140960795 + 4271493 * 2 ^ 59
def prefixEnd_4271493 : Nat := 4983230072969 + 3 ^ 40 * 4271493 * 2
def baseEnd_4271493 : Nat := 2193329021315561497693267

theorem tailTrace_4271493 : CollatzResearch.WordTrace tailWord_4271493 prefixEnd_4271493 2193329021315561497693267 := by
  unfold tailWord_4271493
  simp only [CollatzResearch.WordTrace]
  refine ⟨155794148714117848770019133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103862765809411899180012755 155794148714117848770019133)
  ·
    refine ⟨58422805767794193288757175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 155794148714117848770019133 58422805767794193288757175)
    ·
      refine ⟨87634208651691289933135763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58422805767794193288757175 87634208651691289933135763)
      ·
        refine ⟨131451312977536934899703645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87634208651691289933135763 131451312977536934899703645)
        ·
          refine ⟨49294242366576350587388867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 131451312977536934899703645 49294242366576350587388867)
          ·
            refine ⟨73941363549864525881083301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49294242366576350587388867 73941363549864525881083301)
            ·
              refine ⟨13864005665599598602703119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 73941363549864525881083301 13864005665599598602703119)
              ·
                refine ⟨20796008498399397904054679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13864005665599598602703119 20796008498399397904054679)
                ·
                  refine ⟨31194012747599096856082019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20796008498399397904054679 31194012747599096856082019)
                  ·
                    refine ⟨46791019121398645284123029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31194012747599096856082019 46791019121398645284123029)
                    ·
                      refine ⟨2193329021315561497693267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 46791019121398645284123029 2193329021315561497693267)
                      ·
                        rfl

theorem cell23_4271493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 1, 1, 1, 6].length) (baseStart_4271493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4271493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4271493 prefixEnd_4271493 := by exact prefixLift 4271493
  have htrace : WordTrace (prefixWord ++ tailWord_4271493) baseStart_4271493 baseEnd_4271493 := by
    simpa [prefixWord, tailWord_4271493, baseEnd_4271493] using wordTrace_append hprefix tailTrace_4271493
  have hstable : (prefixWord ++ tailWord_4271493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4271493).length < 2 ^ (prefixWord ++ tailWord_4271493).sum := by decide
  have hdescent : baseEnd_4271493 < baseStart_4271493 := by decide
  rcases family_descends (prefixWord ++ tailWord_4271493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4271500 : List Nat := [2, 2, 1, 2, 1, 3, 3, 1, 3, 2, 3]
def baseStart_4271500 : Nat := 118140960795 + 4271500 * 2 ^ 59
def prefixEnd_4271500 : Nat := 4983230072969 + 3 ^ 40 * 4271500 * 2
def baseEnd_4271500 : Nat := 2193332615680142970305735

theorem tailTrace_4271500 : CollatzResearch.WordTrace tailWord_4271500 prefixEnd_4271500 2193332615680142970305735 := by
  unfold tailWord_4271500
  simp only [CollatzResearch.WordTrace]
  refine ⟨77897202012546244482761977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103862936016728325977015969 77897202012546244482761977)
  ·
    refine ⟨58422901509409683362071483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77897202012546244482761977 58422901509409683362071483)
    ·
      refine ⟨87634352264114525043107225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58422901509409683362071483 87634352264114525043107225)
      ·
        refine ⟨65725764198085893782330419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87634352264114525043107225 65725764198085893782330419)
        ·
          refine ⟨98588646297128840673495629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65725764198085893782330419 98588646297128840673495629)
          ·
            refine ⟨36970742361423315252560861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 98588646297128840673495629 36970742361423315252560861)
            ·
              refine ⟨13864028385533743219710323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36970742361423315252560861 13864028385533743219710323)
              ·
                refine ⟨20796042578300614829565485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13864028385533743219710323 20796042578300614829565485)
                ·
                  refine ⟨7798515966862730561087057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20796042578300614829565485 7798515966862730561087057)
                  ·
                    refine ⟨5848886975147047920815293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7798515966862730561087057 5848886975147047920815293)
                    ·
                      refine ⟨2193332615680142970305735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5848886975147047920815293 2193332615680142970305735)
                      ·
                        rfl

theorem cell23_4271500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 1, 3, 2, 3].length) (baseStart_4271500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4271500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4271500 prefixEnd_4271500 := by exact prefixLift 4271500
  have htrace : WordTrace (prefixWord ++ tailWord_4271500) baseStart_4271500 baseEnd_4271500 := by
    simpa [prefixWord, tailWord_4271500, baseEnd_4271500] using wordTrace_append hprefix tailTrace_4271500
  have hstable : (prefixWord ++ tailWord_4271500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4271500).length < 2 ^ (prefixWord ++ tailWord_4271500).sum := by decide
  have hdescent : baseEnd_4271500 < baseStart_4271500 := by decide
  rcases family_descends (prefixWord ++ tailWord_4271500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4271517 : List Nat := [1, 4, 2, 1, 3, 3, 1, 1, 1, 1, 5]
def baseStart_4271517 : Nat := 118140960795 + 4271517 * 2 ^ 59
def prefixEnd_4271517 : Nat := 4983230072969 + 3 ^ 40 * 4271517 * 2
def baseEnd_4271517 : Nat := 2193341344851269403793157

theorem tailTrace_4271517 : CollatzResearch.WordTrace tailWord_4271517 prefixEnd_4271517 2193341344851269403793157 := by
  unfold tailWord_4271517
  simp only [CollatzResearch.WordTrace]
  refine ⟨155795024066030900868892805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103863349377353933912595203 155795024066030900868892805)
  ·
    refine ⟨29211567012380793912917401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 155795024066030900868892805 29211567012380793912917401)
    ·
      refine ⟨21908675259285595434688051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29211567012380793912917401 21908675259285595434688051)
      ·
        refine ⟨32863012888928393152032077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21908675259285595434688051 32863012888928393152032077)
        ·
          refine ⟨12323629833348147432012029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32863012888928393152032077 12323629833348147432012029)
          ·
            refine ⟨4621361187505555287004511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12323629833348147432012029 4621361187505555287004511)
            ·
              refine ⟨6932041781258332930506767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4621361187505555287004511 6932041781258332930506767)
              ·
                refine ⟨10398062671887499395760151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6932041781258332930506767 10398062671887499395760151)
                ·
                  refine ⟨15597094007831249093640227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10398062671887499395760151 15597094007831249093640227)
                  ·
                    refine ⟨23395641011746873640460341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15597094007831249093640227 23395641011746873640460341)
                    ·
                      refine ⟨2193341344851269403793157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23395641011746873640460341 2193341344851269403793157)
                      ·
                        rfl

theorem cell23_4271517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 1, 1, 1, 1, 5].length) (baseStart_4271517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4271517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4271517 prefixEnd_4271517 := by exact prefixLift 4271517
  have htrace : WordTrace (prefixWord ++ tailWord_4271517) baseStart_4271517 baseEnd_4271517 := by
    simpa [prefixWord, tailWord_4271517, baseEnd_4271517] using wordTrace_append hprefix tailTrace_4271517
  have hstable : (prefixWord ++ tailWord_4271517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4271517).length < 2 ^ (prefixWord ++ tailWord_4271517).sum := by decide
  have hdescent : baseEnd_4271517 < baseStart_4271517 := by decide
  rcases family_descends (prefixWord ++ tailWord_4271517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4271581 : List Nat := [1, 4, 3, 1, 1, 4, 1, 2, 2, 1, 3]
def baseStart_4271581 : Nat := 118140960795 + 4271581 * 2 ^ 59
def prefixEnd_4271581 : Nat := 4983230072969 + 3 ^ 40 * 4271581 * 2
def baseEnd_4271581 : Nat := 2193374207613157153392863

theorem tailTrace_4271581 : CollatzResearch.WordTrace tailWord_4271581 prefixEnd_4271581 2193374207613157153392863 := by
  unfold tailWord_4271581
  simp only [CollatzResearch.WordTrace]
  refine ⟨155797358337799039799222597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103864905558532693199481731 155797358337799039799222597)
  ·
    refine ⟨29212004688337319962354237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 155797358337799039799222597 29212004688337319962354237)
    ·
      refine ⟨10954501758126494985882839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29212004688337319962354237 10954501758126494985882839)
      ·
        refine ⟨16431752637189742478824259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10954501758126494985882839 16431752637189742478824259)
        ·
          refine ⟨24647628955784613718236389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16431752637189742478824259 24647628955784613718236389)
          ·
            refine ⟨4621430429209615072169323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24647628955784613718236389 4621430429209615072169323)
            ·
              refine ⟨6932145643814422608253985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4621430429209615072169323 6932145643814422608253985)
              ·
                refine ⟨5199109232860816956190489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6932145643814422608253985 5199109232860816956190489)
                ·
                  refine ⟨3899331924645612717142867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5199109232860816956190489 3899331924645612717142867)
                  ·
                    refine ⟨5848997886968419075714301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3899331924645612717142867 5848997886968419075714301)
                    ·
                      refine ⟨2193374207613157153392863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5848997886968419075714301 2193374207613157153392863)
                      ·
                        rfl

theorem cell23_4271581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 1, 2, 2, 1, 3].length) (baseStart_4271581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4271581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4271581 prefixEnd_4271581 := by exact prefixLift 4271581
  have htrace : WordTrace (prefixWord ++ tailWord_4271581) baseStart_4271581 baseEnd_4271581 := by
    simpa [prefixWord, tailWord_4271581, baseEnd_4271581] using wordTrace_append hprefix tailTrace_4271581
  have hstable : (prefixWord ++ tailWord_4271581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4271581).length < 2 ^ (prefixWord ++ tailWord_4271581).sum := by decide
  have hdescent : baseEnd_4271581 < baseStart_4271581 := by decide
  rcases family_descends (prefixWord ++ tailWord_4271581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4271600 : List Nat := [2, 1, 1, 1, 3, 4, 2, 1, 2, 2, 4]
def baseStart_4271600 : Nat := 118140960795 + 4271600 * 2 ^ 59
def prefixEnd_4271600 : Nat := 4983230072969 + 3 ^ 40 * 4271600 * 2
def baseEnd_4271600 : Nat := 2193383963745592579055275

theorem tailTrace_4271600 : CollatzResearch.WordTrace tailWord_4271600 prefixEnd_4271600 2193383963745592579055275 := by
  unfold tailWord_4271600
  simp only [CollatzResearch.WordTrace]
  refine ⟨77899025662365103022082127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103865367549820137362776169 77899025662365103022082127)
  ·
    refine ⟨116848538493547654533123191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77899025662365103022082127 116848538493547654533123191)
    ·
      refine ⟨175272807740321481799684787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116848538493547654533123191 175272807740321481799684787)
      ·
        refine ⟨262909211610482222699527181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175272807740321481799684787 262909211610482222699527181)
        ·
          refine ⟨98590954353930833512322693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 262909211610482222699527181 98590954353930833512322693)
          ·
            refine ⟨18485803941362031283560505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 98590954353930833512322693 18485803941362031283560505)
            ·
              refine ⟨13864352956021523462670379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18485803941362031283560505 13864352956021523462670379)
              ·
                refine ⟨20796529434032285194005569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13864352956021523462670379 20796529434032285194005569)
                ·
                  refine ⟨15597397075524213895504177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20796529434032285194005569 15597397075524213895504177)
                  ·
                    refine ⟨11698047806643160421628133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15597397075524213895504177 11698047806643160421628133)
                    ·
                      refine ⟨2193383963745592579055275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11698047806643160421628133 2193383963745592579055275)
                      ·
                        rfl

theorem cell23_4271600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 1, 2, 2, 4].length) (baseStart_4271600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4271600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4271600 prefixEnd_4271600 := by exact prefixLift 4271600
  have htrace : WordTrace (prefixWord ++ tailWord_4271600) baseStart_4271600 baseEnd_4271600 := by
    simpa [prefixWord, tailWord_4271600, baseEnd_4271600] using wordTrace_append hprefix tailTrace_4271600
  have hstable : (prefixWord ++ tailWord_4271600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4271600).length < 2 ^ (prefixWord ++ tailWord_4271600).sum := by decide
  have hdescent : baseEnd_4271600 < baseStart_4271600 := by decide
  rcases family_descends (prefixWord ++ tailWord_4271600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4271643 : List Nat := [1, 1, 1, 1, 1, 1, 3, 1, 1, 4, 8]
def baseStart_4271643 : Nat := 118140960795 + 4271643 * 2 ^ 59
def prefixEnd_4271643 : Nat := 4983230072969 + 3 ^ 40 * 4271643 * 2
def baseEnd_4271643 : Nat := 2193406043413735910817577

theorem tailTrace_4271643 : CollatzResearch.WordTrace tailWord_4271643 prefixEnd_4271643 2193406043413735910817577 := by
  unfold tailWord_4271643
  simp only [CollatzResearch.WordTrace]
  refine ⟨155799619663574424387979583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103866413109049616258653055 155799619663574424387979583)
  ·
    refine ⟨233699429495361636581969375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155799619663574424387979583 233699429495361636581969375)
    ·
      refine ⟨350549144243042454872954063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 233699429495361636581969375 350549144243042454872954063)
      ·
        refine ⟨525823716364563682309431095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 350549144243042454872954063 525823716364563682309431095)
        ·
          refine ⟨788735574546845523464146643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 525823716364563682309431095 788735574546845523464146643)
          ·
            refine ⟨1183103361820268285196219965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 788735574546845523464146643 1183103361820268285196219965)
            ·
              refine ⟨443663760682600606948582487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1183103361820268285196219965 443663760682600606948582487)
              ·
                refine ⟨665495641023900910422873731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 443663760682600606948582487 665495641023900910422873731)
                ·
                  refine ⟨998243461535851365634310597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 665495641023900910422873731 998243461535851365634310597)
                  ·
                    refine ⟨187170649037972131056433237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 998243461535851365634310597 187170649037972131056433237)
                    ·
                      refine ⟨2193406043413735910817577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 187170649037972131056433237 2193406043413735910817577)
                      ·
                        rfl

theorem cell23_4271643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 4, 8].length) (baseStart_4271643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4271643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4271643 prefixEnd_4271643 := by exact prefixLift 4271643
  have htrace : WordTrace (prefixWord ++ tailWord_4271643) baseStart_4271643 baseEnd_4271643 := by
    simpa [prefixWord, tailWord_4271643, baseEnd_4271643] using wordTrace_append hprefix tailTrace_4271643
  have hstable : (prefixWord ++ tailWord_4271643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4271643).length < 2 ^ (prefixWord ++ tailWord_4271643).sum := by decide
  have hdescent : baseEnd_4271643 < baseStart_4271643 := by decide
  rcases family_descends (prefixWord ++ tailWord_4271643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4271644 : List Nat := [2, 2, 3, 1, 2, 1, 5, 2, 5]
def baseStart_4271644 : Nat := 118140960795 + 4271644 * 2 ^ 59
def prefixEnd_4271644 : Nat := 4983230072969 + 3 ^ 40 * 4271644 * 2
def baseEnd_4271644 : Nat := 243711839654932267433897

theorem tailTrace_4271644 : CollatzResearch.WordTrace tailWord_4271644 prefixEnd_4271644 243711839654932267433897 := by
  unfold tailWord_4271644
  simp only [CollatzResearch.WordTrace]
  refine ⟨77899828068285400779382993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103866437424380534372510657 77899828068285400779382993)
  ·
    refine ⟨58424871051214050584537245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77899828068285400779382993 58424871051214050584537245)
    ·
      refine ⟨21909326644205268969201467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58424871051214050584537245 21909326644205268969201467)
      ·
        refine ⟨32863989966307903453802201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21909326644205268969201467 32863989966307903453802201)
        ·
          refine ⟨24647992474730927590351651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32863989966307903453802201 24647992474730927590351651)
          ·
            refine ⟨36971988712096391385527477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24647992474730927590351651 36971988712096391385527477)
            ·
              refine ⟨3466123941759036692393201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36971988712096391385527477 3466123941759036692393201)
              ·
                refine ⟨2599592956319277519294901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3466123941759036692393201 2599592956319277519294901)
                ·
                  refine ⟨243711839654932267433897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2599592956319277519294901 243711839654932267433897)
                  ·
                    rfl

theorem cell23_4271644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 5, 2, 5].length) (baseStart_4271644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4271644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4271644 prefixEnd_4271644 := by exact prefixLift 4271644
  have htrace : WordTrace (prefixWord ++ tailWord_4271644) baseStart_4271644 baseEnd_4271644 := by
    simpa [prefixWord, tailWord_4271644, baseEnd_4271644] using wordTrace_append hprefix tailTrace_4271644
  have hstable : (prefixWord ++ tailWord_4271644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4271644).length < 2 ^ (prefixWord ++ tailWord_4271644).sum := by decide
  have hdescent : baseEnd_4271644 < baseStart_4271644 := by decide
  rcases family_descends (prefixWord ++ tailWord_4271644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4271650 : List Nat := [3, 3, 1, 1, 1, 1, 3, 1, 1, 1, 7]
def baseStart_4271650 : Nat := 118140960795 + 4271650 * 2 ^ 59
def prefixEnd_4271650 : Nat := 4983230072969 + 3 ^ 40 * 4271650 * 2
def baseEnd_4271650 : Nat := 2193409637778317383430045

theorem tailTrace_4271650 : CollatzResearch.WordTrace tailWord_4271650 prefixEnd_4271650 2193409637778317383430045 := by
  unfold tailWord_4271650
  simp only [CollatzResearch.WordTrace]
  refine ⟨38949968743637266145871101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103866583316366043055656269 38949968743637266145871101)
  ·
    refine ⟨14606238278863974804701663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38949968743637266145871101 14606238278863974804701663)
    ·
      refine ⟨21909357418295962207052495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14606238278863974804701663 21909357418295962207052495)
      ·
        refine ⟨32864036127443943310578743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21909357418295962207052495 32864036127443943310578743)
        ·
          refine ⟨49296054191165914965868115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32864036127443943310578743 49296054191165914965868115)
          ·
            refine ⟨73944081286748872448802173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49296054191165914965868115 73944081286748872448802173)
            ·
              refine ⟨27729030482530827168300815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 73944081286748872448802173 27729030482530827168300815)
              ·
                refine ⟨41593545723796240752451223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27729030482530827168300815 41593545723796240752451223)
                ·
                  refine ⟨62390318585694361128676835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41593545723796240752451223 62390318585694361128676835)
                  ·
                    refine ⟨93585477878541541693015253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 62390318585694361128676835 93585477878541541693015253)
                    ·
                      refine ⟨2193409637778317383430045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 93585477878541541693015253 2193409637778317383430045)
                      ·
                        rfl

theorem cell23_4271650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 1, 1, 1, 7].length) (baseStart_4271650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4271650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4271650 prefixEnd_4271650 := by exact prefixLift 4271650
  have htrace : WordTrace (prefixWord ++ tailWord_4271650) baseStart_4271650 baseEnd_4271650 := by
    simpa [prefixWord, tailWord_4271650, baseEnd_4271650] using wordTrace_append hprefix tailTrace_4271650
  have hstable : (prefixWord ++ tailWord_4271650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4271650).length < 2 ^ (prefixWord ++ tailWord_4271650).sum := by decide
  have hdescent : baseEnd_4271650 < baseStart_4271650 := by decide
  rcases family_descends (prefixWord ++ tailWord_4271650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4271690 : List Nat := [3, 1, 2, 1, 1, 3, 2, 1, 2, 1, 6]
def baseStart_4271690 : Nat := 118140960795 + 4271690 * 2 ^ 59
def prefixEnd_4271690 : Nat := 4983230072969 + 3 ^ 40 * 4271690 * 2
def baseEnd_4271690 : Nat := 2193430177004497226929861

theorem tailTrace_4271690 : CollatzResearch.WordTrace tailWord_4271690 prefixEnd_4271690 2193430177004497226929861 := by
  unfold tailWord_4271690
  simp only [CollatzResearch.WordTrace]
  refine ⟨38950333473601037853735131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103867555929602767609960349 38950333473601037853735131)
  ·
    refine ⟨58425500210401556780602697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38950333473601037853735131 58425500210401556780602697)
    ·
      refine ⟨43819125157801167585452023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58425500210401556780602697 43819125157801167585452023)
      ·
        refine ⟨65728687736701751378178035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43819125157801167585452023 65728687736701751378178035)
        ·
          refine ⟨98593031605052627067267053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65728687736701751378178035 98593031605052627067267053)
          ·
            refine ⟨36972386851894735150225145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 98593031605052627067267053 36972386851894735150225145)
            ·
              refine ⟨27729290138921051362668859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36972386851894735150225145 27729290138921051362668859)
              ·
                refine ⟨41593935208381577044003289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27729290138921051362668859 41593935208381577044003289)
                ·
                  refine ⟨31195451406286182783002467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41593935208381577044003289 31195451406286182783002467)
                  ·
                    refine ⟨46793177109429274174503701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31195451406286182783002467 46793177109429274174503701)
                    ·
                      refine ⟨2193430177004497226929861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 46793177109429274174503701 2193430177004497226929861)
                      ·
                        rfl

theorem cell23_4271690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 1, 2, 1, 6].length) (baseStart_4271690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4271690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4271690 prefixEnd_4271690 := by exact prefixLift 4271690
  have htrace : WordTrace (prefixWord ++ tailWord_4271690) baseStart_4271690 baseEnd_4271690 := by
    simpa [prefixWord, tailWord_4271690, baseEnd_4271690] using wordTrace_append hprefix tailTrace_4271690
  have hstable : (prefixWord ++ tailWord_4271690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4271690).length < 2 ^ (prefixWord ++ tailWord_4271690).sum := by decide
  have hdescent : baseEnd_4271690 < baseStart_4271690 := by decide
  rcases family_descends (prefixWord ++ tailWord_4271690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4271697 : List Nat := [1, 2, 2, 1, 3, 2, 1, 4, 2, 2, 3]
def baseStart_4271697 : Nat := 118140960795 + 4271697 * 2 ^ 59
def prefixEnd_4271697 : Nat := 4983230072969 + 3 ^ 40 * 4271697 * 2
def baseEnd_4271697 : Nat := 2193433771369078699542329

theorem tailTrace_4271697 : CollatzResearch.WordTrace tailWord_4271697 prefixEnd_4271697 2193433771369078699542329 := by
  unfold tailWord_4271697
  simp only [CollatzResearch.WordTrace]
  refine ⟨155801589205378791610445345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103867726136919194406963563 155801589205378791610445345)
  ·
    refine ⟨116851191904034093707834009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155801589205378791610445345 116851191904034093707834009)
    ·
      refine ⟨87638393928025570280875507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116851191904034093707834009 87638393928025570280875507)
      ·
        refine ⟨131457590892038355421313261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87638393928025570280875507 131457590892038355421313261)
        ·
          refine ⟨49296596584514383282992473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 131457590892038355421313261 49296596584514383282992473)
          ·
            refine ⟨36972447438385787462244355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49296596584514383282992473 36972447438385787462244355)
            ·
              refine ⟨55458671157578681193366533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36972447438385787462244355 55458671157578681193366533)
              ·
                refine ⟨10398500842046002723756225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 55458671157578681193366533 10398500842046002723756225)
                ·
                  refine ⟨7798875631534502042817169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10398500842046002723756225 7798875631534502042817169)
                  ·
                    refine ⟨5849156723650876532112877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7798875631534502042817169 5849156723650876532112877)
                    ·
                      refine ⟨2193433771369078699542329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5849156723650876532112877 2193433771369078699542329)
                      ·
                        rfl

theorem cell23_4271697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 4, 2, 2, 3].length) (baseStart_4271697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4271697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4271697 prefixEnd_4271697 := by exact prefixLift 4271697
  have htrace : WordTrace (prefixWord ++ tailWord_4271697) baseStart_4271697 baseEnd_4271697 := by
    simpa [prefixWord, tailWord_4271697, baseEnd_4271697] using wordTrace_append hprefix tailTrace_4271697
  have hstable : (prefixWord ++ tailWord_4271697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4271697).length < 2 ^ (prefixWord ++ tailWord_4271697).sum := by decide
  have hdescent : baseEnd_4271697 < baseStart_4271697 := by decide
  rcases family_descends (prefixWord ++ tailWord_4271697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4271717 : List Nat := [1, 3, 1, 3, 3, 1, 2, 3, 6]
def baseStart_4271717 : Nat := 118140960795 + 4271717 * 2 ^ 59
def prefixEnd_4271717 : Nat := 4983230072969 + 3 ^ 40 * 4271717 * 2
def baseEnd_4271717 : Nat := 243716004553574291254693

theorem tailTrace_4271717 : CollatzResearch.WordTrace tailWord_4271717 prefixEnd_4271717 243716004553574291254693 := by
  unfold tailWord_4271717
  simp only [CollatzResearch.WordTrace]
  refine ⟨155802318665306335026173405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103868212443537556684115603 155802318665306335026173405)
  ·
    refine ⟨58425869499489875634815027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 155802318665306335026173405 58425869499489875634815027)
    ·
      refine ⟨87638804249234813452222541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58425869499489875634815027 87638804249234813452222541)
      ·
        refine ⟨32864551593463055044583453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87638804249234813452222541 32864551593463055044583453)
        ·
          refine ⟨12324206847548645641718795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32864551593463055044583453 12324206847548645641718795)
          ·
            refine ⟨18486310271322968462578193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12324206847548645641718795 18486310271322968462578193)
            ·
              refine ⟨13864732703492226346933645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18486310271322968462578193 13864732703492226346933645)
              ·
                refine ⟨5199274763809584880100117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13864732703492226346933645 5199274763809584880100117)
                ·
                  refine ⟨243716004553574291254693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5199274763809584880100117 243716004553574291254693)
                  ·
                    rfl

theorem cell23_4271717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 3, 6].length) (baseStart_4271717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4271717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4271717 prefixEnd_4271717 := by exact prefixLift 4271717
  have htrace : WordTrace (prefixWord ++ tailWord_4271717) baseStart_4271717 baseEnd_4271717 := by
    simpa [prefixWord, tailWord_4271717, baseEnd_4271717] using wordTrace_append hprefix tailTrace_4271717
  have hstable : (prefixWord ++ tailWord_4271717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4271717).length < 2 ^ (prefixWord ++ tailWord_4271717).sum := by decide
  have hdescent : baseEnd_4271717 < baseStart_4271717 := by decide
  rcases family_descends (prefixWord ++ tailWord_4271717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4271740 : List Nat := [2, 2, 2, 1, 1, 2, 1, 1, 2, 4, 5]
def baseStart_4271740 : Nat := 118140960795 + 4271740 * 2 ^ 59
def prefixEnd_4271740 : Nat := 4983230072969 + 3 ^ 40 * 4271740 * 2
def baseEnd_4271740 : Nat := 2193455851037222031304631

theorem tailTrace_4271740 : CollatzResearch.WordTrace tailWord_4271740 prefixEnd_4271740 2193455851037222031304631 := by
  unfold tailWord_4271740
  simp only [CollatzResearch.WordTrace]
  refine ⟨77901578772111504977130337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103868771696148673302840449 77901578772111504977130337)
  ·
    refine ⟨58426184079083628732847753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77901578772111504977130337 58426184079083628732847753)
    ·
      refine ⟨43819638059312721549635815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58426184079083628732847753 43819638059312721549635815)
      ·
        refine ⟨65729457088969082324453723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43819638059312721549635815 65729457088969082324453723)
        ·
          refine ⟨98594185633453623486680585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65729457088969082324453723 98594185633453623486680585)
          ·
            refine ⟨73945639225090217615010439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98594185633453623486680585 73945639225090217615010439)
            ·
              refine ⟨110918458837635326422515659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73945639225090217615010439 110918458837635326422515659)
              ·
                refine ⟨166377688256452989633773489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 110918458837635326422515659 166377688256452989633773489)
                ·
                  refine ⟨124783266192339742225330117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 166377688256452989633773489 124783266192339742225330117)
                  ·
                    refine ⟨23396862411063701667249397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 124783266192339742225330117 23396862411063701667249397)
                    ·
                      refine ⟨2193455851037222031304631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23396862411063701667249397 2193455851037222031304631)
                      ·
                        rfl

theorem cell23_4271740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 1, 2, 4, 5].length) (baseStart_4271740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4271740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4271740 prefixEnd_4271740 := by exact prefixLift 4271740
  have htrace : WordTrace (prefixWord ++ tailWord_4271740) baseStart_4271740 baseEnd_4271740 := by
    simpa [prefixWord, tailWord_4271740, baseEnd_4271740] using wordTrace_append hprefix tailTrace_4271740
  have hstable : (prefixWord ++ tailWord_4271740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4271740).length < 2 ^ (prefixWord ++ tailWord_4271740).sum := by decide
  have hdescent : baseEnd_4271740 < baseStart_4271740 := by decide
  rcases family_descends (prefixWord ++ tailWord_4271740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4271760 : List Nat := [2, 1, 1, 1, 1, 1, 3, 4, 3, 6]
def baseStart_4271760 : Nat := 118140960795 + 4271760 * 2 ^ 59
def prefixEnd_4271760 : Nat := 4983230072969 + 3 ^ 40 * 4271760 * 2
def baseEnd_4271760 : Nat := 731155373550103984351513

theorem tailTrace_4271760 : CollatzResearch.WordTrace tailWord_4271760 prefixEnd_4271760 731155373550103984351513 := by
  unfold tailWord_4271760
  simp only [CollatzResearch.WordTrace]
  refine ⟨77901943502075276684994367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103869258002767035579992489 77901943502075276684994367)
  ·
    refine ⟨116852915253112915027491551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77901943502075276684994367 116852915253112915027491551)
    ·
      refine ⟨175279372879669372541237327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116852915253112915027491551 175279372879669372541237327)
      ·
        refine ⟨262919059319504058811855991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175279372879669372541237327 262919059319504058811855991)
        ·
          refine ⟨394378588979256088217783987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 262919059319504058811855991 394378588979256088217783987)
          ·
            refine ⟨591567883468884132326675981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 394378588979256088217783987 591567883468884132326675981)
            ·
              refine ⟨221837956300831549622503493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 591567883468884132326675981 221837956300831549622503493)
              ·
                refine ⟨41594616806405915554219405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 221837956300831549622503493 41594616806405915554219405)
                ·
                  refine ⟨15597981302402218332832277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41594616806405915554219405 15597981302402218332832277)
                  ·
                    refine ⟨731155373550103984351513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15597981302402218332832277 731155373550103984351513)
                    ·
                      rfl

theorem cell23_4271760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 4, 3, 6].length) (baseStart_4271760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4271760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4271760 prefixEnd_4271760 := by exact prefixLift 4271760
  have htrace : WordTrace (prefixWord ++ tailWord_4271760) baseStart_4271760 baseEnd_4271760 := by
    simpa [prefixWord, tailWord_4271760, baseEnd_4271760] using wordTrace_append hprefix tailTrace_4271760
  have hstable : (prefixWord ++ tailWord_4271760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4271760).length < 2 ^ (prefixWord ++ tailWord_4271760).sum := by decide
  have hdescent : baseEnd_4271760 < baseStart_4271760 := by decide
  rcases family_descends (prefixWord ++ tailWord_4271760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4271804 : List Nat := [2, 2, 2, 3, 1, 3, 2, 1, 1, 1, 5]
def baseStart_4271804 : Nat := 118140960795 + 4271804 * 2 ^ 59
def prefixEnd_4271804 : Nat := 4983230072969 + 3 ^ 40 * 4271804 * 2
def baseEnd_4271804 : Nat := 2193488713799109780904337

theorem tailTrace_4271804 : CollatzResearch.WordTrace tailWord_4271804 prefixEnd_4271804 2193488713799109780904337 := by
  unfold tailWord_4271804
  simp only [CollatzResearch.WordTrace]
  refine ⟨77902745907995574442295233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103870327877327432589726977 77902745907995574442295233)
  ·
    refine ⟨58427059430996680831721425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77902745907995574442295233 58427059430996680831721425)
    ·
      refine ⟨43820294573247510623791069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58427059430996680831721425 43820294573247510623791069)
      ·
        refine ⟨16432610464967816483921651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43820294573247510623791069 16432610464967816483921651)
        ·
          refine ⟨24648915697451724725882477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16432610464967816483921651 24648915697451724725882477)
          ·
            refine ⟨9243343386544396772205929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24648915697451724725882477 9243343386544396772205929)
            ·
              refine ⟨6932507539908297579154447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9243343386544396772205929 6932507539908297579154447)
              ·
                refine ⟨10398761309862446368731671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6932507539908297579154447 10398761309862446368731671)
                ·
                  refine ⟨15598141964793669553097507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10398761309862446368731671 15598141964793669553097507)
                  ·
                    refine ⟨23397212947190504329646261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15598141964793669553097507 23397212947190504329646261)
                    ·
                      refine ⟨2193488713799109780904337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23397212947190504329646261 2193488713799109780904337)
                      ·
                        rfl

theorem cell23_4271804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 2, 1, 1, 1, 5].length) (baseStart_4271804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4271804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4271804 prefixEnd_4271804 := by exact prefixLift 4271804
  have htrace : WordTrace (prefixWord ++ tailWord_4271804) baseStart_4271804 baseEnd_4271804 := by
    simpa [prefixWord, tailWord_4271804, baseEnd_4271804] using wordTrace_append hprefix tailTrace_4271804
  have hstable : (prefixWord ++ tailWord_4271804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4271804).length < 2 ^ (prefixWord ++ tailWord_4271804).sum := by decide
  have hdescent : baseEnd_4271804 < baseStart_4271804 := by decide
  rcases family_descends (prefixWord ++ tailWord_4271804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4271821 : List Nat := [1, 6, 2, 1, 1, 1, 2, 2, 1, 1, 5]
def baseStart_4271821 : Nat := 118140960795 + 4271821 * 2 ^ 59
def prefixEnd_4271821 : Nat := 4983230072969 + 3 ^ 40 * 4271821 * 2
def baseEnd_4271821 : Nat := 2193497442970236214391759

theorem tailTrace_4271821 : CollatzResearch.WordTrace tailWord_4271821 prefixEnd_4271821 2193497442970236214391759 := by
  unfold tailWord_4271821
  simp only [CollatzResearch.WordTrace]
  refine ⟨155806111856929560787959317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103870741237953040525306211 155806111856929560787959317)
  ·
    refine ⟨7303411493293573161935593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 155806111856929560787959317 7303411493293573161935593)
    ·
      refine ⟨5477558619970179871451695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7303411493293573161935593 5477558619970179871451695)
      ·
        refine ⟨8216337929955269807177543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5477558619970179871451695 8216337929955269807177543)
        ·
          refine ⟨12324506894932904710766315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8216337929955269807177543 12324506894932904710766315)
          ·
            refine ⟨18486760342399357066149473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12324506894932904710766315 18486760342399357066149473)
            ·
              refine ⟨13865070256799517799612105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18486760342399357066149473 13865070256799517799612105)
              ·
                refine ⟨10398802692599638349709079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13865070256799517799612105 10398802692599638349709079)
                ·
                  refine ⟨15598204038899457524563619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10398802692599638349709079 15598204038899457524563619)
                  ·
                    refine ⟨23397306058349186286845429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15598204038899457524563619 23397306058349186286845429)
                    ·
                      refine ⟨2193497442970236214391759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23397306058349186286845429 2193497442970236214391759)
                      ·
                        rfl

theorem cell23_4271821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_4271821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4271821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4271821 prefixEnd_4271821 := by exact prefixLift 4271821
  have htrace : WordTrace (prefixWord ++ tailWord_4271821) baseStart_4271821 baseEnd_4271821 := by
    simpa [prefixWord, tailWord_4271821, baseEnd_4271821] using wordTrace_append hprefix tailTrace_4271821
  have hstable : (prefixWord ++ tailWord_4271821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4271821).length < 2 ^ (prefixWord ++ tailWord_4271821).sum := by decide
  have hdescent : baseEnd_4271821 < baseStart_4271821 := by decide
  rcases family_descends (prefixWord ++ tailWord_4271821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4271828 : List Nat := [2, 4, 1, 3, 1, 1, 4, 1, 2, 4]
def baseStart_4271828 : Nat := 118140960795 + 4271828 * 2 ^ 59
def prefixEnd_4271828 : Nat := 4983230072969 + 3 ^ 40 * 4271828 * 2
def baseEnd_4271828 : Nat := 731167012444939229001409

theorem tailTrace_4271828 : CollatzResearch.WordTrace tailWord_4271828 prefixEnd_4271828 731167012444939229001409 := by
  unfold tailWord_4271828
  simp only [CollatzResearch.WordTrace]
  refine ⟨77903183583952100491732069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103870911445269467322309425 77903183583952100491732069)
  ·
    refine ⟨14606846921991018842199763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 77903183583952100491732069 14606846921991018842199763)
    ·
      refine ⟨21910270382986528263299645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14606846921991018842199763 21910270382986528263299645)
      ·
        refine ⟨8216351393619948098737367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21910270382986528263299645 8216351393619948098737367)
        ·
          refine ⟨12324527090429922148106051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8216351393619948098737367 12324527090429922148106051)
          ·
            refine ⟨18486790635644883222159077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12324527090429922148106051 18486790635644883222159077)
            ·
              refine ⟨3466273244183415604154827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18486790635644883222159077 3466273244183415604154827)
              ·
                refine ⟨5199409866275123406232241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3466273244183415604154827 5199409866275123406232241)
                ·
                  refine ⟨3899557399706342554674181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5199409866275123406232241 3899557399706342554674181)
                  ·
                    refine ⟨731167012444939229001409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3899557399706342554674181 731167012444939229001409)
                    ·
                      rfl

theorem cell23_4271828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 4, 1, 2, 4].length) (baseStart_4271828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4271828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4271828 prefixEnd_4271828 := by exact prefixLift 4271828
  have htrace : WordTrace (prefixWord ++ tailWord_4271828) baseStart_4271828 baseEnd_4271828 := by
    simpa [prefixWord, tailWord_4271828, baseEnd_4271828] using wordTrace_append hprefix tailTrace_4271828
  have hstable : (prefixWord ++ tailWord_4271828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4271828).length < 2 ^ (prefixWord ++ tailWord_4271828).sum := by decide
  have hdescent : baseEnd_4271828 < baseStart_4271828 := by decide
  rcases family_descends (prefixWord ++ tailWord_4271828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4271874 : List Nat := [3, 4, 1, 1, 1, 1, 1, 1, 1, 5, 4]
def baseStart_4271874 : Nat := 118140960795 + 4271874 * 2 ^ 59
def prefixEnd_4271874 : Nat := 4983230072969 + 3 ^ 40 * 4271874 * 2
def baseEnd_4271874 : Nat := 2193524657444924507029015

theorem tailTrace_4271874 : CollatzResearch.WordTrace tailWord_4271874 prefixEnd_4271874 2193524657444924507029015 := by
  unfold tailWord_4271874
  simp only [CollatzResearch.WordTrace]
  refine ⟨38952011231434387709909669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103872029950491700559759117 38952011231434387709909669)
  ·
    refine ⟨7303502105893947695608063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38952011231434387709909669 7303502105893947695608063)
    ·
      refine ⟨10955253158840921543412095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7303502105893947695608063 10955253158840921543412095)
      ·
        refine ⟨16432879738261382315118143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10955253158840921543412095 16432879738261382315118143)
        ·
          refine ⟨24649319607392073472677215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16432879738261382315118143 24649319607392073472677215)
          ·
            refine ⟨36973979411088110209015823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24649319607392073472677215 36973979411088110209015823)
            ·
              refine ⟨55460969116632165313523735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36973979411088110209015823 55460969116632165313523735)
              ·
                refine ⟨83191453674948247970285603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55460969116632165313523735 83191453674948247970285603)
                ·
                  refine ⟨124787180512422371955428405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 83191453674948247970285603 124787180512422371955428405)
                  ·
                    refine ⟨11698798173039597370821413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 124787180512422371955428405 11698798173039597370821413)
                    ·
                      refine ⟨2193524657444924507029015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11698798173039597370821413 2193524657444924507029015)
                      ·
                        rfl

theorem cell23_4271874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 1, 1, 5, 4].length) (baseStart_4271874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4271874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4271874 prefixEnd_4271874 := by exact prefixLift 4271874
  have htrace : WordTrace (prefixWord ++ tailWord_4271874) baseStart_4271874 baseEnd_4271874 := by
    simpa [prefixWord, tailWord_4271874, baseEnd_4271874] using wordTrace_append hprefix tailTrace_4271874
  have hstable : (prefixWord ++ tailWord_4271874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4271874).length < 2 ^ (prefixWord ++ tailWord_4271874).sum := by decide
  have hdescent : baseEnd_4271874 < baseStart_4271874 := by decide
  rcases family_descends (prefixWord ++ tailWord_4271874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4271942 : List Nat := [6, 1, 1, 2, 1, 3, 1, 1, 1, 4, 2]
def baseStart_4271942 : Nat := 118140960795 + 4271942 * 2 ^ 59
def prefixEnd_4271942 : Nat := 4983230072969 + 3 ^ 40 * 4271942 * 2
def baseEnd_4271942 : Nat := 2193559574129430240978703

theorem tailTrace_4271942 : CollatzResearch.WordTrace tailWord_4271942 prefixEnd_4271942 2193559574129430240978703 := by
  unfold tailWord_4271942
  simp only [CollatzResearch.WordTrace]
  refine ⟨4869078909046599951659815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 103873683392994132302076053 4869078909046599951659815)
  ·
    refine ⟨7303618363569899927489723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4869078909046599951659815 7303618363569899927489723)
    ·
      refine ⟨10955427545354849891234585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7303618363569899927489723 10955427545354849891234585)
      ·
        refine ⟨8216570659016137418425939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10955427545354849891234585 8216570659016137418425939)
        ·
          refine ⟨12324855988524206127638909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8216570659016137418425939 12324855988524206127638909)
          ·
            refine ⟨4621820995696577297864591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12324855988524206127638909 4621820995696577297864591)
            ·
              refine ⟨6932731493544865946796887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4621820995696577297864591 6932731493544865946796887)
              ·
                refine ⟨10399097240317298920195331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6932731493544865946796887 10399097240317298920195331)
                ·
                  refine ⟨15598645860475948380292997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10399097240317298920195331 15598645860475948380292997)
                  ·
                    refine ⟨2924746098839240321304937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15598645860475948380292997 2924746098839240321304937)
                    ·
                      refine ⟨2193559574129430240978703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2924746098839240321304937 2193559574129430240978703)
                      ·
                        rfl

theorem cell23_4271942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 1, 1, 1, 4, 2].length) (baseStart_4271942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4271942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4271942 prefixEnd_4271942 := by exact prefixLift 4271942
  have htrace : WordTrace (prefixWord ++ tailWord_4271942) baseStart_4271942 baseEnd_4271942 := by
    simpa [prefixWord, tailWord_4271942, baseEnd_4271942] using wordTrace_append hprefix tailTrace_4271942
  have hstable : (prefixWord ++ tailWord_4271942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4271942).length < 2 ^ (prefixWord ++ tailWord_4271942).sum := by decide
  have hdescent : baseEnd_4271942 < baseStart_4271942 := by decide
  rcases family_descends (prefixWord ++ tailWord_4271942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4271977 : List Nat := [1, 2, 1, 1, 1, 3, 1, 3, 1, 3, 6]
def baseStart_4271977 : Nat := 118140960795 + 4271977 * 2 ^ 59
def prefixEnd_4271977 : Nat := 4983230072969 + 3 ^ 40 * 4271977 * 2
def baseEnd_4271977 : Nat := 2193577545952337604041041

theorem tailTrace_4271977 : CollatzResearch.WordTrace tailWord_4271977 prefixEnd_4271977 2193577545952337604041041 := by
  unfold tailWord_4271977
  simp only [CollatzResearch.WordTrace]
  refine ⟨155811801644364399430638185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103874534429576266287092123 155811801644364399430638185)
  ·
    refine ⟨116858851233273299572978639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155811801644364399430638185 116858851233273299572978639)
    ·
      refine ⟨175288276849909949359467959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116858851233273299572978639 175288276849909949359467959)
      ·
        refine ⟨262932415274864924039201939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175288276849909949359467959 262932415274864924039201939)
        ·
          refine ⟨394398622912297386058802909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 262932415274864924039201939 394398622912297386058802909)
          ·
            refine ⟨147899483592111519772051091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 394398622912297386058802909 147899483592111519772051091)
            ·
              refine ⟨221849225388167279658076637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 147899483592111519772051091 221849225388167279658076637)
              ·
                refine ⟨83193459520562729871778739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 221849225388167279658076637 83193459520562729871778739)
                ·
                  refine ⟨124790189280844094807668109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 83193459520562729871778739 124790189280844094807668109)
                  ·
                    refine ⟨46796320980316535552875541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 124790189280844094807668109 46796320980316535552875541)
                    ·
                      refine ⟨2193577545952337604041041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 46796320980316535552875541 2193577545952337604041041)
                      ·
                        rfl

theorem cell23_4271977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 3, 1, 3, 6].length) (baseStart_4271977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4271977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4271977 prefixEnd_4271977 := by exact prefixLift 4271977
  have htrace : WordTrace (prefixWord ++ tailWord_4271977) baseStart_4271977 baseEnd_4271977 := by
    simpa [prefixWord, tailWord_4271977, baseEnd_4271977] using wordTrace_append hprefix tailTrace_4271977
  have hstable : (prefixWord ++ tailWord_4271977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4271977).length < 2 ^ (prefixWord ++ tailWord_4271977).sum := by decide
  have hdescent : baseEnd_4271977 < baseStart_4271977 := by decide
  rcases family_descends (prefixWord ++ tailWord_4271977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4271978 : List Nat := [3, 1, 3, 4, 1, 1, 1, 2, 2, 5]
def baseStart_4271978 : Nat := 118140960795 + 4271978 * 2 ^ 59
def prefixEnd_4271978 : Nat := 4983230072969 + 3 ^ 40 * 4271978 * 2
def baseEnd_4271978 : Nat := 731192686477664033376179

theorem tailTrace_4271978 : CollatzResearch.WordTrace tailWord_4271978 prefixEnd_4271978 731192686477664033376179 := by
  unfold tailWord_4271978
  simp only [CollatzResearch.WordTrace]
  refine ⟨38952959529340194150356147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103874558744907184400949725 38952959529340194150356147)
  ·
    refine ⟨58429439294010291225534221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38952959529340194150356147 58429439294010291225534221)
    ·
      refine ⟨21911039735253859209575333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58429439294010291225534221 21911039735253859209575333)
      ·
        refine ⟨4108319950360098601795375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21911039735253859209575333 4108319950360098601795375)
        ·
          refine ⟨6162479925540147902693063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4108319950360098601795375 6162479925540147902693063)
          ·
            refine ⟨9243719888310221854039595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6162479925540147902693063 9243719888310221854039595)
            ·
              refine ⟨13865579832465332781059393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9243719888310221854039595 13865579832465332781059393)
              ·
                refine ⟨10399184874348999585794545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13865579832465332781059393 10399184874348999585794545)
                ·
                  refine ⟨7799388655761749689345909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10399184874348999585794545 7799388655761749689345909)
                  ·
                    refine ⟨731192686477664033376179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7799388655761749689345909 731192686477664033376179)
                    ·
                      rfl

theorem cell23_4271978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 2, 2, 5].length) (baseStart_4271978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4271978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4271978 prefixEnd_4271978 := by exact prefixLift 4271978
  have htrace : WordTrace (prefixWord ++ tailWord_4271978) baseStart_4271978 baseEnd_4271978 := by
    simpa [prefixWord, tailWord_4271978, baseEnd_4271978] using wordTrace_append hprefix tailTrace_4271978
  have hstable : (prefixWord ++ tailWord_4271978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4271978).length < 2 ^ (prefixWord ++ tailWord_4271978).sum := by decide
  have hdescent : baseEnd_4271978 < baseStart_4271978 := by decide
  rcases family_descends (prefixWord ++ tailWord_4271978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4271981 : List Nat := [1, 5, 1, 1, 1, 1, 2, 1, 4, 4, 2]
def baseStart_4271981 : Nat := 118140960795 + 4271981 * 2 ^ 59
def prefixEnd_4271981 : Nat := 4983230072969 + 3 ^ 40 * 4271981 * 2
def baseEnd_4271981 : Nat := 2193579599874955588391023

theorem tailTrace_4271981 : CollatzResearch.WordTrace tailWord_4271981 prefixEnd_4271981 2193579599874955588391023 := by
  unfold tailWord_4271981
  simp only [CollatzResearch.WordTrace]
  refine ⟨155811947536349908113783797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103874631690899938742522531 155811947536349908113783797)
  ·
    refine ⟨14607370081532803885667231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 155811947536349908113783797 14607370081532803885667231)
    ·
      refine ⟨21911055122299205828500847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14607370081532803885667231 21911055122299205828500847)
      ·
        refine ⟨32866582683448808742751271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21911055122299205828500847 32866582683448808742751271)
        ·
          refine ⟨49299874025173213114126907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32866582683448808742751271 49299874025173213114126907)
          ·
            refine ⟨73949811037759819671190361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49299874025173213114126907 73949811037759819671190361)
            ·
              refine ⟨55462358278319864753392771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73949811037759819671190361 55462358278319864753392771)
              ·
                refine ⟨83193537417479797130089157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55462358278319864753392771 83193537417479797130089157)
                ·
                  refine ⟨15598788265777461961891717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 83193537417479797130089157 15598788265777461961891717)
                  ·
                    refine ⟨2924772799833274117854697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15598788265777461961891717 2924772799833274117854697)
                    ·
                      refine ⟨2193579599874955588391023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2924772799833274117854697 2193579599874955588391023)
                      ·
                        rfl

theorem cell23_4271981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 1, 4, 4, 2].length) (baseStart_4271981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4271981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4271981 prefixEnd_4271981 := by exact prefixLift 4271981
  have htrace : WordTrace (prefixWord ++ tailWord_4271981) baseStart_4271981 baseEnd_4271981 := by
    simpa [prefixWord, tailWord_4271981, baseEnd_4271981] using wordTrace_append hprefix tailTrace_4271981
  have hstable : (prefixWord ++ tailWord_4271981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4271981).length < 2 ^ (prefixWord ++ tailWord_4271981).sum := by decide
  have hdescent : baseEnd_4271981 < baseStart_4271981 := by decide
  rcases family_descends (prefixWord ++ tailWord_4271981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4272018 : List Nat := [3, 2, 3, 2, 1, 1, 1, 3, 2, 2, 3]
def baseStart_4272018 : Nat := 118140960795 + 4272018 * 2 ^ 59
def prefixEnd_4272018 : Nat := 4983230072969 + 3 ^ 40 * 4272018 * 2
def baseEnd_4272018 : Nat := 2193598598659171943628353

theorem tailTrace_4272018 : CollatzResearch.WordTrace tailWord_4272018 prefixEnd_4272018 2193598598659171943628353 := by
  unfold tailWord_4272018
  simp only [CollatzResearch.WordTrace]
  refine ⟨38953324259303965858220177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103875531358143908955253805 38953324259303965858220177)
  ·
    refine ⟨29214993194477974393665133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38953324259303965858220177 29214993194477974393665133)
    ·
      refine ⟨10955622447929240397624425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29214993194477974393665133 10955622447929240397624425)
      ·
        refine ⟨8216716835946930298218319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10955622447929240397624425 8216716835946930298218319)
        ·
          refine ⟨12325075253920395447327479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8216716835946930298218319 12325075253920395447327479)
          ·
            refine ⟨18487612880880593170991219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12325075253920395447327479 18487612880880593170991219)
            ·
              refine ⟨27731419321320889756486829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18487612880880593170991219 27731419321320889756486829)
              ·
                refine ⟨10399282245495333658682561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27731419321320889756486829 10399282245495333658682561)
                ·
                  refine ⟨7799461684121500244011921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10399282245495333658682561 7799461684121500244011921)
                  ·
                    refine ⟨5849596263091125183008941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7799461684121500244011921 5849596263091125183008941)
                    ·
                      refine ⟨2193598598659171943628353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5849596263091125183008941 2193598598659171943628353)
                      ·
                        rfl

theorem cell23_4272018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 3, 2, 2, 3].length) (baseStart_4272018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4272018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4272018 prefixEnd_4272018 := by exact prefixLift 4272018
  have htrace : WordTrace (prefixWord ++ tailWord_4272018) baseStart_4272018 baseEnd_4272018 := by
    simpa [prefixWord, tailWord_4272018, baseEnd_4272018] using wordTrace_append hprefix tailTrace_4272018
  have hstable : (prefixWord ++ tailWord_4272018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4272018).length < 2 ^ (prefixWord ++ tailWord_4272018).sum := by decide
  have hdescent : baseEnd_4272018 < baseStart_4272018 := by decide
  rcases family_descends (prefixWord ++ tailWord_4272018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4272041 : List Nat := [1, 2, 1, 1, 1, 1, 4, 3, 4, 3, 2]
def baseStart_4272041 : Nat := 118140960795 + 4272041 * 2 ^ 59
def prefixEnd_4272041 : Nat := 4983230072969 + 3 ^ 40 * 4272041 * 2
def baseEnd_4272041 : Nat := 2193610408714225353640747

theorem tailTrace_4272041 : CollatzResearch.WordTrace tailWord_4272041 prefixEnd_4272041 2193610408714225353640747 := by
  unfold tailWord_4272041
  simp only [CollatzResearch.WordTrace]
  refine ⟨155814135916132538360967977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103876090610755025573978651 155814135916132538360967977)
  ·
    refine ⟨116860601937099403770725983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155814135916132538360967977 116860601937099403770725983)
    ·
      refine ⟨175290902905649105656088975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116860601937099403770725983 175290902905649105656088975)
      ·
        refine ⟨262936354358473658484133463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175290902905649105656088975 262936354358473658484133463)
        ·
          refine ⟨394404531537710487726200195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 262936354358473658484133463 394404531537710487726200195)
          ·
            refine ⟨591606797306565731589300293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 394404531537710487726200195 591606797306565731589300293)
            ·
              refine ⟨110926274494981074672993805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 591606797306565731589300293 110926274494981074672993805)
              ·
                refine ⟨41597352935617903002372677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 110926274494981074672993805 41597352935617903002372677)
                ·
                  refine ⟨7799503675428356812944877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 41597352935617903002372677 7799503675428356812944877)
                  ·
                    refine ⟨2924813878285633804854329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7799503675428356812944877 2924813878285633804854329)
                    ·
                      refine ⟨2193610408714225353640747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2924813878285633804854329 2193610408714225353640747)
                      ·
                        rfl

theorem cell23_4272041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 3, 4, 3, 2].length) (baseStart_4272041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4272041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4272041 prefixEnd_4272041 := by exact prefixLift 4272041
  have htrace : WordTrace (prefixWord ++ tailWord_4272041) baseStart_4272041 baseEnd_4272041 := by
    simpa [prefixWord, tailWord_4272041, baseEnd_4272041] using wordTrace_append hprefix tailTrace_4272041
  have hstable : (prefixWord ++ tailWord_4272041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4272041).length < 2 ^ (prefixWord ++ tailWord_4272041).sum := by decide
  have hdescent : baseEnd_4272041 < baseStart_4272041 := by decide
  rcases family_descends (prefixWord ++ tailWord_4272041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4272071 : List Nat := [1, 1, 4, 1, 1, 2, 1, 6, 1, 1, 4]
def baseStart_4272071 : Nat := 118140960795 + 4272071 * 2 ^ 59
def prefixEnd_4272071 : Nat := 4983230072969 + 3 ^ 40 * 4272071 * 2
def baseEnd_4272071 : Nat := 2193625813133860236265609

theorem tailTrace_4272071 : CollatzResearch.WordTrace tailWord_4272071 prefixEnd_4272071 2193625813133860236265609 := by
  unfold tailWord_4272071
  simp only [CollatzResearch.WordTrace]
  refine ⟨155815230106023853484560067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103876820070682568989706711 155815230106023853484560067)
  ·
    refine ⟨233722845159035780226840101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155815230106023853484560067 233722845159035780226840101)
    ·
      refine ⟨43823033467319208792532519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 233722845159035780226840101 43823033467319208792532519)
      ·
        refine ⟨65734550200978813188798779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43823033467319208792532519 65734550200978813188798779)
        ·
          refine ⟨98601825301468219783198169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65734550200978813188798779 98601825301468219783198169)
          ·
            refine ⟨73951368976101164837398627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98601825301468219783198169 73951368976101164837398627)
            ·
              refine ⟨110927053464151747256097941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73951368976101164837398627 110927053464151747256097941)
              ·
                refine ⟨5199705631132113152629591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 110927053464151747256097941 5199705631132113152629591)
                ·
                  refine ⟨7799558446698169728944387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5199705631132113152629591 7799558446698169728944387)
                  ·
                    refine ⟨11699337670047254593416581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7799558446698169728944387 11699337670047254593416581)
                    ·
                      refine ⟨2193625813133860236265609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11699337670047254593416581 2193625813133860236265609)
                      ·
                        rfl

theorem cell23_4272071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 6, 1, 1, 4].length) (baseStart_4272071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4272071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4272071 prefixEnd_4272071 := by exact prefixLift 4272071
  have htrace : WordTrace (prefixWord ++ tailWord_4272071) baseStart_4272071 baseEnd_4272071 := by
    simpa [prefixWord, tailWord_4272071, baseEnd_4272071] using wordTrace_append hprefix tailTrace_4272071
  have hstable : (prefixWord ++ tailWord_4272071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4272071).length < 2 ^ (prefixWord ++ tailWord_4272071).sum := by decide
  have hdescent : baseEnd_4272071 < baseStart_4272071 := by decide
  rcases family_descends (prefixWord ++ tailWord_4272071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4272085 : List Nat := [1, 3, 2, 3, 2, 3, 2, 1, 1, 5]
def baseStart_4272085 : Nat := 118140960795 + 4272085 * 2 ^ 59
def prefixEnd_4272085 : Nat := 4983230072969 + 3 ^ 40 * 4272085 * 2
def baseEnd_4272085 : Nat := 731211000621007727163515

theorem tailTrace_4272085 : CollatzResearch.WordTrace tailWord_4272085 prefixEnd_4272085 731211000621007727163515 := by
  unfold tailWord_4272085
  simp only [CollatzResearch.WordTrace]
  refine ⟨155815740727973133875569709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103877160485315422583713139 155815740727973133875569709)
  ·
    refine ⟨58430902772989925203338641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 155815740727973133875569709 58430902772989925203338641)
    ·
      refine ⟨43823177079742443902503981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58430902772989925203338641 43823177079742443902503981)
      ·
        refine ⟨16433691404903416463438993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43823177079742443902503981 16433691404903416463438993)
        ·
          refine ⟨12325268553677562347579245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16433691404903416463438993 12325268553677562347579245)
          ·
            refine ⟨4621975707629085880342217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12325268553677562347579245 4621975707629085880342217)
            ·
              refine ⟨3466481780721814410256663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4621975707629085880342217 3466481780721814410256663)
              ·
                refine ⟨5199722671082721615384995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3466481780721814410256663 5199722671082721615384995)
                ·
                  refine ⟨7799584006624082423077493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5199722671082721615384995 7799584006624082423077493)
                  ·
                    refine ⟨731211000621007727163515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7799584006624082423077493 731211000621007727163515)
                    ·
                      rfl

theorem cell23_4272085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 2, 1, 1, 5].length) (baseStart_4272085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4272085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4272085 prefixEnd_4272085 := by exact prefixLift 4272085
  have htrace : WordTrace (prefixWord ++ tailWord_4272085) baseStart_4272085 baseEnd_4272085 := by
    simpa [prefixWord, tailWord_4272085, baseEnd_4272085] using wordTrace_append hprefix tailTrace_4272085
  have hstable : (prefixWord ++ tailWord_4272085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4272085).length < 2 ^ (prefixWord ++ tailWord_4272085).sum := by decide
  have hdescent : baseEnd_4272085 < baseStart_4272085 := by decide
  rcases family_descends (prefixWord ++ tailWord_4272085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4272088 : List Nat := [2, 1, 2, 2, 2, 2, 1, 2, 5, 2, 2]
def baseStart_4272088 : Nat := 118140960795 + 4272088 * 2 ^ 59
def prefixEnd_4272088 : Nat := 4983230072969 + 3 ^ 40 * 4272088 * 2
def baseEnd_4272088 : Nat := 2193634542304986669753031

theorem tailTrace_4272088 : CollatzResearch.WordTrace tailWord_4272088 prefixEnd_4272088 2193634542304986669753031 := by
  unfold tailWord_4272088
  simp only [CollatzResearch.WordTrace]
  refine ⟨77907925073481132693964459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103877233431308176925285945 77907925073481132693964459)
  ·
    refine ⟨116861887610221699040946689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77907925073481132693964459 116861887610221699040946689)
    ·
      refine ⟨87646415707666274280710017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116861887610221699040946689 87646415707666274280710017)
      ·
        refine ⟨65734811780749705710532513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87646415707666274280710017 65734811780749705710532513)
        ·
          refine ⟨49301108835562279282899385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65734811780749705710532513 49301108835562279282899385)
          ·
            refine ⟨36975831626671709462174539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49301108835562279282899385 36975831626671709462174539)
            ·
              refine ⟨55463747440007564193261809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36975831626671709462174539 55463747440007564193261809)
              ·
                refine ⟨41597810580005673144946357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55463747440007564193261809 41597810580005673144946357)
                ·
                  refine ⟨3899794741875531857338721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 41597810580005673144946357 3899794741875531857338721)
                  ·
                    refine ⟨2924846056406648893004041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3899794741875531857338721 2924846056406648893004041)
                    ·
                      refine ⟨2193634542304986669753031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2924846056406648893004041 2193634542304986669753031)
                      ·
                        rfl

theorem cell23_4272088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 2, 5, 2, 2].length) (baseStart_4272088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4272088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4272088 prefixEnd_4272088 := by exact prefixLift 4272088
  have htrace : WordTrace (prefixWord ++ tailWord_4272088) baseStart_4272088 baseEnd_4272088 := by
    simpa [prefixWord, tailWord_4272088, baseEnd_4272088] using wordTrace_append hprefix tailTrace_4272088
  have hstable : (prefixWord ++ tailWord_4272088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4272088).length < 2 ^ (prefixWord ++ tailWord_4272088).sum := by decide
  have hdescent : baseEnd_4272088 < baseStart_4272088 := by decide
  rcases family_descends (prefixWord ++ tailWord_4272088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4272104 : List Nat := [2, 1, 4, 1, 1, 1, 1, 1, 2, 2, 7]
def baseStart_4272104 : Nat := 118140960795 + 4272104 * 2 ^ 59
def prefixEnd_4272104 : Nat := 4983230072969 + 3 ^ 40 * 4272104 * 2
def baseEnd_4272104 : Nat := 2193642757995458607152957

theorem tailTrace_4272104 : CollatzResearch.WordTrace tailWord_4272104 prefixEnd_4272104 2193642757995458607152957 := by
  unfold tailWord_4272104
  simp only [CollatzResearch.WordTrace]
  refine ⟨77908216857452150060255683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103877622476602866747007577 77908216857452150060255683)
  ·
    refine ⟨116862325286178225090383525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77908216857452150060255683 116862325286178225090383525)
    ·
      refine ⟨21911685991158417204446911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 116862325286178225090383525 21911685991158417204446911)
      ·
        refine ⟨32867528986737625806670367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21911685991158417204446911 32867528986737625806670367)
        ·
          refine ⟨49301293480106438710005551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32867528986737625806670367 49301293480106438710005551)
          ·
            refine ⟨73951940220159658065008327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49301293480106438710005551 73951940220159658065008327)
            ·
              refine ⟨110927910330239487097512491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73951940220159658065008327 110927910330239487097512491)
              ·
                refine ⟨166391865495359230646268737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 110927910330239487097512491 166391865495359230646268737)
                ·
                  refine ⟨124793899121519422984701553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 166391865495359230646268737 124793899121519422984701553)
                  ·
                    refine ⟨93595424341139567238526165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 124793899121519422984701553 93595424341139567238526165)
                    ·
                      refine ⟨2193642757995458607152957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 93595424341139567238526165 2193642757995458607152957)
                      ·
                        rfl

theorem cell23_4272104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 1, 2, 2, 7].length) (baseStart_4272104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4272104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4272104 prefixEnd_4272104 := by exact prefixLift 4272104
  have htrace : WordTrace (prefixWord ++ tailWord_4272104) baseStart_4272104 baseEnd_4272104 := by
    simpa [prefixWord, tailWord_4272104, baseEnd_4272104] using wordTrace_append hprefix tailTrace_4272104
  have hstable : (prefixWord ++ tailWord_4272104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4272104).length < 2 ^ (prefixWord ++ tailWord_4272104).sum := by decide
  have hdescent : baseEnd_4272104 < baseStart_4272104 := by decide
  rcases family_descends (prefixWord ++ tailWord_4272104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4272118 : List Nat := [5, 1, 1, 1, 4, 1, 1, 1, 1, 1, 6]
def baseStart_4272118 : Nat := 118140960795 + 4272118 * 2 ^ 59
def prefixEnd_4272118 : Nat := 4983230072969 + 3 ^ 40 * 4272118 * 2
def baseEnd_4272118 : Nat := 2193649946724621552377893

theorem tailTrace_4272118 : CollatzResearch.WordTrace tailWord_4272118 prefixEnd_4272118 2193649946724621552377893 := by
  unfold tailWord_4272118
  simp only [CollatzResearch.WordTrace]
  refine ⟨9738559021053348781970063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 103877962891235720341014005 9738559021053348781970063)
  ·
    refine ⟨14607838531580023172955095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9738559021053348781970063 14607838531580023172955095)
    ·
      refine ⟨21911757797370034759432643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14607838531580023172955095 21911757797370034759432643)
      ·
        refine ⟨32867636696055052139148965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21911757797370034759432643 32867636696055052139148965)
        ·
          refine ⟨6162681880510322276090431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32867636696055052139148965 6162681880510322276090431)
          ·
            refine ⟨9244022820765483414135647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6162681880510322276090431 9244022820765483414135647)
            ·
              refine ⟨13866034231148225121203471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9244022820765483414135647 13866034231148225121203471)
              ·
                refine ⟨20799051346722337681805207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13866034231148225121203471 20799051346722337681805207)
                ·
                  refine ⟨31198577020083506522707811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20799051346722337681805207 31198577020083506522707811)
                  ·
                    refine ⟨46797865530125259784061717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31198577020083506522707811 46797865530125259784061717)
                    ·
                      refine ⟨2193649946724621552377893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 46797865530125259784061717 2193649946724621552377893)
                      ·
                        rfl

theorem cell23_4272118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 1, 1, 1, 6].length) (baseStart_4272118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4272118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4272118 prefixEnd_4272118 := by exact prefixLift 4272118
  have htrace : WordTrace (prefixWord ++ tailWord_4272118) baseStart_4272118 baseEnd_4272118 := by
    simpa [prefixWord, tailWord_4272118, baseEnd_4272118] using wordTrace_append hprefix tailTrace_4272118
  have hstable : (prefixWord ++ tailWord_4272118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4272118).length < 2 ^ (prefixWord ++ tailWord_4272118).sum := by decide
  have hdescent : baseEnd_4272118 < baseStart_4272118 := by decide
  rcases family_descends (prefixWord ++ tailWord_4272118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4272131 : List Nat := [1, 1, 1, 3, 2, 1, 1, 2, 2, 7, 2]
def baseStart_4272131 : Nat := 118140960795 + 4272131 * 2 ^ 59
def prefixEnd_4272131 : Nat := 4983230072969 + 3 ^ 40 * 4272131 * 2
def baseEnd_4272131 : Nat := 2193656621973130001515333

theorem tailTrace_4272131 : CollatzResearch.WordTrace tailWord_4272131 prefixEnd_4272131 2193656621973130001515333 := by
  unfold tailWord_4272131
  simp only [CollatzResearch.WordTrace]
  refine ⟨155817418485806483731744247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103878278990537655821162831 155817418485806483731744247)
  ·
    refine ⟨233726127728709725597616371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155817418485806483731744247 233726127728709725597616371)
    ·
      refine ⟨350589191593064588396424557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 233726127728709725597616371 350589191593064588396424557)
      ·
        refine ⟨131470946847399220648659209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 350589191593064588396424557 131470946847399220648659209)
        ·
          refine ⟨98603210135549415486494407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 131470946847399220648659209 98603210135549415486494407)
          ·
            refine ⟨147904815203324123229741611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98603210135549415486494407 147904815203324123229741611)
            ·
              refine ⟨221857222804986184844612417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 147904815203324123229741611 221857222804986184844612417)
              ·
                refine ⟨166392917103739638633459313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 221857222804986184844612417 166392917103739638633459313)
                ·
                  refine ⟨124794687827804728975094485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 166392917103739638633459313 124794687827804728975094485)
                  ·
                    refine ⟨2924875495964173335353777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 124794687827804728975094485 2924875495964173335353777)
                    ·
                      refine ⟨2193656621973130001515333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2924875495964173335353777 2193656621973130001515333)
                      ·
                        rfl

theorem cell23_4272131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 2, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 2, 2, 7, 2].length) (baseStart_4272131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4272131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4272131 prefixEnd_4272131 := by exact prefixLift 4272131
  have htrace : WordTrace (prefixWord ++ tailWord_4272131) baseStart_4272131 baseEnd_4272131 := by
    simpa [prefixWord, tailWord_4272131, baseEnd_4272131] using wordTrace_append hprefix tailTrace_4272131
  have hstable : (prefixWord ++ tailWord_4272131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4272131).length < 2 ^ (prefixWord ++ tailWord_4272131).sum := by decide
  have hdescent : baseEnd_4272131 < baseStart_4272131 := by decide
  rcases family_descends (prefixWord ++ tailWord_4272131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4272181 : List Nat := [1, 3, 3, 1, 1, 1, 3, 2, 2, 1, 5]
def baseStart_4272181 : Nat := 118140960795 + 4272181 * 2 ^ 59
def prefixEnd_4272181 : Nat := 4983230072969 + 3 ^ 40 * 4272181 * 2
def baseEnd_4272181 : Nat := 2193682296005854805890103

theorem tailTrace_4272181 : CollatzResearch.WordTrace tailWord_4272181 prefixEnd_4272181 2193682296005854805890103 := by
  unfold tailWord_4272181
  simp only [CollatzResearch.WordTrace]
  refine ⟨155819242135625342271064397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103879494757083561514042931 155819242135625342271064397)
  ·
    refine ⟨58432215800859503351649149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 155819242135625342271064397 58432215800859503351649149)
    ·
      refine ⟨21912080925322313756868431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58432215800859503351649149 21912080925322313756868431)
      ·
        refine ⟨32868121387983470635302647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21912080925322313756868431 32868121387983470635302647)
        ·
          refine ⟨49302182081975205952953971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32868121387983470635302647 49302182081975205952953971)
          ·
            refine ⟨73953273122962808929430957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49302182081975205952953971 73953273122962808929430957)
            ·
              refine ⟨27732477421111053348536609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 73953273122962808929430957 27732477421111053348536609)
              ·
                refine ⟨20799358065833290011402457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27732477421111053348536609 20799358065833290011402457)
                ·
                  refine ⟨15599518549374967508551843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20799358065833290011402457 15599518549374967508551843)
                  ·
                    refine ⟨23399277824062451262827765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15599518549374967508551843 23399277824062451262827765)
                    ·
                      refine ⟨2193682296005854805890103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23399277824062451262827765 2193682296005854805890103)
                      ·
                        rfl

theorem cell23_4272181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 2, 2, 1, 5].length) (baseStart_4272181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4272181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4272181 prefixEnd_4272181 := by exact prefixLift 4272181
  have htrace : WordTrace (prefixWord ++ tailWord_4272181) baseStart_4272181 baseEnd_4272181 := by
    simpa [prefixWord, tailWord_4272181, baseEnd_4272181] using wordTrace_append hprefix tailTrace_4272181
  have hstable : (prefixWord ++ tailWord_4272181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4272181).length < 2 ^ (prefixWord ++ tailWord_4272181).sum := by decide
  have hdescent : baseEnd_4272181 < baseStart_4272181 := by decide
  rcases family_descends (prefixWord ++ tailWord_4272181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4272218 : List Nat := [3, 1, 1, 2, 1, 1, 5, 4, 5]
def baseStart_4272218 : Nat := 118140960795 + 4272218 * 2 ^ 59
def prefixEnd_4272218 : Nat := 4983230072969 + 3 ^ 40 * 4272218 * 2
def baseEnd_4272218 : Nat := 243744588310007906791937

theorem tailTrace_4272218 : CollatzResearch.WordTrace tailWord_4272218 prefixEnd_4272218 243744588310007906791937 := by
  unfold tailWord_4272218
  simp only [CollatzResearch.WordTrace]
  refine ⟨38955147909122824397540327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103880394424327531726774205 38955147909122824397540327)
  ·
    refine ⟨58432721863684236596310491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38955147909122824397540327 58432721863684236596310491)
    ·
      refine ⟨87649082795526354894465737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58432721863684236596310491 87649082795526354894465737)
      ·
        refine ⟨65736812096644766170849303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87649082795526354894465737 65736812096644766170849303)
        ·
          refine ⟨98605218144967149256273955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65736812096644766170849303 98605218144967149256273955)
          ·
            refine ⟨147907827217450723884410933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98605218144967149256273955 147907827217450723884410933)
            ·
              refine ⟨13866358801636005364163525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 147907827217450723884410933 13866358801636005364163525)
              ·
                refine ⟨2599942275306751005780661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13866358801636005364163525 2599942275306751005780661)
                ·
                  refine ⟨243744588310007906791937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2599942275306751005780661 243744588310007906791937)
                  ·
                    rfl

theorem cell23_4272218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 4, 5].length) (baseStart_4272218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4272218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4272218 prefixEnd_4272218 := by exact prefixLift 4272218
  have htrace : WordTrace (prefixWord ++ tailWord_4272218) baseStart_4272218 baseEnd_4272218 := by
    simpa [prefixWord, tailWord_4272218, baseEnd_4272218] using wordTrace_append hprefix tailTrace_4272218
  have hstable : (prefixWord ++ tailWord_4272218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4272218).length < 2 ^ (prefixWord ++ tailWord_4272218).sum := by decide
  have hdescent : baseEnd_4272218 < baseStart_4272218 := by decide
  rcases family_descends (prefixWord ++ tailWord_4272218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4272222 : List Nat := [4, 4, 1, 1, 2, 1, 1, 1, 2, 6]
def baseStart_4272222 : Nat := 118140960795 + 4272222 * 2 ^ 59
def prefixEnd_4272222 : Nat := 4983230072969 + 3 ^ 40 * 4272222 * 2
def baseEnd_4272222 : Nat := 731234449570896381825805

theorem tailTrace_4272222 : CollatzResearch.WordTrace tailWord_4272222 prefixEnd_4272222 731234449570896381825805 := by
  unfold tailWord_4272222
  simp only [CollatzResearch.WordTrace]
  refine ⟨19477592191059600784163365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 103880491685651204182204613 19477592191059600784163365)
  ·
    refine ⟨3652048535823675147030631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19477592191059600784163365 3652048535823675147030631)
    ·
      refine ⟨5478072803735512720545947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3652048535823675147030631 5478072803735512720545947)
      ·
        refine ⟨8217109205603269080818921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5478072803735512720545947 8217109205603269080818921)
        ·
          refine ⟨6162831904202451810614191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8217109205603269080818921 6162831904202451810614191)
          ·
            refine ⟨9244247856303677715921287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6162831904202451810614191 9244247856303677715921287)
            ·
              refine ⟨13866371784455516573881931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9244247856303677715921287 13866371784455516573881931)
              ·
                refine ⟨20799557676683274860822897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13866371784455516573881931 20799557676683274860822897)
                ·
                  refine ⟨15599668257512456145617173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20799557676683274860822897 15599668257512456145617173)
                  ·
                    refine ⟨731234449570896381825805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15599668257512456145617173 731234449570896381825805)
                    ·
                      rfl

theorem cell23_4272222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 1, 2, 6].length) (baseStart_4272222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4272222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4272222 prefixEnd_4272222 := by exact prefixLift 4272222
  have htrace : WordTrace (prefixWord ++ tailWord_4272222) baseStart_4272222 baseEnd_4272222 := by
    simpa [prefixWord, tailWord_4272222, baseEnd_4272222] using wordTrace_append hprefix tailTrace_4272222
  have hstable : (prefixWord ++ tailWord_4272222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4272222).length < 2 ^ (prefixWord ++ tailWord_4272222).sum := by decide
  have hdescent : baseEnd_4272222 < baseStart_4272222 := by decide
  rcases family_descends (prefixWord ++ tailWord_4272222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4272231 : List Nat := [1, 1, 5, 1, 1, 2, 2, 2, 1, 7]
def baseStart_4272231 : Nat := 118140960795 + 4272231 * 2 ^ 59
def prefixEnd_4272231 : Nat := 4983230072969 + 3 ^ 40 * 4272231 * 2
def baseEnd_4272231 : Nat := 731235990012859870088291

theorem tailTrace_4272231 : CollatzResearch.WordTrace tailWord_4272231 prefixEnd_4272231 731235990012859870088291 := by
  unfold tailWord_4272231
  simp only [CollatzResearch.WordTrace]
  refine ⟨155821065785444200810384547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103880710523629467206923031 155821065785444200810384547)
  ·
    refine ⟨233731598678166301215576821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155821065785444200810384547 233731598678166301215576821)
    ·
      refine ⟨21912337376078090738960327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 233731598678166301215576821 21912337376078090738960327)
      ·
        refine ⟨32868506064117136108440491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21912337376078090738960327 32868506064117136108440491)
        ·
          refine ⟨49302759096175704162660737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32868506064117136108440491 49302759096175704162660737)
          ·
            refine ⟨36977069322131778121995553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49302759096175704162660737 36977069322131778121995553)
            ·
              refine ⟨27732801991598833591496665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36977069322131778121995553 27732801991598833591496665)
              ·
                refine ⟨20799601493699125193622499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27732801991598833591496665 20799601493699125193622499)
                ·
                  refine ⟨31199402240548687790433749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20799601493699125193622499 31199402240548687790433749)
                  ·
                    refine ⟨731235990012859870088291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31199402240548687790433749 731235990012859870088291)
                    ·
                      rfl

theorem cell23_4272231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 2, 1, 7].length) (baseStart_4272231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4272231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4272231 prefixEnd_4272231 := by exact prefixLift 4272231
  have htrace : WordTrace (prefixWord ++ tailWord_4272231) baseStart_4272231 baseEnd_4272231 := by
    simpa [prefixWord, tailWord_4272231, baseEnd_4272231] using wordTrace_append hprefix tailTrace_4272231
  have hstable : (prefixWord ++ tailWord_4272231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4272231).length < 2 ^ (prefixWord ++ tailWord_4272231).sum := by decide
  have hdescent : baseEnd_4272231 < baseStart_4272231 := by decide
  rcases family_descends (prefixWord ++ tailWord_4272231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4272285 : List Nat := [1, 4, 2, 1, 1, 3, 2, 1, 2, 4, 2]
def baseStart_4272285 : Nat := 118140960795 + 4272285 * 2 ^ 59
def prefixEnd_4272285 : Nat := 4983230072969 + 3 ^ 40 * 4272285 * 2
def baseEnd_4272285 : Nat := 2193735697993922398989625

theorem tailTrace_4272285 : CollatzResearch.WordTrace tailWord_4272285 prefixEnd_4272285 2193735697993922398989625 := by
  unfold tailWord_4272285
  simp only [CollatzResearch.WordTrace]
  refine ⟨155823035327248568032850309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103882023551499045355233539 155823035327248568032850309)
  ·
    refine ⟨29216819123859106506159433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 155823035327248568032850309 29216819123859106506159433)
    ·
      refine ⟨21912614342894329879619575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29216819123859106506159433 21912614342894329879619575)
      ·
        refine ⟨32868921514341494819429363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21912614342894329879619575 32868921514341494819429363)
        ·
          refine ⟨49303382271512242229144045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32868921514341494819429363 49303382271512242229144045)
          ·
            refine ⟨18488768351817090835929017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49303382271512242229144045 18488768351817090835929017)
            ·
              refine ⟨13866576263862818126946763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18488768351817090835929017 13866576263862818126946763)
              ·
                refine ⟨20799864395794227190420145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13866576263862818126946763 20799864395794227190420145)
                ·
                  refine ⟨15599898296845670392815109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20799864395794227190420145 15599898296845670392815109)
                  ·
                    refine ⟨2924980930658563198652833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15599898296845670392815109 2924980930658563198652833)
                    ·
                      refine ⟨2193735697993922398989625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2924980930658563198652833 2193735697993922398989625)
                      ·
                        rfl

theorem cell23_4272285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 1, 2, 4, 2].length) (baseStart_4272285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4272285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4272285 prefixEnd_4272285 := by exact prefixLift 4272285
  have htrace : WordTrace (prefixWord ++ tailWord_4272285) baseStart_4272285 baseEnd_4272285 := by
    simpa [prefixWord, tailWord_4272285, baseEnd_4272285] using wordTrace_append hprefix tailTrace_4272285
  have hstable : (prefixWord ++ tailWord_4272285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4272285).length < 2 ^ (prefixWord ++ tailWord_4272285).sum := by decide
  have hdescent : baseEnd_4272285 < baseStart_4272285 := by decide
  rcases family_descends (prefixWord ++ tailWord_4272285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4272288 : List Nat := [2, 1, 1, 4, 2, 2, 1, 2, 1, 4, 3]
def baseStart_4272288 : Nat := 118140960795 + 4272288 * 2 ^ 59
def prefixEnd_4272288 : Nat := 4983230072969 + 3 ^ 40 * 4272288 * 2
def baseEnd_4272288 : Nat := 2193737238435885887252111

theorem tailTrace_4272288 : CollatzResearch.WordTrace tailWord_4272288 prefixEnd_4272288 2193737238435885887252111 := by
  unfold tailWord_4272288
  simp only [CollatzResearch.WordTrace]
  refine ⟨77911572373118849772604759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103882096497491799696806345 77911572373118849772604759)
  ·
    refine ⟨116867358559678274658907139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77911572373118849772604759 116867358559678274658907139)
    ·
      refine ⟨175301037839517411988360709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116867358559678274658907139 175301037839517411988360709)
      ·
        refine ⟨32868944594909514747817633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 175301037839517411988360709 32868944594909514747817633)
        ·
          refine ⟨24651708446182136060863225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32868944594909514747817633 24651708446182136060863225)
          ·
            refine ⟨18488781334636602045647419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24651708446182136060863225 18488781334636602045647419)
            ·
              refine ⟨27733172001954903068471129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18488781334636602045647419 27733172001954903068471129)
              ·
                refine ⟨20799879001466177301353347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27733172001954903068471129 20799879001466177301353347)
                ·
                  refine ⟨31199818502199265952030021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20799879001466177301353347 31199818502199265952030021)
                  ·
                    refine ⟨5849965969162362366005629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 31199818502199265952030021 5849965969162362366005629)
                    ·
                      refine ⟨2193737238435885887252111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5849965969162362366005629 2193737238435885887252111)
                      ·
                        rfl

theorem cell23_4272288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 2, 1, 4, 3].length) (baseStart_4272288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4272288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4272288 prefixEnd_4272288 := by exact prefixLift 4272288
  have htrace : WordTrace (prefixWord ++ tailWord_4272288) baseStart_4272288 baseEnd_4272288 := by
    simpa [prefixWord, tailWord_4272288, baseEnd_4272288] using wordTrace_append hprefix tailTrace_4272288
  have hstable : (prefixWord ++ tailWord_4272288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4272288).length < 2 ^ (prefixWord ++ tailWord_4272288).sum := by decide
  have hdescent : baseEnd_4272288 < baseStart_4272288 := by decide
  rcases family_descends (prefixWord ++ tailWord_4272288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4272342 : List Nat := [5, 2, 1, 2, 1, 2, 1, 3, 6]
def baseStart_4272342 : Nat := 118140960795 + 4272342 * 2 ^ 59
def prefixEnd_4272342 : Nat := 4983230072969 + 3 ^ 40 * 4272342 * 2
def baseEnd_4272342 : Nat := 243751662932358741775207

theorem tailTrace_4272342 : CollatzResearch.WordTrace tailWord_4272342 prefixEnd_4272342 243751662932358741775207 := by
  unfold tailWord_4272342
  simp only [CollatzResearch.WordTrace]
  refine ⟨9739069643002629172979705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 103883409525361377845116853 9739069643002629172979705)
  ·
    refine ⟨7304302232251971879734779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9739069643002629172979705 7304302232251971879734779)
    ·
      refine ⟨10956453348377957819602169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7304302232251971879734779 10956453348377957819602169)
      ·
        refine ⟨8217340011283468364701627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10956453348377957819602169 8217340011283468364701627)
        ·
          refine ⟨12326010016925202547052441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8217340011283468364701627 12326010016925202547052441)
          ·
            refine ⟨9244507512693901910289331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12326010016925202547052441 9244507512693901910289331)
            ·
              refine ⟨13866761269040852865433997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9244507512693901910289331 13866761269040852865433997)
              ·
                refine ⟨5200035475890319824537749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13866761269040852865433997 5200035475890319824537749)
                ·
                  refine ⟨243751662932358741775207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5200035475890319824537749 243751662932358741775207)
                  ·
                    rfl

theorem cell23_4272342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 3, 6].length) (baseStart_4272342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4272342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4272342 prefixEnd_4272342 := by exact prefixLift 4272342
  have htrace : WordTrace (prefixWord ++ tailWord_4272342) baseStart_4272342 baseEnd_4272342 := by
    simpa [prefixWord, tailWord_4272342, baseEnd_4272342] using wordTrace_append hprefix tailTrace_4272342
  have hstable : (prefixWord ++ tailWord_4272342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4272342).length < 2 ^ (prefixWord ++ tailWord_4272342).sum := by decide
  have hdescent : baseEnd_4272342 < baseStart_4272342 := by decide
  rcases family_descends (prefixWord ++ tailWord_4272342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4272362 : List Nat := [3, 1, 3, 1, 1, 2, 4, 1, 2, 3, 2]
def baseStart_4272362 : Nat := 118140960795 + 4272362 * 2 ^ 59
def prefixEnd_4272362 : Nat := 4983230072969 + 3 ^ 40 * 4272362 * 2
def baseEnd_4272362 : Nat := 2193775236004318597726771

theorem tailTrace_4272362 : CollatzResearch.WordTrace tailWord_4272362 prefixEnd_4272362 2193775236004318597726771 := by
  unfold tailWord_4272362
  simp only [CollatzResearch.WordTrace]
  refine ⟨38956460936992402545850835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103883895831979740122268893 38956460936992402545850835)
  ·
    refine ⟨58434691405488603818776253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38956460936992402545850835 58434691405488603818776253)
    ·
      refine ⟨21913009277058226432041095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58434691405488603818776253 21913009277058226432041095)
      ·
        refine ⟨32869513915587339648061643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21913009277058226432041095 32869513915587339648061643)
        ·
          refine ⟨49304270873381009472092465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32869513915587339648061643 49304270873381009472092465)
          ·
            refine ⟨36978203155035757104069349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49304270873381009472092465 36978203155035757104069349)
            ·
              refine ⟨6933413091569204457013003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36978203155035757104069349 6933413091569204457013003)
              ·
                refine ⟨10400119637353806685519505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6933413091569204457013003 10400119637353806685519505)
                ·
                  refine ⟨7800089728015355014139629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10400119637353806685519505 7800089728015355014139629)
                  ·
                    refine ⟨2925033648005758130302361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7800089728015355014139629 2925033648005758130302361)
                    ·
                      refine ⟨2193775236004318597726771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2925033648005758130302361 2193775236004318597726771)
                      ·
                        rfl

theorem cell23_4272362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 4, 1, 2, 3, 2].length) (baseStart_4272362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4272362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4272362 prefixEnd_4272362 := by exact prefixLift 4272362
  have htrace : WordTrace (prefixWord ++ tailWord_4272362) baseStart_4272362 baseEnd_4272362 := by
    simpa [prefixWord, tailWord_4272362, baseEnd_4272362] using wordTrace_append hprefix tailTrace_4272362
  have hstable : (prefixWord ++ tailWord_4272362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4272362).length < 2 ^ (prefixWord ++ tailWord_4272362).sum := by decide
  have hdescent : baseEnd_4272362 < baseStart_4272362 := by decide
  rcases family_descends (prefixWord ++ tailWord_4272362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4272368 : List Nat := [2, 1, 1, 1, 3, 1, 1, 3, 6, 4]
def baseStart_4272368 : Nat := 118140960795 + 4272368 * 2 ^ 59
def prefixEnd_4272368 : Nat := 4983230072969 + 3 ^ 40 * 4272368 * 2
def baseEnd_4272368 : Nat := 731259438962748524750581

theorem tailTrace_4272368 : CollatzResearch.WordTrace tailWord_4272368 prefixEnd_4272368 731259438962748524750581 := by
  unfold tailWord_4272368
  simp only [CollatzResearch.WordTrace]
  refine ⟨77913031292973936604060879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103884041723965248805414505 77913031292973936604060879)
  ·
    refine ⟨116869546939460904906091319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77913031292973936604060879 116869546939460904906091319)
    ·
      refine ⟨175304320409191357359136979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116869546939460904906091319 175304320409191357359136979)
      ·
        refine ⟨262956480613787036038705469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175304320409191357359136979 262956480613787036038705469)
        ·
          refine ⟨98608680230170138514514551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 262956480613787036038705469 98608680230170138514514551)
          ·
            refine ⟨147913020345255207771771827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98608680230170138514514551 147913020345255207771771827)
            ·
              refine ⟨221869530517882811657657741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 147913020345255207771771827 221869530517882811657657741)
              ·
                refine ⟨83201073944206054371621653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 221869530517882811657657741 83201073944206054371621653)
                ·
                  refine ⟨3900050341134658798669765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 83201073944206054371621653 3900050341134658798669765)
                  ·
                    refine ⟨731259438962748524750581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3900050341134658798669765 731259438962748524750581)
                    ·
                      rfl

theorem cell23_4272368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 3, 6, 4].length) (baseStart_4272368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4272368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4272368 prefixEnd_4272368 := by exact prefixLift 4272368
  have htrace : WordTrace (prefixWord ++ tailWord_4272368) baseStart_4272368 baseEnd_4272368 := by
    simpa [prefixWord, tailWord_4272368, baseEnd_4272368] using wordTrace_append hprefix tailTrace_4272368
  have hstable : (prefixWord ++ tailWord_4272368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4272368).length < 2 ^ (prefixWord ++ tailWord_4272368).sum := by decide
  have hdescent : baseEnd_4272368 < baseStart_4272368 := by decide
  rcases family_descends (prefixWord ++ tailWord_4272368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4272386 : List Nat := [3, 4, 1, 1, 2, 2, 1, 4, 1, 1, 3]
def baseStart_4272386 : Nat := 118140960795 + 4272386 * 2 ^ 59
def prefixEnd_4272386 : Nat := 4983230072969 + 3 ^ 40 * 4272386 * 2
def baseEnd_4272386 : Nat := 2193787559540026503826661

theorem tailTrace_4272386 : CollatzResearch.WordTrace tailWord_4272386 prefixEnd_4272386 2193787559540026503826661 := by
  unfold tailWord_4272386
  simp only [CollatzResearch.WordTrace]
  refine ⟨38956679774970665570569253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103884479399921774854851341 38956679774970665570569253)
  ·
    refine ⟨7304377457806999794481735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38956679774970665570569253 7304377457806999794481735)
    ·
      refine ⟨10956566186710499691722603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7304377457806999794481735 10956566186710499691722603)
      ·
        refine ⟨16434849280065749537583905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10956566186710499691722603 16434849280065749537583905)
        ·
          refine ⟨12326136960049312153187929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16434849280065749537583905 12326136960049312153187929)
          ·
            refine ⟨9244602720036984114890947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12326136960049312153187929 9244602720036984114890947)
            ·
              refine ⟨13866904080055476172336421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9244602720036984114890947 13866904080055476172336421)
              ·
                refine ⟨2600044515010401782313079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13866904080055476172336421 2600044515010401782313079)
                ·
                  refine ⟨3900066772515602673469619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2600044515010401782313079 3900066772515602673469619)
                  ·
                    refine ⟨5850100158773404010204429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3900066772515602673469619 5850100158773404010204429)
                    ·
                      refine ⟨2193787559540026503826661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5850100158773404010204429 2193787559540026503826661)
                      ·
                        rfl

theorem cell23_4272386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 4, 1, 1, 3].length) (baseStart_4272386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4272386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4272386 prefixEnd_4272386 := by exact prefixLift 4272386
  have htrace : WordTrace (prefixWord ++ tailWord_4272386) baseStart_4272386 baseEnd_4272386 := by
    simpa [prefixWord, tailWord_4272386, baseEnd_4272386] using wordTrace_append hprefix tailTrace_4272386
  have hstable : (prefixWord ++ tailWord_4272386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4272386).length < 2 ^ (prefixWord ++ tailWord_4272386).sum := by decide
  have hdescent : baseEnd_4272386 < baseStart_4272386 := by decide
  rcases family_descends (prefixWord ++ tailWord_4272386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4272415 : List Nat := [1, 1, 2, 4, 3, 2, 3, 7]
def baseStart_4272415 : Nat := 118140960795 + 4272415 * 2 ^ 59
def prefixEnd_4272415 : Nat := 4983230072969 + 3 ^ 40 * 4272415 * 2
def baseEnd_4272415 : Nat := 81251942610333588532001

theorem tailTrace_4272415 : CollatzResearch.WordTrace tailWord_4272415 prefixEnd_4272415 81251942610333588532001 := by
  unfold tailWord_4272415
  simp only [CollatzResearch.WordTrace]
  refine ⟨155827776816777600235082699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103885184544518400156721799 155827776816777600235082699)
  ·
    refine ⟨233741665225166400352624049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155827776816777600235082699 233741665225166400352624049)
    ·
      refine ⟨175306248918874800264468037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 233741665225166400352624049 175306248918874800264468037)
      ·
        refine ⟨32869921672289025049587757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 175306248918874800264468037 32869921672289025049587757)
        ·
          refine ⟨12326220627108384393595409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32869921672289025049587757 12326220627108384393595409)
          ·
            refine ⟨9244665470331288295196557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12326220627108384393595409 9244665470331288295196557)
            ·
              refine ⟨3466749551374233110698709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9244665470331288295196557 3466749551374233110698709)
              ·
                refine ⟨81251942610333588532001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3466749551374233110698709 81251942610333588532001)
                ·
                  rfl

theorem cell23_4272415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 3, 7].length) (baseStart_4272415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4272415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4272415 prefixEnd_4272415 := by exact prefixLift 4272415
  have htrace : WordTrace (prefixWord ++ tailWord_4272415) baseStart_4272415 baseEnd_4272415 := by
    simpa [prefixWord, tailWord_4272415, baseEnd_4272415] using wordTrace_append hprefix tailTrace_4272415
  have hstable : (prefixWord ++ tailWord_4272415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4272415).length < 2 ^ (prefixWord ++ tailWord_4272415).sum := by decide
  have hdescent : baseEnd_4272415 < baseStart_4272415 := by decide
  rcases family_descends (prefixWord ++ tailWord_4272415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4272423 : List Nat := [1, 1, 8, 1, 1, 2, 2, 1, 1, 5]
def baseStart_4272423 : Nat := 118140960795 + 4272423 * 2 ^ 59
def prefixEnd_4272423 : Nat := 4983230072969 + 3 ^ 40 * 4272423 * 2
def baseEnd_4272423 : Nat := 731268852774747619687997

theorem tailTrace_4272423 : CollatzResearch.WordTrace tailWord_4272423 prefixEnd_4272423 731268852774747619687997 := by
  unfold tailWord_4272423
  simp only [CollatzResearch.WordTrace]
  refine ⟨155828068600748617601373923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103885379067165745067582615 155828068600748617601373923)
  ·
    refine ⟨233742102901122926402060885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155828068600748617601373923 233742102901122926402060885)
    ·
      refine ⟨2739165268372534293774151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 233742102901122926402060885 2739165268372534293774151)
      ·
        refine ⟨4108747902558801440661227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2739165268372534293774151 4108747902558801440661227)
        ·
          refine ⟨6163121853838202160991841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4108747902558801440661227 6163121853838202160991841)
          ·
            refine ⟨4622341390378651620743881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6163121853838202160991841 4622341390378651620743881)
            ·
              refine ⟨3466756042783988715557911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4622341390378651620743881 3466756042783988715557911)
              ·
                refine ⟨5200134064175983073336867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3466756042783988715557911 5200134064175983073336867)
                ·
                  refine ⟨7800201096263974610005301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5200134064175983073336867 7800201096263974610005301)
                  ·
                    refine ⟨731268852774747619687997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7800201096263974610005301 731268852774747619687997)
                    ·
                      rfl

theorem cell23_4272423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_4272423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4272423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4272423 prefixEnd_4272423 := by exact prefixLift 4272423
  have htrace : WordTrace (prefixWord ++ tailWord_4272423) baseStart_4272423 baseEnd_4272423 := by
    simpa [prefixWord, tailWord_4272423, baseEnd_4272423] using wordTrace_append hprefix tailTrace_4272423
  have hstable : (prefixWord ++ tailWord_4272423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4272423).length < 2 ^ (prefixWord ++ tailWord_4272423).sum := by decide
  have hdescent : baseEnd_4272423 < baseStart_4272423 := by decide
  rcases family_descends (prefixWord ++ tailWord_4272423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4272426 : List Nat := [3, 1, 4, 2, 2, 2, 2, 1, 1, 1, 4]
def baseStart_4272426 : Nat := 118140960795 + 4272426 * 2 ^ 59
def prefixEnd_4272426 : Nat := 4983230072969 + 3 ^ 40 * 4272426 * 2
def baseEnd_4272426 : Nat := 2193808098766206347326477

theorem tailTrace_4272426 : CollatzResearch.WordTrace tailWord_4272426 prefixEnd_4272426 2193808098766206347326477 := by
  unfold tailWord_4272426
  simp only [CollatzResearch.WordTrace]
  refine ⟨38957044504934437278433283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103885452013158499409155421 38957044504934437278433283)
  ·
    refine ⟨58435566757401655917649925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38957044504934437278433283 58435566757401655917649925)
    ·
      refine ⟨10956668767012810484559361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58435566757401655917649925 10956668767012810484559361)
      ·
        refine ⟨8217501575259607863419521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10956668767012810484559361 8217501575259607863419521)
        ·
          refine ⟨6163126181444705897564641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8217501575259607863419521 6163126181444705897564641)
          ·
            refine ⟨4622344636083529423173481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6163126181444705897564641 4622344636083529423173481)
            ·
              refine ⟨3466758477062647067380111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4622344636083529423173481 3466758477062647067380111)
              ·
                refine ⟨5200137715593970601070167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3466758477062647067380111 5200137715593970601070167)
                ·
                  refine ⟨7800206573390955901605251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5200137715593970601070167 7800206573390955901605251)
                  ·
                    refine ⟨11700309860086433852407877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7800206573390955901605251 11700309860086433852407877)
                    ·
                      refine ⟨2193808098766206347326477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11700309860086433852407877 2193808098766206347326477)
                      ·
                        rfl

theorem cell23_4272426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 2, 1, 1, 1, 4].length) (baseStart_4272426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4272426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4272426 prefixEnd_4272426 := by exact prefixLift 4272426
  have htrace : WordTrace (prefixWord ++ tailWord_4272426) baseStart_4272426 baseEnd_4272426 := by
    simpa [prefixWord, tailWord_4272426, baseEnd_4272426] using wordTrace_append hprefix tailTrace_4272426
  have hstable : (prefixWord ++ tailWord_4272426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4272426).length < 2 ^ (prefixWord ++ tailWord_4272426).sum := by decide
  have hdescent : baseEnd_4272426 < baseStart_4272426 := by decide
  rcases family_descends (prefixWord ++ tailWord_4272426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4272442 : List Nat := [3, 1, 1, 1, 4, 3, 1, 1, 4, 1, 3]
def baseStart_4272442 : Nat := 118140960795 + 4272442 * 2 ^ 59
def prefixEnd_4272442 : Nat := 4983230072969 + 3 ^ 40 * 4272442 * 2
def baseEnd_4272442 : Nat := 2193816314456678284726403

theorem tailTrace_4272442 : CollatzResearch.WordTrace tailWord_4272442 prefixEnd_4272442 2193816314456678284726403 := by
  unfold tailWord_4272442
  simp only [CollatzResearch.WordTrace]
  refine ⟨38957190396919945961578895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103885841058453189230877053 38957190396919945961578895)
  ·
    refine ⟨58435785595379918942368343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38957190396919945961578895 58435785595379918942368343)
    ·
      refine ⟨87653678393069878413552515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58435785595379918942368343 87653678393069878413552515)
      ·
        refine ⟨131480517589604817620328773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87653678393069878413552515 131480517589604817620328773)
        ·
          refine ⟨24652597048050903303811645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 131480517589604817620328773 24652597048050903303811645)
          ·
            refine ⟨9244723893019088738929367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24652597048050903303811645 9244723893019088738929367)
            ·
              refine ⟨13867085839528633108394051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9244723893019088738929367 13867085839528633108394051)
              ·
                refine ⟨20800628759292949662591077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13867085839528633108394051 20800628759292949662591077)
                ·
                  refine ⟨3900117892367428061735827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20800628759292949662591077 3900117892367428061735827)
                  ·
                    refine ⟨5850176838551142092603741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3900117892367428061735827 5850176838551142092603741)
                    ·
                      refine ⟨2193816314456678284726403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5850176838551142092603741 2193816314456678284726403)
                      ·
                        rfl

theorem cell23_4272442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 1, 4, 1, 3].length) (baseStart_4272442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4272442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4272442 prefixEnd_4272442 := by exact prefixLift 4272442
  have htrace : WordTrace (prefixWord ++ tailWord_4272442) baseStart_4272442 baseEnd_4272442 := by
    simpa [prefixWord, tailWord_4272442, baseEnd_4272442] using wordTrace_append hprefix tailTrace_4272442
  have hstable : (prefixWord ++ tailWord_4272442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4272442).length < 2 ^ (prefixWord ++ tailWord_4272442).sum := by decide
  have hdescent : baseEnd_4272442 < baseStart_4272442 := by decide
  rcases family_descends (prefixWord ++ tailWord_4272442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4272448 : List Nat := [2, 1, 1, 2, 2, 1, 2, 3, 2, 3, 4]
def baseStart_4272448 : Nat := 118140960795 + 4272448 * 2 ^ 59
def prefixEnd_4272448 : Nat := 4983230072969 + 3 ^ 40 * 4272448 * 2
def baseEnd_4272448 : Nat := 2193819395340605261251375

theorem tailTrace_4272448 : CollatzResearch.WordTrace tailWord_4272448 prefixEnd_4272448 2193819395340605261251375 := by
  unfold tailWord_4272448
  simp only [CollatzResearch.WordTrace]
  refine ⟨77914490212829023435516999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103885986950438697914022665 77914490212829023435516999)
  ·
    refine ⟨116871735319243535153275499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77914490212829023435516999 116871735319243535153275499)
    ·
      refine ⟨175307602978865302729913249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116871735319243535153275499 175307602978865302729913249)
      ·
        refine ⟨131480702234148977047434937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 175307602978865302729913249 131480702234148977047434937)
        ·
          refine ⟨98610526675611732785576203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 131480702234148977047434937 98610526675611732785576203)
          ·
            refine ⟨147915790013417599178364305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98610526675611732785576203 147915790013417599178364305)
            ·
              refine ⟨110936842510063199383773229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 147915790013417599178364305 110936842510063199383773229)
              ·
                refine ⟨41601315941273699768914961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 110936842510063199383773229 41601315941273699768914961)
                ·
                  refine ⟨31200986955955274826686221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41601315941273699768914961 31200986955955274826686221)
                  ·
                    refine ⟨11700370108483228060007333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 31200986955955274826686221 11700370108483228060007333)
                    ·
                      refine ⟨2193819395340605261251375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11700370108483228060007333 2193819395340605261251375)
                      ·
                        rfl

theorem cell23_4272448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 3, 2, 3, 4].length) (baseStart_4272448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4272448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4272448 prefixEnd_4272448 := by exact prefixLift 4272448
  have htrace : WordTrace (prefixWord ++ tailWord_4272448) baseStart_4272448 baseEnd_4272448 := by
    simpa [prefixWord, tailWord_4272448, baseEnd_4272448] using wordTrace_append hprefix tailTrace_4272448
  have hstable : (prefixWord ++ tailWord_4272448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4272448).length < 2 ^ (prefixWord ++ tailWord_4272448).sum := by decide
  have hdescent : baseEnd_4272448 < baseStart_4272448 := by decide
  rcases family_descends (prefixWord ++ tailWord_4272448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4272485 : List Nat := [1, 3, 1, 3, 1, 4, 1, 1, 2, 1, 5]
def baseStart_4272485 : Nat := 118140960795 + 4272485 * 2 ^ 59
def prefixEnd_4272485 : Nat := 4983230072969 + 3 ^ 40 * 4272485 * 2
def baseEnd_4272485 : Nat := 2193838394124821616488705

theorem tailTrace_4272485 : CollatzResearch.WordTrace tailWord_4272485 prefixEnd_4272485 2193838394124821616488705 := by
  unfold tailWord_4272485
  simp only [CollatzResearch.WordTrace]
  refine ⟨155830329926524002190130909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103886886617682668126753939 155830329926524002190130909)
  ·
    refine ⟨58436373722446500821299091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 155830329926524002190130909 58436373722446500821299091)
    ·
      refine ⟨87654560583669751231948637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58436373722446500821299091 87654560583669751231948637)
      ·
        refine ⟨32870460218876156711980739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87654560583669751231948637 32870460218876156711980739)
        ·
          refine ⟨49305690328314235067971109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32870460218876156711980739 49305690328314235067971109)
          ·
            refine ⟨9244816936558919075244583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49305690328314235067971109 9244816936558919075244583)
            ·
              refine ⟨13867225404838378612866875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9244816936558919075244583 13867225404838378612866875)
              ·
                refine ⟨20800838107257567919300313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13867225404838378612866875 20800838107257567919300313)
                ·
                  refine ⟨15600628580443175939475235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20800838107257567919300313 15600628580443175939475235)
                  ·
                    refine ⟨23400942870664763909212853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15600628580443175939475235 23400942870664763909212853)
                    ·
                      refine ⟨2193838394124821616488705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23400942870664763909212853 2193838394124821616488705)
                      ·
                        rfl

theorem cell23_4272485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 1, 2, 1, 5].length) (baseStart_4272485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4272485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4272485 prefixEnd_4272485 := by exact prefixLift 4272485
  have htrace : WordTrace (prefixWord ++ tailWord_4272485) baseStart_4272485 baseEnd_4272485 := by
    simpa [prefixWord, tailWord_4272485, baseEnd_4272485] using wordTrace_append hprefix tailTrace_4272485
  have hstable : (prefixWord ++ tailWord_4272485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4272485).length < 2 ^ (prefixWord ++ tailWord_4272485).sum := by decide
  have hdescent : baseEnd_4272485 < baseStart_4272485 := by decide
  rcases family_descends (prefixWord ++ tailWord_4272485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4272508 : List Nat := [2, 2, 2, 1, 1, 1, 2, 1, 2, 1, 8]
def baseStart_4272508 : Nat := 118140960795 + 4272508 * 2 ^ 59
def prefixEnd_4272508 : Nat := 4983230072969 + 3 ^ 40 * 4272508 * 2
def baseEnd_4272508 : Nat := 2193850204179875026501099

theorem tailTrace_4272508 : CollatzResearch.WordTrace tailWord_4272508 prefixEnd_4272508 2193850204179875026501099 := by
  unfold tailWord_4272508
  simp only [CollatzResearch.WordTrace]
  refine ⟨77915584402720338559109089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103887445870293784745478785 77915584402720338559109089)
  ·
    refine ⟨58436688302040253919331817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77915584402720338559109089 58436688302040253919331817)
    ·
      refine ⟨43827516226530190439498863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58436688302040253919331817 43827516226530190439498863)
      ·
        refine ⟨65741274339795285659248295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43827516226530190439498863 65741274339795285659248295)
        ·
          refine ⟨98611911509692928488872443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65741274339795285659248295 98611911509692928488872443)
          ·
            refine ⟨147917867264539392733308665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98611911509692928488872443 147917867264539392733308665)
            ·
              refine ⟨110938400448404544549981499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 147917867264539392733308665 110938400448404544549981499)
              ·
                refine ⟨166407600672606816824972249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 110938400448404544549981499 166407600672606816824972249)
                ·
                  refine ⟨124805700504455112618729187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 166407600672606816824972249 124805700504455112618729187)
                  ·
                    refine ⟨187208550756682668928093781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 124805700504455112618729187 187208550756682668928093781)
                    ·
                      refine ⟨2193850204179875026501099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 187208550756682668928093781 2193850204179875026501099)
                      ·
                        rfl

theorem cell23_4272508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 2, 1, 8].length) (baseStart_4272508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4272508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4272508 prefixEnd_4272508 := by exact prefixLift 4272508
  have htrace : WordTrace (prefixWord ++ tailWord_4272508) baseStart_4272508 baseEnd_4272508 := by
    simpa [prefixWord, tailWord_4272508, baseEnd_4272508] using wordTrace_append hprefix tailTrace_4272508
  have hstable : (prefixWord ++ tailWord_4272508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4272508).length < 2 ^ (prefixWord ++ tailWord_4272508).sum := by decide
  have hdescent : baseEnd_4272508 < baseStart_4272508 := by decide
  rcases family_descends (prefixWord ++ tailWord_4272508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4272528 : List Nat := [2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 5]
def baseStart_4272528 : Nat := 118140960795 + 4272528 * 2 ^ 59
def prefixEnd_4272528 : Nat := 4983230072969 + 3 ^ 40 * 4272528 * 2
def baseEnd_4272528 : Nat := 2193860473792964948251007

theorem tailTrace_4272528 : CollatzResearch.WordTrace tailWord_4272528 prefixEnd_4272528 2193860473792964948251007 := by
  unfold tailWord_4272528
  simp only [CollatzResearch.WordTrace]
  refine ⟨77915949132684110266973119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103887932176912147022630825 77915949132684110266973119)
  ·
    refine ⟨116873923699026165400459679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77915949132684110266973119 116873923699026165400459679)
    ·
      refine ⟨175310885548539248100689519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116873923699026165400459679 175310885548539248100689519)
      ·
        refine ⟨262966328322808872151034279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175310885548539248100689519 262966328322808872151034279)
        ·
          refine ⟨394449492484213308226551419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 262966328322808872151034279 394449492484213308226551419)
          ·
            refine ⟨591674238726319962339827129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 394449492484213308226551419 591674238726319962339827129)
            ·
              refine ⟨443755679044739971754870347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 591674238726319962339827129 443755679044739971754870347)
              ·
                refine ⟨665633518567109957632305521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 443755679044739971754870347 665633518567109957632305521)
                ·
                  refine ⟨499225138925332468224229141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 665633518567109957632305521 499225138925332468224229141)
                  ·
                    refine ⟨23401178387124959448010741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 499225138925332468224229141 23401178387124959448010741)
                    ·
                      refine ⟨2193860473792964948251007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23401178387124959448010741 2193860473792964948251007)
                      ·
                        rfl

theorem cell23_4272528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 5].length) (baseStart_4272528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4272528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4272528 prefixEnd_4272528 := by exact prefixLift 4272528
  have htrace : WordTrace (prefixWord ++ tailWord_4272528) baseStart_4272528 baseEnd_4272528 := by
    simpa [prefixWord, tailWord_4272528, baseEnd_4272528] using wordTrace_append hprefix tailTrace_4272528
  have hstable : (prefixWord ++ tailWord_4272528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4272528).length < 2 ^ (prefixWord ++ tailWord_4272528).sum := by decide
  have hdescent : baseEnd_4272528 < baseStart_4272528 := by decide
  rcases family_descends (prefixWord ++ tailWord_4272528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4272535 : List Nat := [1, 1, 3, 3, 1, 1, 3, 3, 2, 5]
def baseStart_4272535 : Nat := 118140960795 + 4272535 * 2 ^ 59
def prefixEnd_4272535 : Nat := 4983230072969 + 3 ^ 40 * 4272535 * 2
def baseEnd_4272535 : Nat := 731288022719182140287825

theorem tailTrace_4272535 : CollatzResearch.WordTrace tailWord_4272535 prefixEnd_4272535 731288022719182140287825 := by
  unfold tailWord_4272535
  simp only [CollatzResearch.WordTrace]
  refine ⟨155832153576342860729451059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103888102384228573819634039 155832153576342860729451059)
  ·
    refine ⟨233748230364514291094176589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155832153576342860729451059 233748230364514291094176589)
    ·
      refine ⟨87655586386692859160316221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 233748230364514291094176589 87655586386692859160316221)
      ·
        refine ⟨32870844895009822185118583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87655586386692859160316221 32870844895009822185118583)
        ·
          refine ⟨49306267342514733277677875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32870844895009822185118583 49306267342514733277677875)
          ·
            refine ⟨73959401013772099916516813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49306267342514733277677875 73959401013772099916516813)
            ·
              refine ⟨27734775380164537468693805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 73959401013772099916516813 27734775380164537468693805)
              ·
                refine ⟨10400540767561701550760177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27734775380164537468693805 10400540767561701550760177)
                ·
                  refine ⟨7800405575671276163070133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10400540767561701550760177 7800405575671276163070133)
                  ·
                    refine ⟨731288022719182140287825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7800405575671276163070133 731288022719182140287825)
                    ·
                      rfl

theorem cell23_4272535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 3, 2, 5].length) (baseStart_4272535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4272535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4272535 prefixEnd_4272535 := by exact prefixLift 4272535
  have htrace : WordTrace (prefixWord ++ tailWord_4272535) baseStart_4272535 baseEnd_4272535 := by
    simpa [prefixWord, tailWord_4272535, baseEnd_4272535] using wordTrace_append hprefix tailTrace_4272535
  have hstable : (prefixWord ++ tailWord_4272535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4272535).length < 2 ^ (prefixWord ++ tailWord_4272535).sum := by decide
  have hdescent : baseEnd_4272535 < baseStart_4272535 := by decide
  rcases family_descends (prefixWord ++ tailWord_4272535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4272615 : List Nat := [1, 1, 5, 2, 1, 1, 1, 1, 1, 1, 8]
def baseStart_4272615 : Nat := 118140960795 + 4272615 * 2 ^ 59
def prefixEnd_4272615 : Nat := 4983230072969 + 3 ^ 40 * 4272615 * 2
def baseEnd_4272615 : Nat := 2193905146609906107863107

theorem tailTrace_4272615 : CollatzResearch.WordTrace tailWord_4272615 prefixEnd_4272615 2193905146609906107863107 := by
  unfold tailWord_4272615
  simp only [CollatzResearch.WordTrace]
  refine ⟨155835071416053034392363299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103890047610702022928242199 155835071416053034392363299)
  ·
    refine ⟨233752607124079551588544949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155835071416053034392363299 233752607124079551588544949)
    ·
      refine ⟨21914306917882457961426089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 233752607124079551588544949 21914306917882457961426089)
      ·
        refine ⟨16435730188411843471069567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21914306917882457961426089 16435730188411843471069567)
        ·
          refine ⟨24653595282617765206604351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16435730188411843471069567 24653595282617765206604351)
          ·
            refine ⟨36980392923926647809906527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24653595282617765206604351 36980392923926647809906527)
            ·
              refine ⟨55470589385889971714859791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36980392923926647809906527 55470589385889971714859791)
              ·
                refine ⟨83205884078834957572289687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55470589385889971714859791 83205884078834957572289687)
                ·
                  refine ⟨124808826118252436358434531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 83205884078834957572289687 124808826118252436358434531)
                  ·
                    refine ⟨187213239177378654537651797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 124808826118252436358434531 187213239177378654537651797)
                    ·
                      refine ⟨2193905146609906107863107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 187213239177378654537651797 2193905146609906107863107)
                      ·
                        rfl

theorem cell23_4272615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 1, 1, 1, 8].length) (baseStart_4272615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4272615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4272615 prefixEnd_4272615 := by exact prefixLift 4272615
  have htrace : WordTrace (prefixWord ++ tailWord_4272615) baseStart_4272615 baseEnd_4272615 := by
    simpa [prefixWord, tailWord_4272615, baseEnd_4272615] using wordTrace_append hprefix tailTrace_4272615
  have hstable : (prefixWord ++ tailWord_4272615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4272615).length < 2 ^ (prefixWord ++ tailWord_4272615).sum := by decide
  have hdescent : baseEnd_4272615 < baseStart_4272615 := by decide
  rcases family_descends (prefixWord ++ tailWord_4272615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4272632 : List Nat := [2, 1, 2, 1, 1, 4, 1, 1, 3, 5, 2]
def baseStart_4272632 : Nat := 118140960795 + 4272632 * 2 ^ 59
def prefixEnd_4272632 : Nat := 4983230072969 + 3 ^ 40 * 4272632 * 2
def baseEnd_4272632 : Nat := 2193913875781032541350529

theorem tailTrace_4272632 : CollatzResearch.WordTrace tailWord_4272632 prefixEnd_4272632 2193913875781032541350529 := by
  unfold tailWord_4272632
  simp only [CollatzResearch.WordTrace]
  refine ⟨77917845728495723147866075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103890460971327630863821433 77917845728495723147866075)
  ·
    refine ⟨116876768592743584721799113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77917845728495723147866075 116876768592743584721799113)
    ·
      refine ⟨87657576444557688541349335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116876768592743584721799113 87657576444557688541349335)
      ·
        refine ⟨131486364666836532812024003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87657576444557688541349335 131486364666836532812024003)
        ·
          refine ⟨197229547000254799218036005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131486364666836532812024003 197229547000254799218036005)
          ·
            refine ⟨36980540062547774853381751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 197229547000254799218036005 36980540062547774853381751)
            ·
              refine ⟨55470810093821662280072627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36980540062547774853381751 55470810093821662280072627)
              ·
                refine ⟨83206215140732493420108941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55470810093821662280072627 83206215140732493420108941)
                ·
                  refine ⟨31202330677774685032540853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 83206215140732493420108941 31202330677774685032540853)
                  ·
                    refine ⟨2925218501041376721800705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31202330677774685032540853 2925218501041376721800705)
                    ·
                      refine ⟨2193913875781032541350529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2925218501041376721800705 2193913875781032541350529)
                      ·
                        rfl

theorem cell23_4272632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 1, 3, 5, 2].length) (baseStart_4272632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4272632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4272632 prefixEnd_4272632 := by exact prefixLift 4272632
  have htrace : WordTrace (prefixWord ++ tailWord_4272632) baseStart_4272632 baseEnd_4272632 := by
    simpa [prefixWord, tailWord_4272632, baseEnd_4272632] using wordTrace_append hprefix tailTrace_4272632
  have hstable : (prefixWord ++ tailWord_4272632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4272632).length < 2 ^ (prefixWord ++ tailWord_4272632).sum := by decide
  have hdescent : baseEnd_4272632 < baseStart_4272632 := by decide
  rcases family_descends (prefixWord ++ tailWord_4272632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4272646 : List Nat := [6, 2, 1, 1, 1, 1, 1, 2, 8]
def baseStart_4272646 : Nat := 118140960795 + 4272646 * 2 ^ 59
def prefixEnd_4272646 : Nat := 4983230072969 + 3 ^ 40 * 4272646 * 2
def baseEnd_4272646 : Nat := 243769007167799498508385

theorem tailTrace_4272646 : CollatzResearch.WordTrace tailWord_4272646 prefixEnd_4272646 243769007167799498508385 := by
  unfold tailWord_4272646
  simp only [CollatzResearch.WordTrace]
  refine ⟨4869881314966897708960681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 103890801385960484457827861 4869881314966897708960681)
  ·
    refine ⟨3652410986225173281720511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4869881314966897708960681 3652410986225173281720511)
    ·
      refine ⟨5478616479337759922580767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3652410986225173281720511 5478616479337759922580767)
      ·
        refine ⟨8217924719006639883871151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5478616479337759922580767 8217924719006639883871151)
        ·
          refine ⟨12326887078509959825806727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8217924719006639883871151 12326887078509959825806727)
          ·
            refine ⟨18490330617764939738710091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12326887078509959825806727 18490330617764939738710091)
            ·
              refine ⟨27735495926647409608065137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18490330617764939738710091 27735495926647409608065137)
              ·
                refine ⟨20801621944985557206048853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27735495926647409608065137 20801621944985557206048853)
                ·
                  refine ⟨243769007167799498508385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20801621944985557206048853 243769007167799498508385)
                  ·
                    rfl

theorem cell23_4272646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 2, 8].length) (baseStart_4272646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4272646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4272646 prefixEnd_4272646 := by exact prefixLift 4272646
  have htrace : WordTrace (prefixWord ++ tailWord_4272646) baseStart_4272646 baseEnd_4272646 := by
    simpa [prefixWord, tailWord_4272646, baseEnd_4272646] using wordTrace_append hprefix tailTrace_4272646
  have hstable : (prefixWord ++ tailWord_4272646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4272646).length < 2 ^ (prefixWord ++ tailWord_4272646).sum := by decide
  have hdescent : baseEnd_4272646 < baseStart_4272646 := by decide
  rcases family_descends (prefixWord ++ tailWord_4272646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4272665 : List Nat := [1, 2, 1, 2, 1, 1, 2, 2, 5, 1, 5]
def baseStart_4272665 : Nat := 118140960795 + 4272665 * 2 ^ 59
def prefixEnd_4272665 : Nat := 4983230072969 + 3 ^ 40 * 4272665 * 2
def baseEnd_4272665 : Nat := 2193930820642630912237877

theorem tailTrace_4272665 : CollatzResearch.WordTrace tailWord_4272665 prefixEnd_4272665 2193930820642630912237877 := by
  unfold tailWord_4272665
  simp only [CollatzResearch.WordTrace]
  refine ⟨155836895065871892931683449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103891263377247928621122299 155836895065871892931683449)
  ·
    refine ⟨116877671299403919698762587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155836895065871892931683449 116877671299403919698762587)
    ·
      refine ⟨175316506949105879548143881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116877671299403919698762587 175316506949105879548143881)
      ·
        refine ⟨131487380211829409661107911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 175316506949105879548143881 131487380211829409661107911)
        ·
          refine ⟨197231070317744114491661867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131487380211829409661107911 197231070317744114491661867)
          ·
            refine ⟨295846605476616171737492801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 197231070317744114491661867 295846605476616171737492801)
            ·
              refine ⟨221884954107462128803119601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 295846605476616171737492801 221884954107462128803119601)
              ·
                refine ⟨166413715580596596602339701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 221884954107462128803119601 166413715580596596602339701)
                ·
                  refine ⟨15601285835680930931469347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 166413715580596596602339701 15601285835680930931469347)
                  ·
                    refine ⟨23401928753521396397204021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15601285835680930931469347 23401928753521396397204021)
                    ·
                      refine ⟨2193930820642630912237877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23401928753521396397204021 2193930820642630912237877)
                      ·
                        rfl

theorem cell23_4272665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 2, 5, 1, 5].length) (baseStart_4272665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4272665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4272665 prefixEnd_4272665 := by exact prefixLift 4272665
  have htrace : WordTrace (prefixWord ++ tailWord_4272665) baseStart_4272665 baseEnd_4272665 := by
    simpa [prefixWord, tailWord_4272665, baseEnd_4272665] using wordTrace_append hprefix tailTrace_4272665
  have hstable : (prefixWord ++ tailWord_4272665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4272665).length < 2 ^ (prefixWord ++ tailWord_4272665).sum := by decide
  have hdescent : baseEnd_4272665 < baseStart_4272665 := by decide
  rcases family_descends (prefixWord ++ tailWord_4272665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4272673 : List Nat := [1, 2, 3, 2, 2, 1, 5, 2, 1, 1, 3]
def baseStart_4272673 : Nat := 118140960795 + 4272673 * 2 ^ 59
def prefixEnd_4272673 : Nat := 4983230072969 + 3 ^ 40 * 4272673 * 2
def baseEnd_4272673 : Nat := 2193934928487866880937841

theorem tailTrace_4272673 : CollatzResearch.WordTrace tailWord_4272673 prefixEnd_4272673 2193934928487866880937841 := by
  unfold tailWord_4272673
  simp only [CollatzResearch.WordTrace]
  refine ⟨155837186849842910297974673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103891457899895273531983115 155837186849842910297974673)
  ·
    refine ⟨116877890137382182723481005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155837186849842910297974673 116877890137382182723481005)
    ·
      refine ⟨43829208801518318521305377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 116877890137382182723481005 43829208801518318521305377)
      ·
        refine ⟨32871906601138738890979033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43829208801518318521305377 32871906601138738890979033)
        ·
          refine ⟨24653929950854054168234275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32871906601138738890979033 24653929950854054168234275)
          ·
            refine ⟨36980894926281081252351413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24653929950854054168234275 36980894926281081252351413)
            ·
              refine ⟨3466958899338851367407945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36980894926281081252351413 3466958899338851367407945)
              ·
                refine ⟨2600219174504138525555959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3466958899338851367407945 2600219174504138525555959)
                ·
                  refine ⟨3900328761756207788333939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2600219174504138525555959 3900328761756207788333939)
                  ·
                    refine ⟨5850493142634311682500909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3900328761756207788333939 5850493142634311682500909)
                    ·
                      refine ⟨2193934928487866880937841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5850493142634311682500909 2193934928487866880937841)
                      ·
                        rfl

theorem cell23_4272673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 5, 2, 1, 1, 3].length) (baseStart_4272673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4272673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4272673 prefixEnd_4272673 := by exact prefixLift 4272673
  have htrace : WordTrace (prefixWord ++ tailWord_4272673) baseStart_4272673 baseEnd_4272673 := by
    simpa [prefixWord, tailWord_4272673, baseEnd_4272673] using wordTrace_append hprefix tailTrace_4272673
  have hstable : (prefixWord ++ tailWord_4272673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4272673).length < 2 ^ (prefixWord ++ tailWord_4272673).sum := by decide
  have hdescent : baseEnd_4272673 < baseStart_4272673 := by decide
  rcases family_descends (prefixWord ++ tailWord_4272673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4272716 : List Nat := [2, 2, 1, 3, 1, 2, 5, 1, 1, 2, 3]
def baseStart_4272716 : Nat := 118140960795 + 4272716 * 2 ^ 59
def prefixEnd_4272716 : Nat := 4983230072969 + 3 ^ 40 * 4272716 * 2
def baseEnd_4272716 : Nat := 2193957008156010212700143

theorem tailTrace_4272716 : CollatzResearch.WordTrace tailWord_4272716 prefixEnd_4272716 2193957008156010212700143 := by
  unfold tailWord_4272716
  simp only [CollatzResearch.WordTrace]
  refine ⟨77919377594343564320895001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103892503459124752427860001 77919377594343564320895001)
  ·
    refine ⟨58439533195757673240671251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77919377594343564320895001 58439533195757673240671251)
    ·
      refine ⟨87659299793636509861006877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58439533195757673240671251 87659299793636509861006877)
      ·
        refine ⟨32872237422613691197877579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87659299793636509861006877 32872237422613691197877579)
        ·
          refine ⟨49308356133920536796816369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32872237422613691197877579 49308356133920536796816369)
          ·
            refine ⟨36981267100440402597612277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49308356133920536796816369 36981267100440402597612277)
            ·
              refine ⟨3466993790666287743526151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36981267100440402597612277 3466993790666287743526151)
              ·
                refine ⟨5200490685999431615289227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3466993790666287743526151 5200490685999431615289227)
                ·
                  refine ⟨7800736028999147422933841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5200490685999431615289227 7800736028999147422933841)
                  ·
                    refine ⟨5850552021749360567200381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7800736028999147422933841 5850552021749360567200381)
                    ·
                      refine ⟨2193957008156010212700143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5850552021749360567200381 2193957008156010212700143)
                      ·
                        rfl

theorem cell23_4272716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 5, 1, 1, 2, 3].length) (baseStart_4272716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4272716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4272716 prefixEnd_4272716 := by exact prefixLift 4272716
  have htrace : WordTrace (prefixWord ++ tailWord_4272716) baseStart_4272716 baseEnd_4272716 := by
    simpa [prefixWord, tailWord_4272716, baseEnd_4272716] using wordTrace_append hprefix tailTrace_4272716
  have hstable : (prefixWord ++ tailWord_4272716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4272716).length < 2 ^ (prefixWord ++ tailWord_4272716).sum := by decide
  have hdescent : baseEnd_4272716 < baseStart_4272716 := by decide
  rcases family_descends (prefixWord ++ tailWord_4272716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4272739 : List Nat := [1, 1, 1, 5, 1, 2, 1, 1, 5, 3, 2]
def baseStart_4272739 : Nat := 118140960795 + 4272739 * 2 ^ 59
def prefixEnd_4272739 : Nat := 4983230072969 + 3 ^ 40 * 4272739 * 2
def baseEnd_4272739 : Nat := 2193968818211063622712537

theorem tailTrace_4272739 : CollatzResearch.WordTrace tailWord_4272739 prefixEnd_4272739 2193968818211063622712537 := by
  unfold tailWord_4272739
  simp only [CollatzResearch.WordTrace]
  refine ⟨155839594067603803569877271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103893062711735869046584847 155839594067603803569877271)
  ·
    refine ⟨233759391101405705354815907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155839594067603803569877271 233759391101405705354815907)
    ·
      refine ⟨350639086652108558032223861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 233759391101405705354815907 350639086652108558032223861)
      ·
        refine ⟨32872414373635177315520987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 350639086652108558032223861 32872414373635177315520987)
        ·
          refine ⟨49308621560452765973281481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32872414373635177315520987 49308621560452765973281481)
          ·
            refine ⟨36981466170339574479961111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49308621560452765973281481 36981466170339574479961111)
            ·
              refine ⟨55472199255509361719941667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36981466170339574479961111 55472199255509361719941667)
              ·
                refine ⟨83208298883264042579912501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55472199255509361719941667 83208298883264042579912501)
                ·
                  refine ⟨7800778020306003991866797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 83208298883264042579912501 7800778020306003991866797)
                  ·
                    refine ⟨2925291757614751496950049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7800778020306003991866797 2925291757614751496950049)
                    ·
                      refine ⟨2193968818211063622712537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2925291757614751496950049 2193968818211063622712537)
                      ·
                        rfl

theorem cell23_4272739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 1, 5, 3, 2].length) (baseStart_4272739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4272739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4272739 prefixEnd_4272739 := by exact prefixLift 4272739
  have htrace : WordTrace (prefixWord ++ tailWord_4272739) baseStart_4272739 baseEnd_4272739 := by
    simpa [prefixWord, tailWord_4272739, baseEnd_4272739] using wordTrace_append hprefix tailTrace_4272739
  have hstable : (prefixWord ++ tailWord_4272739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4272739).length < 2 ^ (prefixWord ++ tailWord_4272739).sum := by decide
  have hdescent : baseEnd_4272739 < baseStart_4272739 := by decide
  rcases family_descends (prefixWord ++ tailWord_4272739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4272746 : List Nat := [3, 1, 3, 2, 1, 1, 1, 5, 2, 1, 3]
def baseStart_4272746 : Nat := 118140960795 + 4272746 * 2 ^ 59
def prefixEnd_4272746 : Nat := 4983230072969 + 3 ^ 40 * 4272746 * 2
def baseEnd_4272746 : Nat := 2193972412575645095325005

theorem tailTrace_4272746 : CollatzResearch.WordTrace tailWord_4272746 prefixEnd_4272746 2193972412575645095325005 := by
  unfold tailWord_4272746
  simp only [CollatzResearch.WordTrace]
  refine ⟨38959962344644610941345523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103893232919052295843588061 38959962344644610941345523)
  ·
    refine ⟨58439943516966916412018285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38959962344644610941345523 58439943516966916412018285)
    ·
      refine ⟨21914978818862593654506857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58439943516966916412018285 21914978818862593654506857)
      ·
        refine ⟨16436234114146945240880143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21914978818862593654506857 16436234114146945240880143)
        ·
          refine ⟨24654351171220417861320215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16436234114146945240880143 24654351171220417861320215)
          ·
            refine ⟨36981526756830626791980323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24654351171220417861320215 36981526756830626791980323)
            ·
              refine ⟨55472290135245940187970485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36981526756830626791980323 55472290135245940187970485)
              ·
                refine ⟨5200527200179306892622233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 55472290135245940187970485 5200527200179306892622233)
                ·
                  refine ⟨3900395400134480169466675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5200527200179306892622233 3900395400134480169466675)
                  ·
                    refine ⟨5850593100201720254200013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3900395400134480169466675 5850593100201720254200013)
                    ·
                      refine ⟨2193972412575645095325005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5850593100201720254200013 2193972412575645095325005)
                      ·
                        rfl

theorem cell23_4272746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 5, 2, 1, 3].length) (baseStart_4272746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4272746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4272746 prefixEnd_4272746 := by exact prefixLift 4272746
  have htrace : WordTrace (prefixWord ++ tailWord_4272746) baseStart_4272746 baseEnd_4272746 := by
    simpa [prefixWord, tailWord_4272746, baseEnd_4272746] using wordTrace_append hprefix tailTrace_4272746
  have hstable : (prefixWord ++ tailWord_4272746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4272746).length < 2 ^ (prefixWord ++ tailWord_4272746).sum := by decide
  have hdescent : baseEnd_4272746 < baseStart_4272746 := by decide
  rcases family_descends (prefixWord ++ tailWord_4272746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4272773 : List Nat := [1, 3, 1, 1, 4, 2, 4, 1, 1, 3, 2]
def baseStart_4272773 : Nat := 118140960795 + 4272773 * 2 ^ 59
def prefixEnd_4272773 : Nat := 4983230072969 + 3 ^ 40 * 4272773 * 2
def baseEnd_4272773 : Nat := 2193986276553316489687381

theorem tailTrace_4272773 : CollatzResearch.WordTrace tailWord_4272773 prefixEnd_4272773 2193986276553316489687381 := by
  unfold tailWord_4272773
  simp only [CollatzResearch.WordTrace]
  refine ⟨155840834149480627376614973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103893889432987084917743315 155840834149480627376614973)
  ·
    refine ⟨58440312806055235266230615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 155840834149480627376614973 58440312806055235266230615)
    ·
      refine ⟨87660469209082852899345923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58440312806055235266230615 87660469209082852899345923)
      ·
        refine ⟨131490703813624279349018885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87660469209082852899345923 131490703813624279349018885)
        ·
          refine ⟨24654506965054552377941041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 131490703813624279349018885 24654506965054552377941041)
          ·
            refine ⟨18490880223790914283455781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24654506965054552377941041 18490880223790914283455781)
            ·
              refine ⟨3467040041960796428147959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18490880223790914283455781 3467040041960796428147959)
              ·
                refine ⟨5200560062941194642221939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3467040041960796428147959 5200560062941194642221939)
                ·
                  refine ⟨7800840094411791963332909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5200560062941194642221939 7800840094411791963332909)
                  ·
                    refine ⟨2925315035404421986249841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7800840094411791963332909 2925315035404421986249841)
                    ·
                      refine ⟨2193986276553316489687381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2925315035404421986249841 2193986276553316489687381)
                      ·
                        rfl

theorem cell23_4272773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 4, 1, 1, 3, 2].length) (baseStart_4272773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4272773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4272773 prefixEnd_4272773 := by exact prefixLift 4272773
  have htrace : WordTrace (prefixWord ++ tailWord_4272773) baseStart_4272773 baseEnd_4272773 := by
    simpa [prefixWord, tailWord_4272773, baseEnd_4272773] using wordTrace_append hprefix tailTrace_4272773
  have hstable : (prefixWord ++ tailWord_4272773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4272773).length < 2 ^ (prefixWord ++ tailWord_4272773).sum := by decide
  have hdescent : baseEnd_4272773 < baseStart_4272773 := by decide
  rcases family_descends (prefixWord ++ tailWord_4272773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4272929 : List Nat := [1, 2, 3, 2, 1, 2, 1, 3, 3, 5]
def baseStart_4272929 : Nat := 118140960795 + 4272929 * 2 ^ 59
def prefixEnd_4272929 : Nat := 4983230072969 + 3 ^ 40 * 4272929 * 2
def baseEnd_4272929 : Nat := 731355459845139293112221

theorem tailTrace_4272929 : CollatzResearch.WordTrace tailWord_4272929 prefixEnd_4272929 731355459845139293112221 := by
  unfold tailWord_4272929
  simp only [CollatzResearch.WordTrace]
  refine ⟨155846523936915466019293841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103897682624610310679529227 155846523936915466019293841)
  ·
    refine ⟨116884892952686599514470381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155846523936915466019293841 116884892952686599514470381)
    ·
      refine ⟨43831834857257474817926393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 116884892952686599514470381 43831834857257474817926393)
      ·
        refine ⟨32873876142943106113444795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43831834857257474817926393 32873876142943106113444795)
        ·
          refine ⟨49310814214414659170167193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32873876142943106113444795 49310814214414659170167193)
          ·
            refine ⟨36983110660810994377625395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49310814214414659170167193 36983110660810994377625395)
            ·
              refine ⟨55474665991216491566438093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36983110660810994377625395 55474665991216491566438093)
              ·
                refine ⟨20802999746706184337414285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55474665991216491566438093 20802999746706184337414285)
                ·
                  refine ⟨7801124905014819126530357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20802999746706184337414285 7801124905014819126530357)
                  ·
                    refine ⟨731355459845139293112221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7801124905014819126530357 731355459845139293112221)
                    ·
                      rfl

theorem cell23_4272929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 3, 3, 5].length) (baseStart_4272929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4272929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4272929 prefixEnd_4272929 := by exact prefixLift 4272929
  have htrace : WordTrace (prefixWord ++ tailWord_4272929) baseStart_4272929 baseEnd_4272929 := by
    simpa [prefixWord, tailWord_4272929, baseEnd_4272929] using wordTrace_append hprefix tailTrace_4272929
  have hstable : (prefixWord ++ tailWord_4272929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4272929).length < 2 ^ (prefixWord ++ tailWord_4272929).sum := by decide
  have hdescent : baseEnd_4272929 < baseStart_4272929 := by decide
  rcases family_descends (prefixWord ++ tailWord_4272929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4272946 : List Nat := [3, 2, 1, 1, 3, 1, 3, 3, 1, 5]
def baseStart_4272946 : Nat := 118140960795 + 4272946 * 2 ^ 59
def prefixEnd_4272946 : Nat := 4983230072969 + 3 ^ 40 * 4272946 * 2
def baseEnd_4272946 : Nat := 731358369568848104274695

theorem tailTrace_4272946 : CollatzResearch.WordTrace tailWord_4272946 prefixEnd_4272946 731358369568848104274695 := by
  unfold tailWord_4272946
  simp only [CollatzResearch.WordTrace]
  refine ⟨38961785994463469480665673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103898095985235918615108461 38961785994463469480665673)
  ·
    refine ⟨29221339495847602110499255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38961785994463469480665673 29221339495847602110499255)
    ·
      refine ⟨43832009243771403165748883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29221339495847602110499255 43832009243771403165748883)
      ·
        refine ⟨65748013865657104748623325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43832009243771403165748883 65748013865657104748623325)
        ·
          refine ⟨24655505199621414280733747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65748013865657104748623325 24655505199621414280733747)
          ·
            refine ⟨36983257799432121421100621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24655505199621414280733747 36983257799432121421100621)
            ·
              refine ⟨13868721674787045532912733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36983257799432121421100621 13868721674787045532912733)
              ·
                refine ⟨5200770628045142074842275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13868721674787045532912733 5200770628045142074842275)
                ·
                  refine ⟨7801155942067713112263413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5200770628045142074842275 7801155942067713112263413)
                  ·
                    refine ⟨731358369568848104274695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7801155942067713112263413 731358369568848104274695)
                    ·
                      rfl

theorem cell23_4272946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 3, 1, 5].length) (baseStart_4272946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4272946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4272946 prefixEnd_4272946 := by exact prefixLift 4272946
  have htrace : WordTrace (prefixWord ++ tailWord_4272946) baseStart_4272946 baseEnd_4272946 := by
    simpa [prefixWord, tailWord_4272946, baseEnd_4272946] using wordTrace_append hprefix tailTrace_4272946
  have hstable : (prefixWord ++ tailWord_4272946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4272946).length < 2 ^ (prefixWord ++ tailWord_4272946).sum := by decide
  have hdescent : baseEnd_4272946 < baseStart_4272946 := by decide
  rcases family_descends (prefixWord ++ tailWord_4272946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4272950 : List Nat := [5, 1, 2, 2, 2, 2, 1, 2, 6]
def baseStart_4272950 : Nat := 118140960795 + 4272950 * 2 ^ 59
def prefixEnd_4272950 : Nat := 4983230072969 + 3 ^ 40 * 4272950 * 2
def baseEnd_4272950 : Nat := 243786351403240255241563

theorem tailTrace_4272950 : CollatzResearch.WordTrace tailWord_4272950 prefixEnd_4272950 243786351403240255241563 := by
  unfold tailWord_4272950
  simp only [CollatzResearch.WordTrace]
  refine ⟨9740455616864961662863019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 103898193246559591070538869 9740455616864961662863019)
  ·
    refine ⟨14610683425297442494294529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9740455616864961662863019 14610683425297442494294529)
    ·
      refine ⟨10958012568973081870720897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14610683425297442494294529 10958012568973081870720897)
      ·
        refine ⟨8218509426729811403040673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10958012568973081870720897 8218509426729811403040673)
        ·
          refine ⟨6163882070047358552280505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8218509426729811403040673 6163882070047358552280505)
          ·
            refine ⟨4622911552535518914210379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6163882070047358552280505 4622911552535518914210379)
            ·
              refine ⟨6934367328803278371315569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4622911552535518914210379 6934367328803278371315569)
              ·
                refine ⟨5200775496602458778486677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6934367328803278371315569 5200775496602458778486677)
                ·
                  refine ⟨243786351403240255241563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5200775496602458778486677 243786351403240255241563)
                  ·
                    rfl

theorem cell23_4272950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 1, 2, 6].length) (baseStart_4272950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4272950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4272950 prefixEnd_4272950 := by exact prefixLift 4272950
  have htrace : WordTrace (prefixWord ++ tailWord_4272950) baseStart_4272950 baseEnd_4272950 := by
    simpa [prefixWord, tailWord_4272950, baseEnd_4272950] using wordTrace_append hprefix tailTrace_4272950
  have hstable : (prefixWord ++ tailWord_4272950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4272950).length < 2 ^ (prefixWord ++ tailWord_4272950).sum := by decide
  have hdescent : baseEnd_4272950 < baseStart_4272950 := by decide
  rcases family_descends (prefixWord ++ tailWord_4272950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4272969 : List Nat := [1, 2, 1, 1, 2, 5, 1, 1, 3, 1, 5]
def baseStart_4272969 : Nat := 118140960795 + 4272969 * 2 ^ 59
def prefixEnd_4272969 : Nat := 4983230072969 + 3 ^ 40 * 4272969 * 2
def baseEnd_4272969 : Nat := 2194086918761597722836479

theorem tailTrace_4272969 : CollatzResearch.WordTrace tailWord_4272969 prefixEnd_4272969 2194086918761597722836479 := by
  unfold tailWord_4272969
  simp only [CollatzResearch.WordTrace]
  refine ⟨155847982856770552850749961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103898655237847035233833307 155847982856770552850749961)
  ·
    refine ⟨116885987142577914638062471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155847982856770552850749961 116885987142577914638062471)
    ·
      refine ⟨175328980713866871957093707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116885987142577914638062471 175328980713866871957093707)
      ·
        refine ⟨262993471070800307935640561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175328980713866871957093707 262993471070800307935640561)
        ·
          refine ⟨197245103303100230951730421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 262993471070800307935640561 197245103303100230951730421)
          ·
            refine ⟨18491728434665646651724727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 197245103303100230951730421 18491728434665646651724727)
            ·
              refine ⟨27737592651998469977587091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18491728434665646651724727 27737592651998469977587091)
              ·
                refine ⟨41606388977997704966380637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27737592651998469977587091 41606388977997704966380637)
                ·
                  refine ⟨15602395866749139362392739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41606388977997704966380637 15602395866749139362392739)
                  ·
                    refine ⟨23403593800123709043589109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15602395866749139362392739 23403593800123709043589109)
                    ·
                      refine ⟨2194086918761597722836479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23403593800123709043589109 2194086918761597722836479)
                      ·
                        rfl

theorem cell23_4272969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 1, 3, 1, 5].length) (baseStart_4272969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4272969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4272969 prefixEnd_4272969 := by exact prefixLift 4272969
  have htrace : WordTrace (prefixWord ++ tailWord_4272969) baseStart_4272969 baseEnd_4272969 := by
    simpa [prefixWord, tailWord_4272969, baseEnd_4272969] using wordTrace_append hprefix tailTrace_4272969
  have hstable : (prefixWord ++ tailWord_4272969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4272969).length < 2 ^ (prefixWord ++ tailWord_4272969).sum := by decide
  have hdescent : baseEnd_4272969 < baseStart_4272969 := by decide
  rcases family_descends (prefixWord ++ tailWord_4272969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4272976 : List Nat := [2, 1, 1, 1, 1, 4, 2, 5, 2, 4]
def baseStart_4272976 : Nat := 118140960795 + 4272976 * 2 ^ 59
def prefixEnd_4272976 : Nat := 4983230072969 + 3 ^ 40 * 4272976 * 2
def baseEnd_4272976 : Nat := 731363504375393065149649

theorem tailTrace_4272976 : CollatzResearch.WordTrace tailWord_4272976 prefixEnd_4272976 731363504375393065149649 := by
  unfold tailWord_4272976
  simp only [CollatzResearch.WordTrace]
  refine ⟨77924119083872596523127391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103898825445163462030836521 77924119083872596523127391)
  ·
    refine ⟨116886178625808894784691087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77924119083872596523127391 116886178625808894784691087)
    ·
      refine ⟨175329267938713342177036631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116886178625808894784691087 175329267938713342177036631)
      ·
        refine ⟨262993901908070013265554947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175329267938713342177036631 262993901908070013265554947)
        ·
          refine ⟨394490852862105019898332421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 262993901908070013265554947 394490852862105019898332421)
          ·
            refine ⟨73967034911644691230937329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 394490852862105019898332421 73967034911644691230937329)
            ·
              refine ⟨55475276183733518423202997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73967034911644691230937329 55475276183733518423202997)
              ·
                refine ⟨5200807142225017352175281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 55475276183733518423202997 5200807142225017352175281)
                ·
                  refine ⟨3900605356668763014131461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5200807142225017352175281 3900605356668763014131461)
                  ·
                    refine ⟨731363504375393065149649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3900605356668763014131461 731363504375393065149649)
                    ·
                      rfl

theorem cell23_4272976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 5, 2, 4].length) (baseStart_4272976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4272976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4272976 prefixEnd_4272976 := by exact prefixLift 4272976
  have htrace : WordTrace (prefixWord ++ tailWord_4272976) baseStart_4272976 baseEnd_4272976 := by
    simpa [prefixWord, tailWord_4272976, baseEnd_4272976] using wordTrace_append hprefix tailTrace_4272976
  have hstable : (prefixWord ++ tailWord_4272976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4272976).length < 2 ^ (prefixWord ++ tailWord_4272976).sum := by decide
  have hdescent : baseEnd_4272976 < baseStart_4272976 := by decide
  rcases family_descends (prefixWord ++ tailWord_4272976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4272983 : List Nat := [1, 1, 3, 2, 4, 2, 2, 2, 1, 1, 4]
def baseStart_4272983 : Nat := 118140960795 + 4272983 * 2 ^ 59
def prefixEnd_4272983 : Nat := 4983230072969 + 3 ^ 40 * 4272983 * 2
def baseEnd_4272983 : Nat := 2194094107490760668061415

theorem tailTrace_4272983 : CollatzResearch.WordTrace tailWord_4272983 prefixEnd_4272983 2194094107490760668061415 := by
  unfold tailWord_4272983
  simp only [CollatzResearch.WordTrace]
  refine ⟨155848493478719833241759603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103898995652479888827839735 155848493478719833241759603)
  ·
    refine ⟨233772740218079749862639405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155848493478719833241759603 233772740218079749862639405)
    ·
      refine ⟨87664777581779906198489777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 233772740218079749862639405 87664777581779906198489777)
      ·
        refine ⟨65748583186334929648867333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87664777581779906198489777 65748583186334929648867333)
        ·
          refine ⟨12327859347437799309162625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 65748583186334929648867333 12327859347437799309162625)
          ·
            refine ⟨9245894510578349481871969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12327859347437799309162625 9245894510578349481871969)
            ·
              refine ⟨6934420882933762111403977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9245894510578349481871969 6934420882933762111403977)
              ·
                refine ⟨5200815662200321583552983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6934420882933762111403977 5200815662200321583552983)
                ·
                  refine ⟨7801223493300482375329475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5200815662200321583552983 7801223493300482375329475)
                  ·
                    refine ⟨11701835239950723562994213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7801223493300482375329475 11701835239950723562994213)
                    ·
                      refine ⟨2194094107490760668061415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11701835239950723562994213 2194094107490760668061415)
                      ·
                        rfl

theorem cell23_4272983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 2, 2, 1, 1, 4].length) (baseStart_4272983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4272983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4272983 prefixEnd_4272983 := by exact prefixLift 4272983
  have htrace : WordTrace (prefixWord ++ tailWord_4272983) baseStart_4272983 baseEnd_4272983 := by
    simpa [prefixWord, tailWord_4272983, baseEnd_4272983] using wordTrace_append hprefix tailTrace_4272983
  have hstable : (prefixWord ++ tailWord_4272983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4272983).length < 2 ^ (prefixWord ++ tailWord_4272983).sum := by decide
  have hdescent : baseEnd_4272983 < baseStart_4272983 := by decide
  rcases family_descends (prefixWord ++ tailWord_4272983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4272994 : List Nat := [3, 3, 2, 1, 3, 2, 1, 3, 1, 1, 3]
def baseStart_4272994 : Nat := 118140960795 + 4272994 * 2 ^ 59
def prefixEnd_4272994 : Nat := 4983230072969 + 3 ^ 40 * 4272994 * 2
def baseEnd_4272994 : Nat := 2194099755777960125023865

theorem tailTrace_4272994 : CollatzResearch.WordTrace tailWord_4272994 prefixEnd_4272994 2194099755777960125023865 := by
  unfold tailWord_4272994
  simp only [CollatzResearch.WordTrace]
  refine ⟨38962223670419995530102509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103899263121119988080273357 38962223670419995530102509)
  ·
    refine ⟨14610833876407498323788441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38962223670419995530102509 14610833876407498323788441)
    ·
      refine ⟨10958125407305623742841331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14610833876407498323788441 10958125407305623742841331)
      ·
        refine ⟨16437188110958435614261997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10958125407305623742841331 16437188110958435614261997)
        ·
          refine ⟨6163945541609413355348249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16437188110958435614261997 6163945541609413355348249)
          ·
            refine ⟨4622959156207060016511187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6163945541609413355348249 4622959156207060016511187)
            ·
              refine ⟨6934438734310590024766781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4622959156207060016511187 6934438734310590024766781)
              ·
                refine ⟨2600414525366471259287543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6934438734310590024766781 2600414525366471259287543)
                ·
                  refine ⟨3900621788049706888931315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2600414525366471259287543 3900621788049706888931315)
                  ·
                    refine ⟨5850932682074560333396973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3900621788049706888931315 5850932682074560333396973)
                    ·
                      refine ⟨2194099755777960125023865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5850932682074560333396973 2194099755777960125023865)
                      ·
                        rfl

theorem cell23_4272994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 1, 3, 1, 1, 3].length) (baseStart_4272994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4272994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4272994 prefixEnd_4272994 := by exact prefixLift 4272994
  have htrace : WordTrace (prefixWord ++ tailWord_4272994) baseStart_4272994 baseEnd_4272994 := by
    simpa [prefixWord, tailWord_4272994, baseEnd_4272994] using wordTrace_append hprefix tailTrace_4272994
  have hstable : (prefixWord ++ tailWord_4272994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4272994).length < 2 ^ (prefixWord ++ tailWord_4272994).sum := by decide
  have hdescent : baseEnd_4272994 < baseStart_4272994 := by decide
  rcases family_descends (prefixWord ++ tailWord_4272994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4273043 : List Nat := [1, 1, 1, 2, 1, 2, 1, 8, 1, 3, 2]
def baseStart_4273043 : Nat := 118140960795 + 4273043 * 2 ^ 59
def prefixEnd_4273043 : Nat := 4983230072969 + 3 ^ 40 * 4273043 * 2
def baseEnd_4273043 : Nat := 2194124916330030433311139

theorem tailTrace_4273043 : CollatzResearch.WordTrace tailWord_4273043 prefixEnd_4273043 2194124916330030433311139 := by
  unfold tailWord_4273043
  simp only [CollatzResearch.WordTrace]
  refine ⟨155850681858502463488943783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103900454572334975659295855 155850681858502463488943783)
  ·
    refine ⟨233776022787753695233415675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155850681858502463488943783 233776022787753695233415675)
    ·
      refine ⟨350664034181630542850123513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 233776022787753695233415675 350664034181630542850123513)
      ·
        refine ⟨262998025636222907137592635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 350664034181630542850123513 262998025636222907137592635)
        ·
          refine ⟨394497038454334360706388953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 262998025636222907137592635 394497038454334360706388953)
          ·
            refine ⟨295872778840750770529791715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 394497038454334360706388953 295872778840750770529791715)
            ·
              refine ⟨443809168261126155794687573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 295872778840750770529791715 443809168261126155794687573)
              ·
                refine ⟨5200888690560072138218995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 443809168261126155794687573 5200888690560072138218995)
                ·
                  refine ⟨7801333035840108207328493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5200888690560072138218995 7801333035840108207328493)
                  ·
                    refine ⟨2925499888440040577748185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7801333035840108207328493 2925499888440040577748185)
                    ·
                      refine ⟨2194124916330030433311139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2925499888440040577748185 2194124916330030433311139)
                      ·
                        rfl

theorem cell23_4273043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 8, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 8, 1, 3, 2].length) (baseStart_4273043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4273043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4273043 prefixEnd_4273043 := by exact prefixLift 4273043
  have htrace : WordTrace (prefixWord ++ tailWord_4273043) baseStart_4273043 baseEnd_4273043 := by
    simpa [prefixWord, tailWord_4273043, baseEnd_4273043] using wordTrace_append hprefix tailTrace_4273043
  have hstable : (prefixWord ++ tailWord_4273043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4273043).length < 2 ^ (prefixWord ++ tailWord_4273043).sum := by decide
  have hdescent : baseEnd_4273043 < baseStart_4273043 := by decide
  rcases family_descends (prefixWord ++ tailWord_4273043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4273049 : List Nat := [1, 2, 1, 2, 1, 3, 1, 2, 4, 6]
def baseStart_4273049 : Nat := 118140960795 + 4273049 * 2 ^ 59
def prefixEnd_4273049 : Nat := 4983230072969 + 3 ^ 40 * 4273049 * 2
def baseEnd_4273049 : Nat := 731375999071319136612037

theorem tailTrace_4273049 : CollatzResearch.WordTrace tailWord_4273049 prefixEnd_4273049 731375999071319136612037 := by
  unfold tailWord_4273049
  simp only [CollatzResearch.WordTrace]
  refine ⟨155850900696480726513662201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103900600464320484342441467 155850900696480726513662201)
  ·
    refine ⟨116888175522360544885246651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155850900696480726513662201 116888175522360544885246651)
    ·
      refine ⟨175332263283540817327869977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116888175522360544885246651 175332263283540817327869977)
      ·
        refine ⟨131499197462655612995902483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 175332263283540817327869977 131499197462655612995902483)
        ·
          refine ⟨197248796193983419493853725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131499197462655612995902483 197248796193983419493853725)
          ·
            refine ⟨73968298572743782310195147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 197248796193983419493853725 73968298572743782310195147)
            ·
              refine ⟨110952447859115673465292721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73968298572743782310195147 110952447859115673465292721)
              ·
                refine ⟨83214335894336755098969541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 110952447859115673465292721 83214335894336755098969541)
                ·
                  refine ⟨15602687980188141581056789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 83214335894336755098969541 15602687980188141581056789)
                  ·
                    refine ⟨731375999071319136612037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15602687980188141581056789 731375999071319136612037)
                    ·
                      rfl

theorem cell23_4273049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 2, 4, 6].length) (baseStart_4273049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4273049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4273049 prefixEnd_4273049 := by exact prefixLift 4273049
  have htrace : WordTrace (prefixWord ++ tailWord_4273049) baseStart_4273049 baseEnd_4273049 := by
    simpa [prefixWord, tailWord_4273049, baseEnd_4273049] using wordTrace_append hprefix tailTrace_4273049
  have hstable : (prefixWord ++ tailWord_4273049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4273049).length < 2 ^ (prefixWord ++ tailWord_4273049).sum := by decide
  have hdescent : baseEnd_4273049 < baseStart_4273049 := by decide
  rcases family_descends (prefixWord ++ tailWord_4273049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4273113 : List Nat := [1, 2, 1, 2, 5, 1, 1, 5, 5]
def baseStart_4273113 : Nat := 118140960795 + 4273113 * 2 ^ 59
def prefixEnd_4273113 : Nat := 4983230072969 + 3 ^ 40 * 4273113 * 2
def baseEnd_4273113 : Nat := 243795651108427239937313

theorem tailTrace_4273113 : CollatzResearch.WordTrace tailWord_4273113 prefixEnd_4273113 243795651108427239937313 := by
  unfold tailWord_4273113
  simp only [CollatzResearch.WordTrace]
  refine ⟨155853234968248865443991993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103902156645499243629327995 155853234968248865443991993)
  ·
    refine ⟨116889926226186649082993995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155853234968248865443991993 116889926226186649082993995)
    ·
      refine ⟨175334889339279973624490993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116889926226186649082993995 175334889339279973624490993)
      ·
        refine ⟨131501167004459980218368245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 175334889339279973624490993 131501167004459980218368245)
        ·
          refine ⟨12328234406668123145472023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 131501167004459980218368245 12328234406668123145472023)
          ·
            refine ⟨18492351610002184718208035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12328234406668123145472023 18492351610002184718208035)
            ·
              refine ⟨27738527415003277077312053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18492351610002184718208035 27738527415003277077312053)
              ·
                refine ⟨2600486945156557225998005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27738527415003277077312053 2600486945156557225998005)
                ·
                  refine ⟨243795651108427239937313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2600486945156557225998005 243795651108427239937313)
                  ·
                    rfl

theorem cell23_4273113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 5, 5].length) (baseStart_4273113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4273113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4273113 prefixEnd_4273113 := by exact prefixLift 4273113
  have htrace : WordTrace (prefixWord ++ tailWord_4273113) baseStart_4273113 baseEnd_4273113 := by
    simpa [prefixWord, tailWord_4273113, baseEnd_4273113] using wordTrace_append hprefix tailTrace_4273113
  have hstable : (prefixWord ++ tailWord_4273113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4273113).length < 2 ^ (prefixWord ++ tailWord_4273113).sum := by decide
  have hdescent : baseEnd_4273113 < baseStart_4273113 := by decide
  rcases family_descends (prefixWord ++ tailWord_4273113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4273141 : List Nat := [1, 3, 5, 2, 2, 1, 1, 1, 1, 4, 2]
def baseStart_4273141 : Nat := 118140960795 + 4273141 * 2 ^ 59
def prefixEnd_4273141 : Nat := 4983230072969 + 3 ^ 40 * 4273141 * 2
def baseEnd_4273141 : Nat := 2194175237434171049885689

theorem tailTrace_4273141 : CollatzResearch.WordTrace tailWord_4273141 prefixEnd_4273141 2194175237434171049885689 := by
  unfold tailWord_4273141
  simp only [CollatzResearch.WordTrace]
  refine ⟨155854256212147426226011277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103902837474764950817340851 155854256212147426226011277)
  ·
    refine ⟨58445346079555284834754229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 155854256212147426226011277 58445346079555284834754229)
    ·
      refine ⟨5479251194958307953258209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 58445346079555284834754229 5479251194958307953258209)
      ·
        refine ⟨4109438396218730964943657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5479251194958307953258209 4109438396218730964943657)
        ·
          refine ⟨3082078797164048223707743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4109438396218730964943657 3082078797164048223707743)
          ·
            refine ⟨4623118195746072335561615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3082078797164048223707743 4623118195746072335561615)
            ·
              refine ⟨6934677293619108503342423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4623118195746072335561615 6934677293619108503342423)
              ·
                refine ⟨10402015940428662755013635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6934677293619108503342423 10402015940428662755013635)
                ·
                  refine ⟨15603023910642994132520453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10402015940428662755013635 15603023910642994132520453)
                  ·
                    refine ⟨2925566983245561399847585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15603023910642994132520453 2925566983245561399847585)
                    ·
                      refine ⟨2194175237434171049885689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2925566983245561399847585 2194175237434171049885689)
                      ·
                        rfl

theorem cell23_4273141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 1, 1, 1, 4, 2].length) (baseStart_4273141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4273141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4273141 prefixEnd_4273141 := by exact prefixLift 4273141
  have htrace : WordTrace (prefixWord ++ tailWord_4273141) baseStart_4273141 baseEnd_4273141 := by
    simpa [prefixWord, tailWord_4273141, baseEnd_4273141] using wordTrace_append hprefix tailTrace_4273141
  have hstable : (prefixWord ++ tailWord_4273141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4273141).length < 2 ^ (prefixWord ++ tailWord_4273141).sum := by decide
  have hdescent : baseEnd_4273141 < baseStart_4273141 := by decide
  rcases family_descends (prefixWord ++ tailWord_4273141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4273180 : List Nat := [2, 2, 3, 1, 4, 1, 1, 2, 2, 1, 4]
def baseStart_4273180 : Nat := 118140960795 + 4273180 * 2 ^ 59
def prefixEnd_4273180 : Nat := 4983230072969 + 3 ^ 40 * 4273180 * 2
def baseEnd_4273180 : Nat := 2194195263179696397298009

theorem tailTrace_4273180 : CollatzResearch.WordTrace tailWord_4273180 prefixEnd_4273180 2194195263179696397298009 := by
  unfold tailWord_4273180
  simp only [CollatzResearch.WordTrace]
  refine ⟨77927839329503067943340497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103903785772670757257787329 77927839329503067943340497)
  ·
    refine ⟨58445879497127300957505373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77927839329503067943340497 58445879497127300957505373)
    ·
      refine ⟨21917204811422737859064515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58445879497127300957505373 21917204811422737859064515)
      ·
        refine ⟨32875807217134106788596773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21917204811422737859064515 32875807217134106788596773)
        ·
          refine ⟨6164213853212645022861895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32875807217134106788596773 6164213853212645022861895)
          ·
            refine ⟨9246320779818967534292843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6164213853212645022861895 9246320779818967534292843)
            ·
              refine ⟨13869481169728451301439265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9246320779818967534292843 13869481169728451301439265)
              ·
                refine ⟨10402110877296338476079449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13869481169728451301439265 10402110877296338476079449)
                ·
                  refine ⟨7801583157972253857059587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10402110877296338476079449 7801583157972253857059587)
                  ·
                    refine ⟨11702374736958380785589381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7801583157972253857059587 11702374736958380785589381)
                    ·
                      refine ⟨2194195263179696397298009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11702374736958380785589381 2194195263179696397298009)
                      ·
                        rfl

theorem cell23_4273180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 2, 2, 1, 4].length) (baseStart_4273180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4273180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4273180 prefixEnd_4273180 := by exact prefixLift 4273180
  have htrace : WordTrace (prefixWord ++ tailWord_4273180) baseStart_4273180 baseEnd_4273180 := by
    simpa [prefixWord, tailWord_4273180, baseEnd_4273180] using wordTrace_append hprefix tailTrace_4273180
  have hstable : (prefixWord ++ tailWord_4273180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4273180).length < 2 ^ (prefixWord ++ tailWord_4273180).sum := by decide
  have hdescent : baseEnd_4273180 < baseStart_4273180 := by decide
  rcases family_descends (prefixWord ++ tailWord_4273180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4273183 : List Nat := [1, 1, 2, 4, 1, 3, 1, 1, 4, 2, 3]
def baseStart_4273183 : Nat := 118140960795 + 4273183 * 2 ^ 59
def prefixEnd_4273183 : Nat := 4983230072969 + 3 ^ 40 * 4273183 * 2
def baseEnd_4273183 : Nat := 2194196803621659885560495

theorem tailTrace_4273183 : CollatzResearch.WordTrace tailWord_4273183 prefixEnd_4273183 2194196803621659885560495 := by
  unfold tailWord_4273183
  simp only [CollatzResearch.WordTrace]
  refine ⟨155855788077995267399040203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103903858718663511599360135 155855788077995267399040203)
  ·
    refine ⟨233783682116992901098560305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155855788077995267399040203 233783682116992901098560305)
    ·
      refine ⟨175337761587744675823920229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 233783682116992901098560305 175337761587744675823920229)
      ·
        refine ⟨32875830297702126716985043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 175337761587744675823920229 32875830297702126716985043)
        ·
          refine ⟨49313745446553190075477565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32875830297702126716985043 49313745446553190075477565)
          ·
            refine ⟨18492654542457446278304087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49313745446553190075477565 18492654542457446278304087)
            ·
              refine ⟨27738981813686169417456131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18492654542457446278304087 27738981813686169417456131)
              ·
                refine ⟨41608472720529254126184197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27738981813686169417456131 41608472720529254126184197)
                ·
                  refine ⟨7801588635099235148659537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 41608472720529254126184197 7801588635099235148659537)
                  ·
                    refine ⟨5851191476324426361494653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7801588635099235148659537 5851191476324426361494653)
                    ·
                      refine ⟨2194196803621659885560495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5851191476324426361494653 2194196803621659885560495)
                      ·
                        rfl

theorem cell23_4273183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 1, 4, 2, 3].length) (baseStart_4273183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4273183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4273183 prefixEnd_4273183 := by exact prefixLift 4273183
  have htrace : WordTrace (prefixWord ++ tailWord_4273183) baseStart_4273183 baseEnd_4273183 := by
    simpa [prefixWord, tailWord_4273183, baseEnd_4273183] using wordTrace_append hprefix tailTrace_4273183
  have hstable : (prefixWord ++ tailWord_4273183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4273183).length < 2 ^ (prefixWord ++ tailWord_4273183).sum := by decide
  have hdescent : baseEnd_4273183 < baseStart_4273183 := by decide
  rcases family_descends (prefixWord ++ tailWord_4273183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4273217 : List Nat := [1, 2, 5, 1, 3, 1, 2, 1, 2, 2, 3]
def baseStart_4273217 : Nat := 118140960795 + 4273217 * 2 ^ 59
def prefixEnd_4273217 : Nat := 4983230072969 + 3 ^ 40 * 4273217 * 2
def baseEnd_4273217 : Nat := 2194214261963912752535339

theorem tailTrace_4273217 : CollatzResearch.WordTrace tailWord_4273217 prefixEnd_4273217 2194214261963912752535339 := by
  unfold tailWord_4273217
  simp only [CollatzResearch.WordTrace]
  refine ⟨155857028159872091205777905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103904685439914727470518603 155857028159872091205777905)
  ·
    refine ⟨116892771119904068404333429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155857028159872091205777905 116892771119904068404333429)
    ·
      refine ⟨10958697292491006412906259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 116892771119904068404333429 10958697292491006412906259)
      ·
        refine ⟨16438045938736509619359389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10958697292491006412906259 16438045938736509619359389)
        ·
          refine ⟨6164267227026191107259771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16438045938736509619359389 6164267227026191107259771)
          ·
            refine ⟨9246400840539286660889657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6164267227026191107259771 9246400840539286660889657)
            ·
              refine ⟨6934800630404464995667243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9246400840539286660889657 6934800630404464995667243)
              ·
                refine ⟨10402200945606697493500865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6934800630404464995667243 10402200945606697493500865)
                ·
                  refine ⟨7801650709205023120125649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10402200945606697493500865 7801650709205023120125649)
                  ·
                    refine ⟨5851238031903767340094237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7801650709205023120125649 5851238031903767340094237)
                    ·
                      refine ⟨2194214261963912752535339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5851238031903767340094237 2194214261963912752535339)
                      ·
                        rfl

theorem cell23_4273217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 2, 1, 2, 2, 3].length) (baseStart_4273217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4273217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4273217 prefixEnd_4273217 := by exact prefixLift 4273217
  have htrace : WordTrace (prefixWord ++ tailWord_4273217) baseStart_4273217 baseEnd_4273217 := by
    simpa [prefixWord, tailWord_4273217, baseEnd_4273217] using wordTrace_append hprefix tailTrace_4273217
  have hstable : (prefixWord ++ tailWord_4273217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4273217).length < 2 ^ (prefixWord ++ tailWord_4273217).sum := by decide
  have hdescent : baseEnd_4273217 < baseStart_4273217 := by decide
  rcases family_descends (prefixWord ++ tailWord_4273217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4273233 : List Nat := [1, 2, 2, 1, 3, 1, 2, 5, 1, 5]
def baseStart_4273233 : Nat := 118140960795 + 4273233 * 2 ^ 59
def prefixEnd_4273233 : Nat := 4983230072969 + 3 ^ 40 * 4273233 * 2
def baseEnd_4273233 : Nat := 731407492551461563311755

theorem tailTrace_4273233 : CollatzResearch.WordTrace tailWord_4273233 prefixEnd_4273233 731407492551461563311755 := by
  unfold tailWord_4273233
  simp only [CollatzResearch.WordTrace]
  refine ⟨155857611727814125938360353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103905074485209417292240235 155857611727814125938360353)
  ·
    refine ⟨116893208795860594453770265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155857611727814125938360353 116893208795860594453770265)
    ·
      refine ⟨87669906596895445840327699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116893208795860594453770265 87669906596895445840327699)
      ·
        refine ⟨131504859895343168760491549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87669906596895445840327699 131504859895343168760491549)
        ·
          refine ⟨49314322460753688285184331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 131504859895343168760491549 49314322460753688285184331)
          ·
            refine ⟨73971483691130532427776497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49314322460753688285184331 73971483691130532427776497)
            ·
              refine ⟨55478612768347899320832373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73971483691130532427776497 55478612768347899320832373)
              ·
                refine ⟨5201119947032615561328035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 55478612768347899320832373 5201119947032615561328035)
                ·
                  refine ⟨7801679920548923341992053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5201119947032615561328035 7801679920548923341992053)
                  ·
                    refine ⟨731407492551461563311755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7801679920548923341992053 731407492551461563311755)
                    ·
                      rfl

theorem cell23_4273233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 5, 1, 5].length) (baseStart_4273233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4273233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4273233 prefixEnd_4273233 := by exact prefixLift 4273233
  have htrace : WordTrace (prefixWord ++ tailWord_4273233) baseStart_4273233 baseEnd_4273233 := by
    simpa [prefixWord, tailWord_4273233, baseEnd_4273233] using wordTrace_append hprefix tailTrace_4273233
  have hstable : (prefixWord ++ tailWord_4273233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4273233).length < 2 ^ (prefixWord ++ tailWord_4273233).sum := by decide
  have hdescent : baseEnd_4273233 < baseStart_4273233 := by decide
  rcases family_descends (prefixWord ++ tailWord_4273233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4273240 : List Nat := [2, 1, 2, 2, 1, 3, 1, 4, 2, 3, 2]
def baseStart_4273240 : Nat := 118140960795 + 4273240 * 2 ^ 59
def prefixEnd_4273240 : Nat := 4983230072969 + 3 ^ 40 * 4273240 * 2
def baseEnd_4273240 : Nat := 2194226072018966162547733

theorem tailTrace_4273240 : CollatzResearch.WordTrace tailWord_4273240 prefixEnd_4273240 2194226072018966162547733 := by
  unfold tailWord_4273240
  simp only [CollatzResearch.WordTrace]
  refine ⟨77928933519394383066932587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103905244692525844089243449 77928933519394383066932587)
  ·
    refine ⟨116893400279091574600398881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77928933519394383066932587 116893400279091574600398881)
    ·
      refine ⟨87670050209318680950299161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116893400279091574600398881 87670050209318680950299161)
      ·
        refine ⟨65752537656989010712724371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87670050209318680950299161 65752537656989010712724371)
        ·
          refine ⟨98628806485483516069086557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65752537656989010712724371 98628806485483516069086557)
          ·
            refine ⟨36985802432056318525907459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 98628806485483516069086557 36985802432056318525907459)
            ·
              refine ⟨55478703648084477788861189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36985802432056318525907459 55478703648084477788861189)
              ·
                refine ⟨10402256934015839585411473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 55478703648084477788861189 10402256934015839585411473)
                ·
                  refine ⟨7801692700511879689058605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10402256934015839585411473 7801692700511879689058605)
                  ·
                    refine ⟨2925634762691954883396977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7801692700511879689058605 2925634762691954883396977)
                    ·
                      refine ⟨2194226072018966162547733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2925634762691954883396977 2194226072018966162547733)
                      ·
                        rfl

theorem cell23_4273240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 4, 2, 3, 2].length) (baseStart_4273240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4273240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4273240 prefixEnd_4273240 := by exact prefixLift 4273240
  have htrace : WordTrace (prefixWord ++ tailWord_4273240) baseStart_4273240 baseEnd_4273240 := by
    simpa [prefixWord, tailWord_4273240, baseEnd_4273240] using wordTrace_append hprefix tailTrace_4273240
  have hstable : (prefixWord ++ tailWord_4273240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4273240).length < 2 ^ (prefixWord ++ tailWord_4273240).sum := by decide
  have hdescent : baseEnd_4273240 < baseStart_4273240 := by decide
  rcases family_descends (prefixWord ++ tailWord_4273240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4273247 : List Nat := [1, 1, 2, 3, 1, 1, 5, 4, 1, 1, 3]
def baseStart_4273247 : Nat := 118140960795 + 4273247 * 2 ^ 59
def prefixEnd_4273247 : Nat := 4983230072969 + 3 ^ 40 * 4273247 * 2
def baseEnd_4273247 : Nat := 2194229666383547635160201

theorem tailTrace_4273247 : CollatzResearch.WordTrace tailWord_4273247 prefixEnd_4273247 2194229666383547635160201 := by
  unfold tailWord_4273247
  simp only [CollatzResearch.WordTrace]
  refine ⟨155858122349763406329369995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103905414899842270886246663 155858122349763406329369995)
  ·
    refine ⟨233787183524645109494054993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155858122349763406329369995 233787183524645109494054993)
    ·
      refine ⟨175340387643483832120541245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 233787183524645109494054993 175340387643483832120541245)
      ·
        refine ⟨65752645366306437045202967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 175340387643483832120541245 65752645366306437045202967)
        ·
          refine ⟨98628968049459655567804451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65752645366306437045202967 98628968049459655567804451)
          ·
            refine ⟨147943452074189483351706677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98628968049459655567804451 147943452074189483351706677)
            ·
              refine ⟨13869698631955264064222501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 147943452074189483351706677 13869698631955264064222501)
              ·
                refine ⟨2600568493491612012041719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13869698631955264064222501 2600568493491612012041719)
                ·
                  refine ⟨3900852740237418018062579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2600568493491612012041719 3900852740237418018062579)
                  ·
                    refine ⟨5851279110356127027093869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3900852740237418018062579 5851279110356127027093869)
                    ·
                      refine ⟨2194229666383547635160201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5851279110356127027093869 2194229666383547635160201)
                      ·
                        rfl

theorem cell23_4273247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 4, 1, 1, 3].length) (baseStart_4273247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4273247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4273247 prefixEnd_4273247 := by exact prefixLift 4273247
  have htrace : WordTrace (prefixWord ++ tailWord_4273247) baseStart_4273247 baseEnd_4273247 := by
    simpa [prefixWord, tailWord_4273247, baseEnd_4273247] using wordTrace_append hprefix tailTrace_4273247
  have hstable : (prefixWord ++ tailWord_4273247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4273247).length < 2 ^ (prefixWord ++ tailWord_4273247).sum := by decide
  have hdescent : baseEnd_4273247 < baseStart_4273247 := by decide
  rcases family_descends (prefixWord ++ tailWord_4273247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4273250 : List Nat := [3, 3, 2, 2, 1, 1, 1, 2, 3, 5]
def baseStart_4273250 : Nat := 118140960795 + 4273250 * 2 ^ 59
def prefixEnd_4273250 : Nat := 4983230072969 + 3 ^ 40 * 4273250 * 2
def baseEnd_4273250 : Nat := 731410402275170374474229

theorem tailTrace_4273250 : CollatzResearch.WordTrace tailWord_4273250 prefixEnd_4273250 731410402275170374474229 := by
  unfold tailWord_4273250
  simp only [CollatzResearch.WordTrace]
  refine ⟨38964557942188134460432301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103905487845835025227819469 38964557942188134460432301)
  ·
    refine ⟨14611709228320550422662113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38964557942188134460432301 14611709228320550422662113)
    ·
      refine ⟨10958781921240412816996585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14611709228320550422662113 10958781921240412816996585)
      ·
        refine ⟨8219086440930309612747439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10958781921240412816996585 8219086440930309612747439)
        ·
          refine ⟨12328629661395464419121159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8219086440930309612747439 12328629661395464419121159)
          ·
            refine ⟨18492944492093196628681739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12328629661395464419121159 18492944492093196628681739)
            ·
              refine ⟨27739416738139794943022609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18492944492093196628681739 27739416738139794943022609)
              ·
                refine ⟨20804562553604846207266957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27739416738139794943022609 20804562553604846207266957)
                ·
                  refine ⟨7801710957601817327725109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20804562553604846207266957 7801710957601817327725109)
                  ·
                    refine ⟨731410402275170374474229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7801710957601817327725109 731410402275170374474229)
                    ·
                      rfl

theorem cell23_4273250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 2, 3, 5].length) (baseStart_4273250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4273250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4273250 prefixEnd_4273250 := by exact prefixLift 4273250
  have htrace : WordTrace (prefixWord ++ tailWord_4273250) baseStart_4273250 baseEnd_4273250 := by
    simpa [prefixWord, tailWord_4273250, baseEnd_4273250] using wordTrace_append hprefix tailTrace_4273250
  have hstable : (prefixWord ++ tailWord_4273250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4273250).length < 2 ^ (prefixWord ++ tailWord_4273250).sum := by decide
  have hdescent : baseEnd_4273250 < baseStart_4273250 := by decide
  rcases family_descends (prefixWord ++ tailWord_4273250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4273253 : List Nat := [1, 3, 1, 3, 2, 1, 1, 1, 5, 1, 4]
def baseStart_4273253 : Nat := 118140960795 + 4273253 * 2 ^ 59
def prefixEnd_4273253 : Nat := 4983230072969 + 3 ^ 40 * 4273253 * 2
def baseEnd_4273253 : Nat := 2194232747267474611685173

theorem tailTrace_4273253 : CollatzResearch.WordTrace tailWord_4273253 prefixEnd_4273253 2194232747267474611685173 := by
  unfold tailWord_4273253
  simp only [CollatzResearch.WordTrace]
  refine ⟨155858341187741669354088413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103905560791827779569392275 155858341187741669354088413)
  ·
    refine ⟨58446877945403126007783155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 155858341187741669354088413 58446877945403126007783155)
    ·
      refine ⟨87670316918104689011674733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58446877945403126007783155 87670316918104689011674733)
      ·
        refine ⟨32876368844289258379378025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87670316918104689011674733 32876368844289258379378025)
        ·
          refine ⟨24657276633216943784533519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32876368844289258379378025 24657276633216943784533519)
          ·
            refine ⟨36985914949825415676800279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24657276633216943784533519 36985914949825415676800279)
            ·
              refine ⟨55478872424738123515200419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36985914949825415676800279 55478872424738123515200419)
              ·
                refine ⟨83218308637107185272800629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55478872424738123515200419 83218308637107185272800629)
                ·
                  refine ⟨7801716434728798619325059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 83218308637107185272800629 7801716434728798619325059)
                  ·
                    refine ⟨11702574652093197928987589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7801716434728798619325059 11702574652093197928987589)
                    ·
                      refine ⟨2194232747267474611685173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11702574652093197928987589 2194232747267474611685173)
                      ·
                        rfl

theorem cell23_4273253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 1, 5, 1, 4].length) (baseStart_4273253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4273253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4273253 prefixEnd_4273253 := by exact prefixLift 4273253
  have htrace : WordTrace (prefixWord ++ tailWord_4273253) baseStart_4273253 baseEnd_4273253 := by
    simpa [prefixWord, tailWord_4273253, baseEnd_4273253] using wordTrace_append hprefix tailTrace_4273253
  have hstable : (prefixWord ++ tailWord_4273253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4273253).length < 2 ^ (prefixWord ++ tailWord_4273253).sum := by decide
  have hdescent : baseEnd_4273253 < baseStart_4273253 := by decide
  rcases family_descends (prefixWord ++ tailWord_4273253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4273263 : List Nat := [1, 1, 2, 1, 3, 3, 4, 1, 1, 6]
def baseStart_4273263 : Nat := 118140960795 + 4273263 * 2 ^ 59
def prefixEnd_4273263 : Nat := 4983230072969 + 3 ^ 40 * 4273263 * 2
def baseEnd_4273263 : Nat := 731412627358006524186709

theorem tailTrace_4273263 : CollatzResearch.WordTrace tailWord_4273263 prefixEnd_4273263 731412627358006524186709 := by
  unfold tailWord_4273263
  simp only [CollatzResearch.WordTrace]
  refine ⟨155858705917705441061952443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103905803945136960707968295 155858705917705441061952443)
  ·
    refine ⟨233788058876558161592928665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155858705917705441061952443 233788058876558161592928665)
    ·
      refine ⟨175341044157418621194696499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 233788058876558161592928665 175341044157418621194696499)
      ·
        refine ⟨263011566236127931792044749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175341044157418621194696499 263011566236127931792044749)
        ·
          refine ⟨98629337338547974422016781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 263011566236127931792044749 98629337338547974422016781)
          ·
            refine ⟨36986001501955490408256293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 98629337338547974422016781 36986001501955490408256293)
            ·
              refine ⟨6934875281616654451548055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36986001501955490408256293 6934875281616654451548055)
              ·
                refine ⟨10402312922424981677322083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6934875281616654451548055 10402312922424981677322083)
                ·
                  refine ⟨15603469383637472515983125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10402312922424981677322083 15603469383637472515983125)
                  ·
                    refine ⟨731412627358006524186709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15603469383637472515983125 731412627358006524186709)
                    ·
                      rfl

theorem cell23_4273263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 4, 1, 1, 6].length) (baseStart_4273263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4273263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4273263 prefixEnd_4273263 := by exact prefixLift 4273263
  have htrace : WordTrace (prefixWord ++ tailWord_4273263) baseStart_4273263 baseEnd_4273263 := by
    simpa [prefixWord, tailWord_4273263, baseEnd_4273263] using wordTrace_append hprefix tailTrace_4273263
  have hstable : (prefixWord ++ tailWord_4273263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4273263).length < 2 ^ (prefixWord ++ tailWord_4273263).sum := by decide
  have hdescent : baseEnd_4273263 < baseStart_4273263 := by decide
  rcases family_descends (prefixWord ++ tailWord_4273263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4273270 : List Nat := [5, 1, 1, 2, 1, 1, 1, 3, 3, 1, 4]
def baseStart_4273270 : Nat := 118140960795 + 4273270 * 2 ^ 59
def prefixEnd_4273270 : Nat := 4983230072969 + 3 ^ 40 * 4273270 * 2
def baseEnd_4273270 : Nat := 2194241476438601045172595

theorem tailTrace_4273270 : CollatzResearch.WordTrace tailWord_4273270 prefixEnd_4273270 2194241476438601045172595 := by
  unfold tailWord_4273270
  simp only [CollatzResearch.WordTrace]
  refine ⟨9741185076792505078591079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 103905974152453387504971509 9741185076792505078591079)
  ·
    refine ⟨14611777615188757617886619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9741185076792505078591079 14611777615188757617886619)
    ·
      refine ⟨21917666422783136426829929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14611777615188757617886619 21917666422783136426829929)
      ·
        refine ⟨16438249817087352320122447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21917666422783136426829929 16438249817087352320122447)
        ·
          refine ⟨24657374725631028480183671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16438249817087352320122447 24657374725631028480183671)
          ·
            refine ⟨36986062088446542720275507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24657374725631028480183671 36986062088446542720275507)
            ·
              refine ⟨55479093132669814080413261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36986062088446542720275507 55479093132669814080413261)
              ·
                refine ⟨20804659924751180280154973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55479093132669814080413261 20804659924751180280154973)
                ·
                  refine ⟨7801747471781692605058115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20804659924751180280154973 7801747471781692605058115)
                  ·
                    refine ⟨11702621207672538907587173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7801747471781692605058115 11702621207672538907587173)
                    ·
                      refine ⟨2194241476438601045172595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11702621207672538907587173 2194241476438601045172595)
                      ·
                        rfl

theorem cell23_4273270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 3, 3, 1, 4].length) (baseStart_4273270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4273270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4273270 prefixEnd_4273270 := by exact prefixLift 4273270
  have htrace : WordTrace (prefixWord ++ tailWord_4273270) baseStart_4273270 baseEnd_4273270 := by
    simpa [prefixWord, tailWord_4273270, baseEnd_4273270] using wordTrace_append hprefix tailTrace_4273270
  have hstable : (prefixWord ++ tailWord_4273270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4273270).length < 2 ^ (prefixWord ++ tailWord_4273270).sum := by decide
  have hdescent : baseEnd_4273270 < baseStart_4273270 := by decide
  rcases family_descends (prefixWord ++ tailWord_4273270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4273283 : List Nat := [1, 1, 1, 3, 3, 2, 1, 4, 1, 2, 4]
def baseStart_4273283 : Nat := 118140960795 + 4273283 * 2 ^ 59
def prefixEnd_4273283 : Nat := 4983230072969 + 3 ^ 40 * 4273283 * 2
def baseEnd_4273283 : Nat := 2194248151687109494310035

theorem tailTrace_4273283 : CollatzResearch.WordTrace tailWord_4273283 prefixEnd_4273283 2194248151687109494310035 := by
  unfold tailWord_4273283
  simp only [CollatzResearch.WordTrace]
  refine ⟨155859435377632984477680503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103906290251755322985120335 155859435377632984477680503)
  ·
    refine ⟨233789153066449476716520755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155859435377632984477680503 233789153066449476716520755)
    ·
      refine ⟨350683729599674215074781133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 233789153066449476716520755 350683729599674215074781133)
      ·
        refine ⟨131506398599877830653042925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 350683729599674215074781133 131506398599877830653042925)
        ·
          refine ⟨49314899474954186494891097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 131506398599877830653042925 49314899474954186494891097)
          ·
            refine ⟨36986174606215639871168323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49314899474954186494891097 36986174606215639871168323)
            ·
              refine ⟨55479261909323459806752485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36986174606215639871168323 55479261909323459806752485)
              ·
                refine ⟨10402361607998148713766091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 55479261909323459806752485 10402361607998148713766091)
                ·
                  refine ⟨15603542411997223070649137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10402361607998148713766091 15603542411997223070649137)
                  ·
                    refine ⟨11702656808997917302986853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15603542411997223070649137 11702656808997917302986853)
                    ·
                      refine ⟨2194248151687109494310035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11702656808997917302986853 2194248151687109494310035)
                      ·
                        rfl

theorem cell23_4273283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 4, 1, 2, 4].length) (baseStart_4273283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4273283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4273283 prefixEnd_4273283 := by exact prefixLift 4273283
  have htrace : WordTrace (prefixWord ++ tailWord_4273283) baseStart_4273283 baseEnd_4273283 := by
    simpa [prefixWord, tailWord_4273283, baseEnd_4273283] using wordTrace_append hprefix tailTrace_4273283
  have hstable : (prefixWord ++ tailWord_4273283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4273283).length < 2 ^ (prefixWord ++ tailWord_4273283).sum := by decide
  have hdescent : baseEnd_4273283 < baseStart_4273283 := by decide
  rcases family_descends (prefixWord ++ tailWord_4273283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4273304 : List Nat := [2, 1, 2, 4, 2, 2, 2, 1, 3, 2, 2]
def baseStart_4273304 : Nat := 118140960795 + 4273304 * 2 ^ 59
def prefixEnd_4273304 : Nat := 4983230072969 + 3 ^ 40 * 4273304 * 2
def baseEnd_4273304 : Nat := 2194258934780853912147439

theorem tailTrace_4273304 : CollatzResearch.WordTrace tailWord_4273304 prefixEnd_4273304 2194258934780853912147439 := by
  unfold tailWord_4273304
  simp only [CollatzResearch.WordTrace]
  refine ⟨77930100655278452532097483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103906800873704603376129977 77930100655278452532097483)
  ·
    refine ⟨116895150982917678798146225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77930100655278452532097483 116895150982917678798146225)
    ·
      refine ⟨87671363237188259098609669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116895150982917678798146225 87671363237188259098609669)
      ·
        refine ⟨16438380606972798580989313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 87671363237188259098609669 16438380606972798580989313)
        ·
          refine ⟨12328785455229598935741985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16438380606972798580989313 12328785455229598935741985)
          ·
            refine ⟨9246589091422199201806489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12328785455229598935741985 9246589091422199201806489)
            ·
              refine ⟨6934941818566649401354867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9246589091422199201806489 6934941818566649401354867)
              ·
                refine ⟨10402412727849974102032301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6934941818566649401354867 10402412727849974102032301)
                ·
                  refine ⟨3900904772943740288262113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10402412727849974102032301 3900904772943740288262113)
                  ·
                    refine ⟨2925678579707805216196585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3900904772943740288262113 2925678579707805216196585)
                    ·
                      refine ⟨2194258934780853912147439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2925678579707805216196585 2194258934780853912147439)
                      ·
                        rfl

theorem cell23_4273304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 2, 1, 3, 2, 2].length) (baseStart_4273304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4273304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4273304 prefixEnd_4273304 := by exact prefixLift 4273304
  have htrace : WordTrace (prefixWord ++ tailWord_4273304) baseStart_4273304 baseEnd_4273304 := by
    simpa [prefixWord, tailWord_4273304, baseEnd_4273304] using wordTrace_append hprefix tailTrace_4273304
  have hstable : (prefixWord ++ tailWord_4273304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4273304).length < 2 ^ (prefixWord ++ tailWord_4273304).sum := by decide
  have hdescent : baseEnd_4273304 < baseStart_4273304 := by decide
  rcases family_descends (prefixWord ++ tailWord_4273304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4273314 : List Nat := [3, 3, 1, 3, 3, 1, 1, 1, 1, 6]
def baseStart_4273314 : Nat := 118140960795 + 4273314 * 2 ^ 59
def prefixEnd_4273314 : Nat := 4983230072969 + 3 ^ 40 * 4273314 * 2
def baseEnd_4273314 : Nat := 731421356529132957674131

theorem tailTrace_4273314 : CollatzResearch.WordTrace tailWord_4273314 prefixEnd_4273314 731421356529132957674131 := by
  unfold tailWord_4273314
  simp only [CollatzResearch.WordTrace]
  refine ⟨38965141510130169193014749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103907044027013784514705997 38965141510130169193014749)
  ·
    refine ⟨14611928066298813447380531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38965141510130169193014749 14611928066298813447380531)
    ·
      refine ⟨21917892099448220171070797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14611928066298813447380531 21917892099448220171070797)
      ·
        refine ⟨8219209537293082564151549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21917892099448220171070797 8219209537293082564151549)
        ·
          refine ⟨3082203576484905961556831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8219209537293082564151549 3082203576484905961556831)
          ·
            refine ⟨4623305364727358942335247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3082203576484905961556831 4623305364727358942335247)
            ·
              refine ⟨6934958047091038413502871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4623305364727358942335247 6934958047091038413502871)
              ·
                refine ⟨10402437070636557620254307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6934958047091038413502871 10402437070636557620254307)
                ·
                  refine ⟨15603655605954836430381461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10402437070636557620254307 15603655605954836430381461)
                  ·
                    refine ⟨731421356529132957674131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15603655605954836430381461 731421356529132957674131)
                    ·
                      rfl

theorem cell23_4273314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 1, 1, 1, 6].length) (baseStart_4273314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4273314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4273314 prefixEnd_4273314 := by exact prefixLift 4273314
  have htrace : WordTrace (prefixWord ++ tailWord_4273314) baseStart_4273314 baseEnd_4273314 := by
    simpa [prefixWord, tailWord_4273314, baseEnd_4273314] using wordTrace_append hprefix tailTrace_4273314
  have hstable : (prefixWord ++ tailWord_4273314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4273314).length < 2 ^ (prefixWord ++ tailWord_4273314).sum := by decide
  have hdescent : baseEnd_4273314 < baseStart_4273314 := by decide
  rcases family_descends (prefixWord ++ tailWord_4273314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4273363 : List Nat := [1, 1, 1, 2, 1, 1, 1, 5, 1, 6, 3]
def baseStart_4273363 : Nat := 118140960795 + 4273363 * 2 ^ 59
def prefixEnd_4273363 : Nat := 4983230072969 + 3 ^ 40 * 4273363 * 2
def baseEnd_4273363 : Nat := 2194289230139469181309667

theorem tailTrace_4273363 : CollatzResearch.WordTrace tailWord_4273363 prefixEnd_4273363 2194289230139469181309667 := by
  unfold tailWord_4273363
  simp only [CollatzResearch.WordTrace]
  refine ⟨155862353217343158140592743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103908235478228772093728495 155862353217343158140592743)
  ·
    refine ⟨233793529826014737210889115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155862353217343158140592743 233793529826014737210889115)
    ·
      refine ⟨350690294739022105816333673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 233793529826014737210889115 350690294739022105816333673)
      ·
        refine ⟨263017721054266579362250255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 350690294739022105816333673 263017721054266579362250255)
        ·
          refine ⟨394526581581399869043375383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 263017721054266579362250255 394526581581399869043375383)
          ·
            refine ⟨591789872372099803565063075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 394526581581399869043375383 591789872372099803565063075)
            ·
              refine ⟨887684808558149705347594613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 591789872372099803565063075 887684808558149705347594613)
              ·
                refine ⟨83220450802326534876336995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 887684808558149705347594613 83220450802326534876336995)
                ·
                  refine ⟨124830676203489802314505493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 83220450802326534876336995 124830676203489802314505493)
                  ·
                    refine ⟨5851437947038584483492445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 124830676203489802314505493 5851437947038584483492445)
                    ·
                      refine ⟨2194289230139469181309667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5851437947038584483492445 2194289230139469181309667)
                      ·
                        rfl

theorem cell23_4273363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 5, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 5, 1, 6, 3].length) (baseStart_4273363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4273363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4273363 prefixEnd_4273363 := by exact prefixLift 4273363
  have htrace : WordTrace (prefixWord ++ tailWord_4273363) baseStart_4273363 baseEnd_4273363 := by
    simpa [prefixWord, tailWord_4273363, baseEnd_4273363] using wordTrace_append hprefix tailTrace_4273363
  have hstable : (prefixWord ++ tailWord_4273363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4273363).length < 2 ^ (prefixWord ++ tailWord_4273363).sum := by decide
  have hdescent : baseEnd_4273363 < baseStart_4273363 := by decide
  rcases family_descends (prefixWord ++ tailWord_4273363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4273381 : List Nat := [1, 3, 1, 4, 3, 2, 1, 2, 1, 3, 2]
def baseStart_4273381 : Nat := 118140960795 + 4273381 * 2 ^ 59
def prefixEnd_4273381 : Nat := 4983230072969 + 3 ^ 40 * 4273381 * 2
def baseEnd_4273381 : Nat := 2194298472791250110884585

theorem tailTrace_4273381 : CollatzResearch.WordTrace tailWord_4273381 prefixEnd_4273381 2194298472791250110884585 := by
  unfold tailWord_4273381
  simp only [CollatzResearch.WordTrace]
  refine ⟨155863009731277947214747997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103908673154185298143165331 155863009731277947214747997)
  ·
    refine ⟨58448628649229230205530499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 155863009731277947214747997 58448628649229230205530499)
    ·
      refine ⟨87672942973843845308295749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58448628649229230205530499 87672942973843845308295749)
      ·
        refine ⟨16438676807595720995305453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 87672942973843845308295749 16438676807595720995305453)
        ·
          refine ⟨6164503802848395373239545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16438676807595720995305453 6164503802848395373239545)
          ·
            refine ⟨4623377852136296529929659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6164503802848395373239545 4623377852136296529929659)
            ·
              refine ⟨6935066778204444794894489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4623377852136296529929659 6935066778204444794894489)
              ·
                refine ⟨5201300083653333596170867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6935066778204444794894489 5201300083653333596170867)
                ·
                  refine ⟨7801950125480000394256301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5201300083653333596170867 7801950125480000394256301)
                  ·
                    refine ⟨2925731297055000147846113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7801950125480000394256301 2925731297055000147846113)
                    ·
                      refine ⟨2194298472791250110884585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2925731297055000147846113 2194298472791250110884585)
                      ·
                        rfl

theorem cell23_4273381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 1, 2, 1, 3, 2].length) (baseStart_4273381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4273381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4273381 prefixEnd_4273381 := by exact prefixLift 4273381
  have htrace : WordTrace (prefixWord ++ tailWord_4273381) baseStart_4273381 baseEnd_4273381 := by
    simpa [prefixWord, tailWord_4273381, baseEnd_4273381] using wordTrace_append hprefix tailTrace_4273381
  have hstable : (prefixWord ++ tailWord_4273381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4273381).length < 2 ^ (prefixWord ++ tailWord_4273381).sum := by decide
  have hdescent : baseEnd_4273381 < baseStart_4273381 := by decide
  rcases family_descends (prefixWord ++ tailWord_4273381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4273394 : List Nat := [3, 2, 1, 3, 3, 1, 1, 2, 1, 4, 2]
def baseStart_4273394 : Nat := 118140960795 + 4273394 * 2 ^ 59
def prefixEnd_4273394 : Nat := 4983230072969 + 3 ^ 40 * 4273394 * 2
def baseEnd_4273394 : Nat := 2194305148039758560022025

theorem tailTrace_4273394 : CollatzResearch.WordTrace tailWord_4273394 prefixEnd_4273394 2194305148039758560022025 := by
  unfold tailWord_4273394
  simp only [CollatzResearch.WordTrace]
  refine ⟨38965870970057712608742809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103908989253487233623314157 38965870970057712608742809)
  ·
    refine ⟨29224403227543284456557107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38965870970057712608742809 29224403227543284456557107)
    ·
      refine ⟨43836604841314926684835661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29224403227543284456557107 43836604841314926684835661)
      ·
        refine ⟨16438726815493097506813373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43836604841314926684835661 16438726815493097506813373)
        ·
          refine ⟨6164522555809911565055015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16438726815493097506813373 6164522555809911565055015)
          ·
            refine ⟨9246783833714867347582523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6164522555809911565055015 9246783833714867347582523)
            ·
              refine ⟨13870175750572301021373785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9246783833714867347582523 13870175750572301021373785)
              ·
                refine ⟨10402631812929225766030339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13870175750572301021373785 10402631812929225766030339)
                ·
                  refine ⟨15603947719393838649045509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10402631812929225766030339 15603947719393838649045509)
                  ·
                    refine ⟨2925740197386344746696033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15603947719393838649045509 2925740197386344746696033)
                    ·
                      refine ⟨2194305148039758560022025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2925740197386344746696033 2194305148039758560022025)
                      ·
                        rfl

theorem cell23_4273394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 2, 1, 4, 2].length) (baseStart_4273394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4273394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4273394 prefixEnd_4273394 := by exact prefixLift 4273394
  have htrace : WordTrace (prefixWord ++ tailWord_4273394) baseStart_4273394 baseEnd_4273394 := by
    simpa [prefixWord, tailWord_4273394, baseEnd_4273394] using wordTrace_append hprefix tailTrace_4273394
  have hstable : (prefixWord ++ tailWord_4273394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4273394).length < 2 ^ (prefixWord ++ tailWord_4273394).sum := by decide
  have hdescent : baseEnd_4273394 < baseStart_4273394 := by decide
  rcases family_descends (prefixWord ++ tailWord_4273394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4273462 : List Nat := [5, 1, 2, 3, 2, 1, 1, 2, 2, 2, 2]
def baseStart_4273462 : Nat := 118140960795 + 4273462 * 2 ^ 59
def prefixEnd_4273462 : Nat := 4983230072969 + 3 ^ 40 * 4273462 * 2
def baseEnd_4273462 : Nat := 2194340064724264293971713

theorem tailTrace_4273462 : CollatzResearch.WordTrace tailWord_4273462 prefixEnd_4273462 2194340064724264293971713 := by
  unfold tailWord_4273462
  simp only [CollatzResearch.WordTrace]
  refine ⟨9741622752749031128027915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 103910642695989665365631093 9741622752749031128027915)
  ·
    refine ⟨14612434129123546692041873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9741622752749031128027915 14612434129123546692041873)
    ·
      refine ⟨10959325596842660019031405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14612434129123546692041873 10959325596842660019031405)
      ·
        refine ⟨4109747098815997507136777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10959325596842660019031405 4109747098815997507136777)
        ·
          refine ⟨3082310324111998130352583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4109747098815997507136777 3082310324111998130352583)
          ·
            refine ⟨4623465486167997195528875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3082310324111998130352583 4623465486167997195528875)
            ·
              refine ⟨6935198229251995793293313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4623465486167997195528875 6935198229251995793293313)
              ·
                refine ⟨5201398671938996844969985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6935198229251995793293313 5201398671938996844969985)
                ·
                  refine ⟨3901049003954247633727489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5201398671938996844969985 3901049003954247633727489)
                  ·
                    refine ⟨2925786752965685725295617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3901049003954247633727489 2925786752965685725295617)
                    ·
                      refine ⟨2194340064724264293971713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2925786752965685725295617 2194340064724264293971713)
                      ·
                        rfl

theorem cell23_4273462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 1, 2, 2, 2, 2].length) (baseStart_4273462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4273462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4273462 prefixEnd_4273462 := by exact prefixLift 4273462
  have htrace : WordTrace (prefixWord ++ tailWord_4273462) baseStart_4273462 baseEnd_4273462 := by
    simpa [prefixWord, tailWord_4273462, baseEnd_4273462] using wordTrace_append hprefix tailTrace_4273462
  have hstable : (prefixWord ++ tailWord_4273462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4273462).length < 2 ^ (prefixWord ++ tailWord_4273462).sum := by decide
  have hdescent : baseEnd_4273462 < baseStart_4273462 := by decide
  rcases family_descends (prefixWord ++ tailWord_4273462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4273483 : List Nat := [1, 1, 1, 1, 3, 1, 1, 2, 2, 1, 9]
def baseStart_4273483 : Nat := 118140960795 + 4273483 * 2 ^ 59
def prefixEnd_4273483 : Nat := 4983230072969 + 3 ^ 40 * 4273483 * 2
def baseEnd_4273483 : Nat := 2194350847818008711809115

theorem tailTrace_4273483 : CollatzResearch.WordTrace tailWord_4273483 prefixEnd_4273483 2194350847818008711809115 := by
  unfold tailWord_4273483
  simp only [CollatzResearch.WordTrace]
  refine ⟨155866729976908418634961103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103911153317938945756640735 155866729976908418634961103)
  ·
    refine ⟨233800094965362627952441655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155866729976908418634961103 233800094965362627952441655)
    ·
      refine ⟨350700142448043941928662483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 233800094965362627952441655 350700142448043941928662483)
      ·
        refine ⟨526050213672065912892993725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 350700142448043941928662483 526050213672065912892993725)
        ·
          refine ⟨197268830127024717334872647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 526050213672065912892993725 197268830127024717334872647)
          ·
            refine ⟨295903245190537076002308971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 197268830127024717334872647 295903245190537076002308971)
            ·
              refine ⟨443854867785805614003463457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 295903245190537076002308971 443854867785805614003463457)
              ·
                refine ⟨332891150839354210502597593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 443854867785805614003463457 332891150839354210502597593)
                ·
                  refine ⟨249668363129515657876948195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 332891150839354210502597593 249668363129515657876948195)
                  ·
                    refine ⟨374502544694273486815422293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 249668363129515657876948195 374502544694273486815422293)
                    ·
                      refine ⟨2194350847818008711809115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 374502544694273486815422293 2194350847818008711809115)
                      ·
                        rfl

theorem cell23_4273483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 2, 1, 9].length) (baseStart_4273483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4273483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4273483 prefixEnd_4273483 := by exact prefixLift 4273483
  have htrace : WordTrace (prefixWord ++ tailWord_4273483) baseStart_4273483 baseEnd_4273483 := by
    simpa [prefixWord, tailWord_4273483, baseEnd_4273483] using wordTrace_append hprefix tailTrace_4273483
  have hstable : (prefixWord ++ tailWord_4273483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4273483).length < 2 ^ (prefixWord ++ tailWord_4273483).sum := by decide
  have hdescent : baseEnd_4273483 < baseStart_4273483 := by decide
  rcases family_descends (prefixWord ++ tailWord_4273483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4273557 : List Nat := [1, 3, 2, 1, 1, 2, 2, 1, 2, 6, 2]
def baseStart_4273557 : Nat := 118140960795 + 4273557 * 2 ^ 59
def prefixEnd_4273557 : Nat := 4983230072969 + 3 ^ 40 * 4273557 * 2
def baseEnd_4273557 : Nat := 2194388845386441422283775

theorem tailTrace_4273557 : CollatzResearch.WordTrace tailWord_4273557 prefixEnd_4273557 2194388845386441422283775 := by
  unfold tailWord_4273557
  simp only [CollatzResearch.WordTrace]
  refine ⟨155869428978640329273154925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103912952652426886182103283 155869428978640329273154925)
  ·
    refine ⟨58451035866990123477433097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 155869428978640329273154925 58451035866990123477433097)
    ·
      refine ⟨43838276900242592608074823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58451035866990123477433097 43838276900242592608074823)
      ·
        refine ⟨65757415350363888912112235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43838276900242592608074823 65757415350363888912112235)
        ·
          refine ⟨98636123025545833368168353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65757415350363888912112235 98636123025545833368168353)
          ·
            refine ⟨73977092269159375026126265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98636123025545833368168353 73977092269159375026126265)
            ·
              refine ⟨55482819201869531269594699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73977092269159375026126265 55482819201869531269594699)
              ·
                refine ⟨83224228802804296904392049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55482819201869531269594699 83224228802804296904392049)
                ·
                  refine ⟨62418171602103222678294037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 83224228802804296904392049 62418171602103222678294037)
                  ·
                    refine ⟨2925851793848588563045033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 62418171602103222678294037 2925851793848588563045033)
                    ·
                      refine ⟨2194388845386441422283775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2925851793848588563045033 2194388845386441422283775)
                      ·
                        rfl

theorem cell23_4273557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 1, 2, 6, 2].length) (baseStart_4273557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4273557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4273557 prefixEnd_4273557 := by exact prefixLift 4273557
  have htrace : WordTrace (prefixWord ++ tailWord_4273557) baseStart_4273557 baseEnd_4273557 := by
    simpa [prefixWord, tailWord_4273557, baseEnd_4273557] using wordTrace_append hprefix tailTrace_4273557
  have hstable : (prefixWord ++ tailWord_4273557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4273557).length < 2 ^ (prefixWord ++ tailWord_4273557).sum := by decide
  have hdescent : baseEnd_4273557 < baseStart_4273557 := by decide
  rcases family_descends (prefixWord ++ tailWord_4273557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4273567 : List Nat := [1, 1, 2, 5, 1, 3, 1, 2, 1, 6]
def baseStart_4273567 : Nat := 118140960795 + 4273567 * 2 ^ 59
def prefixEnd_4273567 : Nat := 4983230072969 + 3 ^ 40 * 4273567 * 2
def baseEnd_4273567 : Nat := 731464660064328794386243

theorem tailTrace_4273567 : CollatzResearch.WordTrace tailWord_4273567 prefixEnd_4273567 731464660064328794386243 := by
  unfold tailWord_4273567
  simp only [CollatzResearch.WordTrace]
  refine ⟨155869793708604100981018955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103913195805736067320679303 155869793708604100981018955)
  ·
    refine ⟨233804690562906151471528433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155869793708604100981018955 233804690562906151471528433)
    ·
      refine ⟨175353517922179613603646325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 233804690562906151471528433 175353517922179613603646325)
      ·
        refine ⟨16439392305204338775341843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 175353517922179613603646325 16439392305204338775341843)
        ·
          refine ⟨24659088457806508163012765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16439392305204338775341843 24659088457806508163012765)
          ·
            refine ⟨9247158171677440561129787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24659088457806508163012765 9247158171677440561129787)
            ·
              refine ⟨13870737257516160841694681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9247158171677440561129787 13870737257516160841694681)
              ·
                refine ⟨10403052943137120631271011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13870737257516160841694681 10403052943137120631271011)
                ·
                  refine ⟨15604579414705680946906517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10403052943137120631271011 15604579414705680946906517)
                  ·
                    refine ⟨731464660064328794386243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15604579414705680946906517 731464660064328794386243)
                    ·
                      rfl

theorem cell23_4273567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 2, 1, 6].length) (baseStart_4273567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4273567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4273567 prefixEnd_4273567 := by exact prefixLift 4273567
  have htrace : WordTrace (prefixWord ++ tailWord_4273567) baseStart_4273567 baseEnd_4273567 := by
    simpa [prefixWord, tailWord_4273567, baseEnd_4273567] using wordTrace_append hprefix tailTrace_4273567
  have hstable : (prefixWord ++ tailWord_4273567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4273567).length < 2 ^ (prefixWord ++ tailWord_4273567).sum := by decide
  have hdescent : baseEnd_4273567 < baseStart_4273567 := by decide
  rcases family_descends (prefixWord ++ tailWord_4273567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4273600 : List Nat := [2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 6]
def baseStart_4273600 : Nat := 118140960795 + 4273600 * 2 ^ 59
def prefixEnd_4273600 : Nat := 4983230072969 + 3 ^ 40 * 4273600 * 2
def baseEnd_4273600 : Nat := 2194410925054584754046077

theorem tailTrace_4273600 : CollatzResearch.WordTrace tailWord_4273600 prefixEnd_4273600 2194410925054584754046077 := by
  unfold tailWord_4273600
  simp only [CollatzResearch.WordTrace]
  refine ⟨77935498658742273808485127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103913998211656365077980169 77935498658742273808485127)
  ·
    refine ⟨116903247988113410712727691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77935498658742273808485127 116903247988113410712727691)
    ·
      refine ⟨175354871982170116069091537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116903247988113410712727691 175354871982170116069091537)
      ·
        refine ⟨131516153986627587051818653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 175354871982170116069091537 131516153986627587051818653)
        ·
          refine ⟨49318557744985345144431995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 131516153986627587051818653 49318557744985345144431995)
          ·
            refine ⟨73977836617478017716647993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49318557744985345144431995 73977836617478017716647993)
            ·
              refine ⟨55483377463108513287485995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73977836617478017716647993 55483377463108513287485995)
              ·
                refine ⟨83225066194662769931228993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55483377463108513287485995 83225066194662769931228993)
                ·
                  refine ⟨62418799645997077448421745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 83225066194662769931228993 62418799645997077448421745)
                  ·
                    refine ⟨46814099734497808086316309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 62418799645997077448421745 46814099734497808086316309)
                    ·
                      refine ⟨2194410925054584754046077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 46814099734497808086316309 2194410925054584754046077)
                      ·
                        rfl

theorem cell23_4273600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 6].length) (baseStart_4273600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4273600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4273600 prefixEnd_4273600 := by exact prefixLift 4273600
  have htrace : WordTrace (prefixWord ++ tailWord_4273600) baseStart_4273600 baseEnd_4273600 := by
    simpa [prefixWord, tailWord_4273600, baseEnd_4273600] using wordTrace_append hprefix tailTrace_4273600
  have hstable : (prefixWord ++ tailWord_4273600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4273600).length < 2 ^ (prefixWord ++ tailWord_4273600).sum := by decide
  have hdescent : baseEnd_4273600 < baseStart_4273600 := by decide
  rcases family_descends (prefixWord ++ tailWord_4273600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4273602 : List Nat := [3, 5, 2, 1, 1, 1, 1, 2, 3, 1, 3]
def baseStart_4273602 : Nat := 118140960795 + 4273602 * 2 ^ 59
def prefixEnd_4273602 : Nat := 4983230072969 + 3 ^ 40 * 4273602 * 2
def baseEnd_4273602 : Nat := 2194411952015893746221069

theorem tailTrace_4273602 : CollatzResearch.WordTrace tailWord_4273602 prefixEnd_4273602 2194411952015893746221069 := by
  unfold tailWord_4273602
  simp only [CollatzResearch.WordTrace]
  refine ⟨38967767565869325489635765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103914046842318201305695373 38967767565869325489635765)
  ·
    refine ⟨3653228209300249264653353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 38967767565869325489635765 3653228209300249264653353)
    ·
      refine ⟨2739921156975186948490015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3653228209300249264653353 2739921156975186948490015)
      ·
        refine ⟨4109881735462780422735023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2739921156975186948490015 4109881735462780422735023)
        ·
          refine ⟨6164822603194170634102535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4109881735462780422735023 6164822603194170634102535)
          ·
            refine ⟨9247233904791255951153803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6164822603194170634102535 9247233904791255951153803)
            ·
              refine ⟨13870850857186883926730705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9247233904791255951153803 13870850857186883926730705)
              ·
                refine ⟨10403138142890162945048029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13870850857186883926730705 10403138142890162945048029)
                ·
                  refine ⟨3901176803583811104393011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10403138142890162945048029 3901176803583811104393011)
                  ·
                    refine ⟨5851765205375716656589517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3901176803583811104393011 5851765205375716656589517)
                    ·
                      refine ⟨2194411952015893746221069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5851765205375716656589517 2194411952015893746221069)
                      ·
                        rfl

theorem cell23_4273602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_4273602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4273602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4273602 prefixEnd_4273602 := by exact prefixLift 4273602
  have htrace : WordTrace (prefixWord ++ tailWord_4273602) baseStart_4273602 baseEnd_4273602 := by
    simpa [prefixWord, tailWord_4273602, baseEnd_4273602] using wordTrace_append hprefix tailTrace_4273602
  have hstable : (prefixWord ++ tailWord_4273602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4273602).length < 2 ^ (prefixWord ++ tailWord_4273602).sum := by decide
  have hdescent : baseEnd_4273602 < baseStart_4273602 := by decide
  rcases family_descends (prefixWord ++ tailWord_4273602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4273604 : List Nat := [2, 3, 3, 2, 1, 1, 1, 3, 1, 2, 4]
def baseStart_4273604 : Nat := 118140960795 + 4273604 * 2 ^ 59
def prefixEnd_4273604 : Nat := 4983230072969 + 3 ^ 40 * 4273604 * 2
def baseEnd_4273604 : Nat := 2194412978977202738396059

theorem tailTrace_4273604 : CollatzResearch.WordTrace tailWord_4273604 prefixEnd_4273604 2194412978977202738396059 := by
  unfold tailWord_4273604
  simp only [CollatzResearch.WordTrace]
  refine ⟨77935571604735028150057933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103914095472980037533410577 77935571604735028150057933)
  ·
    refine ⟨29225839351775635556271725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77935571604735028150057933 29225839351775635556271725)
    ·
      refine ⟨10959689756915863333601897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29225839351775635556271725 10959689756915863333601897)
      ·
        refine ⟨8219767317686897500201423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10959689756915863333601897 8219767317686897500201423)
        ·
          refine ⟨12329650976530346250302135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8219767317686897500201423 12329650976530346250302135)
          ·
            refine ⟨18494476464795519375453203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12329650976530346250302135 18494476464795519375453203)
            ·
              refine ⟨27741714697193279063179805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18494476464795519375453203 27741714697193279063179805)
              ·
                refine ⟨10403143011447479648692427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27741714697193279063179805 10403143011447479648692427)
                ·
                  refine ⟨15604714517171219473038641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10403143011447479648692427 15604714517171219473038641)
                  ·
                    refine ⟨11703535887878414604778981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15604714517171219473038641 11703535887878414604778981)
                    ·
                      refine ⟨2194412978977202738396059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11703535887878414604778981 2194412978977202738396059)
                      ·
                        rfl

theorem cell23_4273604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_4273604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4273604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4273604 prefixEnd_4273604 := by exact prefixLift 4273604
  have htrace : WordTrace (prefixWord ++ tailWord_4273604) baseStart_4273604 baseEnd_4273604 := by
    simpa [prefixWord, tailWord_4273604, baseEnd_4273604] using wordTrace_append hprefix tailTrace_4273604
  have hstable : (prefixWord ++ tailWord_4273604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4273604).length < 2 ^ (prefixWord ++ tailWord_4273604).sum := by decide
  have hdescent : baseEnd_4273604 < baseStart_4273604 := by decide
  rcases family_descends (prefixWord ++ tailWord_4273604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4273715 : List Nat := [1, 1, 1, 2, 4, 5, 2, 1, 2, 2, 2]
def baseStart_4273715 : Nat := 118140960795 + 4273715 * 2 ^ 59
def prefixEnd_4273715 : Nat := 4983230072969 + 3 ^ 40 * 4273715 * 2
def baseEnd_4273715 : Nat := 2194469975329851804108049

theorem tailTrace_4273715 : CollatzResearch.WordTrace tailWord_4273715 prefixEnd_4273715 2194469975329851804108049 := by
  unfold tailWord_4273715
  simp only [CollatzResearch.WordTrace]
  refine ⟨155875191712067922257406599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103916794474711948171604399 155875191712067922257406599)
  ·
    refine ⟨233812787568101883386109899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155875191712067922257406599 233812787568101883386109899)
    ·
      refine ⟨350719181352152825079164849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 233812787568101883386109899 350719181352152825079164849)
      ·
        refine ⟨263039386014114618809373637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 350719181352152825079164849 263039386014114618809373637)
        ·
          refine ⟨49319884877646491026757557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 263039386014114618809373637 49319884877646491026757557)
          ·
            refine ⟨4623739207279358533758521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 49319884877646491026757557 4623739207279358533758521)
            ·
              refine ⟨3467804405459518900318891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4623739207279358533758521 3467804405459518900318891)
              ·
                refine ⟨5201706608189278350478337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3467804405459518900318891 5201706608189278350478337)
                ·
                  refine ⟨3901279956141958762858753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5201706608189278350478337 3901279956141958762858753)
                  ·
                    refine ⟨2925959967106469072144065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3901279956141958762858753 2925959967106469072144065)
                    ·
                      refine ⟨2194469975329851804108049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2925959967106469072144065 2194469975329851804108049)
                      ·
                        rfl

theorem cell23_4273715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 2, 1, 2, 2, 2].length) (baseStart_4273715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4273715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4273715 prefixEnd_4273715 := by exact prefixLift 4273715
  have htrace : WordTrace (prefixWord ++ tailWord_4273715) baseStart_4273715 baseEnd_4273715 := by
    simpa [prefixWord, tailWord_4273715, baseEnd_4273715] using wordTrace_append hprefix tailTrace_4273715
  have hstable : (prefixWord ++ tailWord_4273715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4273715).length < 2 ^ (prefixWord ++ tailWord_4273715).sum := by decide
  have hdescent : baseEnd_4273715 < baseStart_4273715 := by decide
  rcases family_descends (prefixWord ++ tailWord_4273715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4273737 : List Nat := [1, 2, 1, 1, 2, 2, 1, 5, 1, 3, 4]
def baseStart_4273737 : Nat := 118140960795 + 4273737 * 2 ^ 59
def prefixEnd_4273737 : Nat := 4983230072969 + 3 ^ 40 * 4273737 * 2
def baseEnd_4273737 : Nat := 2194481271904250718032947

theorem tailTrace_4273737 : CollatzResearch.WordTrace tailWord_4273737 prefixEnd_4273737 2194481271904250718032947 := by
  unfold tailWord_4273737
  simp only [CollatzResearch.WordTrace]
  refine ⟨155875994117988220014707465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103917329411992146676471643 155875994117988220014707465)
  ·
    refine ⟨116906995588491165011030599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155875994117988220014707465 116906995588491165011030599)
    ·
      refine ⟨175360493382736747516545899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116906995588491165011030599 175360493382736747516545899)
      ·
        refine ⟨263040740074105121274818849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175360493382736747516545899 263040740074105121274818849)
        ·
          refine ⟨197280555055578840956114137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 263040740074105121274818849 197280555055578840956114137)
          ·
            refine ⟨147960416291684130717085603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 197280555055578840956114137 147960416291684130717085603)
            ·
              refine ⟨221940624437526196075628405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 147960416291684130717085603 221940624437526196075628405)
              ·
                refine ⟨20806933541018080882090163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 221940624437526196075628405 20806933541018080882090163)
                ·
                  refine ⟨31210400311527121323135245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20806933541018080882090163 31210400311527121323135245)
                  ·
                    refine ⟨11703900116822670496175717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 31210400311527121323135245 11703900116822670496175717)
                    ·
                      refine ⟨2194481271904250718032947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11703900116822670496175717 2194481271904250718032947)
                      ·
                        rfl

theorem cell23_4273737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 5, 1, 3, 4].length) (baseStart_4273737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4273737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4273737 prefixEnd_4273737 := by exact prefixLift 4273737
  have htrace : WordTrace (prefixWord ++ tailWord_4273737) baseStart_4273737 baseEnd_4273737 := by
    simpa [prefixWord, tailWord_4273737, baseEnd_4273737] using wordTrace_append hprefix tailTrace_4273737
  have hstable : (prefixWord ++ tailWord_4273737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4273737).length < 2 ^ (prefixWord ++ tailWord_4273737).sum := by decide
  have hdescent : baseEnd_4273737 < baseStart_4273737 := by decide
  rcases family_descends (prefixWord ++ tailWord_4273737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4273754 : List Nat := [3, 1, 1, 2, 1, 1, 1, 2, 3, 6, 2]
def baseStart_4273754 : Nat := 118140960795 + 4273754 * 2 ^ 59
def prefixEnd_4273754 : Nat := 4983230072969 + 3 ^ 40 * 4273754 * 2
def baseEnd_4273754 : Nat := 2194490001075377151520369

theorem tailTrace_4273754 : CollatzResearch.WordTrace tailWord_4273754 prefixEnd_4273754 2194490001075377151520369 := by
  unfold tailWord_4273754
  simp only [CollatzResearch.WordTrace]
  refine ⟨38969153539731657979519079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103917742772617754612050877 38969153539731657979519079)
  ·
    refine ⟨58453730309597486969278619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38969153539731657979519079 58453730309597486969278619)
    ·
      refine ⟨87680595464396230453917929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58453730309597486969278619 87680595464396230453917929)
      ·
        refine ⟨65760446598297172840438447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87680595464396230453917929 65760446598297172840438447)
        ·
          refine ⟨98640669897445759260657671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65760446598297172840438447 98640669897445759260657671)
          ·
            refine ⟨147961004846168638890986507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98640669897445759260657671 147961004846168638890986507)
            ·
              refine ⟨221941507269252958336479761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 147961004846168638890986507 221941507269252958336479761)
              ·
                refine ⟨166456130451939718752359821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 221941507269252958336479761 166456130451939718752359821)
                ·
                  refine ⟨62421048919477394532134933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 166456130451939718752359821 62421048919477394532134933)
                  ·
                    refine ⟨2925986668100502868693825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 62421048919477394532134933 2925986668100502868693825)
                    ·
                      refine ⟨2194490001075377151520369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2925986668100502868693825 2194490001075377151520369)
                      ·
                        rfl

theorem cell23_4273754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 2, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 2, 3, 6, 2].length) (baseStart_4273754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4273754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4273754 prefixEnd_4273754 := by exact prefixLift 4273754
  have htrace : WordTrace (prefixWord ++ tailWord_4273754) baseStart_4273754 baseEnd_4273754 := by
    simpa [prefixWord, tailWord_4273754, baseEnd_4273754] using wordTrace_append hprefix tailTrace_4273754
  have hstable : (prefixWord ++ tailWord_4273754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4273754).length < 2 ^ (prefixWord ++ tailWord_4273754).sum := by decide
  have hdescent : baseEnd_4273754 < baseStart_4273754 := by decide
  rcases family_descends (prefixWord ++ tailWord_4273754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4273781 : List Nat := [1, 3, 4, 2, 1, 1, 1, 1, 5, 4]
def baseStart_4273781 : Nat := 118140960795 + 4273781 * 2 ^ 59
def prefixEnd_4273781 : Nat := 4983230072969 + 3 ^ 40 * 4273781 * 2
def baseEnd_4273781 : Nat := 731501288351016181960915

theorem tailTrace_4273781 : CollatzResearch.WordTrace tailWord_4273781 prefixEnd_4273781 731501288351016181960915 := by
  unfold tailWord_4273781
  simp only [CollatzResearch.WordTrace]
  refine ⟨155877598929828815529309197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103918399286552543686206131 155877598929828815529309197)
  ·
    refine ⟨58454099598685805823490949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 155877598929828815529309197 58454099598685805823490949)
    ·
      refine ⟨10960143674753588591904553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58454099598685805823490949 10960143674753588591904553)
      ·
        refine ⟨8220107756065191443928415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10960143674753588591904553 8220107756065191443928415)
        ·
          refine ⟨12330161634097787165892623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8220107756065191443928415 12330161634097787165892623)
          ·
            refine ⟨18495242451146680748838935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12330161634097787165892623 18495242451146680748838935)
            ·
              refine ⟨27742863676720021123258403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18495242451146680748838935 27742863676720021123258403)
              ·
                refine ⟨41614295515080031684887605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27742863676720021123258403 41614295515080031684887605)
                ·
                  refine ⟨3901340204538752970458213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 41614295515080031684887605 3901340204538752970458213)
                  ·
                    refine ⟨731501288351016181960915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3901340204538752970458213 731501288351016181960915)
                    ·
                      rfl

theorem cell23_4273781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 1, 5, 4].length) (baseStart_4273781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4273781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4273781 prefixEnd_4273781 := by exact prefixLift 4273781
  have htrace : WordTrace (prefixWord ++ tailWord_4273781) baseStart_4273781 baseEnd_4273781 := by
    simpa [prefixWord, tailWord_4273781, baseEnd_4273781] using wordTrace_append hprefix tailTrace_4273781
  have hstable : (prefixWord ++ tailWord_4273781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4273781).length < 2 ^ (prefixWord ++ tailWord_4273781).sum := by decide
  have hdescent : baseEnd_4273781 < baseStart_4273781 := by decide
  rcases family_descends (prefixWord ++ tailWord_4273781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4273817 : List Nat := [1, 2, 1, 2, 1, 2, 2, 2, 2, 1, 7]
def baseStart_4273817 : Nat := 118140960795 + 4273817 * 2 ^ 59
def prefixEnd_4273817 : Nat := 4983230072969 + 3 ^ 40 * 4273817 * 2
def baseEnd_4273817 : Nat := 2194522350356610405032579

theorem tailTrace_4273817 : CollatzResearch.WordTrace tailWord_4273817 prefixEnd_4273817 2194522350356610405032579 := by
  unfold tailWord_4273817
  simp only [CollatzResearch.WordTrace]
  refine ⟨155878911957698393677619705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103919274638465595785079803 155878911957698393677619705)
  ·
    refine ⟨116909183968273795258214779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155878911957698393677619705 116909183968273795258214779)
    ·
      refine ⟨175363775952410692887322169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116909183968273795258214779 175363775952410692887322169)
      ·
        refine ⟨131522831964308019665491627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 175363775952410692887322169 131522831964308019665491627)
        ·
          refine ⟨197284247946462029498237441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131522831964308019665491627 197284247946462029498237441)
          ·
            refine ⟨147963185959846522123678081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 197284247946462029498237441 147963185959846522123678081)
            ·
              refine ⟨110972389469884891592758561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 147963185959846522123678081 110972389469884891592758561)
              ·
                refine ⟨83229292102413668694568921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 110972389469884891592758561 83229292102413668694568921)
                ·
                  refine ⟨62421969076810251520926691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 83229292102413668694568921 62421969076810251520926691)
                  ·
                    refine ⟨93632953615215377281390037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 62421969076810251520926691 93632953615215377281390037)
                    ·
                      refine ⟨2194522350356610405032579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 93632953615215377281390037 2194522350356610405032579)
                      ·
                        rfl

theorem cell23_4273817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 2, 2, 1, 7].length) (baseStart_4273817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4273817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4273817 prefixEnd_4273817 := by exact prefixLift 4273817
  have htrace : WordTrace (prefixWord ++ tailWord_4273817) baseStart_4273817 baseEnd_4273817 := by
    simpa [prefixWord, tailWord_4273817, baseEnd_4273817] using wordTrace_append hprefix tailTrace_4273817
  have hstable : (prefixWord ++ tailWord_4273817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4273817).length < 2 ^ (prefixWord ++ tailWord_4273817).sum := by decide
  have hdescent : baseEnd_4273817 < baseStart_4273817 := by decide
  rcases family_descends (prefixWord ++ tailWord_4273817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4273888 : List Nat := [2, 1, 1, 3, 1, 2, 6, 1, 2, 4]
def baseStart_4273888 : Nat := 118140960795 + 4273888 * 2 ^ 59
def prefixEnd_4273888 : Nat := 4983230072969 + 3 ^ 40 * 4273888 * 2
def baseEnd_4273888 : Nat := 731519602494359875748251

theorem tailTrace_4273888 : CollatzResearch.WordTrace tailWord_4273888 prefixEnd_4273888 731519602494359875748251 := by
  unfold tailWord_4273888
  simp only [CollatzResearch.WordTrace]
  refine ⟨77940750770220586401727159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103921001026960781868969545 77940750770220586401727159)
  ·
    refine ⟨116911126155330879602590739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77940750770220586401727159 116911126155330879602590739)
    ·
      refine ⟨175366689232996319403886109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116911126155330879602590739 175366689232996319403886109)
      ·
        refine ⟨65762508462373619776457291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 175366689232996319403886109 65762508462373619776457291)
        ·
          refine ⟨98643762693560429664685937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65762508462373619776457291 98643762693560429664685937)
          ·
            refine ⟨73982822020170322248514453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98643762693560429664685937 73982822020170322248514453)
            ·
              refine ⟨3467944782195483855399115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 73982822020170322248514453 3467944782195483855399115)
              ·
                refine ⟨5201917173293225783098673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3467944782195483855399115 5201917173293225783098673)
                ·
                  refine ⟨3901437879969919337324005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5201917173293225783098673 3901437879969919337324005)
                  ·
                    refine ⟨731519602494359875748251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3901437879969919337324005 731519602494359875748251)
                    ·
                      rfl

theorem cell23_4273888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 6, 1, 2, 4].length) (baseStart_4273888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4273888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4273888 prefixEnd_4273888 := by exact prefixLift 4273888
  have htrace : WordTrace (prefixWord ++ tailWord_4273888) baseStart_4273888 baseEnd_4273888 := by
    simpa [prefixWord, tailWord_4273888, baseEnd_4273888] using wordTrace_append hprefix tailTrace_4273888
  have hstable : (prefixWord ++ tailWord_4273888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4273888).length < 2 ^ (prefixWord ++ tailWord_4273888).sum := by decide
  have hdescent : baseEnd_4273888 < baseStart_4273888 := by decide
  rcases family_descends (prefixWord ++ tailWord_4273888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4273898 : List Nat := [3, 1, 3, 1, 1, 1, 5, 2, 1, 2, 3]
def baseStart_4273898 : Nat := 118140960795 + 4273898 * 2 ^ 59
def prefixEnd_4273898 : Nat := 4983230072969 + 3 ^ 40 * 4273898 * 2
def baseEnd_4273898 : Nat := 2194563942289624588119707

theorem tailTrace_4273898 : CollatzResearch.WordTrace tailWord_4273898 prefixEnd_4273898 2194563942289624588119707 := by
  unfold tailWord_4273898
  simp only [CollatzResearch.WordTrace]
  refine ⟨38970466567601236127829587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103921244180269963007545565 38970466567601236127829587)
  ·
    refine ⟨58455699851401854191744381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38970466567601236127829587 58455699851401854191744381)
    ·
      refine ⟨21920887444275695321904143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58455699851401854191744381 21920887444275695321904143)
      ·
        refine ⟨32881331166413542982856215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21920887444275695321904143 32881331166413542982856215)
        ·
          refine ⟨49321996749620314474284323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32881331166413542982856215 49321996749620314474284323)
          ·
            refine ⟨73982995124430471711426485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49321996749620314474284323 73982995124430471711426485)
            ·
              refine ⟨6935905792915356722946233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 73982995124430471711426485 6935905792915356722946233)
              ·
                refine ⟨5201929344686517542209675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6935905792915356722946233 5201929344686517542209675)
                ·
                  refine ⟨7802894017029776313314513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5201929344686517542209675 7802894017029776313314513)
                  ·
                    refine ⟨5852170512772332234985885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7802894017029776313314513 5852170512772332234985885)
                    ·
                      refine ⟨2194563942289624588119707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5852170512772332234985885 2194563942289624588119707)
                      ·
                        rfl

theorem cell23_4273898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 5, 2, 1, 2, 3].length) (baseStart_4273898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4273898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4273898 prefixEnd_4273898 := by exact prefixLift 4273898
  have htrace : WordTrace (prefixWord ++ tailWord_4273898) baseStart_4273898 baseEnd_4273898 := by
    simpa [prefixWord, tailWord_4273898, baseEnd_4273898] using wordTrace_append hprefix tailTrace_4273898
  have hstable : (prefixWord ++ tailWord_4273898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4273898).length < 2 ^ (prefixWord ++ tailWord_4273898).sum := by decide
  have hdescent : baseEnd_4273898 < baseStart_4273898 := by decide
  rcases family_descends (prefixWord ++ tailWord_4273898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4273911 : List Nat := [1, 1, 3, 1, 1, 1, 4, 1, 6, 1, 3]
def baseStart_4273911 : Nat := 118140960795 + 4273911 * 2 ^ 59
def prefixEnd_4273911 : Nat := 4983230072969 + 3 ^ 40 * 4273911 * 2
def baseEnd_4273911 : Nat := 2194570617538133037257147

theorem tailTrace_4273911 : CollatzResearch.WordTrace tailWord_4273911 prefixEnd_4273911 2194570617538133037257147 := by
  unfold tailWord_4273911
  simp only [CollatzResearch.WordTrace]
  refine ⟨155882340419357847731541587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103921560279571898487694391 155882340419357847731541587)
  ·
    refine ⟨233823510629036771597312381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155882340419357847731541587 233823510629036771597312381)
    ·
      refine ⟨87683816485888789348992143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 233823510629036771597312381 87683816485888789348992143)
      ·
        refine ⟨131525724728833184023488215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87683816485888789348992143 131525724728833184023488215)
        ·
          refine ⟨197288587093249776035232323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131525724728833184023488215 197288587093249776035232323)
          ·
            refine ⟨295932880639874664052848485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 197288587093249776035232323 295932880639874664052848485)
            ·
              refine ⟨55487415119976499509909091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 295932880639874664052848485 55487415119976499509909091)
              ·
                refine ⟨83231122679964749264863637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55487415119976499509909091 83231122679964749264863637)
                ·
                  refine ⟨3901458875623347621790483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 83231122679964749264863637 3901458875623347621790483)
                  ·
                    refine ⟨5852188313435021432685725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3901458875623347621790483 5852188313435021432685725)
                    ·
                      refine ⟨2194570617538133037257147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5852188313435021432685725 2194570617538133037257147)
                      ·
                        rfl

theorem cell23_4273911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 1, 6, 1, 3].length) (baseStart_4273911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4273911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4273911 prefixEnd_4273911 := by exact prefixLift 4273911
  have htrace : WordTrace (prefixWord ++ tailWord_4273911) baseStart_4273911 baseEnd_4273911 := by
    simpa [prefixWord, tailWord_4273911, baseEnd_4273911] using wordTrace_append hprefix tailTrace_4273911
  have hstable : (prefixWord ++ tailWord_4273911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4273911).length < 2 ^ (prefixWord ++ tailWord_4273911).sum := by decide
  have hdescent : baseEnd_4273911 < baseStart_4273911 := by decide
  rcases family_descends (prefixWord ++ tailWord_4273911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4273944 : List Nat := [2, 1, 2, 3, 1, 1, 3, 1, 1, 8]
def baseStart_4273944 : Nat := 118140960795 + 4273944 * 2 ^ 59
def prefixEnd_4273944 : Nat := 4983230072969 + 3 ^ 40 * 4273944 * 2
def baseEnd_4273944 : Nat := 731529187466577136048165

theorem tailTrace_4273944 : CollatzResearch.WordTrace tailWord_4273944 prefixEnd_4273944 731529187466577136048165 := by
  unfold tailWord_4273944
  simp only [CollatzResearch.WordTrace]
  refine ⟨77941772014119147183746443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103922362685492196244995257 77941772014119147183746443)
  ·
    refine ⟨116912658021178720775619665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77941772014119147183746443 116912658021178720775619665)
    ·
      refine ⟨87684493515884040581714749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116912658021178720775619665 87684493515884040581714749)
      ·
        refine ⟨32881685068456515218143031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87684493515884040581714749 32881685068456515218143031)
        ·
          refine ⟨49322527602684772827214547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32881685068456515218143031 49322527602684772827214547)
          ·
            refine ⟨73983791404027159240821821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49322527602684772827214547 73983791404027159240821821)
            ·
              refine ⟨27743921776510184715308183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 73983791404027159240821821 27743921776510184715308183)
              ·
                refine ⟨41615882664765277072962275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27743921776510184715308183 41615882664765277072962275)
                ·
                  refine ⟨62423823997147915609443413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41615882664765277072962275 62423823997147915609443413)
                  ·
                    refine ⟨731529187466577136048165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 62423823997147915609443413 731529187466577136048165)
                    ·
                      rfl

theorem cell23_4273944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 1, 1, 8].length) (baseStart_4273944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4273944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4273944 prefixEnd_4273944 := by exact prefixLift 4273944
  have htrace : WordTrace (prefixWord ++ tailWord_4273944) baseStart_4273944 baseEnd_4273944 := by
    simpa [prefixWord, tailWord_4273944, baseEnd_4273944] using wordTrace_append hprefix tailTrace_4273944
  have hstable : (prefixWord ++ tailWord_4273944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4273944).length < 2 ^ (prefixWord ++ tailWord_4273944).sum := by decide
  have hdescent : baseEnd_4273944 < baseStart_4273944 := by decide
  rcases family_descends (prefixWord ++ tailWord_4273944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4273972 : List Nat := [2, 5, 1, 1, 2, 2, 1, 3, 1, 3, 2]
def baseStart_4273972 : Nat := 118140960795 + 4273972 * 2 ^ 59
def prefixEnd_4273972 : Nat := 4983230072969 + 3 ^ 40 * 4273972 * 2
def baseEnd_4273972 : Nat := 2194601939858057298594367

theorem tailTrace_4273972 : CollatzResearch.WordTrace tailWord_4273972 prefixEnd_4273972 2194601939858057298594367 := by
  unfold tailWord_4273972
  simp only [CollatzResearch.WordTrace]
  refine ⟨77942282636068427574756085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103923043514757903433008113 77942282636068427574756085)
  ·
    refine ⟨7307088997131415085133383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 77942282636068427574756085 7307088997131415085133383)
    ·
      refine ⟨10960633495697122627700075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7307088997131415085133383 10960633495697122627700075)
      ·
        refine ⟨16440950243545683941550113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10960633495697122627700075 16440950243545683941550113)
        ·
          refine ⟨12330712682659262956162585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16440950243545683941550113 12330712682659262956162585)
          ·
            refine ⟨9248034511994447217121939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12330712682659262956162585 9248034511994447217121939)
            ·
              refine ⟨13872051767991670825682909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9248034511994447217121939 13872051767991670825682909)
              ·
                refine ⟨5202019412996876559631091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13872051767991670825682909 5202019412996876559631091)
                ·
                  refine ⟨7803029119495314839446637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5202019412996876559631091 7803029119495314839446637)
                  ·
                    refine ⟨2926135919810743064792489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7803029119495314839446637 2926135919810743064792489)
                    ·
                      refine ⟨2194601939858057298594367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2926135919810743064792489 2194601939858057298594367)
                      ·
                        rfl

theorem cell23_4273972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 3, 1, 3, 2].length) (baseStart_4273972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4273972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4273972 prefixEnd_4273972 := by exact prefixLift 4273972
  have htrace : WordTrace (prefixWord ++ tailWord_4273972) baseStart_4273972 baseEnd_4273972 := by
    simpa [prefixWord, tailWord_4273972, baseEnd_4273972] using wordTrace_append hprefix tailTrace_4273972
  have hstable : (prefixWord ++ tailWord_4273972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4273972).length < 2 ^ (prefixWord ++ tailWord_4273972).sum := by decide
  have hdescent : baseEnd_4273972 < baseStart_4273972 := by decide
  rcases family_descends (prefixWord ++ tailWord_4273972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4274021 : List Nat := [1, 3, 1, 3, 1, 1, 1, 5, 2, 5]
def baseStart_4274021 : Nat := 118140960795 + 4274021 * 2 ^ 59
def prefixEnd_4274021 : Nat := 4983230072969 + 3 ^ 40 * 4274021 * 2
def baseEnd_4274021 : Nat := 731542366803375868960547

theorem tailTrace_4274021 : CollatzResearch.WordTrace tailWord_4274021 prefixEnd_4274021 731542366803375868960547 := by
  unfold tailWord_4274021
  simp only [CollatzResearch.WordTrace]
  refine ⟨155886352448959336518045917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103924234965972891012030611 155886352448959336518045917)
  ·
    refine ⟨58457382168359751194267219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 155886352448959336518045917 58457382168359751194267219)
    ·
      refine ⟨87686073252539626791400829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58457382168359751194267219 87686073252539626791400829)
      ·
        refine ⟨32882277469702360046775311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87686073252539626791400829 32882277469702360046775311)
        ·
          refine ⟨49323416204553540070162967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32882277469702360046775311 49323416204553540070162967)
          ·
            refine ⟨73985124306830310105244451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49323416204553540070162967 73985124306830310105244451)
            ·
              refine ⟨110977686460245465157866677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73985124306830310105244451 110977686460245465157866677)
              ·
                refine ⟨10404158105648012358550001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 110977686460245465157866677 10404158105648012358550001)
                ·
                  refine ⟨7803118579236009268912501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10404158105648012358550001 7803118579236009268912501)
                  ·
                    refine ⟨731542366803375868960547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7803118579236009268912501 731542366803375868960547)
                    ·
                      rfl

theorem cell23_4274021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 5, 2, 5].length) (baseStart_4274021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4274021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4274021 prefixEnd_4274021 := by exact prefixLift 4274021
  have htrace : WordTrace (prefixWord ++ tailWord_4274021) baseStart_4274021 baseEnd_4274021 := by
    simpa [prefixWord, tailWord_4274021, baseEnd_4274021] using wordTrace_append hprefix tailTrace_4274021
  have hstable : (prefixWord ++ tailWord_4274021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4274021).length < 2 ^ (prefixWord ++ tailWord_4274021).sum := by decide
  have hdescent : baseEnd_4274021 < baseStart_4274021 := by decide
  rcases family_descends (prefixWord ++ tailWord_4274021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4274111 : List Nat := [1, 1, 2, 2, 2, 1, 3, 1, 5, 5]
def baseStart_4274111 : Nat := 118140960795 + 4274111 * 2 ^ 59
def prefixEnd_4274111 : Nat := 4983230072969 + 3 ^ 40 * 4274111 * 2
def baseEnd_4274111 : Nat := 731557771223010751585409

theorem tailTrace_4274111 : CollatzResearch.WordTrace tailWord_4274111 prefixEnd_4274111 731557771223010751585409 := by
  unfold tailWord_4274111
  simp only [CollatzResearch.WordTrace]
  refine ⟨155889635018633281888822187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103926423345755521259214791 155889635018633281888822187)
  ·
    refine ⟨233834452527949922833233281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155889635018633281888822187 233834452527949922833233281)
    ·
      refine ⟨175375839395962442124924961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 233834452527949922833233281 175375839395962442124924961)
      ·
        refine ⟨131531879546971831593693721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 175375839395962442124924961 131531879546971831593693721)
        ·
          refine ⟨98648909660228873695270291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 131531879546971831593693721 98648909660228873695270291)
          ·
            refine ⟨147973364490343310542905437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98648909660228873695270291 147973364490343310542905437)
            ·
              refine ⟨55490011683878741453589539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 147973364490343310542905437 55490011683878741453589539)
              ·
                refine ⟨83235017525818112180384309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55490011683878741453589539 83235017525818112180384309)
                ·
                  refine ⟨7803282893045448016911029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 83235017525818112180384309 7803282893045448016911029)
                  ·
                    refine ⟨731557771223010751585409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7803282893045448016911029 731557771223010751585409)
                    ·
                      rfl

theorem cell23_4274111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 1, 5, 5].length) (baseStart_4274111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4274111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4274111 prefixEnd_4274111 := by exact prefixLift 4274111
  have htrace : WordTrace (prefixWord ++ tailWord_4274111) baseStart_4274111 baseEnd_4274111 := by
    simpa [prefixWord, tailWord_4274111, baseEnd_4274111] using wordTrace_append hprefix tailTrace_4274111
  have hstable : (prefixWord ++ tailWord_4274111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4274111).length < 2 ^ (prefixWord ++ tailWord_4274111).sum := by decide
  have hdescent : baseEnd_4274111 < baseStart_4274111 := by decide
  rcases family_descends (prefixWord ++ tailWord_4274111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4274145 : List Nat := [1, 2, 3, 1, 2, 1, 6, 1, 1, 5]
def baseStart_4274145 : Nat := 118140960795 + 4274145 * 2 ^ 59
def prefixEnd_4274145 : Nat := 4983230072969 + 3 ^ 40 * 4274145 * 2
def baseEnd_4274145 : Nat := 731563590670428373910357

theorem tailTrace_4274145 : CollatzResearch.WordTrace tailWord_4274145 prefixEnd_4274145 731563590670428373910357 := by
  unfold tailWord_4274145
  simp only [CollatzResearch.WordTrace]
  refine ⟨155890875100510105695559889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103927250067006737130373259 155890875100510105695559889)
  ·
    refine ⟨116918156325382579271669917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155890875100510105695559889 116918156325382579271669917)
    ·
      refine ⟨43844308622018467226876219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 116918156325382579271669917 43844308622018467226876219)
      ·
        refine ⟨65766462933027700840314329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43844308622018467226876219 65766462933027700840314329)
        ·
          refine ⟨49324847199770775630235747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65766462933027700840314329 49324847199770775630235747)
          ·
            refine ⟨73987270799656163445353621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49324847199770775630235747 73987270799656163445353621)
            ·
              refine ⟨3468153318733882661500951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 73987270799656163445353621 3468153318733882661500951)
              ·
                refine ⟨5202229978100823992251427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3468153318733882661500951 5202229978100823992251427)
                ·
                  refine ⟨7803344967151235988377141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5202229978100823992251427 7803344967151235988377141)
                  ·
                    refine ⟨731563590670428373910357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7803344967151235988377141 731563590670428373910357)
                    ·
                      rfl

theorem cell23_4274145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 6, 1, 1, 5].length) (baseStart_4274145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4274145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4274145 prefixEnd_4274145 := by exact prefixLift 4274145
  have htrace : WordTrace (prefixWord ++ tailWord_4274145) baseStart_4274145 baseEnd_4274145 := by
    simpa [prefixWord, tailWord_4274145, baseEnd_4274145] using wordTrace_append hprefix tailTrace_4274145
  have hstable : (prefixWord ++ tailWord_4274145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4274145).length < 2 ^ (prefixWord ++ tailWord_4274145).sum := by decide
  have hdescent : baseEnd_4274145 < baseStart_4274145 := by decide
  rcases family_descends (prefixWord ++ tailWord_4274145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4274168 : List Nat := [2, 1, 2, 1, 1, 3, 2, 1, 5, 2, 3]
def baseStart_4274168 : Nat := 118140960795 + 4274168 * 2 ^ 59
def prefixEnd_4274168 : Nat := 4983230072969 + 3 ^ 40 * 4274168 * 2
def baseEnd_4274168 : Nat := 2194702582066338531743465

theorem tailTrace_4274168 : CollatzResearch.WordTrace tailWord_4274168 prefixEnd_4274168 2194702582066338531743465 := by
  unfold tailWord_4274168
  simp only [CollatzResearch.WordTrace]
  refine ⟨77945856989713390311823579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103927809319617853749098105 77945856989713390311823579)
  ·
    refine ⟨116918785484570085467735369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77945856989713390311823579 116918785484570085467735369)
    ·
      refine ⟨87689089113427564100801527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116918785484570085467735369 87689089113427564100801527)
      ·
        refine ⟨131533633670141346151202291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87689089113427564100801527 131533633670141346151202291)
        ·
          refine ⟨197300450505212019226803437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131533633670141346151202291 197300450505212019226803437)
          ·
            refine ⟨73987668939454507210051289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 197300450505212019226803437 73987668939454507210051289)
            ·
              refine ⟨55490751704590880407538467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73987668939454507210051289 55490751704590880407538467)
              ·
                refine ⟨83236127556886320611307701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55490751704590880407538467 83236127556886320611307701)
                ·
                  refine ⟨7803386958458092557310097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 83236127556886320611307701 7803386958458092557310097)
                  ·
                    refine ⟨5852540218843569417982573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7803386958458092557310097 5852540218843569417982573)
                    ·
                      refine ⟨2194702582066338531743465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5852540218843569417982573 2194702582066338531743465)
                      ·
                        rfl

theorem cell23_4274168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 1, 5, 2, 3].length) (baseStart_4274168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4274168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4274168 prefixEnd_4274168 := by exact prefixLift 4274168
  have htrace : WordTrace (prefixWord ++ tailWord_4274168) baseStart_4274168 baseEnd_4274168 := by
    simpa [prefixWord, tailWord_4274168, baseEnd_4274168] using wordTrace_append hprefix tailTrace_4274168
  have hstable : (prefixWord ++ tailWord_4274168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4274168).length < 2 ^ (prefixWord ++ tailWord_4274168).sum := by decide
  have hdescent : baseEnd_4274168 < baseStart_4274168 := by decide
  rcases family_descends (prefixWord ++ tailWord_4274168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4274201 : List Nat := [1, 2, 1, 2, 1, 1, 3, 2, 1, 9]
def baseStart_4274201 : Nat := 118140960795 + 4274201 * 2 ^ 59
def prefixEnd_4274201 : Nat := 4983230072969 + 3 ^ 40 * 4274201 * 2
def baseEnd_4274201 : Nat := 731573175642645634210271

theorem tailTrace_4274201 : CollatzResearch.WordTrace tailWord_4274201 prefixEnd_4274201 731573175642645634210271 := by
  unfold tailWord_4274201
  simp only [CollatzResearch.WordTrace]
  refine ⟨155892917588307227259598457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103928611725538151506398971 155892917588307227259598457)
  ·
    refine ⟨116919688191230420444698843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155892917588307227259598457 116919688191230420444698843)
    ·
      refine ⟨175379532286845630667048265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116919688191230420444698843 175379532286845630667048265)
      ·
        refine ⟨131534649215134223000286199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 175379532286845630667048265 131534649215134223000286199)
        ·
          refine ⟨197301973822701334500429299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131534649215134223000286199 197301973822701334500429299)
          ·
            refine ⟨295952960734052001750643949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 197301973822701334500429299 295952960734052001750643949)
            ·
              refine ⟨110982360275269500656491481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 295952960734052001750643949 110982360275269500656491481)
              ·
                refine ⟨83236770206452125492368611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 110982360275269500656491481 83236770206452125492368611)
                ·
                  refine ⟨124855155309678188238552917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 83236770206452125492368611 124855155309678188238552917)
                  ·
                    refine ⟨731573175642645634210271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 124855155309678188238552917 731573175642645634210271)
                    ·
                      rfl

theorem cell23_4274201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 2, 1, 9].length) (baseStart_4274201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4274201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4274201 prefixEnd_4274201 := by exact prefixLift 4274201
  have htrace : WordTrace (prefixWord ++ tailWord_4274201) baseStart_4274201 baseEnd_4274201 := by
    simpa [prefixWord, tailWord_4274201, baseEnd_4274201] using wordTrace_append hprefix tailTrace_4274201
  have hstable : (prefixWord ++ tailWord_4274201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4274201).length < 2 ^ (prefixWord ++ tailWord_4274201).sum := by decide
  have hdescent : baseEnd_4274201 < baseStart_4274201 := by decide
  rcases family_descends (prefixWord ++ tailWord_4274201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4274255 : List Nat := [1, 1, 2, 1, 1, 2, 2, 6, 1, 4, 2]
def baseStart_4274255 : Nat := 118140960795 + 4274255 * 2 ^ 59
def prefixEnd_4274255 : Nat := 4983230072969 + 3 ^ 40 * 4274255 * 2
def baseEnd_4274255 : Nat := 2194747254883279691355565

theorem tailTrace_4274255 : CollatzResearch.WordTrace tailWord_4274255 prefixEnd_4274255 2194747254883279691355565 := by
  unfold tailWord_4274255
  simp only [CollatzResearch.WordTrace]
  refine ⟨155894887130111594482064219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103929924753407729654709479 155894887130111594482064219)
  ·
    refine ⟨233842330695167391723096329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155894887130111594482064219 233842330695167391723096329)
    ·
      refine ⟨175381748021375543792322247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 233842330695167391723096329 175381748021375543792322247)
      ·
        refine ⟨263072622032063315688483371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175381748021375543792322247 263072622032063315688483371)
        ·
          refine ⟨394608933048094973532725057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 263072622032063315688483371 394608933048094973532725057)
          ·
            refine ⟨295956699786071230149543793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 394608933048094973532725057 295956699786071230149543793)
            ·
              refine ⟨221967524839553422612157845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 295956699786071230149543793 221967524839553422612157845)
              ·
                refine ⟨10404727726854066684944899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 221967524839553422612157845 10404727726854066684944899)
                ·
                  refine ⟨15607091590281100027417349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10404727726854066684944899 15607091590281100027417349)
                  ·
                    refine ⟨2926329673177706255140753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15607091590281100027417349 2926329673177706255140753)
                    ·
                      refine ⟨2194747254883279691355565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2926329673177706255140753 2194747254883279691355565)
                      ·
                        rfl

theorem cell23_4274255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 6, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 6, 1, 4, 2].length) (baseStart_4274255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4274255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4274255 prefixEnd_4274255 := by exact prefixLift 4274255
  have htrace : WordTrace (prefixWord ++ tailWord_4274255) baseStart_4274255 baseEnd_4274255 := by
    simpa [prefixWord, tailWord_4274255, baseEnd_4274255] using wordTrace_append hprefix tailTrace_4274255
  have hstable : (prefixWord ++ tailWord_4274255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4274255).length < 2 ^ (prefixWord ++ tailWord_4274255).sum := by decide
  have hdescent : baseEnd_4274255 < baseStart_4274255 := by decide
  rcases family_descends (prefixWord ++ tailWord_4274255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4274285 : List Nat := [1, 5, 1, 1, 2, 1, 3, 1, 2, 2, 4]
def baseStart_4274285 : Nat := 118140960795 + 4274285 * 2 ^ 59
def prefixEnd_4274285 : Nat := 4983230072969 + 3 ^ 40 * 4274285 * 2
def baseEnd_4274285 : Nat := 2194762659302914573980427

theorem tailTrace_4274285 : CollatzResearch.WordTrace tailWord_4274285 prefixEnd_4274285 2194762659302914573980427 := by
  unfold tailWord_4274285
  simp only [CollatzResearch.WordTrace]
  refine ⟨155895981320002909605656309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103930654213335273070437539 155895981320002909605656309)
  ·
    refine ⟨14615248248750272775530279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 155895981320002909605656309 14615248248750272775530279)
    ·
      refine ⟨21922872373125409163295419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14615248248750272775530279 21922872373125409163295419)
      ·
        refine ⟨32884308559688113744943129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21922872373125409163295419 32884308559688113744943129)
        ·
          refine ⟨24663231419766085308707347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32884308559688113744943129 24663231419766085308707347)
          ·
            refine ⟨36994847129649127963061021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24663231419766085308707347 36994847129649127963061021)
            ·
              refine ⟨13873067673618422986147883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36994847129649127963061021 13873067673618422986147883)
              ·
                refine ⟨20809601510427634479221825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13873067673618422986147883 20809601510427634479221825)
                ·
                  refine ⟨15607201132820725859416369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20809601510427634479221825 15607201132820725859416369)
                  ·
                    refine ⟨11705400849615544394562277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15607201132820725859416369 11705400849615544394562277)
                    ·
                      refine ⟨2194762659302914573980427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11705400849615544394562277 2194762659302914573980427)
                      ·
                        rfl

theorem cell23_4274285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 1, 2, 2, 4].length) (baseStart_4274285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4274285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4274285 prefixEnd_4274285 := by exact prefixLift 4274285
  have htrace : WordTrace (prefixWord ++ tailWord_4274285) baseStart_4274285 baseEnd_4274285 := by
    simpa [prefixWord, tailWord_4274285, baseEnd_4274285] using wordTrace_append hprefix tailTrace_4274285
  have hstable : (prefixWord ++ tailWord_4274285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4274285).length < 2 ^ (prefixWord ++ tailWord_4274285).sum := by decide
  have hdescent : baseEnd_4274285 < baseStart_4274285 := by decide
  rcases family_descends (prefixWord ++ tailWord_4274285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4274312 : List Nat := [2, 1, 3, 4, 1, 1, 1, 5, 5]
def baseStart_4274312 : Nat := 118140960795 + 4274312 * 2 ^ 59
def prefixEnd_4274312 : Nat := 4983230072969 + 3 ^ 40 * 4274312 * 2
def baseEnd_4274312 : Nat := 243864058142287329815867

theorem tailTrace_4274312 : CollatzResearch.WordTrace tailWord_4274312 prefixEnd_4274312 243864058142287329815867 := by
  unfold tailWord_4274312
  simp only [CollatzResearch.WordTrace]
  refine ⟨77948483045452546608444595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103931310727270062144592793 77948483045452546608444595)
  ·
    refine ⟨116922724568178819912666893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77948483045452546608444595 116922724568178819912666893)
    ·
      refine ⟨43846021713067057467250085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 116922724568178819912666893 43846021713067057467250085)
      ·
        refine ⟨8221129071200073275109391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43846021713067057467250085 8221129071200073275109391)
        ·
          refine ⟨12331693606800109912664087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8221129071200073275109391 12331693606800109912664087)
          ·
            refine ⟨18497540410200164868996131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12331693606800109912664087 18497540410200164868996131)
            ·
              refine ⟨27746310615300247303494197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18497540410200164868996131 27746310615300247303494197)
              ·
                refine ⟨2601216620184398184702581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27746310615300247303494197 2601216620184398184702581)
                ·
                  refine ⟨243864058142287329815867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2601216620184398184702581 243864058142287329815867)
                  ·
                    rfl

theorem cell23_4274312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 5, 5].length) (baseStart_4274312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4274312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4274312 prefixEnd_4274312 := by exact prefixLift 4274312
  have htrace : WordTrace (prefixWord ++ tailWord_4274312) baseStart_4274312 baseEnd_4274312 := by
    simpa [prefixWord, tailWord_4274312, baseEnd_4274312] using wordTrace_append hprefix tailTrace_4274312
  have hstable : (prefixWord ++ tailWord_4274312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4274312).length < 2 ^ (prefixWord ++ tailWord_4274312).sum := by decide
  have hdescent : baseEnd_4274312 < baseStart_4274312 := by decide
  rcases family_descends (prefixWord ++ tailWord_4274312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4274348 : List Nat := [2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 5]
def baseStart_4274348 : Nat := 118140960795 + 4274348 * 2 ^ 59
def prefixEnd_4274348 : Nat := 4983230072969 + 3 ^ 40 * 4274348 * 2
def baseEnd_4274348 : Nat := 2194795008584147827492637

theorem tailTrace_4274348 : CollatzResearch.WordTrace tailWord_4274348 prefixEnd_4274348 2194795008584147827492637 := by
  unfold tailWord_4274348
  simp only [CollatzResearch.WordTrace]
  refine ⟨77949139559387335682599849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103932186079183114243466465 77949139559387335682599849)
  ·
    refine ⟨58461854669540501761949887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77949139559387335682599849 58461854669540501761949887)
    ·
      refine ⟨87692782004310752642924831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58461854669540501761949887 87692782004310752642924831)
      ·
        refine ⟨131539173006466128964387247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87692782004310752642924831 131539173006466128964387247)
        ·
          refine ⟨197308759509699193446580871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131539173006466128964387247 197308759509699193446580871)
          ·
            refine ⟨295963139264548790169871307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 197308759509699193446580871 295963139264548790169871307)
            ·
              refine ⟨443944708896823185254806961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 295963139264548790169871307 443944708896823185254806961)
              ·
                refine ⟨332958531672617388941105221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 443944708896823185254806961 332958531672617388941105221)
                ·
                  refine ⟨62429724688615760426457229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 332958531672617388941105221 62429724688615760426457229)
                  ·
                    refine ⟨23411146758230910159921461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 62429724688615760426457229 23411146758230910159921461)
                    ·
                      refine ⟨2194795008584147827492637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23411146758230910159921461 2194795008584147827492637)
                      ·
                        rfl

theorem cell23_4274348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 5].length) (baseStart_4274348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4274348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4274348 prefixEnd_4274348 := by exact prefixLift 4274348
  have htrace : WordTrace (prefixWord ++ tailWord_4274348) baseStart_4274348 baseEnd_4274348 := by
    simpa [prefixWord, tailWord_4274348, baseEnd_4274348] using wordTrace_append hprefix tailTrace_4274348
  have hstable : (prefixWord ++ tailWord_4274348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4274348).length < 2 ^ (prefixWord ++ tailWord_4274348).sum := by decide
  have hdescent : baseEnd_4274348 < baseStart_4274348 := by decide
  rcases family_descends (prefixWord ++ tailWord_4274348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4274382 : List Nat := [4, 1, 1, 1, 4, 1, 1, 1, 4, 2, 3]
def baseStart_4274382 : Nat := 118140960795 + 4274382 * 2 ^ 59
def prefixEnd_4274382 : Nat := 4983230072969 + 3 ^ 40 * 4274382 * 2
def baseEnd_4274382 : Nat := 2194812466926400694467481

theorem tailTrace_4274382 : CollatzResearch.WordTrace tailWord_4274382 prefixEnd_4274382 2194812466926400694467481 := by
  unfold tailWord_4274382
  simp only [CollatzResearch.WordTrace]
  refine ⟨19487439900081436896492175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 103933012800434330114624933 19487439900081436896492175)
  ·
    refine ⟨29231159850122155344738263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19487439900081436896492175 29231159850122155344738263)
    ·
      refine ⟨43846739775183233017107395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29231159850122155344738263 43846739775183233017107395)
      ·
        refine ⟨65770109662774849525661093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43846739775183233017107395 65770109662774849525661093)
        ·
          refine ⟨12331895561770284286061455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 65770109662774849525661093 12331895561770284286061455)
          ·
            refine ⟨18497843342655426429092183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12331895561770284286061455 18497843342655426429092183)
            ·
              refine ⟨27746765013983139643638275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18497843342655426429092183 27746765013983139643638275)
              ·
                refine ⟨41620147520974709465457413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27746765013983139643638275 41620147520974709465457413)
                ·
                  refine ⟨7803777660182758024773265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 41620147520974709465457413 7803777660182758024773265)
                  ·
                    refine ⟨5852833245137068518579949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7803777660182758024773265 5852833245137068518579949)
                    ·
                      refine ⟨2194812466926400694467481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5852833245137068518579949 2194812466926400694467481)
                      ·
                        rfl

theorem cell23_4274382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 1, 4, 2, 3].length) (baseStart_4274382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4274382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4274382 prefixEnd_4274382 := by exact prefixLift 4274382
  have htrace : WordTrace (prefixWord ++ tailWord_4274382) baseStart_4274382 baseEnd_4274382 := by
    simpa [prefixWord, tailWord_4274382, baseEnd_4274382] using wordTrace_append hprefix tailTrace_4274382
  have hstable : (prefixWord ++ tailWord_4274382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4274382).length < 2 ^ (prefixWord ++ tailWord_4274382).sum := by decide
  have hdescent : baseEnd_4274382 < baseStart_4274382 := by decide
  rcases family_descends (prefixWord ++ tailWord_4274382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4274412 : List Nat := [2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 3]
def baseStart_4274412 : Nat := 118140960795 + 4274412 * 2 ^ 59
def prefixEnd_4274412 : Nat := 4983230072969 + 3 ^ 40 * 4274412 * 2
def baseEnd_4274412 : Nat := 2194827871346035577092343

theorem tailTrace_4274412 : CollatzResearch.WordTrace tailWord_4274412 prefixEnd_4274412 2194827871346035577092343 := by
  unfold tailWord_4274412
  simp only [CollatzResearch.WordTrace]
  refine ⟨77950306695271405147764745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103933742260361873530352993 77950306695271405147764745)
  ·
    refine ⟨58462730021453553860823559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77950306695271405147764745 58462730021453553860823559)
    ·
      refine ⟨87694095032180330791235339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58462730021453553860823559 87694095032180330791235339)
      ·
        refine ⟨131541142548270496186853009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87694095032180330791235339 131541142548270496186853009)
        ·
          refine ⟨98655856911202872140139757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 131541142548270496186853009 98655856911202872140139757)
          ·
            refine ⟨36995946341701077052552409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 98655856911202872140139757 36995946341701077052552409)
            ·
              refine ⟨27746959756275807789414307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36995946341701077052552409 27746959756275807789414307)
              ·
                refine ⟨41620439634413711684121461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27746959756275807789414307 41620439634413711684121461)
                ·
                  refine ⟨3901916215726285470386387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 41620439634413711684121461 3901916215726285470386387)
                  ·
                    refine ⟨5852874323589428205579581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3901916215726285470386387 5852874323589428205579581)
                    ·
                      refine ⟨2194827871346035577092343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5852874323589428205579581 2194827871346035577092343)
                      ·
                        rfl

theorem cell23_4274412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 3].length) (baseStart_4274412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4274412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4274412 prefixEnd_4274412 := by exact prefixLift 4274412
  have htrace : WordTrace (prefixWord ++ tailWord_4274412) baseStart_4274412 baseEnd_4274412 := by
    simpa [prefixWord, tailWord_4274412, baseEnd_4274412] using wordTrace_append hprefix tailTrace_4274412
  have hstable : (prefixWord ++ tailWord_4274412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4274412).length < 2 ^ (prefixWord ++ tailWord_4274412).sum := by decide
  have hdescent : baseEnd_4274412 < baseStart_4274412 := by decide
  rcases family_descends (prefixWord ++ tailWord_4274412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4274446 : List Nat := [4, 1, 1, 2, 1, 2, 3, 4, 1, 1, 3]
def baseStart_4274446 : Nat := 118140960795 + 4274446 * 2 ^ 59
def prefixEnd_4274446 : Nat := 4983230072969 + 3 ^ 40 * 4274446 * 2
def baseEnd_4274446 : Nat := 2194845329688288444067187

theorem tailTrace_4274446 : CollatzResearch.WordTrace tailWord_4274446 prefixEnd_4274446 2194845329688288444067187 := by
  unfold tailWord_4274446
  simp only [CollatzResearch.WordTrace]
  refine ⟨19487731684052454262783399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 103934568981613089401511461 19487731684052454262783399)
  ·
    refine ⟨29231597526078681394175099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19487731684052454262783399 29231597526078681394175099)
    ·
      refine ⟨43847396289118022091262649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29231597526078681394175099 43847396289118022091262649)
      ·
        refine ⟨32885547216838516568446987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43847396289118022091262649 32885547216838516568446987)
        ·
          refine ⟨49328320825257774852670481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32885547216838516568446987 49328320825257774852670481)
          ·
            refine ⟨36996240618943331139502861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49328320825257774852670481 36996240618943331139502861)
            ·
              refine ⟨13873590232103749177313573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36996240618943331139502861 13873590232103749177313573)
              ·
                refine ⟨2601298168519452970746295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13873590232103749177313573 2601298168519452970746295)
                ·
                  refine ⟨3901947252779179456119443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2601298168519452970746295 3901947252779179456119443)
                  ·
                    refine ⟨5852920879168769184179165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3901947252779179456119443 5852920879168769184179165)
                    ·
                      refine ⟨2194845329688288444067187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5852920879168769184179165 2194845329688288444067187)
                      ·
                        rfl

theorem cell23_4274446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 4, 1, 1, 3].length) (baseStart_4274446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4274446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4274446 prefixEnd_4274446 := by exact prefixLift 4274446
  have htrace : WordTrace (prefixWord ++ tailWord_4274446) baseStart_4274446 baseEnd_4274446 := by
    simpa [prefixWord, tailWord_4274446, baseEnd_4274446] using wordTrace_append hprefix tailTrace_4274446
  have hstable : (prefixWord ++ tailWord_4274446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4274446).length < 2 ^ (prefixWord ++ tailWord_4274446).sum := by decide
  have hdescent : baseEnd_4274446 < baseStart_4274446 := by decide
  rcases family_descends (prefixWord ++ tailWord_4274446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4274465 : List Nat := [1, 2, 3, 2, 1, 1, 2, 3, 1, 1, 6]
def baseStart_4274465 : Nat := 118140960795 + 4274465 * 2 ^ 59
def prefixEnd_4274465 : Nat := 4983230072969 + 3 ^ 40 * 4274465 * 2
def baseEnd_4274465 : Nat := 2194855085820723869729599

theorem tailTrace_4274465 : CollatzResearch.WordTrace tailWord_4274465 prefixEnd_4274465 2194855085820723869729599 := by
  unfold tailWord_4274465
  simp only [CollatzResearch.WordTrace]
  refine ⟨155902546459350800347208849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103935030972900533564805899 155902546459350800347208849)
  ·
    refine ⟨116926909844513100260406637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155902546459350800347208849 116926909844513100260406637)
    ·
      refine ⟨43847591191692412597652489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 116926909844513100260406637 43847591191692412597652489)
      ·
        refine ⟨32885693393769309448239367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43847591191692412597652489 32885693393769309448239367)
        ·
          refine ⟨49328540090653964172359051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32885693393769309448239367 49328540090653964172359051)
          ·
            refine ⟨73992810135980946258538577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49328540090653964172359051 73992810135980946258538577)
            ·
              refine ⟨55494607601985709693903933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73992810135980946258538577 55494607601985709693903933)
              ·
                refine ⟨20810477850744641135213975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55494607601985709693903933 20810477850744641135213975)
                ·
                  refine ⟨31215716776116961702820963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20810477850744641135213975 31215716776116961702820963)
                  ·
                    refine ⟨46823575164175442554231445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31215716776116961702820963 46823575164175442554231445)
                    ·
                      refine ⟨2194855085820723869729599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 46823575164175442554231445 2194855085820723869729599)
                      ·
                        rfl

theorem cell23_4274465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 3, 1, 1, 6].length) (baseStart_4274465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4274465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4274465 prefixEnd_4274465 := by exact prefixLift 4274465
  have htrace : WordTrace (prefixWord ++ tailWord_4274465) baseStart_4274465 baseEnd_4274465 := by
    simpa [prefixWord, tailWord_4274465, baseEnd_4274465] using wordTrace_append hprefix tailTrace_4274465
  have hstable : (prefixWord ++ tailWord_4274465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4274465).length < 2 ^ (prefixWord ++ tailWord_4274465).sum := by decide
  have hdescent : baseEnd_4274465 < baseStart_4274465 := by decide
  rcases family_descends (prefixWord ++ tailWord_4274465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4274546 : List Nat := [3, 2, 1, 2, 1, 3, 2, 3, 1, 3, 2]
def baseStart_4274546 : Nat := 118140960795 + 4274546 * 2 ^ 59
def prefixEnd_4274546 : Nat := 4983230072969 + 3 ^ 40 * 4274546 * 2
def baseEnd_4274546 : Nat := 2194896677753738052816727

theorem tailTrace_4274546 : CollatzResearch.WordTrace tailWord_4274546 prefixEnd_4274546 2194896677753738052816727 := by
  unfold tailWord_4274546
  simp only [CollatzResearch.WordTrace]
  refine ⟨38976375193014337795226873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103937000514704900787271661 38976375193014337795226873)
  ·
    refine ⟨29232281394760753346420155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38976375193014337795226873 29232281394760753346420155)
    ·
      refine ⟨43848422092141130019630233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29232281394760753346420155 43848422092141130019630233)
      ·
        refine ⟨32886316569105847514722675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43848422092141130019630233 32886316569105847514722675)
        ·
          refine ⟨49329474853658771272084013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32886316569105847514722675 49329474853658771272084013)
          ·
            refine ⟨18498553070122039227031505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49329474853658771272084013 18498553070122039227031505)
            ·
              refine ⟨13873914802591529420273629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18498553070122039227031505 13873914802591529420273629)
              ·
                refine ⟨5202718050971823532602611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13873914802591529420273629 5202718050971823532602611)
                ·
                  refine ⟨7804077076457735298903917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5202718050971823532602611 7804077076457735298903917)
                  ·
                    refine ⟨2926528903671650737088969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7804077076457735298903917 2926528903671650737088969)
                    ·
                      refine ⟨2194896677753738052816727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2926528903671650737088969 2194896677753738052816727)
                      ·
                        rfl

theorem cell23_4274546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 3, 1, 3, 2].length) (baseStart_4274546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4274546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4274546 prefixEnd_4274546 := by exact prefixLift 4274546
  have htrace : WordTrace (prefixWord ++ tailWord_4274546) baseStart_4274546 baseEnd_4274546 := by
    simpa [prefixWord, tailWord_4274546, baseEnd_4274546] using wordTrace_append hprefix tailTrace_4274546
  have hstable : (prefixWord ++ tailWord_4274546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4274546).length < 2 ^ (prefixWord ++ tailWord_4274546).sum := by decide
  have hdescent : baseEnd_4274546 < baseStart_4274546 := by decide
  rcases family_descends (prefixWord ++ tailWord_4274546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4274580 : List Nat := [2, 4, 2, 1, 3, 2, 1, 2, 1, 3, 2]
def baseStart_4274580 : Nat := 118140960795 + 4274580 * 2 ^ 59
def prefixEnd_4274580 : Nat := 4983230072969 + 3 ^ 40 * 4274580 * 2
def baseEnd_4274580 : Nat := 2194914136095990919791571

theorem tailTrace_4274580 : CollatzResearch.WordTrace tailWord_4274580 prefixEnd_4274580 2194914136095990919791571 := by
  unfold tailWord_4274580
  simp only [CollatzResearch.WordTrace]
  refine ⟨77953370426967087493822597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103937827235956116658430129 77953370426967087493822597)
  ·
    refine ⟨14616256955056328905091737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 77953370426967087493822597 14616256955056328905091737)
    ·
      refine ⟨10962192716292246678818803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14616256955056328905091737 10962192716292246678818803)
      ·
        refine ⟨16443289074438370018228205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10962192716292246678818803 16443289074438370018228205)
        ·
          refine ⟨6166233402914388756835577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16443289074438370018228205 6166233402914388756835577)
          ·
            refine ⟨4624675052185791567626683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6166233402914388756835577 4624675052185791567626683)
            ·
              refine ⟨6937012578278687351440025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4624675052185791567626683 6937012578278687351440025)
              ·
                refine ⟨5202759433709015513580019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6937012578278687351440025 5202759433709015513580019)
                ·
                  refine ⟨7804139150563523270370029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5202759433709015513580019 7804139150563523270370029)
                  ·
                    refine ⟨2926552181461321226388761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7804139150563523270370029 2926552181461321226388761)
                    ·
                      refine ⟨2194914136095990919791571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2926552181461321226388761 2194914136095990919791571)
                      ·
                        rfl

theorem cell23_4274580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 1, 2, 1, 3, 2].length) (baseStart_4274580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4274580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4274580 prefixEnd_4274580 := by exact prefixLift 4274580
  have htrace : WordTrace (prefixWord ++ tailWord_4274580) baseStart_4274580 baseEnd_4274580 := by
    simpa [prefixWord, tailWord_4274580, baseEnd_4274580] using wordTrace_append hprefix tailTrace_4274580
  have hstable : (prefixWord ++ tailWord_4274580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4274580).length < 2 ^ (prefixWord ++ tailWord_4274580).sum := by decide
  have hdescent : baseEnd_4274580 < baseStart_4274580 := by decide
  rcases family_descends (prefixWord ++ tailWord_4274580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4274593 : List Nat := [1, 2, 3, 5, 1, 1, 1, 2, 1, 4, 2]
def baseStart_4274593 : Nat := 118140960795 + 4274593 * 2 ^ 59
def prefixEnd_4274593 : Nat := 4983230072969 + 3 ^ 40 * 4274593 * 2
def baseEnd_4274593 : Nat := 2194920811344499368929011

theorem tailTrace_4274593 : CollatzResearch.WordTrace tailWord_4274593 prefixEnd_4274593 2194920811344499368929011 := by
  unfold tailWord_4274593
  simp only [CollatzResearch.WordTrace]
  refine ⟨155907215002887078207868433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103938143335258052138578955 155907215002887078207868433)
  ·
    refine ⟨116930411252165308655901325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155907215002887078207868433 116930411252165308655901325)
    ·
      refine ⟨43848904219561990745962997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 116930411252165308655901325 43848904219561990745962997)
      ·
        refine ⟨4110834770583936632434031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 43848904219561990745962997 4110834770583936632434031)
        ·
          refine ⟨6166252155875904948651047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4110834770583936632434031 6166252155875904948651047)
          ·
            refine ⟨9249378233813857422976571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6166252155875904948651047 9249378233813857422976571)
            ·
              refine ⟨13874067350720786134464857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9249378233813857422976571 13874067350720786134464857)
              ·
                refine ⟨10405550513040589600848643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13874067350720786134464857 10405550513040589600848643)
                ·
                  refine ⟨15608325769560884401272965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10405550513040589600848643 15608325769560884401272965)
                  ·
                    refine ⟨2926561081792665825238681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15608325769560884401272965 2926561081792665825238681)
                    ·
                      refine ⟨2194920811344499368929011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2926561081792665825238681 2194920811344499368929011)
                      ·
                        rfl

theorem cell23_4274593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 2, 1, 4, 2].length) (baseStart_4274593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4274593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4274593 prefixEnd_4274593 := by exact prefixLift 4274593
  have htrace : WordTrace (prefixWord ++ tailWord_4274593) baseStart_4274593 baseEnd_4274593 := by
    simpa [prefixWord, tailWord_4274593, baseEnd_4274593] using wordTrace_append hprefix tailTrace_4274593
  have hstable : (prefixWord ++ tailWord_4274593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4274593).length < 2 ^ (prefixWord ++ tailWord_4274593).sum := by decide
  have hdescent : baseEnd_4274593 < baseStart_4274593 := by decide
  rcases family_descends (prefixWord ++ tailWord_4274593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4274649 : List Nat := [1, 2, 1, 2, 4, 1, 1, 2, 1, 6, 2]
def baseStart_4274649 : Nat := 118140960795 + 4274649 * 2 ^ 59
def prefixEnd_4274649 : Nat := 4983230072969 + 3 ^ 40 * 4274649 * 2
def baseEnd_4274649 : Nat := 2194949566261151149828753

theorem tailTrace_4274649 : CollatzResearch.WordTrace tailWord_4274649 prefixEnd_4274649 2194949566261151149828753 := by
  unfold tailWord_4274649
  simp only [CollatzResearch.WordTrace]
  refine ⟨155909257490684199771907001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103939504993789466514604667 155909257490684199771907001)
  ·
    refine ⟨116931943118013149828930251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155909257490684199771907001 116931943118013149828930251)
    ·
      refine ⟨175397914677019724743395377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116931943118013149828930251 175397914677019724743395377)
      ·
        refine ⟨131548436007764793557546533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 175397914677019724743395377 131548436007764793557546533)
        ·
          refine ⟨24665331751455898792039975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 131548436007764793557546533 24665331751455898792039975)
          ·
            refine ⟨36997997627183848188059963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24665331751455898792039975 36997997627183848188059963)
            ·
              refine ⟨55496996440775772282089945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36997997627183848188059963 55496996440775772282089945)
              ·
                refine ⟨41622747330581829211567459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55496996440775772282089945 41622747330581829211567459)
                ·
                  refine ⟨62434120995872743817351189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41622747330581829211567459 62434120995872743817351189)
                  ·
                    refine ⟨2926599421681534866438337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 62434120995872743817351189 2926599421681534866438337)
                    ·
                      refine ⟨2194949566261151149828753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2926599421681534866438337 2194949566261151149828753)
                      ·
                        rfl

theorem cell23_4274649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 2, 1, 6, 2].length) (baseStart_4274649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4274649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4274649 prefixEnd_4274649 := by exact prefixLift 4274649
  have htrace : WordTrace (prefixWord ++ tailWord_4274649) baseStart_4274649 baseEnd_4274649 := by
    simpa [prefixWord, tailWord_4274649, baseEnd_4274649] using wordTrace_append hprefix tailTrace_4274649
  have hstable : (prefixWord ++ tailWord_4274649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4274649).length < 2 ^ (prefixWord ++ tailWord_4274649).sum := by decide
  have hdescent : baseEnd_4274649 < baseStart_4274649 := by decide
  rcases family_descends (prefixWord ++ tailWord_4274649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4274666 : List Nat := [3, 1, 3, 1, 3, 1, 1, 2, 2, 4, 2]
def baseStart_4274666 : Nat := 118140960795 + 4274666 * 2 ^ 59
def prefixEnd_4274666 : Nat := 4983230072969 + 3 ^ 40 * 4274666 * 2
def baseEnd_4274666 : Nat := 2194958295432277583316175

theorem tailTrace_4274666 : CollatzResearch.WordTrace tailWord_4274666 prefixEnd_4274666 2194958295432277583316175 := by
  unfold tailWord_4274666
  simp only [CollatzResearch.WordTrace]
  refine ⟨38977469382905652918818963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103939918354415074450183901 38977469382905652918818963)
  ·
    refine ⟨58466204074358479378228445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38977469382905652918818963 58466204074358479378228445)
    ·
      refine ⟨21924826527884429766835667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58466204074358479378228445 21924826527884429766835667)
      ·
        refine ⟨32887239791826644650253501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21924826527884429766835667 32887239791826644650253501)
        ·
          refine ⟨12332714921934991743845063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32887239791826644650253501 12332714921934991743845063)
          ·
            refine ⟨18499072382902487615767595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12332714921934991743845063 18499072382902487615767595)
            ·
              refine ⟨27748608574353731423651393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18499072382902487615767595 27748608574353731423651393)
              ·
                refine ⟨20811456430765298567738545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27748608574353731423651393 20811456430765298567738545)
                ·
                  refine ⟨15608592323073973925803909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20811456430765298567738545 15608592323073973925803909)
                  ·
                    refine ⟨2926611060576370111088233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15608592323073973925803909 2926611060576370111088233)
                    ·
                      refine ⟨2194958295432277583316175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2926611060576370111088233 2194958295432277583316175)
                      ·
                        rfl

theorem cell23_4274666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 2, 2, 4, 2].length) (baseStart_4274666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4274666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4274666 prefixEnd_4274666 := by exact prefixLift 4274666
  have htrace : WordTrace (prefixWord ++ tailWord_4274666) baseStart_4274666 baseEnd_4274666 := by
    simpa [prefixWord, tailWord_4274666, baseEnd_4274666] using wordTrace_append hprefix tailTrace_4274666
  have hstable : (prefixWord ++ tailWord_4274666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4274666).length < 2 ^ (prefixWord ++ tailWord_4274666).sum := by decide
  have hdescent : baseEnd_4274666 < baseStart_4274666 := by decide
  rcases family_descends (prefixWord ++ tailWord_4274666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4274672 : List Nat := [2, 1, 1, 1, 3, 3, 3, 1, 8]
def baseStart_4274672 : Nat := 118140960795 + 4274672 * 2 ^ 59
def prefixEnd_4274672 : Nat := 4983230072969 + 3 ^ 40 * 4274672 * 2
def baseEnd_4274672 : Nat := 243884597368467173315683

theorem tailTrace_4274672 : CollatzResearch.WordTrace tailWord_4274672 prefixEnd_4274672 243884597368467173315683 := by
  unfold tailWord_4274672
  simp only [CollatzResearch.WordTrace]
  refine ⟨77955048184800437349997135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103940064246400583133329513 77955048184800437349997135)
  ·
    refine ⟨116932572277200656024995703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77955048184800437349997135 116932572277200656024995703)
    ·
      refine ⟨175398858415800984037493555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116932572277200656024995703 175398858415800984037493555)
      ·
        refine ⟨263098287623701476056240333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175398858415800984037493555 263098287623701476056240333)
        ·
          refine ⟨98661857858888053521090125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 263098287623701476056240333 98661857858888053521090125)
          ·
            refine ⟨36998196697083020070408797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 98661857858888053521090125 36998196697083020070408797)
            ·
              refine ⟨13874323761406132526403299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36998196697083020070408797 13874323761406132526403299)
              ·
                refine ⟨20811485642109198789604949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13874323761406132526403299 20811485642109198789604949)
                ·
                  refine ⟨243884597368467173315683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20811485642109198789604949 243884597368467173315683)
                  ·
                    rfl

theorem cell23_4274672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 1, 8].length) (baseStart_4274672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4274672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4274672 prefixEnd_4274672 := by exact prefixLift 4274672
  have htrace : WordTrace (prefixWord ++ tailWord_4274672) baseStart_4274672 baseEnd_4274672 := by
    simpa [prefixWord, tailWord_4274672, baseEnd_4274672] using wordTrace_append hprefix tailTrace_4274672
  have hstable : (prefixWord ++ tailWord_4274672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4274672).length < 2 ^ (prefixWord ++ tailWord_4274672).sum := by decide
  have hdescent : baseEnd_4274672 < baseStart_4274672 := by decide
  rcases family_descends (prefixWord ++ tailWord_4274672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4274727 : List Nat := [1, 1, 7, 2, 2, 1, 1, 1, 3, 4]
def baseStart_4274727 : Nat := 118140960795 + 4274727 * 2 ^ 59
def prefixEnd_4274727 : Nat := 4983230072969 + 3 ^ 40 * 4274727 * 2
def baseEnd_4274727 : Nat := 731663205917400614884465

theorem tailTrace_4274727 : CollatzResearch.WordTrace tailWord_4274727 prefixEnd_4274727 731663205917400614884465 := by
  unfold tailWord_4274727
  simp only [CollatzResearch.WordTrace]
  refine ⟨155912102384401619093246435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103941401589601079395497623 155912102384401619093246435)
  ·
    refine ⟨233868153576602428639869653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155912102384401619093246435 233868153576602428639869653)
    ·
      refine ⟨5481284849451619421246945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 233868153576602428639869653 5481284849451619421246945)
      ·
        refine ⟨4110963637088714565935209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5481284849451619421246945 4110963637088714565935209)
        ·
          refine ⟨3083222727816535924451407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4110963637088714565935209 3083222727816535924451407)
          ·
            refine ⟨4624834091724803886677111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3083222727816535924451407 4624834091724803886677111)
            ·
              refine ⟨6937251137587205830015667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4624834091724803886677111 6937251137587205830015667)
              ·
                refine ⟨10405876706380808745023501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6937251137587205830015667 10405876706380808745023501)
                ·
                  refine ⟨3902203764892803279383813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10405876706380808745023501 3902203764892803279383813)
                  ·
                    refine ⟨731663205917400614884465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3902203764892803279383813 731663205917400614884465)
                    ·
                      rfl

theorem cell23_4274727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 1, 1, 3, 4].length) (baseStart_4274727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4274727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4274727 prefixEnd_4274727 := by exact prefixLift 4274727
  have htrace : WordTrace (prefixWord ++ tailWord_4274727) baseStart_4274727 baseEnd_4274727 := by
    simpa [prefixWord, tailWord_4274727, baseEnd_4274727] using wordTrace_append hprefix tailTrace_4274727
  have hstable : (prefixWord ++ tailWord_4274727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4274727).length < 2 ^ (prefixWord ++ tailWord_4274727).sum := by decide
  have hdescent : baseEnd_4274727 < baseStart_4274727 := by decide
  rcases family_descends (prefixWord ++ tailWord_4274727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4274739 : List Nat := [1, 1, 1, 2, 4, 2, 2, 2, 3, 1, 4]
def baseStart_4274739 : Nat := 118140960795 + 4274739 * 2 ^ 59
def prefixEnd_4274739 : Nat := 4983230072969 + 3 ^ 40 * 4274739 * 2
def baseEnd_4274739 : Nat := 2194995779520055797703339

theorem tailTrace_4274739 : CollatzResearch.WordTrace tailWord_4274739 prefixEnd_4274739 2194995779520055797703339 := by
  unfold tailWord_4274739
  simp only [CollatzResearch.WordTrace]
  refine ⟨155912540060358145142683271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103941693373572096761788847 155912540060358145142683271)
  ·
    refine ⟨233868810090537217714024907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155912540060358145142683271 233868810090537217714024907)
    ·
      refine ⟨350803215135805826571037361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 233868810090537217714024907 350803215135805826571037361)
      ·
        refine ⟨263102411351854369928278021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 350803215135805826571037361 263102411351854369928278021)
        ·
          refine ⟨49331702128472694361552129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 263102411351854369928278021 49331702128472694361552129)
          ·
            refine ⟨36998776596354520771164097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49331702128472694361552129 36998776596354520771164097)
            ·
              refine ⟨27749082447265890578373073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36998776596354520771164097 27749082447265890578373073)
              ·
                refine ⟨20811811835449417933779805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27749082447265890578373073 20811811835449417933779805)
                ·
                  refine ⟨7804429438293531725167427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20811811835449417933779805 7804429438293531725167427)
                  ·
                    refine ⟨11706644157440297587751141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7804429438293531725167427 11706644157440297587751141)
                    ·
                      refine ⟨2194995779520055797703339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11706644157440297587751141 2194995779520055797703339)
                      ·
                        rfl

theorem cell23_4274739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 2, 3, 1, 4].length) (baseStart_4274739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4274739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4274739 prefixEnd_4274739 := by exact prefixLift 4274739
  have htrace : WordTrace (prefixWord ++ tailWord_4274739) baseStart_4274739 baseEnd_4274739 := by
    simpa [prefixWord, tailWord_4274739, baseEnd_4274739] using wordTrace_append hprefix tailTrace_4274739
  have hstable : (prefixWord ++ tailWord_4274739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4274739).length < 2 ^ (prefixWord ++ tailWord_4274739).sum := by decide
  have hdescent : baseEnd_4274739 < baseStart_4274739 := by decide
  rcases family_descends (prefixWord ++ tailWord_4274739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4274753 : List Nat := [1, 2, 5, 1, 1, 4, 1, 2, 1, 5]
def baseStart_4274753 : Nat := 118140960795 + 4274753 * 2 ^ 59
def prefixEnd_4274753 : Nat := 4983230072969 + 3 ^ 40 * 4274753 * 2
def baseEnd_4274753 : Nat := 731667656083072914309425

theorem tailTrace_4274753 : CollatzResearch.WordTrace tailWord_4274753 prefixEnd_4274753 731667656083072914309425 := by
  unfold tailWord_4274753
  simp only [CollatzResearch.WordTrace]
  refine ⟨155913050682307425533692913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103942033788204950355795275 155913050682307425533692913)
  ·
    refine ⟨116934788011730569150269685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155913050682307425533692913 116934788011730569150269685)
    ·
      refine ⟨10962636376099740857837783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 116934788011730569150269685 10962636376099740857837783)
      ·
        refine ⟨16443954564149611286756675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10962636376099740857837783 16443954564149611286756675)
        ·
          refine ⟨24665931846224416930135013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16443954564149611286756675 24665931846224416930135013)
          ·
            refine ⟨4624862221167078174400315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24665931846224416930135013 4624862221167078174400315)
            ·
              refine ⟨6937293331750617261600473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4624862221167078174400315 6937293331750617261600473)
              ·
                refine ⟨5202969998812962946200355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6937293331750617261600473 5202969998812962946200355)
                ·
                  refine ⟨7804454998219444419300533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5202969998812962946200355 7804454998219444419300533)
                  ·
                    refine ⟨731667656083072914309425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7804454998219444419300533 731667656083072914309425)
                    ·
                      rfl

theorem cell23_4274753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 1, 2, 1, 5].length) (baseStart_4274753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4274753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4274753 prefixEnd_4274753 := by exact prefixLift 4274753
  have htrace : WordTrace (prefixWord ++ tailWord_4274753) baseStart_4274753 baseEnd_4274753 := by
    simpa [prefixWord, tailWord_4274753, baseEnd_4274753] using wordTrace_append hprefix tailTrace_4274753
  have hstable : (prefixWord ++ tailWord_4274753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4274753).length < 2 ^ (prefixWord ++ tailWord_4274753).sum := by decide
  have hdescent : baseEnd_4274753 < baseStart_4274753 := by decide
  rcases family_descends (prefixWord ++ tailWord_4274753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4274769 : List Nat := [1, 2, 2, 1, 3, 3, 1, 1, 3, 2, 4]
def baseStart_4274769 : Nat := 118140960795 + 4274769 * 2 ^ 59
def prefixEnd_4274769 : Nat := 4983230072969 + 3 ^ 40 * 4274769 * 2
def baseEnd_4274769 : Nat := 2195011183939690680328201

theorem tailTrace_4274769 : CollatzResearch.WordTrace tailWord_4274769 prefixEnd_4274769 2195011183939690680328201 := by
  unfold tailWord_4274769
  simp only [CollatzResearch.WordTrace]
  refine ⟨155913634250249460266275361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103942422833499640177516907 155913634250249460266275361)
  ·
    refine ⟨116935225687687095199706521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155913634250249460266275361 116935225687687095199706521)
    ·
      refine ⟨87701419265765321399779891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116935225687687095199706521 87701419265765321399779891)
      ·
        refine ⟨131552128898647982099669837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87701419265765321399779891 131552128898647982099669837)
        ·
          refine ⟨49332048336992993287376189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 131552128898647982099669837 49332048336992993287376189)
          ·
            refine ⟨18499518126372372482766071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49332048336992993287376189 18499518126372372482766071)
            ·
              refine ⟨27749277189558558724149107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18499518126372372482766071 27749277189558558724149107)
              ·
                refine ⟨41623915784337838086223661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27749277189558558724149107 41623915784337838086223661)
                ·
                  refine ⟨15608968419126689282333873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41623915784337838086223661 15608968419126689282333873)
                  ·
                    refine ⟨11706726314345016961750405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15608968419126689282333873 11706726314345016961750405)
                    ·
                      refine ⟨2195011183939690680328201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11706726314345016961750405 2195011183939690680328201)
                      ·
                        rfl

theorem cell23_4274769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 1, 3, 2, 4].length) (baseStart_4274769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4274769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4274769 prefixEnd_4274769 := by exact prefixLift 4274769
  have htrace : WordTrace (prefixWord ++ tailWord_4274769) baseStart_4274769 baseEnd_4274769 := by
    simpa [prefixWord, tailWord_4274769, baseEnd_4274769] using wordTrace_append hprefix tailTrace_4274769
  have hstable : (prefixWord ++ tailWord_4274769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4274769).length < 2 ^ (prefixWord ++ tailWord_4274769).sum := by decide
  have hdescent : baseEnd_4274769 < baseStart_4274769 := by decide
  rcases family_descends (prefixWord ++ tailWord_4274769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4274776 : List Nat := [2, 1, 2, 2, 1, 2, 2, 5, 1, 2, 3]
def baseStart_4274776 : Nat := 118140960795 + 4274776 * 2 ^ 59
def prefixEnd_4274776 : Nat := 4983230072969 + 3 ^ 40 * 4274776 * 2
def baseEnd_4274776 : Nat := 2195014778304272152940669

theorem tailTrace_4274776 : CollatzResearch.WordTrace tailWord_4274776 prefixEnd_4274776 2195014778304272152940669 := by
  unfold tailWord_4274776
  simp only [CollatzResearch.WordTrace]
  refine ⟨77956944780612050230890091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103942593040816066974520121 77956944780612050230890091)
  ·
    refine ⟨116935417170918075346335137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77956944780612050230890091 116935417170918075346335137)
    ·
      refine ⟨87701562878188556509751353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116935417170918075346335137 87701562878188556509751353)
      ·
        refine ⟨65776172158641417382313515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87701562878188556509751353 65776172158641417382313515)
        ·
          refine ⟨98664258237962126073470273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65776172158641417382313515 98664258237962126073470273)
          ·
            refine ⟨73998193678471594555102705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98664258237962126073470273 73998193678471594555102705)
            ·
              refine ⟨55498645258853695916327029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73998193678471594555102705 55498645258853695916327029)
              ·
                refine ⟨5202997993017533992155659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 55498645258853695916327029 5202997993017533992155659)
                ·
                  refine ⟨7804496989526300988233489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5202997993017533992155659 7804496989526300988233489)
                  ·
                    refine ⟨5853372742144725741175117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7804496989526300988233489 5853372742144725741175117)
                    ·
                      refine ⟨2195014778304272152940669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5853372742144725741175117 2195014778304272152940669)
                      ·
                        rfl

theorem cell23_4274776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 5, 1, 2, 3].length) (baseStart_4274776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4274776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4274776 prefixEnd_4274776 := by exact prefixLift 4274776
  have htrace : WordTrace (prefixWord ++ tailWord_4274776) baseStart_4274776 baseEnd_4274776 := by
    simpa [prefixWord, tailWord_4274776, baseEnd_4274776] using wordTrace_append hprefix tailTrace_4274776
  have hstable : (prefixWord ++ tailWord_4274776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4274776).length < 2 ^ (prefixWord ++ tailWord_4274776).sum := by decide
  have hdescent : baseEnd_4274776 < baseStart_4274776 := by decide
  rcases family_descends (prefixWord ++ tailWord_4274776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4274839 : List Nat := [1, 1, 3, 3, 2, 1, 1, 1, 4, 6]
def baseStart_4274839 : Nat := 118140960795 + 4274839 * 2 ^ 59
def prefixEnd_4274839 : Nat := 4983230072969 + 3 ^ 40 * 4274839 * 2
def baseEnd_4274839 : Nat := 731682375861835135484293

theorem tailTrace_4274839 : CollatzResearch.WordTrace tailWord_4274839 prefixEnd_4274839 731682375861835135484293 := by
  unfold tailWord_4274839
  simp only [CollatzResearch.WordTrace]
  refine ⟨155916187359995862221323571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103944124906663908147549047 155916187359995862221323571)
  ·
    refine ⟨233874281039993793331985357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155916187359995862221323571 233874281039993793331985357)
    ·
      refine ⟨87702855389997672499494509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 233874281039993793331985357 87702855389997672499494509)
      ·
        refine ⟨32888570771249127187310441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87702855389997672499494509 32888570771249127187310441)
        ·
          refine ⟨24666428078436845390482831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32888570771249127187310441 24666428078436845390482831)
          ·
            refine ⟨36999642117655268085724247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24666428078436845390482831 36999642117655268085724247)
            ·
              refine ⟨55499463176482902128586371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36999642117655268085724247 55499463176482902128586371)
              ·
                refine ⟨83249194764724353192879557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55499463176482902128586371 83249194764724353192879557)
                ·
                  refine ⟨15609224018385816223664917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 83249194764724353192879557 15609224018385816223664917)
                  ·
                    refine ⟨731682375861835135484293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15609224018385816223664917 731682375861835135484293)
                    ·
                      rfl

theorem cell23_4274839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 1, 4, 6].length) (baseStart_4274839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4274839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4274839 prefixEnd_4274839 := by exact prefixLift 4274839
  have htrace : WordTrace (prefixWord ++ tailWord_4274839) baseStart_4274839 baseEnd_4274839 := by
    simpa [prefixWord, tailWord_4274839, baseEnd_4274839] using wordTrace_append hprefix tailTrace_4274839
  have hstable : (prefixWord ++ tailWord_4274839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4274839).length < 2 ^ (prefixWord ++ tailWord_4274839).sum := by decide
  have hdescent : baseEnd_4274839 < baseStart_4274839 := by decide
  rcases family_descends (prefixWord ++ tailWord_4274839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4274863 : List Nat := [1, 1, 2, 1, 2, 5, 3, 1, 1, 4, 2]
def baseStart_4274863 : Nat := 118140960795 + 4274863 * 2 ^ 59
def prefixEnd_4274863 : Nat := 4983230072969 + 3 ^ 40 * 4274863 * 2
def baseEnd_4274863 : Nat := 2195059451121213312552769

theorem tailTrace_4274863 : CollatzResearch.WordTrace tailWord_4274863 prefixEnd_4274863 2195059451121213312552769 := by
  unfold tailWord_4274863
  simp only [CollatzResearch.WordTrace]
  refine ⟨155917062711908914320197243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103944708474605942880131495 155917062711908914320197243)
  ·
    refine ⟨233875594067863371480295865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155917062711908914320197243 233875594067863371480295865)
    ·
      refine ⟨175406695550897528610221899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 233875594067863371480295865 175406695550897528610221899)
      ·
        refine ⟨263110043326346292915332849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175406695550897528610221899 263110043326346292915332849)
        ·
          refine ⟨197332532494759719686499637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 263110043326346292915332849 197332532494759719686499637)
          ·
            refine ⟨18499924921383723720609341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 197332532494759719686499637 18499924921383723720609341)
            ·
              refine ⟨6937471845518896395228503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18499924921383723720609341 6937471845518896395228503)
              ·
                refine ⟨10406207768278344592842755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6937471845518896395228503 10406207768278344592842755)
                ·
                  refine ⟨15609311652417516889264133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10406207768278344592842755 15609311652417516889264133)
                  ·
                    refine ⟨2926745934828284416737025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15609311652417516889264133 2926745934828284416737025)
                    ·
                      refine ⟨2195059451121213312552769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2926745934828284416737025 2195059451121213312552769)
                      ·
                        rfl

theorem cell23_4274863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 3, 1, 1, 4, 2].length) (baseStart_4274863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4274863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4274863 prefixEnd_4274863 := by exact prefixLift 4274863
  have htrace : WordTrace (prefixWord ++ tailWord_4274863) baseStart_4274863 baseEnd_4274863 := by
    simpa [prefixWord, tailWord_4274863, baseEnd_4274863] using wordTrace_append hprefix tailTrace_4274863
  have hstable : (prefixWord ++ tailWord_4274863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4274863).length < 2 ^ (prefixWord ++ tailWord_4274863).sum := by decide
  have hdescent : baseEnd_4274863 < baseStart_4274863 := by decide
  rcases family_descends (prefixWord ++ tailWord_4274863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4274956 : List Nat := [2, 2, 1, 2, 2, 1, 1, 2, 3, 4, 3]
def baseStart_4274956 : Nat := 118140960795 + 4274956 * 2 ^ 59
def prefixEnd_4274956 : Nat := 4983230072969 + 3 ^ 40 * 4274956 * 2
def baseEnd_4274956 : Nat := 2195107204822081448689841

theorem tailTrace_4274956 : CollatzResearch.WordTrace tailWord_4274956 prefixEnd_4274956 2195107204822081448689841 := by
  unfold tailWord_4274956
  simp only [CollatzResearch.WordTrace]
  refine ⟨77960227350285995601666361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103946969800381327468888481 77960227350285995601666361)
  ·
    refine ⟨58470170512714496701249771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77960227350285995601666361 58470170512714496701249771)
    ·
      refine ⟨87705255769071745051874657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58470170512714496701249771 87705255769071745051874657)
      ·
        refine ⟨65778941826803808788905993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87705255769071745051874657 65778941826803808788905993)
        ·
          refine ⟨49334206370102856591679495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65778941826803808788905993 49334206370102856591679495)
          ·
            refine ⟨74001309555154284887519243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49334206370102856591679495 74001309555154284887519243)
            ·
              refine ⟨111001964332731427331278865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74001309555154284887519243 111001964332731427331278865)
              ·
                refine ⟨83251473249548570498459149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 111001964332731427331278865 83251473249548570498459149)
                ·
                  refine ⟨31219302468580713936922181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 83251473249548570498459149 31219302468580713936922181)
                  ·
                    refine ⟨5853619212858883863172909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 31219302468580713936922181 5853619212858883863172909)
                    ·
                      refine ⟨2195107204822081448689841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5853619212858883863172909 2195107204822081448689841)
                      ·
                        rfl

theorem cell23_4274956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 3, 4, 3].length) (baseStart_4274956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4274956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4274956 prefixEnd_4274956 := by exact prefixLift 4274956
  have htrace : WordTrace (prefixWord ++ tailWord_4274956) baseStart_4274956 baseEnd_4274956 := by
    simpa [prefixWord, tailWord_4274956, baseEnd_4274956] using wordTrace_append hprefix tailTrace_4274956
  have hstable : (prefixWord ++ tailWord_4274956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4274956).length < 2 ^ (prefixWord ++ tailWord_4274956).sum := by decide
  have hdescent : baseEnd_4274956 < baseStart_4274956 := by decide
  rcases family_descends (prefixWord ++ tailWord_4274956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4274980 : List Nat := [2, 3, 1, 3, 3, 1, 1, 2, 3, 4]
def baseStart_4274980 : Nat := 118140960795 + 4274980 * 2 ^ 59
def prefixEnd_4274980 : Nat := 4983230072969 + 3 ^ 40 * 4274980 * 2
def baseEnd_4274980 : Nat := 731706509452596451596577

theorem tailTrace_4274980 : CollatzResearch.WordTrace tailWord_4274980 prefixEnd_4274980 731706509452596451596577 := by
  unfold tailWord_4274980
  simp only [CollatzResearch.WordTrace]
  refine ⟨77960665026242521651103197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103947553368323362201470929 77960665026242521651103197)
  ·
    refine ⟨29235249384840945619163699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77960665026242521651103197 29235249384840945619163699)
    ·
      refine ⟨43852874077261418428745549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29235249384840945619163699 43852874077261418428745549)
      ·
        refine ⟨16444827778973031910779581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43852874077261418428745549 16444827778973031910779581)
        ·
          refine ⟨6166810417114886966542343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16444827778973031910779581 6166810417114886966542343)
          ·
            refine ⟨9250215625672330449813515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6166810417114886966542343 9250215625672330449813515)
            ·
              refine ⟨13875323438508495674720273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9250215625672330449813515 13875323438508495674720273)
              ·
                refine ⟨10406492578881371756040205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13875323438508495674720273 10406492578881371756040205)
                ·
                  refine ⟨3902434717080514408515077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10406492578881371756040205 3902434717080514408515077)
                  ·
                    refine ⟨731706509452596451596577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3902434717080514408515077 731706509452596451596577)
                    ·
                      rfl

theorem cell23_4274980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 2, 3, 4].length) (baseStart_4274980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4274980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4274980 prefixEnd_4274980 := by exact prefixLift 4274980
  have htrace : WordTrace (prefixWord ++ tailWord_4274980) baseStart_4274980 baseEnd_4274980 := by
    simpa [prefixWord, tailWord_4274980, baseEnd_4274980] using wordTrace_append hprefix tailTrace_4274980
  have hstable : (prefixWord ++ tailWord_4274980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4274980).length < 2 ^ (prefixWord ++ tailWord_4274980).sum := by decide
  have hdescent : baseEnd_4274980 < baseStart_4274980 := by decide
  rcases family_descends (prefixWord ++ tailWord_4274980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4274990 : List Nat := [4, 1, 3, 2, 1, 2, 1, 1, 1, 4, 3]
def baseStart_4274990 : Nat := 118140960795 + 4274990 * 2 ^ 59
def prefixEnd_4274990 : Nat := 4983230072969 + 3 ^ 40 * 4274990 * 2
def baseEnd_4274990 : Nat := 2195124663164334315664685

theorem tailTrace_4274990 : CollatzResearch.WordTrace tailWord_4274990 prefixEnd_4274990 2195124663164334315664685 := by
  unfold tailWord_4274990
  simp only [CollatzResearch.WordTrace]
  refine ⟨19490211847806101876258803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 103947796521632543340046949 19490211847806101876258803)
  ·
    refine ⟨29235317771709152814388205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19490211847806101876258803 29235317771709152814388205)
    ·
      refine ⟨10963244164390932305395577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29235317771709152814388205 10963244164390932305395577)
      ·
        refine ⟨8222433123293199229046683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10963244164390932305395577 8222433123293199229046683)
        ·
          refine ⟨12333649684939798843570025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8222433123293199229046683 12333649684939798843570025)
          ·
            refine ⟨9250237263704849132677519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12333649684939798843570025 9250237263704849132677519)
            ·
              refine ⟨13875355895557273699016279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9250237263704849132677519 13875355895557273699016279)
              ·
                refine ⟨20813033843335910548524419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13875355895557273699016279 20813033843335910548524419)
                ·
                  refine ⟨31219550765003865822786629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20813033843335910548524419 31219550765003865822786629)
                  ·
                    refine ⟨5853665768438224841772493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 31219550765003865822786629 5853665768438224841772493)
                    ·
                      refine ⟨2195124663164334315664685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5853665768438224841772493 2195124663164334315664685)
                      ·
                        rfl

theorem cell23_4274990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 1, 1, 4, 3].length) (baseStart_4274990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4274990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4274990 prefixEnd_4274990 := by exact prefixLift 4274990
  have htrace : WordTrace (prefixWord ++ tailWord_4274990) baseStart_4274990 baseEnd_4274990 := by
    simpa [prefixWord, tailWord_4274990, baseEnd_4274990] using wordTrace_append hprefix tailTrace_4274990
  have hstable : (prefixWord ++ tailWord_4274990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4274990).length < 2 ^ (prefixWord ++ tailWord_4274990).sum := by decide
  have hdescent : baseEnd_4274990 < baseStart_4274990 := by decide
  rcases family_descends (prefixWord ++ tailWord_4274990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4274997 : List Nat := [1, 3, 3, 1, 3, 2, 2, 3, 1, 4]
def baseStart_4274997 : Nat := 118140960795 + 4274997 * 2 ^ 59
def prefixEnd_4274997 : Nat := 4983230072969 + 3 ^ 40 * 4274997 * 2
def baseEnd_4274997 : Nat := 731709419176305262759051

theorem tailTrace_4274997 : CollatzResearch.WordTrace tailWord_4274997 prefixEnd_4274997 731709419176305262759051 := by
  unfold tailWord_4274997
  simp only [CollatzResearch.WordTrace]
  refine ⟨155921950093423455205575245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103947966728948970137050163 155921950093423455205575245)
  ·
    refine ⟨58470731285033795702090717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 155921950093423455205575245 58470731285033795702090717)
    ·
      refine ⟨21926524231887673388284019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58470731285033795702090717 21926524231887673388284019)
      ·
        refine ⟨32889786347831510082426029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21926524231887673388284019 32889786347831510082426029)
        ·
          refine ⟨12333669880436816280909761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32889786347831510082426029 12333669880436816280909761)
          ·
            refine ⟨9250252410327612210682321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12333669880436816280909761 9250252410327612210682321)
            ·
              refine ⟨6937689307745709158011741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9250252410327612210682321 6937689307745709158011741)
              ·
                refine ⟨2601633490404640934254403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6937689307745709158011741 2601633490404640934254403)
                ·
                  refine ⟨3902450235606961401381605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2601633490404640934254403 3902450235606961401381605)
                  ·
                    refine ⟨731709419176305262759051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3902450235606961401381605 731709419176305262759051)
                    ·
                      rfl

theorem cell23_4274997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 2, 3, 1, 4].length) (baseStart_4274997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4274997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4274997 prefixEnd_4274997 := by exact prefixLift 4274997
  have htrace : WordTrace (prefixWord ++ tailWord_4274997) baseStart_4274997 baseEnd_4274997 := by
    simpa [prefixWord, tailWord_4274997, baseEnd_4274997] using wordTrace_append hprefix tailTrace_4274997
  have hstable : (prefixWord ++ tailWord_4274997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4274997).length < 2 ^ (prefixWord ++ tailWord_4274997).sum := by decide
  have hdescent : baseEnd_4274997 < baseStart_4274997 := by decide
  rcases family_descends (prefixWord ++ tailWord_4274997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4275014 : List Nat := [6, 1, 1, 2, 2, 1, 2, 1, 3, 4]
def baseStart_4275014 : Nat := 118140960795 + 4275014 * 2 ^ 59
def prefixEnd_4275014 : Nat := 4983230072969 + 3 ^ 40 * 4275014 * 2
def baseEnd_4275014 : Nat := 731712328900014073921525

theorem tailTrace_4275014 : CollatzResearch.WordTrace tailWord_4275014 prefixEnd_4275014 731712328900014073921525 := by
  unfold tailWord_4275014
  simp only [CollatzResearch.WordTrace]
  refine ⟨4872580316698808347154503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 103948380089574578072629397 4872580316698808347154503)
  ·
    refine ⟨7308870475048212520731755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4872580316698808347154503 7308870475048212520731755)
    ·
      refine ⟨10963305712572318781097633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7308870475048212520731755 10963305712572318781097633)
      ·
        refine ⟨8222479284429239085823225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10963305712572318781097633 8222479284429239085823225)
        ·
          refine ⟨6166859463321929314367419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8222479284429239085823225 6166859463321929314367419)
          ·
            refine ⟨9250289194982893971551129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6166859463321929314367419 9250289194982893971551129)
            ·
              refine ⟨6937716896237170478663347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9250289194982893971551129 6937716896237170478663347)
              ·
                refine ⟨10406575344355755717995021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6937716896237170478663347 10406575344355755717995021)
                ·
                  refine ⟨3902465754133408394248133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10406575344355755717995021 3902465754133408394248133)
                  ·
                    refine ⟨731712328900014073921525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3902465754133408394248133 731712328900014073921525)
                    ·
                      rfl

theorem cell23_4275014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 2, 1, 3, 4].length) (baseStart_4275014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4275014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4275014 prefixEnd_4275014 := by exact prefixLift 4275014
  have htrace : WordTrace (prefixWord ++ tailWord_4275014) baseStart_4275014 baseEnd_4275014 := by
    simpa [prefixWord, tailWord_4275014, baseEnd_4275014] using wordTrace_append hprefix tailTrace_4275014
  have hstable : (prefixWord ++ tailWord_4275014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4275014).length < 2 ^ (prefixWord ++ tailWord_4275014).sum := by decide
  have hdescent : baseEnd_4275014 < baseStart_4275014 := by decide
  rcases family_descends (prefixWord ++ tailWord_4275014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4275020 : List Nat := [2, 2, 1, 3, 3, 1, 1, 3, 3, 1, 3]
def baseStart_4275020 : Nat := 118140960795 + 4275020 * 2 ^ 59
def prefixEnd_4275020 : Nat := 4983230072969 + 3 ^ 40 * 4275020 * 2
def baseEnd_4275020 : Nat := 2195140067583969198289547

theorem tailTrace_4275020 : CollatzResearch.WordTrace tailWord_4275020 prefixEnd_4275020 2195140067583969198289547 := by
  unfold tailWord_4275020
  simp only [CollatzResearch.WordTrace]
  refine ⟨77961394486170065066831257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103948525981560086755775009 77961394486170065066831257)
  ·
    refine ⟨58471045864627548800123443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77961394486170065066831257 58471045864627548800123443)
    ·
      refine ⟨87706568796941323200185165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58471045864627548800123443 87706568796941323200185165)
      ·
        refine ⟨32889963298852996200069437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87706568796941323200185165 32889963298852996200069437)
        ·
          refine ⟨12333736237069873575026039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32889963298852996200069437 12333736237069873575026039)
          ·
            refine ⟨18500604355604810362539059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12333736237069873575026039 18500604355604810362539059)
            ·
              refine ⟨27750906533407215543808589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18500604355604810362539059 27750906533407215543808589)
              ·
                refine ⟨10406589950027705828928221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27750906533407215543808589 10406589950027705828928221)
                ·
                  refine ⟨3902471231260389685848083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10406589950027705828928221 3902471231260389685848083)
                  ·
                    refine ⟨5853706846890584528772125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3902471231260389685848083 5853706846890584528772125)
                    ·
                      refine ⟨2195140067583969198289547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5853706846890584528772125 2195140067583969198289547)
                      ·
                        rfl

theorem cell23_4275020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 3, 3, 1, 3].length) (baseStart_4275020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4275020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4275020 prefixEnd_4275020 := by exact prefixLift 4275020
  have htrace : WordTrace (prefixWord ++ tailWord_4275020) baseStart_4275020 baseEnd_4275020 := by
    simpa [prefixWord, tailWord_4275020, baseEnd_4275020] using wordTrace_append hprefix tailTrace_4275020
  have hstable : (prefixWord ++ tailWord_4275020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4275020).length < 2 ^ (prefixWord ++ tailWord_4275020).sum := by decide
  have hdescent : baseEnd_4275020 < baseStart_4275020 := by decide
  rcases family_descends (prefixWord ++ tailWord_4275020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4275077 : List Nat := [1, 3, 1, 1, 3, 3, 3, 1, 3, 2, 2]
def baseStart_4275077 : Nat := 118140960795 + 4275077 * 2 ^ 59
def prefixEnd_4275077 : Nat := 4983230072969 + 3 ^ 40 * 4275077 * 2
def baseEnd_4275077 : Nat := 2195169335981275475276785

theorem tailTrace_4275077 : CollatzResearch.WordTrace tailWord_4275077 prefixEnd_4275077 2195169335981275475276785 := by
  unfold tailWord_4275077
  simp only [CollatzResearch.WordTrace]
  refine ⟨155924867933133628868487485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103949911955422419245658323 155924867933133628868487485)
  ·
    refine ⟨58471825474925110825682807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 155924867933133628868487485 58471825474925110825682807)
    ·
      refine ⟨87707738212387666238524211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58471825474925110825682807 87707738212387666238524211)
      ·
        refine ⟨131561607318581499357786317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87707738212387666238524211 131561607318581499357786317)
        ·
          refine ⟨49335602744468062259169869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 131561607318581499357786317 49335602744468062259169869)
          ·
            refine ⟨18500851029175523347188701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49335602744468062259169869 18500851029175523347188701)
            ·
              refine ⟨6937819135940821255195763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18500851029175523347188701 6937819135940821255195763)
              ·
                refine ⟨10406728703911231882793645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6937819135940821255195763 10406728703911231882793645)
                ·
                  refine ⟨3902523263966711956047617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10406728703911231882793645 3902523263966711956047617)
                  ·
                    refine ⟨2926892447975033967035713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3902523263966711956047617 2926892447975033967035713)
                    ·
                      refine ⟨2195169335981275475276785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2926892447975033967035713 2195169335981275475276785)
                      ·
                        rfl

theorem cell23_4275077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 3, 1, 3, 2, 2].length) (baseStart_4275077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4275077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4275077 prefixEnd_4275077 := by exact prefixLift 4275077
  have htrace : WordTrace (prefixWord ++ tailWord_4275077) baseStart_4275077 baseEnd_4275077 := by
    simpa [prefixWord, tailWord_4275077, baseEnd_4275077] using wordTrace_append hprefix tailTrace_4275077
  have hstable : (prefixWord ++ tailWord_4275077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4275077).length < 2 ^ (prefixWord ++ tailWord_4275077).sum := by decide
  have hdescent : baseEnd_4275077 < baseStart_4275077 := by decide
  rcases family_descends (prefixWord ++ tailWord_4275077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4275094 : List Nat := [5, 3, 1, 1, 1, 2, 1, 1, 3, 1, 4]
def baseStart_4275094 : Nat := 118140960795 + 4275094 * 2 ^ 59
def prefixEnd_4275094 : Nat := 4983230072969 + 3 ^ 40 * 4275094 * 2
def baseEnd_4275094 : Nat := 2195178065152401908764207

theorem tailTrace_4275094 : CollatzResearch.WordTrace tailWord_4275094 prefixEnd_4275094 2195178065152401908764207 := by
  unfold tailWord_4275094
  simp only [CollatzResearch.WordTrace]
  refine ⟨9745342998379502548241021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 103950325316048027181237557 9745342998379502548241021)
  ·
    refine ⟨3654503624392313455590383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9745342998379502548241021 3654503624392313455590383)
    ·
      refine ⟨5481755436588470183385575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3654503624392313455590383 5481755436588470183385575)
      ·
        refine ⟨8222633154882705275078363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5481755436588470183385575 8222633154882705275078363)
        ·
          refine ⟨12333949732324057912617545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8222633154882705275078363 12333949732324057912617545)
          ·
            refine ⟨9250462299243043434463159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12333949732324057912617545 9250462299243043434463159)
            ·
              refine ⟨13875693448864565151694739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9250462299243043434463159 13875693448864565151694739)
              ·
                refine ⟨20813540173296847727542109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13875693448864565151694739 20813540173296847727542109)
                ·
                  refine ⟨7805077564986317897828291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20813540173296847727542109 7805077564986317897828291)
                  ·
                    refine ⟨11707616347479476846742437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7805077564986317897828291 11707616347479476846742437)
                    ·
                      refine ⟨2195178065152401908764207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11707616347479476846742437 2195178065152401908764207)
                      ·
                        rfl

theorem cell23_4275094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_4275094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4275094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4275094 prefixEnd_4275094 := by exact prefixLift 4275094
  have htrace : WordTrace (prefixWord ++ tailWord_4275094) baseStart_4275094 baseEnd_4275094 := by
    simpa [prefixWord, tailWord_4275094, baseEnd_4275094] using wordTrace_append hprefix tailTrace_4275094
  have hstable : (prefixWord ++ tailWord_4275094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4275094).length < 2 ^ (prefixWord ++ tailWord_4275094).sum := by decide
  have hdescent : baseEnd_4275094 < baseStart_4275094 := by decide
  rcases family_descends (prefixWord ++ tailWord_4275094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4275116 : List Nat := [2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 8]
def baseStart_4275116 : Nat := 118140960795 + 4275116 * 2 ^ 59
def prefixEnd_4275116 : Nat := 4983230072969 + 3 ^ 40 * 4275116 * 2
def baseEnd_4275116 : Nat := 2195189361726800822689105

theorem tailTrace_4275116 : CollatzResearch.WordTrace tailWord_4275116 prefixEnd_4275116 2195189361726800822689105 := by
  unfold tailWord_4275116
  simp only [CollatzResearch.WordTrace]
  refine ⟨77963145189996169264578601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103950860253328225686104801 77963145189996169264578601)
  ·
    refine ⟨58472358892497126948433951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77963145189996169264578601 58472358892497126948433951)
    ·
      refine ⟨87708538338745690422650927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58472358892497126948433951 87708538338745690422650927)
      ·
        refine ⟨131562807508118535633976391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87708538338745690422650927 131562807508118535633976391)
        ·
          refine ⟨197344211262177803450964587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131562807508118535633976391 197344211262177803450964587)
          ·
            refine ⟨296016316893266705176446881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 197344211262177803450964587 296016316893266705176446881)
            ·
              refine ⟨222012237669950028882335161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 296016316893266705176446881 222012237669950028882335161)
              ·
                refine ⟨166509178252462521661751371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 222012237669950028882335161 166509178252462521661751371)
                ·
                  refine ⟨249763767378693782492627057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 166509178252462521661751371 249763767378693782492627057)
                  ·
                    refine ⟨187322825534020336869470293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 249763767378693782492627057 187322825534020336869470293)
                    ·
                      refine ⟨2195189361726800822689105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 187322825534020336869470293 2195189361726800822689105)
                      ·
                        rfl

theorem cell23_4275116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 8].length) (baseStart_4275116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4275116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4275116 prefixEnd_4275116 := by exact prefixLift 4275116
  have htrace : WordTrace (prefixWord ++ tailWord_4275116) baseStart_4275116 baseEnd_4275116 := by
    simpa [prefixWord, tailWord_4275116, baseEnd_4275116] using wordTrace_append hprefix tailTrace_4275116
  have hstable : (prefixWord ++ tailWord_4275116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4275116).length < 2 ^ (prefixWord ++ tailWord_4275116).sum := by decide
  have hdescent : baseEnd_4275116 < baseStart_4275116 := by decide
  rcases family_descends (prefixWord ++ tailWord_4275116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4275153 : List Nat := [1, 2, 2, 1, 2, 1, 3, 2, 2, 4, 3]
def baseStart_4275153 : Nat := 118140960795 + 4275153 * 2 ^ 59
def prefixEnd_4275153 : Nat := 4983230072969 + 3 ^ 40 * 4275153 * 2
def baseEnd_4275153 : Nat := 2195208360511017177926435

theorem tailTrace_4275153 : CollatzResearch.WordTrace tailWord_4275153 prefixEnd_4275153 2195208360511017177926435 := by
  unfold tailWord_4275153
  simp only [CollatzResearch.WordTrace]
  refine ⟨155927639880858293848254113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103951759920572195898836075 155927639880858293848254113)
  ·
    refine ⟨116945729910643720386190585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155927639880858293848254113 116945729910643720386190585)
    ·
      refine ⟨87709297432982790289642939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116945729910643720386190585 87709297432982790289642939)
      ·
        refine ⟨131563946149474185434464409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87709297432982790289642939 131563946149474185434464409)
        ·
          refine ⟨98672959612105639075848307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 131563946149474185434464409 98672959612105639075848307)
          ·
            refine ⟨148009439418158458613772461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98672959612105639075848307 148009439418158458613772461)
            ·
              refine ⟨55503539781809421980164673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 148009439418158458613772461 55503539781809421980164673)
              ·
                refine ⟨41627654836357066485123505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55503539781809421980164673 41627654836357066485123505)
                ·
                  refine ⟨31220741127267799863842629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41627654836357066485123505 31220741127267799863842629)
                  ·
                    refine ⟨5853888961362712474470493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 31220741127267799863842629 5853888961362712474470493)
                    ·
                      refine ⟨2195208360511017177926435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5853888961362712474470493 2195208360511017177926435)
                      ·
                        rfl

theorem cell23_4275153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 2, 2, 4, 3].length) (baseStart_4275153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4275153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4275153 prefixEnd_4275153 := by exact prefixLift 4275153
  have htrace : WordTrace (prefixWord ++ tailWord_4275153) baseStart_4275153 baseEnd_4275153 := by
    simpa [prefixWord, tailWord_4275153, baseEnd_4275153] using wordTrace_append hprefix tailTrace_4275153
  have hstable : (prefixWord ++ tailWord_4275153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4275153).length < 2 ^ (prefixWord ++ tailWord_4275153).sum := by decide
  have hdescent : baseEnd_4275153 < baseStart_4275153 := by decide
  rcases family_descends (prefixWord ++ tailWord_4275153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4275190 : List Nat := [5, 1, 1, 1, 3, 1, 1, 3, 7]
def baseStart_4275190 : Nat := 118140960795 + 4275190 * 2 ^ 59
def prefixEnd_4275190 : Nat := 4983230072969 + 3 ^ 40 * 4275190 * 2
def baseEnd_4275190 : Nat := 243914151032803725907085

theorem tailTrace_4275190 : CollatzResearch.WordTrace tailWord_4275190 prefixEnd_4275190 243914151032803725907085 := by
  unfold tailWord_4275190
  simp only [CollatzResearch.WordTrace]
  refine ⟨9745561836357765572959439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 103952659587816166111567349 9745561836357765572959439)
  ·
    refine ⟨14618342754536648359439159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9745561836357765572959439 14618342754536648359439159)
    ·
      refine ⟨21927514131804972539158739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14618342754536648359439159 21927514131804972539158739)
      ·
        refine ⟨32891271197707458808738109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21927514131804972539158739 32891271197707458808738109)
        ·
          refine ⟨12334226699140297053276791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32891271197707458808738109 12334226699140297053276791)
          ·
            refine ⟨18501340048710445579915187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12334226699140297053276791 18501340048710445579915187)
            ·
              refine ⟨27752010073065668369872781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18501340048710445579915187 27752010073065668369872781)
              ·
                refine ⟨10407003777399625638702293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27752010073065668369872781 10407003777399625638702293)
                ·
                  refine ⟨243914151032803725907085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10407003777399625638702293 243914151032803725907085)
                  ·
                    rfl

theorem cell23_4275190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 3, 7].length) (baseStart_4275190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4275190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4275190 prefixEnd_4275190 := by exact prefixLift 4275190
  have htrace : WordTrace (prefixWord ++ tailWord_4275190) baseStart_4275190 baseEnd_4275190 := by
    simpa [prefixWord, tailWord_4275190, baseEnd_4275190] using wordTrace_append hprefix tailTrace_4275190
  have hstable : (prefixWord ++ tailWord_4275190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4275190).length < 2 ^ (prefixWord ++ tailWord_4275190).sum := by decide
  have hdescent : baseEnd_4275190 < baseStart_4275190 := by decide
  rcases family_descends (prefixWord ++ tailWord_4275190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4275201 : List Nat := [1, 2, 4, 1, 2, 3, 3, 1, 2, 2, 2]
def baseStart_4275201 : Nat := 118140960795 + 4275201 * 2 ^ 59
def prefixEnd_4275201 : Nat := 4983230072969 + 3 ^ 40 * 4275201 * 2
def baseEnd_4275201 : Nat := 2195233007582432990126215

theorem tailTrace_4275201 : CollatzResearch.WordTrace tailWord_4275201 prefixEnd_4275201 2195233007582432990126215 := by
  unfold tailWord_4275201
  simp only [CollatzResearch.WordTrace]
  refine ⟨155929390584684398046001457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103952927056456265364000971 155929390584684398046001457)
  ·
    refine ⟨116947042938513298534501093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155929390584684398046001457 116947042938513298534501093)
    ·
      refine ⟨21927570550971243475218955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 116947042938513298534501093 21927570550971243475218955)
      ·
        refine ⟨32891355826456865212828433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21927570550971243475218955 32891355826456865212828433)
        ·
          refine ⟨24668516869842648909621325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32891355826456865212828433 24668516869842648909621325)
          ·
            refine ⟨9250693826190993341107997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24668516869842648909621325 9250693826190993341107997)
            ·
              refine ⟨3469010184821622502915499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9250693826190993341107997 3469010184821622502915499)
              ·
                refine ⟨5203515277232433754373249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3469010184821622502915499 5203515277232433754373249)
                ·
                  refine ⟨3902636457924325315779937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5203515277232433754373249 3902636457924325315779937)
                  ·
                    refine ⟨2926977343443243986834953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3902636457924325315779937 2926977343443243986834953)
                    ·
                      refine ⟨2195233007582432990126215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2926977343443243986834953 2195233007582432990126215)
                      ·
                        rfl

theorem cell23_4275201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 3, 1, 2, 2, 2].length) (baseStart_4275201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4275201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4275201 prefixEnd_4275201 := by exact prefixLift 4275201
  have htrace : WordTrace (prefixWord ++ tailWord_4275201) baseStart_4275201 baseEnd_4275201 := by
    simpa [prefixWord, tailWord_4275201, baseEnd_4275201] using wordTrace_append hprefix tailTrace_4275201
  have hstable : (prefixWord ++ tailWord_4275201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4275201).length < 2 ^ (prefixWord ++ tailWord_4275201).sum := by decide
  have hdescent : baseEnd_4275201 < baseStart_4275201 := by decide
  rcases family_descends (prefixWord ++ tailWord_4275201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4275357 : List Nat := [1, 4, 2, 1, 1, 2, 3, 1, 4, 4]
def baseStart_4275357 : Nat := 118140960795 + 4275357 * 2 ^ 59
def prefixEnd_4275357 : Nat := 4983230072969 + 3 ^ 40 * 4275357 * 2
def baseEnd_4275357 : Nat := 731771036854844793258499

theorem tailTrace_4275357 : CollatzResearch.WordTrace tailWord_4275357 prefixEnd_4275357 731771036854844793258499 := by
  unfold tailWord_4275357
  simp only [CollatzResearch.WordTrace]
  refine ⟨155935080372119236688680325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103956720248079491125786883 155935080372119236688680325)
  ·
    refine ⟨29237827569772356879127561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 155935080372119236688680325 29237827569772356879127561)
    ·
      refine ⟨21928370677329267659345671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29237827569772356879127561 21928370677329267659345671)
      ·
        refine ⟨32892556015993901489018507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21928370677329267659345671 32892556015993901489018507)
        ·
          refine ⟨49338834023990852233527761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32892556015993901489018507 49338834023990852233527761)
          ·
            refine ⟨37004125517993139175145821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49338834023990852233527761 37004125517993139175145821)
            ·
              refine ⟨13876547069247427190679683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37004125517993139175145821 13876547069247427190679683)
              ·
                refine ⟨20814820603871140786019525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13876547069247427190679683 20814820603871140786019525)
                ·
                  refine ⟨3902778863225838897378661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20814820603871140786019525 3902778863225838897378661)
                  ·
                    refine ⟨731771036854844793258499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3902778863225838897378661 731771036854844793258499)
                    ·
                      rfl

theorem cell23_4275357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 1, 4, 4].length) (baseStart_4275357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4275357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4275357 prefixEnd_4275357 := by exact prefixLift 4275357
  have htrace : WordTrace (prefixWord ++ tailWord_4275357) baseStart_4275357 baseEnd_4275357 := by
    simpa [prefixWord, tailWord_4275357, baseEnd_4275357] using wordTrace_append hprefix tailTrace_4275357
  have hstable : (prefixWord ++ tailWord_4275357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4275357).length < 2 ^ (prefixWord ++ tailWord_4275357).sum := by decide
  have hdescent : baseEnd_4275357 < baseStart_4275357 := by decide
  rcases family_descends (prefixWord ++ tailWord_4275357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4275358 : List Nat := [4, 3, 1, 1, 2, 1, 2, 4, 1, 1, 3]
def baseStart_4275358 : Nat := 118140960795 + 4275358 * 2 ^ 59
def prefixEnd_4275358 : Nat := 4983230072969 + 3 ^ 40 * 4275358 * 2
def baseEnd_4275358 : Nat := 2195313624045188875862993

theorem tailTrace_4275358 : CollatzResearch.WordTrace tailWord_4275358 prefixEnd_4275358 2195313624045188875862993 := by
  unfold tailWord_4275358
  simp only [CollatzResearch.WordTrace]
  refine ⟨19491889605639451732433341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 103956744563410409239644485 19491889605639451732433341)
  ·
    refine ⟨7309458602114794399662503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19491889605639451732433341 7309458602114794399662503)
    ·
      refine ⟨10964187903172191599493755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7309458602114794399662503 10964187903172191599493755)
      ·
        refine ⟨16446281854758287399240633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10964187903172191599493755 16446281854758287399240633)
        ·
          refine ⟨12334711391068715549430475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16446281854758287399240633 12334711391068715549430475)
          ·
            refine ⟨18502067086603073324145713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12334711391068715549430475 18502067086603073324145713)
            ·
              refine ⟨13876550314952304993109285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18502067086603073324145713 13876550314952304993109285)
              ·
                refine ⟨2601853184053557186207991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13876550314952304993109285 2601853184053557186207991)
                ·
                  refine ⟨3902779776080335779311987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2601853184053557186207991 3902779776080335779311987)
                  ·
                    refine ⟨5854169664120503668967981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3902779776080335779311987 5854169664120503668967981)
                    ·
                      refine ⟨2195313624045188875862993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5854169664120503668967981 2195313624045188875862993)
                      ·
                        rfl

theorem cell23_4275358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 4, 1, 1, 3].length) (baseStart_4275358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4275358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4275358 prefixEnd_4275358 := by exact prefixLift 4275358
  have htrace : WordTrace (prefixWord ++ tailWord_4275358) baseStart_4275358 baseEnd_4275358 := by
    simpa [prefixWord, tailWord_4275358, baseEnd_4275358] using wordTrace_append hprefix tailTrace_4275358
  have hstable : (prefixWord ++ tailWord_4275358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4275358).length < 2 ^ (prefixWord ++ tailWord_4275358).sum := by decide
  have hdescent : baseEnd_4275358 < baseStart_4275358 := by decide
  rcases family_descends (prefixWord ++ tailWord_4275358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4275360 : List Nat := [2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 6]
def baseStart_4275360 : Nat := 118140960795 + 4275360 * 2 ^ 59
def prefixEnd_4275360 : Nat := 4983230072969 + 3 ^ 40 * 4275360 * 2
def baseEnd_4275360 : Nat := 2195314651006497868037983

theorem tailTrace_4275360 : CollatzResearch.WordTrace tailWord_4275360 prefixEnd_4275360 2195314651006497868037983 := by
  unfold tailWord_4275360
  simp only [CollatzResearch.WordTrace]
  refine ⟨77967594895554184100519767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103956793194072245467359689 77967594895554184100519767)
  ·
    refine ⟨116951392343331276150779651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77967594895554184100519767 116951392343331276150779651)
    ·
      refine ⟨175427088514996914226169477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116951392343331276150779651 175427088514996914226169477)
      ·
        refine ⟨32892579096561921417406777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 175427088514996914226169477 32892579096561921417406777)
        ·
          refine ⟨24669434322421441063055083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32892579096561921417406777 24669434322421441063055083)
          ·
            refine ⟨37004151483632161594582625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24669434322421441063055083 37004151483632161594582625)
            ·
              refine ⟨27753113612724121195936969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37004151483632161594582625 27753113612724121195936969)
              ·
                refine ⟨20814835209543090896952727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27753113612724121195936969 20814835209543090896952727)
                ·
                  refine ⟨31222252814314636345429091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20814835209543090896952727 31222252814314636345429091)
                  ·
                    refine ⟨46833379221471954518143637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31222252814314636345429091 46833379221471954518143637)
                    ·
                      refine ⟨2195314651006497868037983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 46833379221471954518143637 2195314651006497868037983)
                      ·
                        rfl

theorem cell23_4275360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 6].length) (baseStart_4275360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4275360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4275360 prefixEnd_4275360 := by exact prefixLift 4275360
  have htrace : WordTrace (prefixWord ++ tailWord_4275360) baseStart_4275360 baseEnd_4275360 := by
    simpa [prefixWord, tailWord_4275360, baseEnd_4275360] using wordTrace_append hprefix tailTrace_4275360
  have hstable : (prefixWord ++ tailWord_4275360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4275360).length < 2 ^ (prefixWord ++ tailWord_4275360).sum := by decide
  have hdescent : baseEnd_4275360 < baseStart_4275360 := by decide
  rcases family_descends (prefixWord ++ tailWord_4275360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4275367 : List Nat := [1, 1, 6, 2, 1, 1, 1, 1, 3, 1, 5]
def baseStart_4275367 : Nat := 118140960795 + 4275367 * 2 ^ 59
def prefixEnd_4275367 : Nat := 4983230072969 + 3 ^ 40 * 4275367 * 2
def baseEnd_4275367 : Nat := 2195318245371079340650451

theorem tailTrace_4275367 : CollatzResearch.WordTrace tailWord_4275367 prefixEnd_4275367 2195318245371079340650451 := by
  unfold tailWord_4275367
  simp only [CollatzResearch.WordTrace]
  refine ⟨155935445102083008396544355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103956963401388672264362903 155935445102083008396544355)
  ·
    refine ⟨233903167653124512594816533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155935445102083008396544355 233903167653124512594816533)
    ·
      refine ⟨10964210983740211527882025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 233903167653124512594816533 10964210983740211527882025)
      ·
        refine ⟨8223158237805158645911519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10964210983740211527882025 8223158237805158645911519)
        ·
          refine ⟨12334737356707737968867279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8223158237805158645911519 12334737356707737968867279)
          ·
            refine ⟨18502106035061606953300919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12334737356707737968867279 18502106035061606953300919)
            ·
              refine ⟨27753159052592410429951379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18502106035061606953300919 27753159052592410429951379)
              ·
                refine ⟨41629738578888615644927069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27753159052592410429951379 41629738578888615644927069)
                ·
                  refine ⟨15611151967083230866847651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41629738578888615644927069 15611151967083230866847651)
                  ·
                    refine ⟨23416727950624846300271477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15611151967083230866847651 23416727950624846300271477)
                    ·
                      refine ⟨2195318245371079340650451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23416727950624846300271477 2195318245371079340650451)
                      ·
                        rfl

theorem cell23_4275367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_4275367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4275367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4275367 prefixEnd_4275367 := by exact prefixLift 4275367
  have htrace : WordTrace (prefixWord ++ tailWord_4275367) baseStart_4275367 baseEnd_4275367 := by
    simpa [prefixWord, tailWord_4275367, baseEnd_4275367] using wordTrace_append hprefix tailTrace_4275367
  have hstable : (prefixWord ++ tailWord_4275367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4275367).length < 2 ^ (prefixWord ++ tailWord_4275367).sum := by decide
  have hdescent : baseEnd_4275367 < baseStart_4275367 := by decide
  rcases family_descends (prefixWord ++ tailWord_4275367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4275377 : List Nat := [1, 2, 2, 5, 1, 2, 1, 1, 1, 1, 6]
def baseStart_4275377 : Nat := 118140960795 + 4275377 * 2 ^ 59
def prefixEnd_4275377 : Nat := 4983230072969 + 3 ^ 40 * 4275377 * 2
def baseEnd_4275377 : Nat := 2195323380177624301525405

theorem tailTrace_4275377 : CollatzResearch.WordTrace tailWord_4275377 prefixEnd_4275377 2195323380177624301525405 := by
  unfold tailWord_4275377
  simp only [CollatzResearch.WordTrace]
  refine ⟨155935809832046780104408385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103957206554697853402938923 155935809832046780104408385)
  ·
    refine ⟨116951857374035085078306289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155935809832046780104408385 116951857374035085078306289)
    ·
      refine ⟨87713893030526313808729717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116951857374035085078306289 87713893030526313808729717)
      ·
        refine ⟨8223177471611841919568411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 87713893030526313808729717 8223177471611841919568411)
        ·
          refine ⟨12334766207417762879352617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8223177471611841919568411 12334766207417762879352617)
          ·
            refine ⟨9251074655563322159514463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12334766207417762879352617 9251074655563322159514463)
            ·
              refine ⟨13876611983344983239271695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9251074655563322159514463 13876611983344983239271695)
              ·
                refine ⟨20814917975017474858907543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13876611983344983239271695 20814917975017474858907543)
                ·
                  refine ⟨31222376962526212288361315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20814917975017474858907543 31222376962526212288361315)
                  ·
                    refine ⟨46833565443789318432541973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31222376962526212288361315 46833565443789318432541973)
                    ·
                      refine ⟨2195323380177624301525405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 46833565443789318432541973 2195323380177624301525405)
                      ·
                        rfl

theorem cell23_4275377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_4275377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4275377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4275377 prefixEnd_4275377 := by exact prefixLift 4275377
  have htrace : WordTrace (prefixWord ++ tailWord_4275377) baseStart_4275377 baseEnd_4275377 := by
    simpa [prefixWord, tailWord_4275377, baseEnd_4275377] using wordTrace_append hprefix tailTrace_4275377
  have hstable : (prefixWord ++ tailWord_4275377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4275377).length < 2 ^ (prefixWord ++ tailWord_4275377).sum := by decide
  have hdescent : baseEnd_4275377 < baseStart_4275377 := by decide
  rcases family_descends (prefixWord ++ tailWord_4275377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4275457 : List Nat := [1, 2, 4, 1, 1, 3, 2, 1, 2, 1, 5]
def baseStart_4275457 : Nat := 118140960795 + 4275457 * 2 ^ 59
def prefixEnd_4275457 : Nat := 4983230072969 + 3 ^ 40 * 4275457 * 2
def baseEnd_4275457 : Nat := 2195364458629983988525037

theorem tailTrace_4275457 : CollatzResearch.WordTrace tailWord_4275457 prefixEnd_4275457 2195364458629983988525037 := by
  unfold tailWord_4275457
  simp only [CollatzResearch.WordTrace]
  refine ⟨155938727671756953767320625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103959151781171302511547083 155938727671756953767320625)
  ·
    refine ⟨116954045753817715325490469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155938727671756953767320625 116954045753817715325490469)
    ·
      refine ⟨21928883578840821623529463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 116954045753817715325490469 21928883578840821623529463)
      ·
        refine ⟨32893325368261232435294195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21928883578840821623529463 32893325368261232435294195)
        ·
          refine ⟨49339988052391848652941293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32893325368261232435294195 49339988052391848652941293)
          ·
            refine ⟨18502495519646943244852985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49339988052391848652941293 18502495519646943244852985)
            ·
              refine ⟨13876871639735207433639739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18502495519646943244852985 13876871639735207433639739)
              ·
                refine ⟨20815307459602811150459609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13876871639735207433639739 20815307459602811150459609)
                ·
                  refine ⟨15611480594702108362844707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20815307459602811150459609 15611480594702108362844707)
                  ·
                    refine ⟨23417220892053162544267061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15611480594702108362844707 23417220892053162544267061)
                    ·
                      refine ⟨2195364458629983988525037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23417220892053162544267061 2195364458629983988525037)
                      ·
                        rfl

theorem cell23_4275457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 1, 2, 1, 5].length) (baseStart_4275457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4275457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4275457 prefixEnd_4275457 := by exact prefixLift 4275457
  have htrace : WordTrace (prefixWord ++ tailWord_4275457) baseStart_4275457 baseEnd_4275457 := by
    simpa [prefixWord, tailWord_4275457, baseEnd_4275457] using wordTrace_append hprefix tailTrace_4275457
  have hstable : (prefixWord ++ tailWord_4275457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4275457).length < 2 ^ (prefixWord ++ tailWord_4275457).sum := by decide
  have hdescent : baseEnd_4275457 < baseStart_4275457 := by decide
  rcases family_descends (prefixWord ++ tailWord_4275457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4275507 : List Nat := [1, 1, 1, 2, 5, 3, 1, 1, 1, 7]
def baseStart_4275507 : Nat := 118140960795 + 4275507 * 2 ^ 59
def prefixEnd_4275507 : Nat := 4983230072969 + 3 ^ 40 * 4275507 * 2
def baseEnd_4275507 : Nat := 731796710887569597633269

theorem tailTrace_4275507 : CollatzResearch.WordTrace tailWord_4275507 prefixEnd_4275507 731796710887569597633269 := by
  unfold tailWord_4275507
  simp only [CollatzResearch.WordTrace]
  refine ⟨155940551321575812306640775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103960367547717208204427183 155940551321575812306640775)
  ·
    refine ⟨233910826982363718459961163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155940551321575812306640775 233910826982363718459961163)
    ·
      refine ⟨350866240473545577689941745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 233910826982363718459961163 350866240473545577689941745)
      ·
        refine ⟨263149680355159183267456309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 350866240473545577689941745 263149680355159183267456309)
        ·
          refine ⟨24670282533296173431324029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 263149680355159183267456309 24670282533296173431324029)
          ·
            refine ⟨9251355949986065036746511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24670282533296173431324029 9251355949986065036746511)
            ·
              refine ⟨13877033924979097555119767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9251355949986065036746511 13877033924979097555119767)
              ·
                refine ⟨20815550887468646332679651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13877033924979097555119767 20815550887468646332679651)
                ·
                  refine ⟨31223326331202969499019477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20815550887468646332679651 31223326331202969499019477)
                  ·
                    refine ⟨731796710887569597633269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31223326331202969499019477 731796710887569597633269)
                    ·
                      rfl

theorem cell23_4275507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 1, 1, 7].length) (baseStart_4275507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4275507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4275507 prefixEnd_4275507 := by exact prefixLift 4275507
  have htrace : WordTrace (prefixWord ++ tailWord_4275507) baseStart_4275507 baseEnd_4275507 := by
    simpa [prefixWord, tailWord_4275507, baseEnd_4275507] using wordTrace_append hprefix tailTrace_4275507
  have hstable : (prefixWord ++ tailWord_4275507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4275507).length < 2 ^ (prefixWord ++ tailWord_4275507).sum := by decide
  have hdescent : baseEnd_4275507 < baseStart_4275507 := by decide
  rcases family_descends (prefixWord ++ tailWord_4275507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
