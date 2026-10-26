import V185TrunkScan20Chunk079

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_487318 : List Nat := [5, 3, 1, 1, 10]
def baseStart_487318 : Nat := 118140960795 + 487318 * 2 ^ 59
def prefixEnd_487318 : Nat := 4983230072969 + 3 ^ 40 * 487318 * 2
def baseEnd_487318 : Nat := 2745990294516648557299

theorem tailTrace_487318 : CollatzResearch.WordTrace tailWord_487318 prefixEnd_487318 2745990294516648557299 := by
  unfold tailWord_487318
  simp only [CollatzResearch.WordTrace]
  refine ⟨1110871728033599258340413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11849298432358392088964405 1110871728033599258340413)
  ·
    refine ⟨416576898012599721877655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1110871728033599258340413 416576898012599721877655)
    ·
      refine ⟨624865347018899582816483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 416576898012599721877655 624865347018899582816483)
      ·
        refine ⟨937298020528349374224725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 624865347018899582816483 937298020528349374224725)
        ·
          refine ⟨2745990294516648557299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 937298020528349374224725 2745990294516648557299)
          ·
            rfl

theorem cell20_487318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 10].length) (baseStart_487318 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_487318 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_487318 prefixEnd_487318 := by exact prefixLift 487318
  have htrace : WordTrace (prefixWord ++ tailWord_487318) baseStart_487318 baseEnd_487318 := by
    simpa [prefixWord, tailWord_487318, baseEnd_487318] using wordTrace_append hprefix tailTrace_487318
  have hstable : (prefixWord ++ tailWord_487318).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487318).length < 2 ^ (prefixWord ++ tailWord_487318).sum := by decide
  have hdescent : baseEnd_487318 < baseStart_487318 := by decide
  rcases family_descends (prefixWord ++ tailWord_487318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487322 : List Nat := [3, 1, 1, 4, 2, 9]
def baseStart_487322 : Nat := 118140960795 + 487322 * 2 ^ 59
def prefixEnd_487322 : Nat := 4983230072969 + 3 ^ 40 * 487322 * 2
def baseEnd_487322 : Nat := 8238038502401566555847

theorem tailTrace_487322 : CollatzResearch.WordTrace tailWord_487322 prefixEnd_487322 8238038502401566555847 := by
  unfold tailWord_487322
  simp only [CollatzResearch.WordTrace]
  refine ⟨4443523385130774204148055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11849395693682064544394813 4443523385130774204148055)
  ·
    refine ⟨6665285077696161306222083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4443523385130774204148055 6665285077696161306222083)
    ·
      refine ⟨9997927616544241959333125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6665285077696161306222083 9997927616544241959333125)
      ·
        refine ⟨1874611428102045367374961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9997927616544241959333125 1874611428102045367374961)
        ·
          refine ⟨1405958571076534025531221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1874611428102045367374961 1405958571076534025531221)
          ·
            refine ⟨8238038502401566555847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1405958571076534025531221 8238038502401566555847)
            ·
              rfl

theorem cell20_487322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 9].length) (baseStart_487322 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_487322 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_487322 prefixEnd_487322 := by exact prefixLift 487322
  have htrace : WordTrace (prefixWord ++ tailWord_487322) baseStart_487322 baseEnd_487322 := by
    simpa [prefixWord, tailWord_487322, baseEnd_487322] using wordTrace_append hprefix tailTrace_487322
  have hstable : (prefixWord ++ tailWord_487322).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487322).length < 2 ^ (prefixWord ++ tailWord_487322).sum := by decide
  have hdescent : baseEnd_487322 < baseStart_487322 := by decide
  rcases family_descends (prefixWord ++ tailWord_487322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487325 : List Nat := [1, 4, 2, 1, 2, 3, 2, 2, 3]
def baseStart_487325 : Nat := 118140960795 + 487325 * 2 ^ 59
def prefixEnd_487325 : Nat := 4983230072969 + 3 ^ 40 * 487325 * 2
def baseEnd_487325 : Nat := 222428408846587619907857

theorem tailTrace_487325 : CollatzResearch.WordTrace tailWord_487325 prefixEnd_487325 222428408846587619907857 := by
  unfold tailWord_487325
  simp only [CollatzResearch.WordTrace]
  refine ⟨17774202959512228328951429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11849468639674818885967619 17774202959512228328951429)
  ·
    refine ⟨3332663054908542811678393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17774202959512228328951429 3332663054908542811678393)
    ·
      refine ⟨2499497291181407108758795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3332663054908542811678393 2499497291181407108758795)
      ·
        refine ⟨3749245936772110663138193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2499497291181407108758795 3749245936772110663138193)
        ·
          refine ⟨2811934452579082997353645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3749245936772110663138193 2811934452579082997353645)
          ·
            refine ⟨1054475419717156124007617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2811934452579082997353645 1054475419717156124007617)
            ·
              refine ⟨790856564787867093005713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1054475419717156124007617 790856564787867093005713)
              ·
                refine ⟨593142423590900319754285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 790856564787867093005713 593142423590900319754285)
                ·
                  refine ⟨222428408846587619907857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 593142423590900319754285 222428408846587619907857)
                  ·
                    rfl

theorem cell20_487325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 2, 2, 3].length) (baseStart_487325 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_487325 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_487325 prefixEnd_487325 := by exact prefixLift 487325
  have htrace : WordTrace (prefixWord ++ tailWord_487325) baseStart_487325 baseEnd_487325 := by
    simpa [prefixWord, tailWord_487325, baseEnd_487325] using wordTrace_append hprefix tailTrace_487325
  have hstable : (prefixWord ++ tailWord_487325).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487325).length < 2 ^ (prefixWord ++ tailWord_487325).sum := by decide
  have hdescent : baseEnd_487325 < baseStart_487325 := by decide
  rcases family_descends (prefixWord ++ tailWord_487325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487353 : List Nat := [1, 2, 1, 4, 2, 1, 3, 2, 4]
def baseStart_487353 : Nat := 118140960795 + 487353 * 2 ^ 59
def prefixEnd_487353 : Nat := 4983230072969 + 3 ^ 40 * 487353 * 2
def baseEnd_487353 : Nat := 222441188809543966974409

theorem tailTrace_487353 : CollatzResearch.WordTrace tailWord_487353 prefixEnd_487353 222441188809543966974409 := by
  unfold tailWord_487353
  simp only [CollatzResearch.WordTrace]
  refine ⟨17775224203410789110970713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11850149468940526073980475 17775224203410789110970713)
  ·
    refine ⟨13331418152558091833228035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17775224203410789110970713 13331418152558091833228035)
    ·
      refine ⟨19997127228837137749842053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13331418152558091833228035 19997127228837137749842053)
      ·
        refine ⟨3749461355406963328095385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19997127228837137749842053 3749461355406963328095385)
        ·
          refine ⟨2812096016555222496071539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3749461355406963328095385 2812096016555222496071539)
          ·
            refine ⟨4218144024832833744107309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2812096016555222496071539 4218144024832833744107309)
            ·
              refine ⟨1581804009312312654040241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4218144024832833744107309 1581804009312312654040241)
              ·
                refine ⟨1186353006984234490530181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1581804009312312654040241 1186353006984234490530181)
                ·
                  refine ⟨222441188809543966974409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1186353006984234490530181 222441188809543966974409)
                  ·
                    rfl

theorem cell20_487353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 2, 4].length) (baseStart_487353 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_487353 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_487353 prefixEnd_487353 := by exact prefixLift 487353
  have htrace : WordTrace (prefixWord ++ tailWord_487353) baseStart_487353 baseEnd_487353 := by
    simpa [prefixWord, tailWord_487353, baseEnd_487353] using wordTrace_append hprefix tailTrace_487353
  have hstable : (prefixWord ++ tailWord_487353).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487353).length < 2 ^ (prefixWord ++ tailWord_487353).sum := by decide
  have hdescent : baseEnd_487353 < baseStart_487353 := by decide
  rcases family_descends (prefixWord ++ tailWord_487353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487367 : List Nat := [1, 1, 4, 1, 1, 2, 1, 4, 5]
def baseStart_487367 : Nat := 118140960795 + 487367 * 2 ^ 59
def prefixEnd_487367 : Nat := 4983230072969 + 3 ^ 40 * 487367 * 2
def baseEnd_487367 : Nat := 222447578791022140507685

theorem tailTrace_487367 : CollatzResearch.WordTrace tailWord_487367 prefixEnd_487367 222447578791022140507685 := by
  unfold tailWord_487367
  simp only [CollatzResearch.WordTrace]
  refine ⟨17775734825360069501980355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11850489883573379667986903 17775734825360069501980355)
  ·
    refine ⟨26663602238040104252970533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17775734825360069501980355 26663602238040104252970533)
    ·
      refine ⟨4999425419632519547431975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26663602238040104252970533 4999425419632519547431975)
      ·
        refine ⟨7499138129448779321147963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4999425419632519547431975 7499138129448779321147963)
        ·
          refine ⟨11248707194173168981721945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7499138129448779321147963 11248707194173168981721945)
          ·
            refine ⟨8436530395629876736291459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11248707194173168981721945 8436530395629876736291459)
            ·
              refine ⟨12654795593444815104437189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8436530395629876736291459 12654795593444815104437189)
              ·
                refine ⟨2372774173770902832081973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12654795593444815104437189 2372774173770902832081973)
                ·
                  refine ⟨222447578791022140507685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2372774173770902832081973 222447578791022140507685)
                  ·
                    rfl

theorem cell20_487367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 4, 5].length) (baseStart_487367 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_487367 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_487367 prefixEnd_487367 := by exact prefixLift 487367
  have htrace : WordTrace (prefixWord ++ tailWord_487367) baseStart_487367 baseEnd_487367 := by
    simpa [prefixWord, tailWord_487367, baseEnd_487367] using wordTrace_append hprefix tailTrace_487367
  have hstable : (prefixWord ++ tailWord_487367).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487367).length < 2 ^ (prefixWord ++ tailWord_487367).sum := by decide
  have hdescent : baseEnd_487367 < baseStart_487367 := by decide
  rcases family_descends (prefixWord ++ tailWord_487367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487370 : List Nat := [3, 1, 2, 1, 2, 1, 3, 5, 2]
def baseStart_487370 : Nat := 118140960795 + 487370 * 2 ^ 59
def prefixEnd_487370 : Nat := 4983230072969 + 3 ^ 40 * 487370 * 2
def baseEnd_487370 : Nat := 222448948072767463407673

theorem tailTrace_487370 : CollatzResearch.WordTrace tailWord_487370 prefixEnd_487370 222448948072767463407673 := by
  unfold tailWord_487370
  simp only [CollatzResearch.WordTrace]
  refine ⟨4443961061087300253584891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11850562829566134009559709 4443961061087300253584891)
  ·
    refine ⟨6665941591630950380377337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4443961061087300253584891 6665941591630950380377337)
    ·
      refine ⟨4999456193723212785283003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6665941591630950380377337 4999456193723212785283003)
      ·
        refine ⟨7499184290584819177924505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4999456193723212785283003 7499184290584819177924505)
        ·
          refine ⟨5624388217938614383443379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7499184290584819177924505 5624388217938614383443379)
          ·
            refine ⟨8436582326907921575165069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5624388217938614383443379 8436582326907921575165069)
            ·
              refine ⟨3163718372590470590686901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8436582326907921575165069 3163718372590470590686901)
              ·
                refine ⟨296598597430356617876897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3163718372590470590686901 296598597430356617876897)
                ·
                  refine ⟨222448948072767463407673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 296598597430356617876897 222448948072767463407673)
                  ·
                    rfl

theorem cell20_487370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 5, 2].length) (baseStart_487370 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_487370 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_487370 prefixEnd_487370 := by exact prefixLift 487370
  have htrace : WordTrace (prefixWord ++ tailWord_487370) baseStart_487370 baseEnd_487370 := by
    simpa [prefixWord, tailWord_487370, baseEnd_487370] using wordTrace_append hprefix tailTrace_487370
  have hstable : (prefixWord ++ tailWord_487370).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487370).length < 2 ^ (prefixWord ++ tailWord_487370).sum := by decide
  have hdescent : baseEnd_487370 < baseStart_487370 := by decide
  rcases family_descends (prefixWord ++ tailWord_487370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487391 : List Nat := [1, 1, 2, 3, 4, 1, 1, 3, 4]
def baseStart_487391 : Nat := 118140960795 + 487391 * 2 ^ 59
def prefixEnd_487391 : Nat := 4983230072969 + 3 ^ 40 * 487391 * 2
def baseEnd_487391 : Nat := 222458533044984723707587

theorem tailTrace_487391 : CollatzResearch.WordTrace tailWord_487391 prefixEnd_487391 222458533044984723707587 := by
  unfold tailWord_487391
  simp only [CollatzResearch.WordTrace]
  refine ⟨17776610177273121600854027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11851073451515414400569351 17776610177273121600854027)
  ·
    refine ⟨26664915265909682401281041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17776610177273121600854027 26664915265909682401281041)
    ·
      refine ⟨19998686449432261800960781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26664915265909682401281041 19998686449432261800960781)
      ·
        refine ⟨7499507418537098175360293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19998686449432261800960781 7499507418537098175360293)
        ·
          refine ⟨1406157640975705907880055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7499507418537098175360293 1406157640975705907880055)
          ·
            refine ⟨2109236461463558861820083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1406157640975705907880055 2109236461463558861820083)
            ·
              refine ⟨3163854692195338292730125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2109236461463558861820083 3163854692195338292730125)
              ·
                refine ⟨1186445509573251859773797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3163854692195338292730125 1186445509573251859773797)
                ·
                  refine ⟨222458533044984723707587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1186445509573251859773797 222458533044984723707587)
                  ·
                    rfl

theorem cell20_487391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 3, 4].length) (baseStart_487391 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_487391 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_487391 prefixEnd_487391 := by exact prefixLift 487391
  have htrace : WordTrace (prefixWord ++ tailWord_487391) baseStart_487391 baseEnd_487391 := by
    simpa [prefixWord, tailWord_487391, baseEnd_487391] using wordTrace_append hprefix tailTrace_487391
  have hstable : (prefixWord ++ tailWord_487391).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487391).length < 2 ^ (prefixWord ++ tailWord_487391).sum := by decide
  have hdescent : baseEnd_487391 < baseStart_487391 := by decide
  rcases family_descends (prefixWord ++ tailWord_487391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487443 : List Nat := [1, 1, 1, 2, 1, 4, 4, 1, 5]
def baseStart_487443 : Nat := 118140960795 + 487443 * 2 ^ 59
def prefixEnd_487443 : Nat := 4983230072969 + 3 ^ 40 * 487443 * 2
def baseEnd_487443 : Nat := 222482267261903653974041

theorem tailTrace_487443 : CollatzResearch.WordTrace tailWord_487443 prefixEnd_487443 222482267261903653974041 := by
  unfold tailWord_487443
  simp only [CollatzResearch.WordTrace]
  refine ⟨17778506773084734481746983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11852337848723156321164655 17778506773084734481746983)
  ·
    refine ⟨26667760159627101722620475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17778506773084734481746983 26667760159627101722620475)
    ·
      refine ⟨40001640239440652583930713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26667760159627101722620475 40001640239440652583930713)
      ·
        refine ⟨30001230179580489437948035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40001640239440652583930713 30001230179580489437948035)
        ·
          refine ⟨45001845269370734156922053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30001230179580489437948035 45001845269370734156922053)
          ·
            refine ⟨8437845988007012654422885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45001845269370734156922053 8437845988007012654422885)
            ·
              refine ⟨1582096122751314872704291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8437845988007012654422885 1582096122751314872704291)
              ·
                refine ⟨2373144184126972309056437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1582096122751314872704291 2373144184126972309056437)
                ·
                  refine ⟨222482267261903653974041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2373144184126972309056437 222482267261903653974041)
                  ·
                    rfl

theorem cell20_487443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 1, 5].length) (baseStart_487443 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_487443 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_487443 prefixEnd_487443 := by exact prefixLift 487443
  have htrace : WordTrace (prefixWord ++ tailWord_487443) baseStart_487443 baseEnd_487443 := by
    simpa [prefixWord, tailWord_487443, baseEnd_487443] using wordTrace_append hprefix tailTrace_487443
  have hstable : (prefixWord ++ tailWord_487443).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487443).length < 2 ^ (prefixWord ++ tailWord_487443).sum := by decide
  have hdescent : baseEnd_487443 < baseStart_487443 := by decide
  rcases family_descends (prefixWord ++ tailWord_487443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487453 : List Nat := [1, 4, 2, 2, 2, 2, 2, 5]
def baseStart_487453 : Nat := 118140960795 + 487453 * 2 ^ 59
def prefixEnd_487453 : Nat := 4983230072969 + 3 ^ 40 * 487453 * 2
def baseEnd_487453 : Nat := 74162277178129354546889

theorem tailTrace_487453 : CollatzResearch.WordTrace tailWord_487453 prefixEnd_487453 74162277178129354546889 := by
  unfold tailWord_487453
  simp only [CollatzResearch.WordTrace]
  refine ⟨17778871503048506189611013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11852581002032337459740675 17778871503048506189611013)
  ·
    refine ⟨3333538406821594910552065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17778871503048506189611013 3333538406821594910552065)
    ·
      refine ⟨2500153805116196182914049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3333538406821594910552065 2500153805116196182914049)
      ·
        refine ⟨1875115353837147137185537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2500153805116196182914049 1875115353837147137185537)
        ·
          refine ⟨1406336515377860352889153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1875115353837147137185537 1406336515377860352889153)
          ·
            refine ⟨1054752386533395264666865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1406336515377860352889153 1054752386533395264666865)
            ·
              refine ⟨791064289900046448500149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1054752386533395264666865 791064289900046448500149)
              ·
                refine ⟨74162277178129354546889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 791064289900046448500149 74162277178129354546889)
                ·
                  rfl

theorem cell20_487453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 2, 5].length) (baseStart_487453 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_487453 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_487453 prefixEnd_487453 := by exact prefixLift 487453
  have htrace : WordTrace (prefixWord ++ tailWord_487453) baseStart_487453 baseEnd_487453 := by
    simpa [prefixWord, tailWord_487453, baseEnd_487453] using wordTrace_append hprefix tailTrace_487453
  have hstable : (prefixWord ++ tailWord_487453).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487453).length < 2 ^ (prefixWord ++ tailWord_487453).sum := by decide
  have hdescent : baseEnd_487453 < baseStart_487453 := by decide
  rcases family_descends (prefixWord ++ tailWord_487453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487474 : List Nat := [3, 2, 1, 1, 2, 3, 2, 6]
def baseStart_487474 : Nat := 118140960795 + 487474 * 2 ^ 59
def prefixEnd_487474 : Nat := 4983230072969 + 3 ^ 40 * 487474 * 2
def baseEnd_487474 : Nat := 74165472168868441313527

theorem tailTrace_487474 : CollatzResearch.WordTrace tailWord_487474 prefixEnd_487474 74165472168868441313527 := by
  unfold tailWord_487474
  simp only [CollatzResearch.WordTrace]
  refine ⟨4444909358993106694031369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11853091623981617850750317 4444909358993106694031369)
  ·
    refine ⟨3333682019244830020523527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4444909358993106694031369 3333682019244830020523527)
    ·
      refine ⟨5000523028867245030785291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3333682019244830020523527 5000523028867245030785291)
      ·
        refine ⟨7500784543300867546177937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5000523028867245030785291 7500784543300867546177937)
        ·
          refine ⟨5625588407475650659633453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7500784543300867546177937 5625588407475650659633453)
          ·
            refine ⟨2109595652803368997362545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5625588407475650659633453 2109595652803368997362545)
            ·
              refine ⟨1582196739602526748021909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2109595652803368997362545 1582196739602526748021909)
              ·
                refine ⟨74165472168868441313527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1582196739602526748021909 74165472168868441313527)
                ·
                  rfl

theorem cell20_487474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 6].length) (baseStart_487474 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_487474 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_487474 prefixEnd_487474 := by exact prefixLift 487474
  have htrace : WordTrace (prefixWord ++ tailWord_487474) baseStart_487474 baseEnd_487474 := by
    simpa [prefixWord, tailWord_487474, baseEnd_487474] using wordTrace_append hprefix tailTrace_487474
  have hstable : (prefixWord ++ tailWord_487474).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487474).length < 2 ^ (prefixWord ++ tailWord_487474).sum := by decide
  have hdescent : baseEnd_487474 < baseStart_487474 := by decide
  rcases family_descends (prefixWord ++ tailWord_487474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487484 : List Nat := [2, 2, 2, 2, 2, 1, 2, 5, 2]
def baseStart_487484 : Nat := 118140960795 + 487484 * 2 ^ 59
def prefixEnd_487484 : Nat := 4983230072969 + 3 ^ 40 * 487484 * 2
def baseEnd_487484 : Nat := 222500980779089733607207

theorem tailTrace_487484 : CollatzResearch.WordTrace tailWord_487484 prefixEnd_487484 222500980779089733607207 := by
  unfold tailWord_487484
  simp only [CollatzResearch.WordTrace]
  refine ⟨8890001082968099241994753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11853334777290798989326337 8890001082968099241994753)
  ·
    refine ⟨6667500812226074431496065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8890001082968099241994753 6667500812226074431496065)
    ·
      refine ⟨5000625609169555823622049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6667500812226074431496065 5000625609169555823622049)
      ·
        refine ⟨3750469206877166867716537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5000625609169555823622049 3750469206877166867716537)
        ·
          refine ⟨2812851905157875150787403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3750469206877166867716537 2812851905157875150787403)
          ·
            refine ⟨4219277857736812726181105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2812851905157875150787403 4219277857736812726181105)
            ·
              refine ⟨3164458393302609544635829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4219277857736812726181105 3164458393302609544635829)
              ·
                refine ⟨296667974372119644809609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3164458393302609544635829 296667974372119644809609)
                ·
                  refine ⟨222500980779089733607207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 296667974372119644809609 222500980779089733607207)
                  ·
                    rfl

theorem cell20_487484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 5, 2].length) (baseStart_487484 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_487484 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_487484 prefixEnd_487484 := by exact prefixLift 487484
  have htrace : WordTrace (prefixWord ++ tailWord_487484) baseStart_487484 baseEnd_487484 := by
    simpa [prefixWord, tailWord_487484, baseEnd_487484] using wordTrace_append hprefix tailTrace_487484
  have hstable : (prefixWord ++ tailWord_487484).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487484).length < 2 ^ (prefixWord ++ tailWord_487484).sum := by decide
  have hdescent : baseEnd_487484 < baseStart_487484 := by decide
  rcases family_descends (prefixWord ++ tailWord_487484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487494 : List Nat := [6, 1, 1, 1, 1, 1, 4, 2, 3]
def baseStart_487494 : Nat := 118140960795 + 487494 * 2 ^ 59
def prefixEnd_487494 : Nat := 4983230072969 + 3 ^ 40 * 487494 * 2
def baseEnd_487494 : Nat := 222505545051574143273833

theorem tailTrace_487494 : CollatzResearch.WordTrace tailWord_487494 prefixEnd_487494 222505545051574143273833 := by
  unfold tailWord_487494
  simp only [CollatzResearch.WordTrace]
  refine ⟨555636465496874068495423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 11853577930599980127902357 555636465496874068495423)
  ·
    refine ⟨833454698245311102743135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 555636465496874068495423 833454698245311102743135)
    ·
      refine ⟨1250182047367966654114703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 833454698245311102743135 1250182047367966654114703)
      ·
        refine ⟨1875273071051949981172055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1250182047367966654114703 1875273071051949981172055)
        ·
          refine ⟨2812909606577924971758083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1875273071051949981172055 2812909606577924971758083)
          ·
            refine ⟨4219364409866887457637125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2812909606577924971758083 4219364409866887457637125)
            ·
              refine ⟨791130826850041398306961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4219364409866887457637125 791130826850041398306961)
              ·
                refine ⟨593348120137531048730221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 791130826850041398306961 593348120137531048730221)
                ·
                  refine ⟨222505545051574143273833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 593348120137531048730221 222505545051574143273833)
                  ·
                    rfl

theorem cell20_487494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 4, 2, 3].length) (baseStart_487494 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_487494 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_487494 prefixEnd_487494 := by exact prefixLift 487494
  have htrace : WordTrace (prefixWord ++ tailWord_487494) baseStart_487494 baseEnd_487494 := by
    simpa [prefixWord, tailWord_487494, baseEnd_487494] using wordTrace_append hprefix tailTrace_487494
  have hstable : (prefixWord ++ tailWord_487494).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487494).length < 2 ^ (prefixWord ++ tailWord_487494).sum := by decide
  have hdescent : baseEnd_487494 < baseStart_487494 := by decide
  rcases family_descends (prefixWord ++ tailWord_487494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487501 : List Nat := [1, 6, 1, 1, 1, 1, 3, 4, 2]
def baseStart_487501 : Nat := 118140960795 + 487501 * 2 ^ 59
def prefixEnd_487501 : Nat := 4983230072969 + 3 ^ 40 * 487501 * 2
def baseEnd_487501 : Nat := 222508740042313230040471

theorem tailTrace_487501 : CollatzResearch.WordTrace tailWord_487501 prefixEnd_487501 222508740042313230040471 := by
  unfold tailWord_487501
  simp only [CollatzResearch.WordTrace]
  refine ⟨17780622206874610387358357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11853748137916406924905571 17780622206874610387358357)
  ·
    refine ⟨833466665947247361907423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 17780622206874610387358357 833466665947247361907423)
    ·
      refine ⟨1250199998920871042861135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 833466665947247361907423 1250199998920871042861135)
      ·
        refine ⟨1875299998381306564291703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1250199998920871042861135 1875299998381306564291703)
        ·
          refine ⟨2812949997571959846437555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1875299998381306564291703 2812949997571959846437555)
          ·
            refine ⟨4219424996357939769656333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2812949997571959846437555 4219424996357939769656333)
            ·
              refine ⟨1582284373634227413621125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4219424996357939769656333 1582284373634227413621125)
              ·
                refine ⟨296678320056417640053961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1582284373634227413621125 296678320056417640053961)
                ·
                  refine ⟨222508740042313230040471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 296678320056417640053961 222508740042313230040471)
                  ·
                    rfl

theorem cell20_487501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 4, 2].length) (baseStart_487501 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_487501 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_487501 prefixEnd_487501 := by exact prefixLift 487501
  have htrace : WordTrace (prefixWord ++ tailWord_487501) baseStart_487501 baseEnd_487501 := by
    simpa [prefixWord, tailWord_487501, baseEnd_487501] using wordTrace_append hprefix tailTrace_487501
  have hstable : (prefixWord ++ tailWord_487501).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487501).length < 2 ^ (prefixWord ++ tailWord_487501).sum := by decide
  have hdescent : baseEnd_487501 < baseStart_487501 := by decide
  rcases family_descends (prefixWord ++ tailWord_487501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487512 : List Nat := [2, 1, 2, 2, 1, 4, 3, 5]
def baseStart_487512 : Nat := 118140960795 + 487512 * 2 ^ 59
def prefixEnd_487512 : Nat := 4983230072969 + 3 ^ 40 * 487512 * 2
def baseEnd_487512 : Nat := 74171253580682026891253

theorem tailTrace_487512 : CollatzResearch.WordTrace tailWord_487512 prefixEnd_487512 74171253580682026891253 := by
  unfold tailWord_487512
  simp only [CollatzResearch.WordTrace]
  refine ⟨8890511704917379633004395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11854015606556506177339193 8890511704917379633004395)
  ·
    refine ⟨13335767557376069449506593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8890511704917379633004395 13335767557376069449506593)
    ·
      refine ⟨10001825668032052087129945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13335767557376069449506593 10001825668032052087129945)
      ·
        refine ⟨7501369251024039065347459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10001825668032052087129945 7501369251024039065347459)
        ·
          refine ⟨11252053876536058598021189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7501369251024039065347459 11252053876536058598021189)
          ·
            refine ⟨2109760101850510987128973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11252053876536058598021189 2109760101850510987128973)
            ·
              refine ⟨791160038193941620173365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2109760101850510987128973 791160038193941620173365)
              ·
                refine ⟨74171253580682026891253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 791160038193941620173365 74171253580682026891253)
                ·
                  rfl

theorem cell20_487512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 3, 5].length) (baseStart_487512 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_487512 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_487512 prefixEnd_487512 := by exact prefixLift 487512
  have htrace : WordTrace (prefixWord ++ tailWord_487512) baseStart_487512 baseEnd_487512 := by
    simpa [prefixWord, tailWord_487512, baseEnd_487512] using wordTrace_append hprefix tailTrace_487512
  have hstable : (prefixWord ++ tailWord_487512).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487512).length < 2 ^ (prefixWord ++ tailWord_487512).sum := by decide
  have hdescent : baseEnd_487512 < baseStart_487512 := by decide
  rcases family_descends (prefixWord ++ tailWord_487512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487518 : List Nat := [4, 4, 1, 1, 2, 1, 1, 2, 4]
def baseStart_487518 : Nat := 118140960795 + 487518 * 2 ^ 59
def prefixEnd_487518 : Nat := 4983230072969 + 3 ^ 40 * 487518 * 2
def baseEnd_487518 : Nat := 222516499305536726473735

theorem tailTrace_487518 : CollatzResearch.WordTrace tailWord_487518 prefixEnd_487518 222516499305536726473735 := by
  unfold tailWord_487518
  simp only [CollatzResearch.WordTrace]
  refine ⟨2222655280976627786340901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11854161498542014860484805 2222655280976627786340901)
  ·
    refine ⟨416747865183117709938919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2222655280976627786340901 416747865183117709938919)
    ·
      refine ⟨625121797774676564908379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 416747865183117709938919 625121797774676564908379)
      ·
        refine ⟨937682696662014847362569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 625121797774676564908379 937682696662014847362569)
        ·
          refine ⟨703262022496511135521927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 937682696662014847362569 703262022496511135521927)
          ·
            refine ⟨1054893033744766703282891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 703262022496511135521927 1054893033744766703282891)
            ·
              refine ⟨1582339550617150054924337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1054893033744766703282891 1582339550617150054924337)
              ·
                refine ⟨1186754662962862541193253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1582339550617150054924337 1186754662962862541193253)
                ·
                  refine ⟨222516499305536726473735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1186754662962862541193253 222516499305536726473735)
                  ·
                    rfl

theorem cell20_487518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_487518 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_487518 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_487518 prefixEnd_487518 := by exact prefixLift 487518
  have htrace : WordTrace (prefixWord ++ tailWord_487518) baseStart_487518 baseEnd_487518 := by
    simpa [prefixWord, tailWord_487518, baseEnd_487518] using wordTrace_append hprefix tailTrace_487518
  have hstable : (prefixWord ++ tailWord_487518).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487518).length < 2 ^ (prefixWord ++ tailWord_487518).sum := by decide
  have hdescent : baseEnd_487518 < baseStart_487518 := by decide
  rcases family_descends (prefixWord ++ tailWord_487518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487560 : List Nat := [2, 1, 3, 4, 1, 2, 2, 1, 4]
def baseStart_487560 : Nat := 118140960795 + 487560 * 2 ^ 59
def prefixEnd_487560 : Nat := 4983230072969 + 3 ^ 40 * 487560 * 2
def baseEnd_487560 : Nat := 222535669249971247073563

theorem tailTrace_487560 : CollatzResearch.WordTrace tailWord_487560 prefixEnd_487560 222535669249971247073563 := by
  unfold tailWord_487560
  simp only [CollatzResearch.WordTrace]
  refine ⟨8891387056830431731878067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11855182742440575642504089 8891387056830431731878067)
  ·
    refine ⟨13337080585245647597817101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8891387056830431731878067 13337080585245647597817101)
    ·
      refine ⟨5001405219467117849181413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13337080585245647597817101 5001405219467117849181413)
      ·
        refine ⟨937763478650084596721515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5001405219467117849181413 937763478650084596721515)
        ·
          refine ⟨1406645217975126895082273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 937763478650084596721515 1406645217975126895082273)
          ·
            refine ⟨1054983913481345171311705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1406645217975126895082273 1054983913481345171311705)
            ·
              refine ⟨791237935111008878483779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1054983913481345171311705 791237935111008878483779)
              ·
                refine ⟨1186856902666513317725669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 791237935111008878483779 1186856902666513317725669)
                ·
                  refine ⟨222535669249971247073563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1186856902666513317725669 222535669249971247073563)
                  ·
                    rfl

theorem cell20_487560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 2, 1, 4].length) (baseStart_487560 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_487560 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_487560 prefixEnd_487560 := by exact prefixLift 487560
  have htrace : WordTrace (prefixWord ++ tailWord_487560) baseStart_487560 baseEnd_487560 := by
    simpa [prefixWord, tailWord_487560, baseEnd_487560] using wordTrace_append hprefix tailTrace_487560
  have hstable : (prefixWord ++ tailWord_487560).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487560).length < 2 ^ (prefixWord ++ tailWord_487560).sum := by decide
  have hdescent : baseEnd_487560 < baseStart_487560 := by decide
  rcases family_descends (prefixWord ++ tailWord_487560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487571 : List Nat := [1, 1, 1, 2, 1, 2, 3, 9]
def baseStart_487571 : Nat := 118140960795 + 487571 * 2 ^ 59
def prefixEnd_487571 : Nat := 4983230072969 + 3 ^ 40 * 487571 * 2
def baseEnd_487571 : Nat := 74180229983234699235617

theorem tailTrace_487571 : CollatzResearch.WordTrace tailWord_487571 prefixEnd_487571 74180229983234699235617 := by
  unfold tailWord_487571
  simp only [CollatzResearch.WordTrace]
  refine ⟨17783175316621012342406567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11855450211080674894937711 17783175316621012342406567)
  ·
    refine ⟨26674762974931518513609851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17783175316621012342406567 26674762974931518513609851)
    ·
      refine ⟨40012144462397277770414777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26674762974931518513609851 40012144462397277770414777)
      ·
        refine ⟨30009108346797958327811083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40012144462397277770414777 30009108346797958327811083)
        ·
          refine ⟨45013662520196937491716625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30009108346797958327811083 45013662520196937491716625)
          ·
            refine ⟨33760246890147703118787469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45013662520196937491716625 33760246890147703118787469)
            ·
              refine ⟨12660092583805388669545301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33760246890147703118787469 12660092583805388669545301)
              ·
                refine ⟨74180229983234699235617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12660092583805388669545301 74180229983234699235617)
                ·
                  rfl

theorem cell20_487571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 9].length) (baseStart_487571 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_487571 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_487571 prefixEnd_487571 := by exact prefixLift 487571
  have htrace : WordTrace (prefixWord ++ tailWord_487571) baseStart_487571 baseEnd_487571 := by
    simpa [prefixWord, tailWord_487571, baseEnd_487571] using wordTrace_append hprefix tailTrace_487571
  have hstable : (prefixWord ++ tailWord_487571).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487571).length < 2 ^ (prefixWord ++ tailWord_487571).sum := by decide
  have hdescent : baseEnd_487571 < baseStart_487571 := by decide
  rcases family_descends (prefixWord ++ tailWord_487571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487581 : List Nat := [1, 4, 2, 1, 1, 3, 2, 2, 4]
def baseStart_487581 : Nat := 118140960795 + 487581 * 2 ^ 59
def prefixEnd_487581 : Nat := 4983230072969 + 3 ^ 40 * 487581 * 2
def baseEnd_487581 : Nat := 222545254222188507373477

theorem tailTrace_487581 : CollatzResearch.WordTrace tailWord_487581 prefixEnd_487581 222545254222188507373477 := by
  unfold tailWord_487581
  simp only [CollatzResearch.WordTrace]
  refine ⟨17783540046584784050270597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11855693364389856033513731 17783540046584784050270597)
  ·
    refine ⟨3334413758734647009425737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17783540046584784050270597 3334413758734647009425737)
    ·
      refine ⟨2500810319050985257069303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3334413758734647009425737 2500810319050985257069303)
      ·
        refine ⟨3751215478576477885603955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2500810319050985257069303 3751215478576477885603955)
        ·
          refine ⟨5626823217864716828405933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3751215478576477885603955 5626823217864716828405933)
          ·
            refine ⟨2110058706699268810652225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5626823217864716828405933 2110058706699268810652225)
            ·
              refine ⟨1582544030024451607989169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2110058706699268810652225 1582544030024451607989169)
              ·
                refine ⟨1186908022518338705991877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1582544030024451607989169 1186908022518338705991877)
                ·
                  refine ⟨222545254222188507373477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1186908022518338705991877 222545254222188507373477)
                  ·
                    rfl

theorem cell20_487581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 2, 4].length) (baseStart_487581 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_487581 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_487581 prefixEnd_487581 := by exact prefixLift 487581
  have htrace : WordTrace (prefixWord ++ tailWord_487581) baseStart_487581 baseEnd_487581 := by
    simpa [prefixWord, tailWord_487581, baseEnd_487581] using wordTrace_append hprefix tailTrace_487581
  have hstable : (prefixWord ++ tailWord_487581).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487581).length < 2 ^ (prefixWord ++ tailWord_487581).sum := by decide
  have hdescent : baseEnd_487581 < baseStart_487581 := by decide
  rcases family_descends (prefixWord ++ tailWord_487581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487626 : List Nat := [3, 1, 2, 1, 3, 1, 4, 5]
def baseStart_487626 : Nat := 118140960795 + 487626 * 2 ^ 59
def prefixEnd_487626 : Nat := 4983230072969 + 3 ^ 40 * 487626 * 2
def baseEnd_487626 : Nat := 74188597816122783624431

theorem tailTrace_487626 : CollatzResearch.WordTrace tailWord_487626 prefixEnd_487626 74188597816122783624431 := by
  unfold tailWord_487626
  simp only [CollatzResearch.WordTrace]
  refine ⟨4446295332855439183914683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11856787554281171157105821 4446295332855439183914683)
  ·
    refine ⟨6669442999283158775872025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4446295332855439183914683 6669442999283158775872025)
    ·
      refine ⟨5002082249462369081904019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6669442999283158775872025 5002082249462369081904019)
      ·
        refine ⟨7503123374193553622856029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5002082249462369081904019 7503123374193553622856029)
        ·
          refine ⟨2813671265322582608571011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7503123374193553622856029 2813671265322582608571011)
          ·
            refine ⟨4220506897983873912856517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2813671265322582608571011 4220506897983873912856517)
            ·
              refine ⟨791345043371976358660597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4220506897983873912856517 791345043371976358660597)
              ·
                refine ⟨74188597816122783624431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 791345043371976358660597 74188597816122783624431)
                ·
                  rfl

theorem cell20_487626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 4, 5].length) (baseStart_487626 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_487626 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_487626 prefixEnd_487626 := by exact prefixLift 487626
  have htrace : WordTrace (prefixWord ++ tailWord_487626) baseStart_487626 baseEnd_487626 := by
    simpa [prefixWord, tailWord_487626, baseEnd_487626] using wordTrace_append hprefix tailTrace_487626
  have hstable : (prefixWord ++ tailWord_487626).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487626).length < 2 ^ (prefixWord ++ tailWord_487626).sum := by decide
  have hdescent : baseEnd_487626 < baseStart_487626 := by decide
  rcases family_descends (prefixWord ++ tailWord_487626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487674 : List Nat := [3, 1, 1, 1, 1, 6, 1, 4, 2]
def baseStart_487674 : Nat := 118140960795 + 487674 * 2 ^ 59
def prefixEnd_487674 : Nat := 4983230072969 + 3 ^ 40 * 487674 * 2
def baseEnd_487674 : Nat := 222587701956293517273097

theorem tailTrace_487674 : CollatzResearch.WordTrace tailWord_487674 prefixEnd_487674 222587701956293517273097 := by
  unfold tailWord_487674
  simp only [CollatzResearch.WordTrace]
  refine ⟨4446733008811965233351519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11857954690165240622270717 4446733008811965233351519)
  ·
    refine ⟨6670099513217947850027279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4446733008811965233351519 6670099513217947850027279)
    ·
      refine ⟨10005149269826921775040919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6670099513217947850027279 10005149269826921775040919)
      ·
        refine ⟨15007723904740382662561379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10005149269826921775040919 15007723904740382662561379)
        ·
          refine ⟨22511585857110573993842069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15007723904740382662561379 22511585857110573993842069)
          ·
            refine ⟨1055230587052058155961347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 22511585857110573993842069 1055230587052058155961347)
            ·
              refine ⟨1582845880578087233942021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1055230587052058155961347 1582845880578087233942021)
              ·
                refine ⟨296783602608391356364129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1582845880578087233942021 296783602608391356364129)
                ·
                  refine ⟨222587701956293517273097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 296783602608391356364129 222587701956293517273097)
                  ·
                    rfl

theorem cell20_487674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 4, 2].length) (baseStart_487674 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_487674 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_487674 prefixEnd_487674 := by exact prefixLift 487674
  have htrace : WordTrace (prefixWord ++ tailWord_487674) baseStart_487674 baseEnd_487674 := by
    simpa [prefixWord, tailWord_487674, baseEnd_487674] using wordTrace_append hprefix tailTrace_487674
  have hstable : (prefixWord ++ tailWord_487674).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487674).length < 2 ^ (prefixWord ++ tailWord_487674).sum := by decide
  have hdescent : baseEnd_487674 < baseStart_487674 := by decide
  rcases family_descends (prefixWord ++ tailWord_487674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487685 : List Nat := [1, 3, 1, 1, 2, 1, 2, 9]
def baseStart_487685 : Nat := 118140960795 + 487685 * 2 ^ 59
def prefixEnd_487685 : Nat := 4983230072969 + 3 ^ 40 * 487685 * 2
def baseEnd_487685 : Nat := 74197574218675455968795

theorem tailTrace_487685 : CollatzResearch.WordTrace tailWord_487685 prefixEnd_487685 74197574218675455968795 := by
  unfold tailWord_487685
  simp only [CollatzResearch.WordTrace]
  refine ⟨17787333238208009812056509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11858222158805339874704339 17787333238208009812056509)
  ·
    refine ⟨6670249964328003679521191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17787333238208009812056509 6670249964328003679521191)
    ·
      refine ⟨10005374946492005519281787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6670249964328003679521191 10005374946492005519281787)
      ·
        refine ⟨15008062419738008278922681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10005374946492005519281787 15008062419738008278922681)
        ·
          refine ⟨11256046814803506209192011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15008062419738008278922681 11256046814803506209192011)
          ·
            refine ⟨16884070222205259313788017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11256046814803506209192011 16884070222205259313788017)
            ·
              refine ⟨12663052666653944485341013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16884070222205259313788017 12663052666653944485341013)
              ·
                refine ⟨74197574218675455968795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12663052666653944485341013 74197574218675455968795)
                ·
                  rfl

theorem cell20_487685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 9].length) (baseStart_487685 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_487685 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_487685 prefixEnd_487685 := by exact prefixLift 487685
  have htrace : WordTrace (prefixWord ++ tailWord_487685) baseStart_487685 baseEnd_487685 := by
    simpa [prefixWord, tailWord_487685, baseEnd_487685] using wordTrace_append hprefix tailTrace_487685
  have hstable : (prefixWord ++ tailWord_487685).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487685).length < 2 ^ (prefixWord ++ tailWord_487685).sum := by decide
  have hdescent : baseEnd_487685 < baseStart_487685 := by decide
  rcases family_descends (prefixWord ++ tailWord_487685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487688 : List Nat := [2, 1, 3, 2, 3, 1, 2, 3, 3]
def baseStart_487688 : Nat := 118140960795 + 487688 * 2 ^ 59
def prefixEnd_487688 : Nat := 4983230072969 + 3 ^ 40 * 487688 * 2
def baseEnd_487688 : Nat := 222594091937771690806373

theorem tailTrace_487688 : CollatzResearch.WordTrace tailWord_487688 prefixEnd_487688 222594091937771690806373 := by
  unfold tailWord_487688
  simp only [CollatzResearch.WordTrace]
  refine ⟨8893721328598570662207859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11858295104798094216277145 8893721328598570662207859)
  ·
    refine ⟨13340581992897855993311789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8893721328598570662207859 13340581992897855993311789)
    ·
      refine ⟨5002718247336695997491921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13340581992897855993311789 5002718247336695997491921)
      ·
        refine ⟨3752038685502521998118941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5002718247336695997491921 3752038685502521998118941)
        ·
          refine ⟨1407014507063445749294603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3752038685502521998118941 1407014507063445749294603)
          ·
            refine ⟨2110521760595168623941905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1407014507063445749294603 2110521760595168623941905)
            ·
              refine ⟨1582891320446376467956429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2110521760595168623941905 1582891320446376467956429)
              ·
                refine ⟨593584245167391175483661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1582891320446376467956429 593584245167391175483661)
                ·
                  refine ⟨222594091937771690806373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 593584245167391175483661 222594091937771690806373)
                  ·
                    rfl

theorem cell20_487688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 3, 3].length) (baseStart_487688 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_487688 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_487688 prefixEnd_487688 := by exact prefixLift 487688
  have htrace : WordTrace (prefixWord ++ tailWord_487688) baseStart_487688 baseEnd_487688 := by
    simpa [prefixWord, tailWord_487688, baseEnd_487688] using wordTrace_append hprefix tailTrace_487688
  have hstable : (prefixWord ++ tailWord_487688).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487688).length < 2 ^ (prefixWord ++ tailWord_487688).sum := by decide
  have hdescent : baseEnd_487688 < baseStart_487688 := by decide
  rcases family_descends (prefixWord ++ tailWord_487688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487712 : List Nat := [2, 1, 1, 5, 2, 1, 1, 5, 2]
def baseStart_487712 : Nat := 118140960795 + 487712 * 2 ^ 59
def prefixEnd_487712 : Nat := 4983230072969 + 3 ^ 40 * 487712 * 2
def baseEnd_487712 : Nat := 222605046191734274006275

theorem tailTrace_487712 : CollatzResearch.WordTrace tailWord_487712 prefixEnd_487712 222605046191734274006275 := by
  unfold tailWord_487712
  simp only [CollatzResearch.WordTrace]
  refine ⟨8894159004555096711644695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11858878672740128948859593 8894159004555096711644695)
  ·
    refine ⟨13341238506832645067467043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8894159004555096711644695 13341238506832645067467043)
    ·
      refine ⟨20011857760248967601200565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13341238506832645067467043 20011857760248967601200565)
      ·
        refine ⟨1876111665023340712612553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20011857760248967601200565 1876111665023340712612553)
        ·
          refine ⟨1407083748767505534459415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1876111665023340712612553 1407083748767505534459415)
          ·
            refine ⟨2110625623151258301689123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1407083748767505534459415 2110625623151258301689123)
            ·
              refine ⟨3165938434726887452533685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2110625623151258301689123 3165938434726887452533685)
              ·
                refine ⟨296806728255645698675033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3165938434726887452533685 296806728255645698675033)
                ·
                  refine ⟨222605046191734274006275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 296806728255645698675033 222605046191734274006275)
                  ·
                    rfl

theorem cell20_487712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 5, 2].length) (baseStart_487712 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_487712 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_487712 prefixEnd_487712 := by exact prefixLift 487712
  have htrace : WordTrace (prefixWord ++ tailWord_487712) baseStart_487712 baseEnd_487712 := by
    simpa [prefixWord, tailWord_487712, baseEnd_487712] using wordTrace_append hprefix tailTrace_487712
  have hstable : (prefixWord ++ tailWord_487712).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487712).length < 2 ^ (prefixWord ++ tailWord_487712).sum := by decide
  have hdescent : baseEnd_487712 < baseStart_487712 := by decide
  rcases family_descends (prefixWord ++ tailWord_487712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487722 : List Nat := [3, 1, 4, 2, 2, 2, 1, 2, 3]
def baseStart_487722 : Nat := 118140960795 + 487722 * 2 ^ 59
def prefixEnd_487722 : Nat := 4983230072969 + 3 ^ 40 * 487722 * 2
def baseEnd_487722 : Nat := 222609610464218683672901

theorem tailTrace_487722 : CollatzResearch.WordTrace tailWord_487722 prefixEnd_487722 222609610464218683672901 := by
  unfold tailWord_487722
  simp only [CollatzResearch.WordTrace]
  refine ⟨4447170684768491282788355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11859121826049310087435613 4447170684768491282788355)
  ·
    refine ⟨6670756027152736924182533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4447170684768491282788355 6670756027152736924182533)
    ·
      refine ⟨1250766755091138173284225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6670756027152736924182533 1250766755091138173284225)
      ·
        refine ⟨938075066318353629963169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1250766755091138173284225 938075066318353629963169)
        ·
          refine ⟨703556299738765222472377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 938075066318353629963169 703556299738765222472377)
          ·
            refine ⟨527667224804073916854283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 703556299738765222472377 527667224804073916854283)
            ·
              refine ⟨791500837206110875281425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 527667224804073916854283 791500837206110875281425)
              ·
                refine ⟨593625627904583156461069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 791500837206110875281425 593625627904583156461069)
                ·
                  refine ⟨222609610464218683672901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 593625627904583156461069 222609610464218683672901)
                  ·
                    rfl

theorem cell20_487722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 1, 2, 3].length) (baseStart_487722 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_487722 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_487722 prefixEnd_487722 := by exact prefixLift 487722
  have htrace : WordTrace (prefixWord ++ tailWord_487722) baseStart_487722 baseEnd_487722 := by
    simpa [prefixWord, tailWord_487722, baseEnd_487722] using wordTrace_append hprefix tailTrace_487722
  have hstable : (prefixWord ++ tailWord_487722).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487722).length < 2 ^ (prefixWord ++ tailWord_487722).sum := by decide
  have hdescent : baseEnd_487722 < baseStart_487722 := by decide
  rcases family_descends (prefixWord ++ tailWord_487722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487733 : List Nat := [1, 3, 3, 1, 2, 1, 4, 1, 4]
def baseStart_487733 : Nat := 118140960795 + 487733 * 2 ^ 59
def prefixEnd_487733 : Nat := 4983230072969 + 3 ^ 40 * 487733 * 2
def baseEnd_487733 : Nat := 222614631163951534306189

theorem tailTrace_487733 : CollatzResearch.WordTrace tailWord_487733 prefixEnd_487733 222614631163951534306189 := by
  unfold tailWord_487733
  simp only [CollatzResearch.WordTrace]
  refine ⟨17789083942034114009803853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11859389294689409339869235 17789083942034114009803853)
  ·
    refine ⟨6670906478262792753676445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17789083942034114009803853 6670906478262792753676445)
    ·
      refine ⟨2501589929348547282628667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6670906478262792753676445 2501589929348547282628667)
      ·
        refine ⟨3752384894022820923943001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2501589929348547282628667 3752384894022820923943001)
        ·
          refine ⟨2814288670517115692957251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3752384894022820923943001 2814288670517115692957251)
          ·
            refine ⟨4221433005775673539435877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2814288670517115692957251 4221433005775673539435877)
            ·
              refine ⟨791518688582938788644227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4221433005775673539435877 791518688582938788644227)
              ·
                refine ⟨1187278032874408182966341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 791518688582938788644227 1187278032874408182966341)
                ·
                  refine ⟨222614631163951534306189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1187278032874408182966341 222614631163951534306189)
                  ·
                    rfl

theorem cell20_487733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 4, 1, 4].length) (baseStart_487733 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_487733 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_487733 prefixEnd_487733 := by exact prefixLift 487733
  have htrace : WordTrace (prefixWord ++ tailWord_487733) baseStart_487733 baseEnd_487733 := by
    simpa [prefixWord, tailWord_487733, baseEnd_487733] using wordTrace_append hprefix tailTrace_487733
  have hstable : (prefixWord ++ tailWord_487733).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487733).length < 2 ^ (prefixWord ++ tailWord_487733).sum := by decide
  have hdescent : baseEnd_487733 < baseStart_487733 := by decide
  rcases family_descends (prefixWord ++ tailWord_487733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487747 : List Nat := [1, 1, 1, 3, 1, 3, 2, 5, 3]
def baseStart_487747 : Nat := 118140960795 + 487747 * 2 ^ 59
def prefixEnd_487747 : Nat := 4983230072969 + 3 ^ 40 * 487747 * 2
def baseEnd_487747 : Nat := 222621021145429707839465

theorem tailTrace_487747 : CollatzResearch.WordTrace tailWord_487747 prefixEnd_487747 222621021145429707839465 := by
  unfold tailWord_487747
  simp only [CollatzResearch.WordTrace]
  refine ⟨17789594563983394400813495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11859729709322262933875663 17789594563983394400813495)
  ·
    refine ⟨26684391845975091601220243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17789594563983394400813495 26684391845975091601220243)
    ·
      refine ⟨40026587768962637401830365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26684391845975091601220243 40026587768962637401830365)
      ·
        refine ⟨15009970413360989025686387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40026587768962637401830365 15009970413360989025686387)
        ·
          refine ⟨22514955620041483538529581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15009970413360989025686387 22514955620041483538529581)
          ·
            refine ⟨8443108357515556326948593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22514955620041483538529581 8443108357515556326948593)
            ·
              refine ⟨6332331268136667245211445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8443108357515556326948593 6332331268136667245211445)
              ·
                refine ⟨593656056387812554238573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6332331268136667245211445 593656056387812554238573)
                ·
                  refine ⟨222621021145429707839465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 593656056387812554238573 222621021145429707839465)
                  ·
                    rfl

theorem cell20_487747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 5, 3].length) (baseStart_487747 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_487747 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_487747 prefixEnd_487747 := by exact prefixLift 487747
  have htrace : WordTrace (prefixWord ++ tailWord_487747) baseStart_487747 baseEnd_487747 := by
    simpa [prefixWord, tailWord_487747, baseEnd_487747] using wordTrace_append hprefix tailTrace_487747
  have hstable : (prefixWord ++ tailWord_487747).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487747).length < 2 ^ (prefixWord ++ tailWord_487747).sum := by decide
  have hdescent : baseEnd_487747 < baseStart_487747 := by decide
  rcases family_descends (prefixWord ++ tailWord_487747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487778 : List Nat := [3, 3, 2, 1, 1, 2, 8]
def baseStart_487778 : Nat := 118140960795 + 487778 * 2 ^ 59
def prefixEnd_487778 : Nat := 4983230072969 + 3 ^ 40 * 487778 * 2
def baseEnd_487778 : Nat := 24737241154459041978445

theorem tailTrace_487778 : CollatzResearch.WordTrace tailWord_487778 prefixEnd_487778 24737241154459041978445 := by
  unfold tailWord_487778
  simp only [CollatzResearch.WordTrace]
  refine ⟨4447681306717771673797997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11860483484580724463461325 4447681306717771673797997)
  ·
    refine ⟨1667880490019164377674249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4447681306717771673797997 1667880490019164377674249)
    ·
      refine ⟨1250910367514373283255687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1667880490019164377674249 1250910367514373283255687)
      ·
        refine ⟨1876365551271559924883531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1250910367514373283255687 1876365551271559924883531)
        ·
          refine ⟨2814548326907339887325297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1876365551271559924883531 2814548326907339887325297)
          ·
            refine ⟨2110911245180504915493973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2814548326907339887325297 2110911245180504915493973)
            ·
              refine ⟨24737241154459041978445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2110911245180504915493973 24737241154459041978445)
              ·
                rfl

theorem cell20_487778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 8].length) (baseStart_487778 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_487778 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_487778 prefixEnd_487778 := by exact prefixLift 487778
  have htrace : WordTrace (prefixWord ++ tailWord_487778) baseStart_487778 baseEnd_487778 := by
    simpa [prefixWord, tailWord_487778, baseEnd_487778] using wordTrace_append hprefix tailTrace_487778
  have hstable : (prefixWord ++ tailWord_487778).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487778).length < 2 ^ (prefixWord ++ tailWord_487778).sum := by decide
  have hdescent : baseEnd_487778 < baseStart_487778 := by decide
  rcases family_descends (prefixWord ++ tailWord_487778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487785 : List Nat := [1, 2, 1, 1, 1, 3, 4, 4, 3]
def baseStart_487785 : Nat := 118140960795 + 487785 * 2 ^ 59
def prefixEnd_487785 : Nat := 4983230072969 + 3 ^ 40 * 487785 * 2
def baseEnd_487785 : Nat := 222638365380870464572643

theorem tailTrace_487785 : CollatzResearch.WordTrace tailWord_487785 prefixEnd_487785 222638365380870464572643 := by
  unfold tailWord_487785
  simp only [CollatzResearch.WordTrace]
  refine ⟨17790980537845726890696809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11860653691897151260464539 17790980537845726890696809)
  ·
    refine ⟨13343235403384295168022607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17790980537845726890696809 13343235403384295168022607)
    ·
      refine ⟨20014853105076442752033911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13343235403384295168022607 20014853105076442752033911)
      ·
        refine ⟨30022279657614664128050867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20014853105076442752033911 30022279657614664128050867)
        ·
          refine ⟨45033419486421996192076301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30022279657614664128050867 45033419486421996192076301)
          ·
            refine ⟨16887532307408248572028613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45033419486421996192076301 16887532307408248572028613)
            ·
              refine ⟨3166412307639046607255365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16887532307408248572028613 3166412307639046607255365)
              ·
                refine ⟨593702307682321238860381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3166412307639046607255365 593702307682321238860381)
                ·
                  refine ⟨222638365380870464572643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 593702307682321238860381 222638365380870464572643)
                  ·
                    rfl

theorem cell20_487785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 4, 3].length) (baseStart_487785 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_487785 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_487785 prefixEnd_487785 := by exact prefixLift 487785
  have htrace : WordTrace (prefixWord ++ tailWord_487785) baseStart_487785 baseEnd_487785 := by
    simpa [prefixWord, tailWord_487785, baseEnd_487785] using wordTrace_append hprefix tailTrace_487785
  have hstable : (prefixWord ++ tailWord_487785).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487785).length < 2 ^ (prefixWord ++ tailWord_487785).sum := by decide
  have hdescent : baseEnd_487785 < baseStart_487785 := by decide
  rcases family_descends (prefixWord ++ tailWord_487785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487788 : List Nat := [2, 2, 1, 1, 6, 2, 1, 1, 4]
def baseStart_487788 : Nat := 118140960795 + 487788 * 2 ^ 59
def prefixEnd_487788 : Nat := 4983230072969 + 3 ^ 40 * 487788 * 2
def baseEnd_487788 : Nat := 222639734662615787472631

theorem tailTrace_487788 : CollatzResearch.WordTrace tailWord_487788 prefixEnd_487788 222639734662615787472631 := by
  unfold tailWord_487788
  simp only [CollatzResearch.WordTrace]
  refine ⟨8895544978417429201528009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11860726637889905602037345 8895544978417429201528009)
  ·
    refine ⟨6671658733813071901146007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8895544978417429201528009 6671658733813071901146007)
    ·
      refine ⟨10007488100719607851719011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6671658733813071901146007 10007488100719607851719011)
      ·
        refine ⟨15011232151079411777578517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10007488100719607851719011 15011232151079411777578517)
        ·
          refine ⟨703651507081847427073993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 15011232151079411777578517 703651507081847427073993)
          ·
            refine ⟨527738630311385570305495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 703651507081847427073993 527738630311385570305495)
            ·
              refine ⟨791607945467078355458243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 527738630311385570305495 791607945467078355458243)
              ·
                refine ⟨1187411918200617533187365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 791607945467078355458243 1187411918200617533187365)
                ·
                  refine ⟨222639734662615787472631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1187411918200617533187365 222639734662615787472631)
                  ·
                    rfl

theorem cell20_487788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 4].length) (baseStart_487788 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_487788 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_487788 prefixEnd_487788 := by exact prefixLift 487788
  have htrace : WordTrace (prefixWord ++ tailWord_487788) baseStart_487788 baseEnd_487788 := by
    simpa [prefixWord, tailWord_487788, baseEnd_487788] using wordTrace_append hprefix tailTrace_487788
  have hstable : (prefixWord ++ tailWord_487788).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487788).length < 2 ^ (prefixWord ++ tailWord_487788).sum := by decide
  have hdescent : baseEnd_487788 < baseStart_487788 := by decide
  rcases family_descends (prefixWord ++ tailWord_487788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487798 : List Nat := [5, 1, 1, 4, 1, 1, 1, 3, 3]
def baseStart_487798 : Nat := 118140960795 + 487798 * 2 ^ 59
def prefixEnd_487798 : Nat := 4983230072969 + 3 ^ 40 * 487798 * 2
def baseEnd_487798 : Nat := 222644298935100197139257

theorem tailTrace_487798 : CollatzResearch.WordTrace tailWord_487798 prefixEnd_487798 222644298935100197139257 := by
  unfold tailWord_487798
  simp only [CollatzResearch.WordTrace]
  refine ⟨1111965917924914381932503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11860969791199086740613365 1111965917924914381932503)
  ·
    refine ⟨1667948876887371572898755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1111965917924914381932503 1667948876887371572898755)
    ·
      refine ⟨2501923315331057359348133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1667948876887371572898755 2501923315331057359348133)
      ·
        refine ⟨469110621624573254877775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2501923315331057359348133 469110621624573254877775)
        ·
          refine ⟨703665932436859882316663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 469110621624573254877775 703665932436859882316663)
          ·
            refine ⟨1055498898655289823474995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 703665932436859882316663 1055498898655289823474995)
            ·
              refine ⟨1583248347982934735212493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1055498898655289823474995 1583248347982934735212493)
              ·
                refine ⟨593718130493600525704685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1583248347982934735212493 593718130493600525704685)
                ·
                  refine ⟨222644298935100197139257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 593718130493600525704685 222644298935100197139257)
                  ·
                    rfl

theorem cell20_487798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 3, 3].length) (baseStart_487798 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_487798 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_487798 prefixEnd_487798 := by exact prefixLift 487798
  have htrace : WordTrace (prefixWord ++ tailWord_487798) baseStart_487798 baseEnd_487798 := by
    simpa [prefixWord, tailWord_487798, baseEnd_487798] using wordTrace_append hprefix tailTrace_487798
  have hstable : (prefixWord ++ tailWord_487798).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487798).length < 2 ^ (prefixWord ++ tailWord_487798).sum := by decide
  have hdescent : baseEnd_487798 < baseStart_487798 := by decide
  rcases family_descends (prefixWord ++ tailWord_487798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487837 : List Nat := [1, 4, 2, 1, 12]
def baseStart_487837 : Nat := 118140960795 + 487837 * 2 ^ 59
def prefixEnd_487837 : Nat := 4983230072969 + 3 ^ 40 * 487837 * 2
def baseEnd_487837 : Nat := 2748914809849251788137

theorem tailTrace_487837 : CollatzResearch.WordTrace tailWord_487837 prefixEnd_487837 2748914809849251788137 := by
  unfold tailWord_487837
  simp only [CollatzResearch.WordTrace]
  refine ⟨17792877133657339771589765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11861918089104893181059843 17792877133657339771589765)
  ·
    refine ⟨3336164462560751207173081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17792877133657339771589765 3336164462560751207173081)
    ·
      refine ⟨2502123346920563405379811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3336164462560751207173081 2502123346920563405379811)
      ·
        refine ⟨3753185020380845108069717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2502123346920563405379811 3753185020380845108069717)
        ·
          refine ⟨2748914809849251788137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 3753185020380845108069717 2748914809849251788137)
          ·
            rfl

theorem cell20_487837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 12].length) (baseStart_487837 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_487837 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_487837 prefixEnd_487837 := by exact prefixLift 487837
  have htrace : WordTrace (prefixWord ++ tailWord_487837) baseStart_487837 baseEnd_487837 := by
    simpa [prefixWord, tailWord_487837, baseEnd_487837] using wordTrace_append hprefix tailTrace_487837
  have hstable : (prefixWord ++ tailWord_487837).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487837).length < 2 ^ (prefixWord ++ tailWord_487837).sum := by decide
  have hdescent : baseEnd_487837 < baseStart_487837 := by decide
  rcases family_descends (prefixWord ++ tailWord_487837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487840 : List Nat := [2, 1, 1, 4, 1, 4, 2, 2, 3]
def baseStart_487840 : Nat := 118140960795 + 487840 * 2 ^ 59
def prefixEnd_487840 : Nat := 4983230072969 + 3 ^ 40 * 487840 * 2
def baseEnd_487840 : Nat := 222663468879534717739085

theorem tailTrace_487840 : CollatzResearch.WordTrace tailWord_487840 prefixEnd_487840 222663468879534717739085 := by
  unfold tailWord_487840
  simp only [CollatzResearch.WordTrace]
  refine ⟨8896493276323235641974487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11861991035097647522632649 8896493276323235641974487)
  ·
    refine ⟨13344739914484853462961731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8896493276323235641974487 13344739914484853462961731)
    ·
      refine ⟨20017109871727280194442597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13344739914484853462961731 20017109871727280194442597)
      ·
        refine ⟨3753208100948865036457987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20017109871727280194442597 3753208100948865036457987)
        ·
          refine ⟨5629812151423297554686981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3753208100948865036457987 5629812151423297554686981)
          ·
            refine ⟨1055589778391868291503809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5629812151423297554686981 1055589778391868291503809)
            ·
              refine ⟨791692333793901218627857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1055589778391868291503809 791692333793901218627857)
              ·
                refine ⟨593769250345425913970893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 791692333793901218627857 593769250345425913970893)
                ·
                  refine ⟨222663468879534717739085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 593769250345425913970893 222663468879534717739085)
                  ·
                    rfl

theorem cell20_487840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 2, 2, 3].length) (baseStart_487840 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_487840 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_487840 prefixEnd_487840 := by exact prefixLift 487840
  have htrace : WordTrace (prefixWord ++ tailWord_487840) baseStart_487840 baseEnd_487840 := by
    simpa [prefixWord, tailWord_487840, baseEnd_487840] using wordTrace_append hprefix tailTrace_487840
  have hstable : (prefixWord ++ tailWord_487840).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487840).length < 2 ^ (prefixWord ++ tailWord_487840).sum := by decide
  have hdescent : baseEnd_487840 < baseStart_487840 := by decide
  rcases family_descends (prefixWord ++ tailWord_487840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487843 : List Nat := [1, 1, 1, 4, 1, 6, 2, 2, 2]
def baseStart_487843 : Nat := 118140960795 + 487843 * 2 ^ 59
def prefixEnd_487843 : Nat := 4983230072969 + 3 ^ 40 * 487843 * 2
def baseEnd_487843 : Nat := 222664838161280040639073

theorem tailTrace_487843 : CollatzResearch.WordTrace tailWord_487843 prefixEnd_487843 222664838161280040639073 := by
  unfold tailWord_487843
  simp only [CollatzResearch.WordTrace]
  refine ⟨17793095971635602796308183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11862063981090401864205455 17793095971635602796308183)
  ·
    refine ⟨26689643957453404194462275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17793095971635602796308183 26689643957453404194462275)
    ·
      refine ⟨40034465936180106291693413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26689643957453404194462275 40034465936180106291693413)
      ·
        refine ⟨7506462363033769929692515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40034465936180106291693413 7506462363033769929692515)
        ·
          refine ⟨11259693544550654894538773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7506462363033769929692515 11259693544550654894538773)
          ·
            refine ⟨527798134900811948181505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 11259693544550654894538773 527798134900811948181505)
            ·
              refine ⟨395848601175608961136129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 527798134900811948181505 395848601175608961136129)
              ·
                refine ⟨296886450881706720852097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 395848601175608961136129 296886450881706720852097)
                ·
                  refine ⟨222664838161280040639073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 296886450881706720852097 222664838161280040639073)
                  ·
                    rfl

theorem cell20_487843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 2, 2, 2].length) (baseStart_487843 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_487843 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_487843 prefixEnd_487843 := by exact prefixLift 487843
  have htrace : WordTrace (prefixWord ++ tailWord_487843) baseStart_487843 baseEnd_487843 := by
    simpa [prefixWord, tailWord_487843, baseEnd_487843] using wordTrace_append hprefix tailTrace_487843
  have hstable : (prefixWord ++ tailWord_487843).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487843).length < 2 ^ (prefixWord ++ tailWord_487843).sum := by decide
  have hdescent : baseEnd_487843 < baseStart_487843 := by decide
  rcases family_descends (prefixWord ++ tailWord_487843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487892 : List Nat := [2, 4, 1, 2, 2, 2, 7]
def baseStart_487892 : Nat := 118140960795 + 487892 * 2 ^ 59
def prefixEnd_487892 : Nat := 4983230072969 + 3 ^ 40 * 487892 * 2
def baseEnd_487892 : Nat := 24743022566272627556171

theorem tailTrace_487892 : CollatzResearch.WordTrace tailWord_487892 prefixEnd_487892 24743022566272627556171 := by
  unfold tailWord_487892
  simp only [CollatzResearch.WordTrace]
  refine ⟨8897441574229042082420965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11863255432305389443227953 8897441574229042082420965)
  ·
    refine ⟨1668270295167945390453931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8897441574229042082420965 1668270295167945390453931)
    ·
      refine ⟨2502405442751918085680897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1668270295167945390453931 2502405442751918085680897)
      ·
        refine ⟨1876804082063938564260673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2502405442751918085680897 1876804082063938564260673)
        ·
          refine ⟨1407603061547953923195505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1876804082063938564260673 1407603061547953923195505)
          ·
            refine ⟨1055702296160965442396629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1407603061547953923195505 1055702296160965442396629)
            ·
              refine ⟨24743022566272627556171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1055702296160965442396629 24743022566272627556171)
              ·
                rfl

theorem cell20_487892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 7].length) (baseStart_487892 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_487892 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_487892 prefixEnd_487892 := by exact prefixLift 487892
  have htrace : WordTrace (prefixWord ++ tailWord_487892) baseStart_487892 baseEnd_487892 := by
    simpa [prefixWord, tailWord_487892, baseEnd_487892] using wordTrace_append hprefix tailTrace_487892
  have hstable : (prefixWord ++ tailWord_487892).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487892).length < 2 ^ (prefixWord ++ tailWord_487892).sum := by decide
  have hdescent : baseEnd_487892 < baseStart_487892 := by decide
  rcases family_descends (prefixWord ++ tailWord_487892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487916 : List Nat := [2, 2, 1, 1, 2, 1, 7, 1, 3]
def baseStart_487916 : Nat := 118140960795 + 487916 * 2 ^ 59
def prefixEnd_487916 : Nat := 4983230072969 + 3 ^ 40 * 487916 * 2
def baseEnd_487916 : Nat := 222698157350416231205441

theorem tailTrace_487916 : CollatzResearch.WordTrace tailWord_487916 prefixEnd_487916 222698157350416231205441 := by
  unfold tailWord_487916
  simp only [CollatzResearch.WordTrace]
  refine ⟨8897879250185568131857801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11863839000247424175810401 8897879250185568131857801)
  ·
    refine ⟨6673409437639176098893351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8897879250185568131857801 6673409437639176098893351)
    ·
      refine ⟨10010114156458764148340027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6673409437639176098893351 10010114156458764148340027)
      ·
        refine ⟨15015171234688146222510041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10010114156458764148340027 15015171234688146222510041)
        ·
          refine ⟨11261378426016109666882531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15015171234688146222510041 11261378426016109666882531)
          ·
            refine ⟨16892067639024164500323797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11261378426016109666882531 16892067639024164500323797)
            ·
              refine ⟨395907835289628855476339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 16892067639024164500323797 395907835289628855476339)
              ·
                refine ⟨593861752934443283214509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 395907835289628855476339 593861752934443283214509)
                ·
                  refine ⟨222698157350416231205441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 593861752934443283214509 222698157350416231205441)
                  ·
                    rfl

theorem cell20_487916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 3].length) (baseStart_487916 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_487916 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_487916 prefixEnd_487916 := by exact prefixLift 487916
  have htrace : WordTrace (prefixWord ++ tailWord_487916) baseStart_487916 baseEnd_487916 := by
    simpa [prefixWord, tailWord_487916, baseEnd_487916] using wordTrace_append hprefix tailTrace_487916
  have hstable : (prefixWord ++ tailWord_487916).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487916).length < 2 ^ (prefixWord ++ tailWord_487916).sum := by decide
  have hdescent : baseEnd_487916 < baseStart_487916 := by decide
  rcases family_descends (prefixWord ++ tailWord_487916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487937 : List Nat := [1, 2, 4, 1, 3, 1, 1, 2, 5]
def baseStart_487937 : Nat := 118140960795 + 487937 * 2 ^ 59
def prefixEnd_487937 : Nat := 4983230072969 + 3 ^ 40 * 487937 * 2
def baseEnd_487937 : Nat := 222707742322633491505355

theorem tailTrace_487937 : CollatzResearch.WordTrace tailWord_487937 prefixEnd_487937 222707742322633491505355 := by
  unfold tailWord_487937
  simp only [CollatzResearch.WordTrace]
  refine ⟨17796524433295056850230065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11864349622196704566820043 17796524433295056850230065)
  ·
    refine ⟨13347393324971292637672549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17796524433295056850230065 13347393324971292637672549)
    ·
      refine ⟨2502636248432117369563603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13347393324971292637672549 2502636248432117369563603)
      ·
        refine ⟨3753954372648176054345405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2502636248432117369563603 3753954372648176054345405)
        ·
          refine ⟨1407732889743066020379527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3753954372648176054345405 1407732889743066020379527)
          ·
            refine ⟨2111599334614599030569291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1407732889743066020379527 2111599334614599030569291)
            ·
              refine ⟨3167399001921898545853937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2111599334614599030569291 3167399001921898545853937)
              ·
                refine ⟨2375549251441423909390453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3167399001921898545853937 2375549251441423909390453)
                ·
                  refine ⟨222707742322633491505355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2375549251441423909390453 222707742322633491505355)
                  ·
                    rfl

theorem cell20_487937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 2, 5].length) (baseStart_487937 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_487937 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_487937 prefixEnd_487937 := by exact prefixLift 487937
  have htrace : WordTrace (prefixWord ++ tailWord_487937) baseStart_487937 baseEnd_487937 := by
    simpa [prefixWord, tailWord_487937, baseEnd_487937] using wordTrace_append hprefix tailTrace_487937
  have hstable : (prefixWord ++ tailWord_487937).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487937).length < 2 ^ (prefixWord ++ tailWord_487937).sum := by decide
  have hdescent : baseEnd_487937 < baseStart_487937 := by decide
  rcases family_descends (prefixWord ++ tailWord_487937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487971 : List Nat := [1, 1, 1, 4, 4, 3, 2, 1, 3]
def baseStart_487971 : Nat := 118140960795 + 487971 * 2 ^ 59
def prefixEnd_487971 : Nat := 4983230072969 + 3 ^ 40 * 487971 * 2
def baseEnd_487971 : Nat := 222723260849080484371883

theorem tailTrace_487971 : CollatzResearch.WordTrace tailWord_487971 prefixEnd_487971 222723260849080484371883 := by
  unfold tailWord_487971
  simp only [CollatzResearch.WordTrace]
  refine ⟨17797764515171880656967767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11865176343447920437978511 17797764515171880656967767)
  ·
    refine ⟨26696646772757820985451651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17797764515171880656967767 26696646772757820985451651)
    ·
      refine ⟨40044970159136731478177477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26696646772757820985451651 40044970159136731478177477)
      ·
        refine ⟨7508431904838137152158277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40044970159136731478177477 7508431904838137152158277)
        ·
          refine ⟨1407830982157150716029677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7508431904838137152158277 1407830982157150716029677)
          ·
            refine ⟨527936618308931518511129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1407830982157150716029677 527936618308931518511129)
            ·
              refine ⟨395952463731698638883347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 527936618308931518511129 395952463731698638883347)
              ·
                refine ⟨593928695597547958325021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 395952463731698638883347 593928695597547958325021)
                ·
                  refine ⟨222723260849080484371883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 593928695597547958325021 222723260849080484371883)
                  ·
                    rfl

theorem cell20_487971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 2, 1, 3].length) (baseStart_487971 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_487971 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_487971 prefixEnd_487971 := by exact prefixLift 487971
  have htrace : WordTrace (prefixWord ++ tailWord_487971) baseStart_487971 baseEnd_487971 := by
    simpa [prefixWord, tailWord_487971, baseEnd_487971] using wordTrace_append hprefix tailTrace_487971
  have hstable : (prefixWord ++ tailWord_487971).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487971).length < 2 ^ (prefixWord ++ tailWord_487971).sum := by decide
  have hdescent : baseEnd_487971 < baseStart_487971 := by decide
  rcases family_descends (prefixWord ++ tailWord_487971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487989 : List Nat := [1, 3, 3, 1, 1, 2, 1, 8]
def baseStart_487989 : Nat := 118140960795 + 487989 * 2 ^ 59
def prefixEnd_487989 : Nat := 4983230072969 + 3 ^ 40 * 487989 * 2
def baseEnd_487989 : Nat := 74243825513184140590603

theorem tailTrace_487989 : CollatzResearch.WordTrace tailWord_487989 prefixEnd_487989 74243825513184140590603 := by
  unfold tailWord_487989
  simp only [CollatzResearch.WordTrace]
  refine ⟨17798421029106669731123021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11865614019404446487415347 17798421029106669731123021)
  ·
    refine ⟨6674407885915001149171133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17798421029106669731123021 6674407885915001149171133)
    ·
      refine ⟨2502902957218125430939175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6674407885915001149171133 2502902957218125430939175)
      ·
        refine ⟨3754354435827188146408763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2502902957218125430939175 3754354435827188146408763)
        ·
          refine ⟨5631531653740782219613145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3754354435827188146408763 5631531653740782219613145)
          ·
            refine ⟨4223648740305586664709859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5631531653740782219613145 4223648740305586664709859)
            ·
              refine ⟨6335473110458379997064789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4223648740305586664709859 6335473110458379997064789)
              ·
                refine ⟨74243825513184140590603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6335473110458379997064789 74243825513184140590603)
                ·
                  rfl

theorem cell20_487989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 8].length) (baseStart_487989 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_487989 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_487989 prefixEnd_487989 := by exact prefixLift 487989
  have htrace : WordTrace (prefixWord ++ tailWord_487989) baseStart_487989 baseEnd_487989 := by
    simpa [prefixWord, tailWord_487989, baseEnd_487989] using wordTrace_append hprefix tailTrace_487989
  have hstable : (prefixWord ++ tailWord_487989).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487989).length < 2 ^ (prefixWord ++ tailWord_487989).sum := by decide
  have hdescent : baseEnd_487989 < baseStart_487989 := by decide
  rcases family_descends (prefixWord ++ tailWord_487989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487999 : List Nat := [1, 1, 2, 2, 3, 2, 2, 5, 2]
def baseStart_487999 : Nat := 118140960795 + 487999 * 2 ^ 59
def prefixEnd_487999 : Nat := 4983230072969 + 3 ^ 40 * 487999 * 2
def baseEnd_487999 : Nat := 222736040812036831438435

theorem tailTrace_487999 : CollatzResearch.WordTrace tailWord_487999 prefixEnd_487999 222736040812036831438435 := by
  unfold tailWord_487999
  simp only [CollatzResearch.WordTrace]
  refine ⟨17798785759070441438987051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11865857172713627625991367 17798785759070441438987051)
  ·
    refine ⟨26698178638605662158480577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17798785759070441438987051 26698178638605662158480577)
    ·
      refine ⟨20023633978954246618860433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26698178638605662158480577 20023633978954246618860433)
      ·
        refine ⟨15017725484215684964145325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20023633978954246618860433 15017725484215684964145325)
        ·
          refine ⟨5631647056580881861554497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15017725484215684964145325 5631647056580881861554497)
          ·
            refine ⟨4223735292435661396165873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5631647056580881861554497 4223735292435661396165873)
            ·
              refine ⟨3167801469326746047124405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4223735292435661396165873 3167801469326746047124405)
              ·
                refine ⟨296981387749382441917913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3167801469326746047124405 296981387749382441917913)
                ·
                  refine ⟨222736040812036831438435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 296981387749382441917913 222736040812036831438435)
                  ·
                    rfl

theorem cell20_487999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 5, 2].length) (baseStart_487999 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_487999 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_487999 prefixEnd_487999 := by exact prefixLift 487999
  have htrace : WordTrace (prefixWord ++ tailWord_487999) baseStart_487999 baseEnd_487999 := by
    simpa [prefixWord, tailWord_487999, baseEnd_487999] using wordTrace_append hprefix tailTrace_487999
  have hstable : (prefixWord ++ tailWord_487999).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487999).length < 2 ^ (prefixWord ++ tailWord_487999).sum := by decide
  have hdescent : baseEnd_487999 < baseStart_487999 := by decide
  rcases family_descends (prefixWord ++ tailWord_487999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488037 : List Nat := [1, 3, 1, 3, 4, 1, 1, 2, 4]
def baseStart_488037 : Nat := 118140960795 + 488037 * 2 ^ 59
def prefixEnd_488037 : Nat := 4983230072969 + 3 ^ 40 * 488037 * 2
def baseEnd_488037 : Nat := 222753385047477588171613

theorem tailTrace_488037 : CollatzResearch.WordTrace tailWord_488037 prefixEnd_488037 222753385047477588171613 := by
  unfold tailWord_488037
  simp only [CollatzResearch.WordTrace]
  refine ⟨17800171732932773928870365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11866781155288515952580243 17800171732932773928870365)
  ·
    refine ⟨6675064399849790223326387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17800171732932773928870365 6675064399849790223326387)
    ·
      refine ⟨10012596599774685334989581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6675064399849790223326387 10012596599774685334989581)
      ·
        refine ⟨3754723724915507000621093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10012596599774685334989581 3754723724915507000621093)
        ·
          refine ⟨704010698421657562616455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3754723724915507000621093 704010698421657562616455)
          ·
            refine ⟨1056016047632486343924683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 704010698421657562616455 1056016047632486343924683)
            ·
              refine ⟨1584024071448729515887025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1056016047632486343924683 1584024071448729515887025)
              ·
                refine ⟨1188018053586547136915269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1584024071448729515887025 1188018053586547136915269)
                ·
                  refine ⟨222753385047477588171613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1188018053586547136915269 222753385047477588171613)
                  ·
                    rfl

theorem cell20_488037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 2, 4].length) (baseStart_488037 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_488037 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_488037 prefixEnd_488037 := by exact prefixLift 488037
  have htrace : WordTrace (prefixWord ++ tailWord_488037) baseStart_488037 baseEnd_488037 := by
    simpa [prefixWord, tailWord_488037, baseEnd_488037] using wordTrace_append hprefix tailTrace_488037
  have hstable : (prefixWord ++ tailWord_488037).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488037).length < 2 ^ (prefixWord ++ tailWord_488037).sum := by decide
  have hdescent : baseEnd_488037 < baseStart_488037 := by decide
  rcases family_descends (prefixWord ++ tailWord_488037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488065 : List Nat := [1, 2, 4, 2, 1, 1, 9]
def baseStart_488065 : Nat := 118140960795 + 488065 * 2 ^ 59
def prefixEnd_488065 : Nat := 4983230072969 + 3 ^ 40 * 488065 * 2
def baseEnd_488065 : Nat := 24751796112270437248685

theorem tailTrace_488065 : CollatzResearch.WordTrace tailWord_488065 prefixEnd_488065 24751796112270437248685 := by
  unfold tailWord_488065
  simp only [CollatzResearch.WordTrace]
  refine ⟨17801192976831334710889649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11867461984554223140593099 17801192976831334710889649)
  ·
    refine ⟨13350894732623501033167237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17801192976831334710889649 13350894732623501033167237)
    ·
      refine ⟨2503292762366906443718857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13350894732623501033167237 2503292762366906443718857)
      ·
        refine ⟨1877469571775179832789143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2503292762366906443718857 1877469571775179832789143)
        ·
          refine ⟨2816204357662769749183715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1877469571775179832789143 2816204357662769749183715)
          ·
            refine ⟨4224306536494154623775573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2816204357662769749183715 4224306536494154623775573)
            ·
              refine ⟨24751796112270437248685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4224306536494154623775573 24751796112270437248685)
              ·
                rfl

theorem cell20_488065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 9].length) (baseStart_488065 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_488065 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_488065 prefixEnd_488065 := by exact prefixLift 488065
  have htrace : WordTrace (prefixWord ++ tailWord_488065) baseStart_488065 baseEnd_488065 := by
    simpa [prefixWord, tailWord_488065, baseEnd_488065] using wordTrace_append hprefix tailTrace_488065
  have hstable : (prefixWord ++ tailWord_488065).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488065).length < 2 ^ (prefixWord ++ tailWord_488065).sum := by decide
  have hdescent : baseEnd_488065 < baseStart_488065 := by decide
  rcases family_descends (prefixWord ++ tailWord_488065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488068 : List Nat := [2, 3, 2, 1, 3, 1, 3, 2, 3]
def baseStart_488068 : Nat := 118140960795 + 488068 * 2 ^ 59
def prefixEnd_488068 : Nat := 4983230072969 + 3 ^ 40 * 488068 * 2
def baseEnd_488068 : Nat := 222767534292179258138153

theorem tailTrace_488068 : CollatzResearch.WordTrace tailWord_488068 prefixEnd_488068 222767534292179258138153 := by
  unfold tailWord_488068
  simp only [CollatzResearch.WordTrace]
  refine ⟨8900651197910233111624429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11867534930546977482165905 8900651197910233111624429)
  ·
    refine ⟨3337744199216337416859161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8900651197910233111624429 3337744199216337416859161)
    ·
      refine ⟨2503308149412253062644371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3337744199216337416859161 2503308149412253062644371)
      ·
        refine ⟨3754962224118379593966557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2503308149412253062644371 3754962224118379593966557)
        ·
          refine ⟨1408110834044392347737459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3754962224118379593966557 1408110834044392347737459)
          ·
            refine ⟨2112166251066588521606189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1408110834044392347737459 2112166251066588521606189)
            ·
              refine ⟨792062344149970695602321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2112166251066588521606189 792062344149970695602321)
              ·
                refine ⟨594046758112478021701741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 792062344149970695602321 594046758112478021701741)
                ·
                  refine ⟨222767534292179258138153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 594046758112478021701741 222767534292179258138153)
                  ·
                    rfl

theorem cell20_488068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 3, 2, 3].length) (baseStart_488068 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_488068 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_488068 prefixEnd_488068 := by exact prefixLift 488068
  have htrace : WordTrace (prefixWord ++ tailWord_488068) baseStart_488068 baseEnd_488068 := by
    simpa [prefixWord, tailWord_488068, baseEnd_488068] using wordTrace_append hprefix tailTrace_488068
  have hstable : (prefixWord ++ tailWord_488068).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488068).length < 2 ^ (prefixWord ++ tailWord_488068).sum := by decide
  have hdescent : baseEnd_488068 < baseStart_488068 := by decide
  rcases family_descends (prefixWord ++ tailWord_488068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488079 : List Nat := [1, 1, 2, 1, 1, 1, 1, 4, 8]
def baseStart_488079 : Nat := 118140960795 + 488079 * 2 ^ 59
def prefixEnd_488079 : Nat := 4983230072969 + 3 ^ 40 * 488079 * 2
def baseEnd_488079 : Nat := 222772554991912108771441

theorem tailTrace_488079 : CollatzResearch.WordTrace tailWord_488079 prefixEnd_488079 222772554991912108771441 := by
  unfold tailWord_488079
  simp only [CollatzResearch.WordTrace]
  refine ⟨17801703598780615101899291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11867802399187076734599527 17801703598780615101899291)
  ·
    refine ⟨26702555398170922652848937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17801703598780615101899291 26702555398170922652848937)
    ·
      refine ⟨20026916548628191989636703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26702555398170922652848937 20026916548628191989636703)
      ·
        refine ⟨30040374822942287984455055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20026916548628191989636703 30040374822942287984455055)
        ·
          refine ⟨45060562234413431976682583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30040374822942287984455055 45060562234413431976682583)
          ·
            refine ⟨67590843351620147965023875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45060562234413431976682583 67590843351620147965023875)
            ·
              refine ⟨101386265027430221947535813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67590843351620147965023875 101386265027430221947535813)
              ·
                refine ⟨19009924692643166615162965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 101386265027430221947535813 19009924692643166615162965)
                ·
                  refine ⟨222772554991912108771441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19009924692643166615162965 222772554991912108771441)
                  ·
                    rfl

theorem cell20_488079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 4, 8].length) (baseStart_488079 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_488079 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_488079 prefixEnd_488079 := by exact prefixLift 488079
  have htrace : WordTrace (prefixWord ++ tailWord_488079) baseStart_488079 baseEnd_488079 := by
    simpa [prefixWord, tailWord_488079, baseEnd_488079] using wordTrace_append hprefix tailTrace_488079
  have hstable : (prefixWord ++ tailWord_488079).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488079).length < 2 ^ (prefixWord ++ tailWord_488079).sum := by decide
  have hdescent : baseEnd_488079 < baseStart_488079 := by decide
  rcases family_descends (prefixWord ++ tailWord_488079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488109 : List Nat := [1, 5, 2, 1, 1, 4, 1, 3, 2]
def baseStart_488109 : Nat := 118140960795 + 488109 * 2 ^ 59
def prefixEnd_488109 : Nat := 4983230072969 + 3 ^ 40 * 488109 * 2
def baseEnd_488109 : Nat := 222786247809365337771319

theorem tailTrace_488109 : CollatzResearch.WordTrace tailWord_488109 prefixEnd_488109 222786247809365337771319 := by
  unfold tailWord_488109
  simp only [CollatzResearch.WordTrace]
  refine ⟨17802797788671930225491381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11868531859114620150327587 17802797788671930225491381)
  ·
    refine ⟨1669012292687993458639817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17802797788671930225491381 1669012292687993458639817)
    ·
      refine ⟨1251759219515995093979863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1669012292687993458639817 1251759219515995093979863)
      ·
        refine ⟨1877638829273992640969795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1251759219515995093979863 1877638829273992640969795)
        ·
          refine ⟨2816458243910988961454693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1877638829273992640969795 2816458243910988961454693)
          ·
            refine ⟨528085920733310430272755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2816458243910988961454693 528085920733310430272755)
            ·
              refine ⟨792128881099965645409133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 528085920733310430272755 792128881099965645409133)
              ·
                refine ⟨297048330412487117028425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 792128881099965645409133 297048330412487117028425)
                ·
                  refine ⟨222786247809365337771319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 297048330412487117028425 222786247809365337771319)
                  ·
                    rfl

theorem cell20_488109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 1, 3, 2].length) (baseStart_488109 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_488109 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_488109 prefixEnd_488109 := by exact prefixLift 488109
  have htrace : WordTrace (prefixWord ++ tailWord_488109) baseStart_488109 baseEnd_488109 := by
    simpa [prefixWord, tailWord_488109, baseEnd_488109] using wordTrace_append hprefix tailTrace_488109
  have hstable : (prefixWord ++ tailWord_488109).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488109).length < 2 ^ (prefixWord ++ tailWord_488109).sum := by decide
  have hdescent : baseEnd_488109 < baseStart_488109 := by decide
  rcases family_descends (prefixWord ++ tailWord_488109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488182 : List Nat := [5, 1, 1, 1, 1, 2, 4, 2, 3]
def baseStart_488182 : Nat := 118140960795 + 488182 * 2 ^ 59
def prefixEnd_488182 : Nat := 4983230072969 + 3 ^ 40 * 488182 * 2
def baseEnd_488182 : Nat := 222819566998501528337687

theorem tailTrace_488182 : CollatzResearch.WordTrace tailWord_488182 prefixEnd_488182 222819566998501528337687 := by
  unfold tailWord_488182
  simp only [CollatzResearch.WordTrace]
  refine ⟨1112841269837966480806175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11870306878271642461932533 1112841269837966480806175)
  ·
    refine ⟨1669261904756949721209263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1112841269837966480806175 1669261904756949721209263)
    ·
      refine ⟨2503892857135424581813895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1669261904756949721209263 2503892857135424581813895)
      ·
        refine ⟨3755839285703136872720843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2503892857135424581813895 3755839285703136872720843)
        ·
          refine ⟨5633758928554705309081265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3755839285703136872720843 5633758928554705309081265)
          ·
            refine ⟨4225319196416028981810949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5633758928554705309081265 4225319196416028981810949)
            ·
              refine ⟨792247349328005434089553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4225319196416028981810949 792247349328005434089553)
              ·
                refine ⟨594185511996004075567165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 792247349328005434089553 594185511996004075567165)
                ·
                  refine ⟨222819566998501528337687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 594185511996004075567165 222819566998501528337687)
                  ·
                    rfl

theorem cell20_488182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 4, 2, 3].length) (baseStart_488182 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_488182 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_488182 prefixEnd_488182 := by exact prefixLift 488182
  have htrace : WordTrace (prefixWord ++ tailWord_488182) baseStart_488182 baseEnd_488182 := by
    simpa [prefixWord, tailWord_488182, baseEnd_488182] using wordTrace_append hprefix tailTrace_488182
  have hstable : (prefixWord ++ tailWord_488182).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488182).length < 2 ^ (prefixWord ++ tailWord_488182).sum := by decide
  have hdescent : baseEnd_488182 < baseStart_488182 := by decide
  rcases family_descends (prefixWord ++ tailWord_488182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488186 : List Nat := [3, 1, 1, 1, 1, 3, 2, 3, 5]
def baseStart_488186 : Nat := 118140960795 + 488186 * 2 ^ 59
def prefixEnd_488186 : Nat := 4983230072969 + 3 ^ 40 * 488186 * 2
def baseEnd_488186 : Nat := 222821392707495292204337

theorem tailTrace_488186 : CollatzResearch.WordTrace tailWord_488186 prefixEnd_488186 222821392707495292204337 := by
  unfold tailWord_488186
  simp only [CollatzResearch.WordTrace]
  refine ⟨4451401552348243094011103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11870404139595314917362941 4451401552348243094011103)
  ·
    refine ⟨6677102328522364641016655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4451401552348243094011103 6677102328522364641016655)
    ·
      refine ⟨10015653492783546961524983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6677102328522364641016655 10015653492783546961524983)
      ·
        refine ⟨15023480239175320442287475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10015653492783546961524983 15023480239175320442287475)
        ·
          refine ⟨22535220358762980663431213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15023480239175320442287475 22535220358762980663431213)
          ·
            refine ⟨8450707634536117748786705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22535220358762980663431213 8450707634536117748786705)
            ·
              refine ⟨6338030725902088311590029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8450707634536117748786705 6338030725902088311590029)
              ·
                refine ⟨2376761522213283116846261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6338030725902088311590029 2376761522213283116846261)
                ·
                  refine ⟨222821392707495292204337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2376761522213283116846261 222821392707495292204337)
                  ·
                    rfl

theorem cell20_488186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 3, 5].length) (baseStart_488186 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_488186 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_488186 prefixEnd_488186 := by exact prefixLift 488186
  have htrace : WordTrace (prefixWord ++ tailWord_488186) baseStart_488186 baseEnd_488186 := by
    simpa [prefixWord, tailWord_488186, baseEnd_488186] using wordTrace_append hprefix tailTrace_488186
  have hstable : (prefixWord ++ tailWord_488186).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488186).length < 2 ^ (prefixWord ++ tailWord_488186).sum := by decide
  have hdescent : baseEnd_488186 < baseStart_488186 := by decide
  rcases family_descends (prefixWord ++ tailWord_488186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488189 : List Nat := [1, 4, 1, 1, 1, 1, 5, 4, 2]
def baseStart_488189 : Nat := 118140960795 + 488189 * 2 ^ 59
def prefixEnd_488189 : Nat := 4983230072969 + 3 ^ 40 * 488189 * 2
def baseEnd_488189 : Nat := 222822761989240615104325

theorem tailTrace_488189 : CollatzResearch.WordTrace tailWord_488189 prefixEnd_488189 222822761989240615104325 := by
  unfold tailWord_488189
  simp only [CollatzResearch.WordTrace]
  refine ⟨17805715628382103888403621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11870477085588069258935747 17805715628382103888403621)
  ·
    refine ⟨3338571680321644479075679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17805715628382103888403621 3338571680321644479075679)
    ·
      refine ⟨5007857520482466718613519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3338571680321644479075679 5007857520482466718613519)
      ·
        refine ⟨7511786280723700077920279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5007857520482466718613519 7511786280723700077920279)
        ·
          refine ⟨11267679421085550116880419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7511786280723700077920279 11267679421085550116880419)
          ·
            refine ⟨16901519131628325175320629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11267679421085550116880419 16901519131628325175320629)
            ·
              refine ⟨1584517418590155485186309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16901519131628325175320629 1584517418590155485186309)
              ·
                refine ⟨297097015985654153472433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1584517418590155485186309 297097015985654153472433)
                ·
                  refine ⟨222822761989240615104325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 297097015985654153472433 222822761989240615104325)
                  ·
                    rfl

theorem cell20_488189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 4, 2].length) (baseStart_488189 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_488189 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_488189 prefixEnd_488189 := by exact prefixLift 488189
  have htrace : WordTrace (prefixWord ++ tailWord_488189) baseStart_488189 baseEnd_488189 := by
    simpa [prefixWord, tailWord_488189, baseEnd_488189] using wordTrace_append hprefix tailTrace_488189
  have hstable : (prefixWord ++ tailWord_488189).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488189).length < 2 ^ (prefixWord ++ tailWord_488189).sum := by decide
  have hdescent : baseEnd_488189 < baseStart_488189 := by decide
  rcases family_descends (prefixWord ++ tailWord_488189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488237 : List Nat := [1, 5, 3, 2, 1, 1, 1, 1, 5]
def baseStart_488237 : Nat := 118140960795 + 488237 * 2 ^ 59
def prefixEnd_488237 : Nat := 4983230072969 + 3 ^ 40 * 488237 * 2
def baseEnd_488237 : Nat := 222844670497165781504129

theorem tailTrace_488237 : CollatzResearch.WordTrace tailWord_488237 prefixEnd_488237 222844670497165781504129 := by
  unfold tailWord_488237
  simp only [CollatzResearch.WordTrace]
  refine ⟨17807466332208208086150965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11871644221472138724100643 17807466332208208086150965)
  ·
    refine ⟨1669449968644519508076653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17807466332208208086150965 1669449968644519508076653)
    ·
      refine ⟨626043738241694815528745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1669449968644519508076653 626043738241694815528745)
      ·
        refine ⟨469532803681271111646559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 626043738241694815528745 469532803681271111646559)
        ·
          refine ⟨704299205521906667469839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 469532803681271111646559 704299205521906667469839)
          ·
            refine ⟨1056448808282860001204759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 704299205521906667469839 1056448808282860001204759)
            ·
              refine ⟨1584673212424290001807139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1056448808282860001204759 1584673212424290001807139)
              ·
                refine ⟨2377009818636435002710709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1584673212424290001807139 2377009818636435002710709)
                ·
                  refine ⟨222844670497165781504129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2377009818636435002710709 222844670497165781504129)
                  ·
                    rfl

theorem cell20_488237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 1, 5].length) (baseStart_488237 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_488237 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_488237 prefixEnd_488237 := by exact prefixLift 488237
  have htrace : WordTrace (prefixWord ++ tailWord_488237) baseStart_488237 baseEnd_488237 := by
    simpa [prefixWord, tailWord_488237, baseEnd_488237] using wordTrace_append hprefix tailTrace_488237
  have hstable : (prefixWord ++ tailWord_488237).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488237).length < 2 ^ (prefixWord ++ tailWord_488237).sum := by decide
  have hdescent : baseEnd_488237 < baseStart_488237 := by decide
  rcases family_descends (prefixWord ++ tailWord_488237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488244 : List Nat := [2, 5, 1, 1, 3, 1, 2, 1, 4]
def baseStart_488244 : Nat := 118140960795 + 488244 * 2 ^ 59
def prefixEnd_488244 : Nat := 4983230072969 + 3 ^ 40 * 488244 * 2
def baseEnd_488244 : Nat := 222847865487904868270767

theorem tailTrace_488244 : CollatzResearch.WordTrace tailWord_488244 prefixEnd_488244 222847865487904868270767 := by
  unfold tailWord_488244
  simp only [CollatzResearch.WordTrace]
  refine ⟨8903860821591424140827893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11871814428788565521103857 8903860821591424140827893)
  ·
    refine ⟨834736952024196013202615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8903860821591424140827893 834736952024196013202615)
    ·
      refine ⟨1252105428036294019803923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 834736952024196013202615 1252105428036294019803923)
      ·
        refine ⟨1878158142054441029705885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1252105428036294019803923 1878158142054441029705885)
        ·
          refine ⟨704309303270415386139707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1878158142054441029705885 704309303270415386139707)
          ·
            refine ⟨1056463954905623079209561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 704309303270415386139707 1056463954905623079209561)
            ·
              refine ⟨792347966179217309407171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1056463954905623079209561 792347966179217309407171)
              ·
                refine ⟨1188521949268825964110757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 792347966179217309407171 1188521949268825964110757)
                ·
                  refine ⟨222847865487904868270767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1188521949268825964110757 222847865487904868270767)
                  ·
                    rfl

theorem cell20_488244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 2, 1, 4].length) (baseStart_488244 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_488244 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_488244 prefixEnd_488244 := by exact prefixLift 488244
  have htrace : WordTrace (prefixWord ++ tailWord_488244) baseStart_488244 baseEnd_488244 := by
    simpa [prefixWord, tailWord_488244, baseEnd_488244] using wordTrace_append hprefix tailTrace_488244
  have hstable : (prefixWord ++ tailWord_488244).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488244).length < 2 ^ (prefixWord ++ tailWord_488244).sum := by decide
  have hdescent : baseEnd_488244 < baseStart_488244 := by decide
  rcases family_descends (prefixWord ++ tailWord_488244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488248 : List Nat := [2, 1, 2, 1, 3, 2, 4, 1, 4]
def baseStart_488248 : Nat := 118140960795 + 488248 * 2 ^ 59
def prefixEnd_488248 : Nat := 4983230072969 + 3 ^ 40 * 488248 * 2
def baseEnd_488248 : Nat := 222849691196898632137417

theorem tailTrace_488248 : CollatzResearch.WordTrace tailWord_488248 prefixEnd_488248 222849691196898632137417 := by
  unfold tailWord_488248
  simp only [CollatzResearch.WordTrace]
  refine ⟨8903933767584178482400699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11871911690112237976534265 8903933767584178482400699)
  ·
    refine ⟨13355900651376267723601049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8903933767584178482400699 13355900651376267723601049)
    ·
      refine ⟨10016925488532200792700787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13355900651376267723601049 10016925488532200792700787)
      ·
        refine ⟨15025388232798301189051181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10016925488532200792700787 15025388232798301189051181)
        ·
          refine ⟨5634520587299362945894193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15025388232798301189051181 5634520587299362945894193)
          ·
            refine ⟨4225890440474522209420645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5634520587299362945894193 4225890440474522209420645)
            ·
              refine ⟨792354457588972914266371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4225890440474522209420645 792354457588972914266371)
              ·
                refine ⟨1188531686383459371399557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 792354457588972914266371 1188531686383459371399557)
                ·
                  refine ⟨222849691196898632137417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1188531686383459371399557 222849691196898632137417)
                  ·
                    rfl

theorem cell20_488248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 4, 1, 4].length) (baseStart_488248 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_488248 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_488248 prefixEnd_488248 := by exact prefixLift 488248
  have htrace : WordTrace (prefixWord ++ tailWord_488248) baseStart_488248 baseEnd_488248 := by
    simpa [prefixWord, tailWord_488248, baseEnd_488248] using wordTrace_append hprefix tailTrace_488248
  have hstable : (prefixWord ++ tailWord_488248).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488248).length < 2 ^ (prefixWord ++ tailWord_488248).sum := by decide
  have hdescent : baseEnd_488248 < baseStart_488248 := by decide
  rcases family_descends (prefixWord ++ tailWord_488248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488282 : List Nat := [3, 1, 1, 2, 1, 6, 1, 3, 2]
def baseStart_488282 : Nat := 118140960795 + 488282 * 2 ^ 59
def prefixEnd_488282 : Nat := 4983230072969 + 3 ^ 40 * 488282 * 2
def baseEnd_488282 : Nat := 222865209723345625003945

theorem tailTrace_488282 : CollatzResearch.WordTrace tailWord_488282 prefixEnd_488282 222865209723345625003945 := by
  unfold tailWord_488282
  simp only [CollatzResearch.WordTrace]
  refine ⟨4452276904261295192884775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11872738411363453847692733 4452276904261295192884775)
  ·
    refine ⟨6678415356391942789327163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4452276904261295192884775 6678415356391942789327163)
    ·
      refine ⟨10017623034587914183990745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6678415356391942789327163 10017623034587914183990745)
      ·
        refine ⟨7513217275940935637993059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10017623034587914183990745 7513217275940935637993059)
        ·
          refine ⟨11269825913911403456989589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7513217275940935637993059 11269825913911403456989589)
          ·
            refine ⟨528273089714597037046387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 11269825913911403456989589 528273089714597037046387)
            ·
              refine ⟨792409634571895555569581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 528273089714597037046387 792409634571895555569581)
              ·
                refine ⟨297153612964460833338593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 792409634571895555569581 297153612964460833338593)
                ·
                  refine ⟨222865209723345625003945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 297153612964460833338593 222865209723345625003945)
                  ·
                    rfl

theorem cell20_488282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 1, 3, 2].length) (baseStart_488282 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_488282 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_488282 prefixEnd_488282 := by exact prefixLift 488282
  have htrace : WordTrace (prefixWord ++ tailWord_488282) baseStart_488282 baseEnd_488282 := by
    simpa [prefixWord, tailWord_488282, baseEnd_488282] using wordTrace_append hprefix tailTrace_488282
  have hstable : (prefixWord ++ tailWord_488282).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488282).length < 2 ^ (prefixWord ++ tailWord_488282).sum := by decide
  have hdescent : baseEnd_488282 < baseStart_488282 := by decide
  rcases family_descends (prefixWord ++ tailWord_488282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488300 : List Nat := [2, 2, 1, 1, 4, 1, 1, 3, 5]
def baseStart_488300 : Nat := 118140960795 + 488300 * 2 ^ 59
def prefixEnd_488300 : Nat := 4983230072969 + 3 ^ 40 * 488300 * 2
def baseEnd_488300 : Nat := 222873425413817562403871

theorem tailTrace_488300 : CollatzResearch.WordTrace tailWord_488300 prefixEnd_488300 222873425413817562403871 := by
  unfold tailWord_488300
  simp only [CollatzResearch.WordTrace]
  refine ⟨8904882065489984922847177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11873176087319979897129569 8904882065489984922847177)
  ·
    refine ⟨6678661549117488692135383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8904882065489984922847177 6678661549117488692135383)
    ·
      refine ⟨10017992323676233038203075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6678661549117488692135383 10017992323676233038203075)
      ·
        refine ⟨15026988485514349557304613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10017992323676233038203075 15026988485514349557304613)
        ·
          refine ⟨2817560341033940541994615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15026988485514349557304613 2817560341033940541994615)
          ·
            refine ⟨4226340511550910812991923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2817560341033940541994615 4226340511550910812991923)
            ·
              refine ⟨6339510767326366219487885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4226340511550910812991923 6339510767326366219487885)
              ·
                refine ⟨2377316537747387332307957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6339510767326366219487885 2377316537747387332307957)
                ·
                  refine ⟨222873425413817562403871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2377316537747387332307957 222873425413817562403871)
                  ·
                    rfl

theorem cell20_488300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 5].length) (baseStart_488300 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_488300 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_488300 prefixEnd_488300 := by exact prefixLift 488300
  have htrace : WordTrace (prefixWord ++ tailWord_488300) baseStart_488300 baseEnd_488300 := by
    simpa [prefixWord, tailWord_488300, baseEnd_488300] using wordTrace_append hprefix tailTrace_488300
  have hstable : (prefixWord ++ tailWord_488300).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488300).length < 2 ^ (prefixWord ++ tailWord_488300).sum := by decide
  have hdescent : baseEnd_488300 < baseStart_488300 := by decide
  rcases family_descends (prefixWord ++ tailWord_488300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488310 : List Nat := [5, 1, 1, 3, 1, 1, 1, 7]
def baseStart_488310 : Nat := 118140960795 + 488310 * 2 ^ 59
def prefixEnd_488310 : Nat := 4983230072969 + 3 ^ 40 * 488310 * 2
def baseEnd_488310 : Nat := 74292663228767324023499

theorem tailTrace_488310 : CollatzResearch.WordTrace tailWord_488310 prefixEnd_488310 74292663228767324023499 := by
  unfold tailWord_488310
  simp only [CollatzResearch.WordTrace]
  refine ⟨1113133053808983847097399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11873419240629161035705589 1113133053808983847097399)
  ·
    refine ⟨1669699580713475770646099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1113133053808983847097399 1669699580713475770646099)
    ·
      refine ⟨2504549371070213655969149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1669699580713475770646099 2504549371070213655969149)
      ·
        refine ⟨939206014151330120988431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2504549371070213655969149 939206014151330120988431)
        ·
          refine ⟨1408809021226995181482647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 939206014151330120988431 1408809021226995181482647)
          ·
            refine ⟨2113213531840492772223971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1408809021226995181482647 2113213531840492772223971)
            ·
              refine ⟨3169820297760739158335957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2113213531840492772223971 3169820297760739158335957)
              ·
                refine ⟨74292663228767324023499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3169820297760739158335957 74292663228767324023499)
                ·
                  rfl

theorem cell20_488310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 7].length) (baseStart_488310 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_488310 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_488310 prefixEnd_488310 := by exact prefixLift 488310
  have htrace : WordTrace (prefixWord ++ tailWord_488310) baseStart_488310 baseEnd_488310 := by
    simpa [prefixWord, tailWord_488310, baseEnd_488310] using wordTrace_append hprefix tailTrace_488310
  have hstable : (prefixWord ++ tailWord_488310).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488310).length < 2 ^ (prefixWord ++ tailWord_488310).sum := by decide
  have hdescent : baseEnd_488310 < baseStart_488310 := by decide
  rcases family_descends (prefixWord ++ tailWord_488310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488348 : List Nat := [2, 2, 3, 3, 3, 7]
def baseStart_488348 : Nat := 118140960795 + 488348 * 2 ^ 59
def prefixEnd_488348 : Nat := 4983230072969 + 3 ^ 40 * 488348 * 2
def baseEnd_488348 : Nat := 8255382737842323289025

theorem tailTrace_488348 : CollatzResearch.WordTrace tailWord_488348 prefixEnd_488348 8255382737842323289025 := by
  unfold tailWord_488348
  simp only [CollatzResearch.WordTrace]
  refine ⟨8905757417403037021720849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11874343223204049362294465 8905757417403037021720849)
  ·
    refine ⟨6679318063052277766290637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8905757417403037021720849 6679318063052277766290637)
    ·
      refine ⟨2504744273644604162358989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6679318063052277766290637 2504744273644604162358989)
      ·
        refine ⟨939279102616726560884621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2504744273644604162358989 939279102616726560884621)
        ·
          refine ⟨352229663481272460331733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 939279102616726560884621 352229663481272460331733)
          ·
            refine ⟨8255382737842323289025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 352229663481272460331733 8255382737842323289025)
            ·
              rfl

theorem cell20_488348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 7].length) (baseStart_488348 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_488348 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_488348 prefixEnd_488348 := by exact prefixLift 488348
  have htrace : WordTrace (prefixWord ++ tailWord_488348) baseStart_488348 baseEnd_488348 := by
    simpa [prefixWord, tailWord_488348, baseEnd_488348] using wordTrace_append hprefix tailTrace_488348
  have hstable : (prefixWord ++ tailWord_488348).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488348).length < 2 ^ (prefixWord ++ tailWord_488348).sum := by decide
  have hdescent : baseEnd_488348 < baseStart_488348 := by decide
  rcases family_descends (prefixWord ++ tailWord_488348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488410 : List Nat := [3, 1, 1, 2, 4, 3, 1, 2, 3]
def baseStart_488410 : Nat := 118140960795 + 488410 * 2 ^ 59
def prefixEnd_488410 : Nat := 4983230072969 + 3 ^ 40 * 488410 * 2
def baseEnd_488410 : Nat := 222923632411146068736755

theorem tailTrace_488410 : CollatzResearch.WordTrace tailWord_488410 prefixEnd_488410 222923632411146068736755 := by
  unfold tailWord_488410
  simp only [CollatzResearch.WordTrace]
  refine ⟨4453444040145364658049671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11875850773720972421465789 4453444040145364658049671)
  ·
    refine ⟨6680166060218046987074507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4453444040145364658049671 6680166060218046987074507)
    ·
      refine ⟨10020249090327070480611761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6680166060218046987074507 10020249090327070480611761)
      ·
        refine ⟨7515186817745302860458821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10020249090327070480611761 7515186817745302860458821)
        ·
          refine ⟨1409097528327244286336029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7515186817745302860458821 1409097528327244286336029)
          ·
            refine ⟨528411573122716607376011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1409097528327244286336029 528411573122716607376011)
            ·
              refine ⟨792617359684074911064017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 528411573122716607376011 792617359684074911064017)
              ·
                refine ⟨594463019763056183298013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 792617359684074911064017 594463019763056183298013)
                ·
                  refine ⟨222923632411146068736755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 594463019763056183298013 222923632411146068736755)
                  ·
                    rfl

theorem cell20_488410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 1, 2, 3].length) (baseStart_488410 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_488410 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_488410 prefixEnd_488410 := by exact prefixLift 488410
  have htrace : WordTrace (prefixWord ++ tailWord_488410) baseStart_488410 baseEnd_488410 := by
    simpa [prefixWord, tailWord_488410, baseEnd_488410] using wordTrace_append hprefix tailTrace_488410
  have hstable : (prefixWord ++ tailWord_488410).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488410).length < 2 ^ (prefixWord ++ tailWord_488410).sum := by decide
  have hdescent : baseEnd_488410 < baseStart_488410 := by decide
  rcases family_descends (prefixWord ++ tailWord_488410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488437 : List Nat := [1, 3, 5, 2, 2, 1, 2, 4]
def baseStart_488437 : Nat := 118140960795 + 488437 * 2 ^ 59
def prefixEnd_488437 : Nat := 4983230072969 + 3 ^ 40 * 488437 * 2
def baseEnd_488437 : Nat := 74311985315617991612215

theorem tailTrace_488437 : CollatzResearch.WordTrace tailWord_488437 prefixEnd_488437 74311985315617991612215 := by
  unfold tailWord_488437
  simp only [CollatzResearch.WordTrace]
  refine ⟨17814760931483642243431565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11876507287655761495621043 17814760931483642243431565)
  ·
    refine ⟨6680535349306365841286837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17814760931483642243431565 6680535349306365841286837)
    ·
      refine ⟨626300188997471797620641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6680535349306365841286837 626300188997471797620641)
      ·
        refine ⟨469725141748103848215481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 626300188997471797620641 469725141748103848215481)
        ·
          refine ⟨352293856311077886161611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 469725141748103848215481 352293856311077886161611)
          ·
            refine ⟨528440784466616829242417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 352293856311077886161611 528440784466616829242417)
            ·
              refine ⟨396330588349962621931813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 528440784466616829242417 396330588349962621931813)
              ·
                refine ⟨74311985315617991612215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 396330588349962621931813 74311985315617991612215)
                ·
                  rfl

theorem cell20_488437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 2, 4].length) (baseStart_488437 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_488437 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_488437 prefixEnd_488437 := by exact prefixLift 488437
  have htrace : WordTrace (prefixWord ++ tailWord_488437) baseStart_488437 baseEnd_488437 := by
    simpa [prefixWord, tailWord_488437, baseEnd_488437] using wordTrace_append hprefix tailTrace_488437
  have hstable : (prefixWord ++ tailWord_488437).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488437).length < 2 ^ (prefixWord ++ tailWord_488437).sum := by decide
  have hdescent : baseEnd_488437 < baseStart_488437 := by decide
  rcases family_descends (prefixWord ++ tailWord_488437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488472 : List Nat := [2, 1, 2, 3, 2, 3, 3, 2, 2]
def baseStart_488472 : Nat := 118140960795 + 488472 * 2 ^ 59
def prefixEnd_488472 : Nat := 4983230072969 + 3 ^ 40 * 488472 * 2
def baseEnd_488472 : Nat := 222951930900549408669835

theorem tailTrace_488472 : CollatzResearch.WordTrace tailWord_488472 prefixEnd_488472 222951930900549408669835 := by
  unfold tailWord_488472
  simp only [CollatzResearch.WordTrace]
  refine ⟨8908018743178421610477835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11877358324237895480637113 8908018743178421610477835)
  ·
    refine ⟨13362028114767632415716753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8908018743178421610477835 13362028114767632415716753)
    ·
      refine ⟨10021521086075724311787565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13362028114767632415716753 10021521086075724311787565)
      ·
        refine ⟨3758070407278396616920337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10021521086075724311787565 3758070407278396616920337)
        ·
          refine ⟨2818552805458797462690253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3758070407278396616920337 2818552805458797462690253)
          ·
            refine ⟨1056957302047049048508845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2818552805458797462690253 1056957302047049048508845)
            ·
              refine ⟨396358988267643393190817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1056957302047049048508845 396358988267643393190817)
              ·
                refine ⟨297269241200732544893113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 396358988267643393190817 297269241200732544893113)
                ·
                  refine ⟨222951930900549408669835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 297269241200732544893113 222951930900549408669835)
                  ·
                    rfl

theorem cell20_488472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 3, 2, 2].length) (baseStart_488472 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_488472 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_488472 prefixEnd_488472 := by exact prefixLift 488472
  have htrace : WordTrace (prefixWord ++ tailWord_488472) baseStart_488472 baseEnd_488472 := by
    simpa [prefixWord, tailWord_488472, baseEnd_488472] using wordTrace_append hprefix tailTrace_488472
  have hstable : (prefixWord ++ tailWord_488472).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488472).length < 2 ^ (prefixWord ++ tailWord_488472).sum := by decide
  have hdescent : baseEnd_488472 < baseStart_488472 := by decide
  rcases family_descends (prefixWord ++ tailWord_488472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488483 : List Nat := [1, 1, 1, 4, 3, 3, 2, 5]
def baseStart_488483 : Nat := 118140960795 + 488483 * 2 ^ 59
def prefixEnd_488483 : Nat := 4983230072969 + 3 ^ 40 * 488483 * 2
def baseEnd_488483 : Nat := 74318983866760753101041

theorem tailTrace_488483 : CollatzResearch.WordTrace tailWord_488483 prefixEnd_488483 74318983866760753101041 := by
  unfold tailWord_488483
  simp only [CollatzResearch.WordTrace]
  refine ⟨17816438689316992099606103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11877625792877994733070735 17816438689316992099606103)
  ·
    refine ⟨26724658033975488149409155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17816438689316992099606103 26724658033975488149409155)
    ·
      refine ⟨40086987050963232224113733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26724658033975488149409155 40086987050963232224113733)
      ·
        refine ⟨7516310072055606042021325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40086987050963232224113733 7516310072055606042021325)
        ·
          refine ⟨2818616277020852265757997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7516310072055606042021325 2818616277020852265757997)
          ·
            refine ⟨1056981103882819599659249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2818616277020852265757997 1056981103882819599659249)
            ·
              refine ⟨792735827912114699744437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1056981103882819599659249 792735827912114699744437)
              ·
                refine ⟨74318983866760753101041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 792735827912114699744437 74318983866760753101041)
                ·
                  rfl

theorem cell20_488483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 2, 5].length) (baseStart_488483 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_488483 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_488483 prefixEnd_488483 := by exact prefixLift 488483
  have htrace : WordTrace (prefixWord ++ tailWord_488483) baseStart_488483 baseEnd_488483 := by
    simpa [prefixWord, tailWord_488483, baseEnd_488483] using wordTrace_append hprefix tailTrace_488483
  have hstable : (prefixWord ++ tailWord_488483).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488483).length < 2 ^ (prefixWord ++ tailWord_488483).sum := by decide
  have hdescent : baseEnd_488483 < baseStart_488483 := by decide
  rcases family_descends (prefixWord ++ tailWord_488483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488497 : List Nat := [1, 2, 2, 3, 1, 2, 2, 1, 6]
def baseStart_488497 : Nat := 118140960795 + 488497 * 2 ^ 59
def prefixEnd_488497 : Nat := 4983230072969 + 3 ^ 40 * 488497 * 2
def baseEnd_488497 : Nat := 222963341581760432836399

theorem tailTrace_488497 : CollatzResearch.WordTrace tailWord_488497 prefixEnd_488497 222963341581760432836399 := by
  unfold tailWord_488497
  simp only [CollatzResearch.WordTrace]
  refine ⟨17816949311266272490615745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11877966207510848327077163 17816949311266272490615745)
  ·
    refine ⟨13362711983449704367961809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17816949311266272490615745 13362711983449704367961809)
    ·
      refine ⟨10022033987587278275971357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13362711983449704367961809 10022033987587278275971357)
      ·
        refine ⟨3758262745345229353489259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10022033987587278275971357 3758262745345229353489259)
        ·
          refine ⟨5637394118017844030233889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3758262745345229353489259 5637394118017844030233889)
          ·
            refine ⟨4228045588513383022675417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5637394118017844030233889 4228045588513383022675417)
            ·
              refine ⟨3171034191385037267006563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4228045588513383022675417 3171034191385037267006563)
              ·
                refine ⟨4756551287077555900509845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3171034191385037267006563 4756551287077555900509845)
                ·
                  refine ⟨222963341581760432836399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4756551287077555900509845 222963341581760432836399)
                  ·
                    rfl

theorem cell20_488497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 1, 6].length) (baseStart_488497 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_488497 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_488497 prefixEnd_488497 := by exact prefixLift 488497
  have htrace : WordTrace (prefixWord ++ tailWord_488497) baseStart_488497 baseEnd_488497 := by
    simpa [prefixWord, tailWord_488497, baseEnd_488497] using wordTrace_append hprefix tailTrace_488497
  have hstable : (prefixWord ++ tailWord_488497).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488497).length < 2 ^ (prefixWord ++ tailWord_488497).sum := by decide
  have hdescent : baseEnd_488497 < baseStart_488497 := by decide
  rcases family_descends (prefixWord ++ tailWord_488497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488500 : List Nat := [2, 5, 1, 2, 1, 1, 2, 6]
def baseStart_488500 : Nat := 118140960795 + 488500 * 2 ^ 59
def prefixEnd_488500 : Nat := 4983230072969 + 3 ^ 40 * 488500 * 2
def baseEnd_488500 : Nat := 74321570287835251912129

theorem tailTrace_488500 : CollatzResearch.WordTrace tailWord_488500 prefixEnd_488500 74321570287835251912129 := by
  unfold tailWord_488500
  simp only [CollatzResearch.WordTrace]
  refine ⟨8908529365127702001487477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11878039153503602668649969 8908529365127702001487477)
  ·
    refine ⟨835174627980722062639451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8908529365127702001487477 835174627980722062639451)
    ·
      refine ⟨1252761941971083093959177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 835174627980722062639451 1252761941971083093959177)
      ·
        refine ⟨939571456478312320469383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1252761941971083093959177 939571456478312320469383)
        ·
          refine ⟨1409357184717468480704075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 939571456478312320469383 1409357184717468480704075)
          ·
            refine ⟨2114035777076202721056113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1409357184717468480704075 2114035777076202721056113)
            ·
              refine ⟨1585526832807152040792085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2114035777076202721056113 1585526832807152040792085)
              ·
                refine ⟨74321570287835251912129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1585526832807152040792085 74321570287835251912129)
                ·
                  rfl

theorem cell20_488500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 6].length) (baseStart_488500 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_488500 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_488500 prefixEnd_488500 := by exact prefixLift 488500
  have htrace : WordTrace (prefixWord ++ tailWord_488500) baseStart_488500 baseEnd_488500 := by
    simpa [prefixWord, tailWord_488500, baseEnd_488500] using wordTrace_append hprefix tailTrace_488500
  have hstable : (prefixWord ++ tailWord_488500).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488500).length < 2 ^ (prefixWord ++ tailWord_488500).sum := by decide
  have hdescent : baseEnd_488500 < baseStart_488500 := by decide
  rcases family_descends (prefixWord ++ tailWord_488500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488534 : List Nat := [5, 2, 2, 1, 2, 2, 1, 5]
def baseStart_488534 : Nat := 118140960795 + 488534 * 2 ^ 59
def prefixEnd_488534 : Nat := 4983230072969 + 3 ^ 40 * 488534 * 2
def baseEnd_488534 : Nat := 74326743129984249534305

theorem tailTrace_488534 : CollatzResearch.WordTrace tailWord_488534 prefixEnd_488534 74326743129984249534305 := by
  unfold tailWord_488534
  simp only [CollatzResearch.WordTrace]
  refine ⟨1113643675758264238107041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11878865874754818539808437 1113643675758264238107041)
  ·
    refine ⟨835232756818698178580281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1113643675758264238107041 835232756818698178580281)
    ·
      refine ⟨626424567614023633935211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 835232756818698178580281 626424567614023633935211)
      ·
        refine ⟨939636851421035450902817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 626424567614023633935211 939636851421035450902817)
        ·
          refine ⟨704727638565776588177113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 939636851421035450902817 704727638565776588177113)
          ·
            refine ⟨528545728924332441132835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 704727638565776588177113 528545728924332441132835)
            ·
              refine ⟨792818593386498661699253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 528545728924332441132835 792818593386498661699253)
              ·
                refine ⟨74326743129984249534305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 792818593386498661699253 74326743129984249534305)
                ·
                  rfl

theorem cell20_488534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 1, 5].length) (baseStart_488534 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_488534 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_488534 prefixEnd_488534 := by exact prefixLift 488534
  have htrace : WordTrace (prefixWord ++ tailWord_488534) baseStart_488534 baseEnd_488534 := by
    simpa [prefixWord, tailWord_488534, baseEnd_488534] using wordTrace_append hprefix tailTrace_488534
  have hstable : (prefixWord ++ tailWord_488534).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488534).length < 2 ^ (prefixWord ++ tailWord_488534).sum := by decide
  have hdescent : baseEnd_488534 < baseStart_488534 := by decide
  rcases family_descends (prefixWord ++ tailWord_488534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488535 : List Nat := [1, 1, 3, 2, 2, 1, 1, 5, 4]
def baseStart_488535 : Nat := 118140960795 + 488535 * 2 ^ 59
def prefixEnd_488535 : Nat := 4983230072969 + 3 ^ 40 * 488535 * 2
def baseEnd_488535 : Nat := 222980685817201189569577

theorem tailTrace_488535 : CollatzResearch.WordTrace tailWord_488535 prefixEnd_488535 222980685817201189569577 := by
  unfold tailWord_488535
  simp only [CollatzResearch.WordTrace]
  refine ⟨17818335285128604980499059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11878890190085736653666039 17818335285128604980499059)
  ·
    refine ⟨26727502927692907470748589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17818335285128604980499059 26727502927692907470748589)
    ·
      refine ⟨10022813597884840301530721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26727502927692907470748589 10022813597884840301530721)
      ·
        refine ⟨7517110198413630226148041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10022813597884840301530721 7517110198413630226148041)
        ·
          refine ⟨5637832648810222669611031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7517110198413630226148041 5637832648810222669611031)
          ·
            refine ⟨8456748973215334004416547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5637832648810222669611031 8456748973215334004416547)
            ·
              refine ⟨12685123459823001006624821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8456748973215334004416547 12685123459823001006624821)
              ·
                refine ⟨1189230324358406344371077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12685123459823001006624821 1189230324358406344371077)
                ·
                  refine ⟨222980685817201189569577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1189230324358406344371077 222980685817201189569577)
                  ·
                    rfl

theorem cell20_488535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 5, 4].length) (baseStart_488535 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_488535 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_488535 prefixEnd_488535 := by exact prefixLift 488535
  have htrace : WordTrace (prefixWord ++ tailWord_488535) baseStart_488535 baseEnd_488535 := by
    simpa [prefixWord, tailWord_488535, baseEnd_488535] using wordTrace_append hprefix tailTrace_488535
  have hstable : (prefixWord ++ tailWord_488535).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488535).length < 2 ^ (prefixWord ++ tailWord_488535).sum := by decide
  have hdescent : baseEnd_488535 < baseStart_488535 := by decide
  rcases family_descends (prefixWord ++ tailWord_488535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488559 : List Nat := [1, 1, 2, 1, 3, 3, 5, 4]
def baseStart_488559 : Nat := 118140960795 + 488559 * 2 ^ 59
def prefixEnd_488559 : Nat := 4983230072969 + 3 ^ 40 * 488559 * 2
def baseEnd_488559 : Nat := 74330546690387924256493

theorem tailTrace_488559 : CollatzResearch.WordTrace tailWord_488559 prefixEnd_488559 74330546690387924256493 := by
  unfold tailWord_488559
  simp only [CollatzResearch.WordTrace]
  refine ⟨17819210637041657079372731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11879473758027771386248487 17819210637041657079372731)
  ·
    refine ⟨26728815955562485619059097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17819210637041657079372731 26728815955562485619059097)
    ·
      refine ⟨20046611966671864214294323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26728815955562485619059097 20046611966671864214294323)
      ·
        refine ⟨30069917950007796321441485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20046611966671864214294323 30069917950007796321441485)
        ·
          refine ⟨11276219231252923620540557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30069917950007796321441485 11276219231252923620540557)
          ·
            refine ⟨4228582211719846357702709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11276219231252923620540557 4228582211719846357702709)
            ·
              refine ⟨396429582348735596034629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4228582211719846357702709 396429582348735596034629)
              ·
                refine ⟨74330546690387924256493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 396429582348735596034629 74330546690387924256493)
                ·
                  rfl

theorem cell20_488559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 5, 4].length) (baseStart_488559 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_488559 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_488559 prefixEnd_488559 := by exact prefixLift 488559
  have htrace : WordTrace (prefixWord ++ tailWord_488559) baseStart_488559 baseEnd_488559 := by
    simpa [prefixWord, tailWord_488559, baseEnd_488559] using wordTrace_append hprefix tailTrace_488559
  have hstable : (prefixWord ++ tailWord_488559).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488559).length < 2 ^ (prefixWord ++ tailWord_488559).sum := by decide
  have hdescent : baseEnd_488559 < baseStart_488559 := by decide
  rcases family_descends (prefixWord ++ tailWord_488559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488565 : List Nat := [1, 3, 4, 3, 1, 1, 2, 3, 2]
def baseStart_488565 : Nat := 118140960795 + 488565 * 2 ^ 59
def prefixEnd_488565 : Nat := 4983230072969 + 3 ^ 40 * 488565 * 2
def baseEnd_488565 : Nat := 222994378634654418569455

theorem tailTrace_488565 : CollatzResearch.WordTrace tailWord_488565 prefixEnd_488565 222994378634654418569455 := by
  unfold tailWord_488565
  simp only [CollatzResearch.WordTrace]
  refine ⟨17819429475019920104091149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11879619650013280069394099 17819429475019920104091149)
  ·
    refine ⟨6682286053132470039034181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17819429475019920104091149 6682286053132470039034181)
    ·
      refine ⟨1252928634962338132318909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6682286053132470039034181 1252928634962338132318909)
      ·
        refine ⟨469848238110876799619591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1252928634962338132318909 469848238110876799619591)
        ·
          refine ⟨704772357166315199429387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 469848238110876799619591 704772357166315199429387)
          ·
            refine ⟨1057158535749472799144081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 704772357166315199429387 1057158535749472799144081)
            ·
              refine ⟨792868901812104599358061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1057158535749472799144081 792868901812104599358061)
              ·
                refine ⟨297325838179539224759273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 792868901812104599358061 297325838179539224759273)
                ·
                  refine ⟨222994378634654418569455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 297325838179539224759273 222994378634654418569455)
                  ·
                    rfl

theorem cell20_488565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 2, 3, 2].length) (baseStart_488565 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_488565 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_488565 prefixEnd_488565 := by exact prefixLift 488565
  have htrace : WordTrace (prefixWord ++ tailWord_488565) baseStart_488565 baseEnd_488565 := by
    simpa [prefixWord, tailWord_488565, baseEnd_488565] using wordTrace_append hprefix tailTrace_488565
  have hstable : (prefixWord ++ tailWord_488565).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488565).length < 2 ^ (prefixWord ++ tailWord_488565).sum := by decide
  have hdescent : baseEnd_488565 < baseStart_488565 := by decide
  rcases family_descends (prefixWord ++ tailWord_488565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488573 : List Nat := [1, 4, 1, 1, 3, 1, 1, 2, 6]
def baseStart_488573 : Nat := 118140960795 + 488573 * 2 ^ 59
def prefixEnd_488573 : Nat := 4983230072969 + 3 ^ 40 * 488573 * 2
def baseEnd_488573 : Nat := 222998030052641946302755

theorem tailTrace_488573 : CollatzResearch.WordTrace tailWord_488573 prefixEnd_488573 222998030052641946302755 := by
  unfold tailWord_488573
  simp only [CollatzResearch.WordTrace]
  refine ⟨17819721258990937470382373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11879814172660624980254915 17819721258990937470382373)
  ·
    refine ⟨3341197736060800775696695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17819721258990937470382373 3341197736060800775696695)
    ·
      refine ⟨5011796604091201163545043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3341197736060800775696695 5011796604091201163545043)
      ·
        refine ⟨7517694906136801745317565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5011796604091201163545043 7517694906136801745317565)
        ·
          refine ⟨2819135589801300654494087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7517694906136801745317565 2819135589801300654494087)
          ·
            refine ⟨4228703384701950981741131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2819135589801300654494087 4228703384701950981741131)
            ·
              refine ⟨6343055077052926472611697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4228703384701950981741131 6343055077052926472611697)
              ·
                refine ⟨4757291307789694854458773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6343055077052926472611697 4757291307789694854458773)
                ·
                  refine ⟨222998030052641946302755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4757291307789694854458773 222998030052641946302755)
                  ·
                    rfl

theorem cell20_488573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 2, 6].length) (baseStart_488573 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_488573 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_488573 prefixEnd_488573 := by exact prefixLift 488573
  have htrace : WordTrace (prefixWord ++ tailWord_488573) baseStart_488573 baseEnd_488573 := by
    simpa [prefixWord, tailWord_488573, baseEnd_488573] using wordTrace_append hprefix tailTrace_488573
  have hstable : (prefixWord ++ tailWord_488573).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488573).length < 2 ^ (prefixWord ++ tailWord_488573).sum := by decide
  have hdescent : baseEnd_488573 < baseStart_488573 := by decide
  rcases family_descends (prefixWord ++ tailWord_488573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488590 : List Nat := [4, 1, 1, 3, 2, 1, 1, 3, 4]
def baseStart_488590 : Nat := 118140960795 + 488590 * 2 ^ 59
def prefixEnd_488590 : Nat := 4983230072969 + 3 ^ 40 * 488590 * 2
def baseEnd_488590 : Nat := 223005789315865442736019

theorem tailTrace_488590 : CollatzResearch.WordTrace tailWord_488590 prefixEnd_488590 223005789315865442736019 := by
  unfold tailWord_488590
  simp only [CollatzResearch.WordTrace]
  refine ⟨2227542662491168671718903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11880227533286232915834149 2227542662491168671718903)
  ·
    refine ⟨3341313993736753007578355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2227542662491168671718903 3341313993736753007578355)
    ·
      refine ⟨5011970990605129511367533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3341313993736753007578355 5011970990605129511367533)
      ·
        refine ⟨1879489121476923566762825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5011970990605129511367533 1879489121476923566762825)
        ·
          refine ⟨1409616841107692675072119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1879489121476923566762825 1409616841107692675072119)
          ·
            refine ⟨2114425261661539012608179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1409616841107692675072119 2114425261661539012608179)
            ·
              refine ⟨3171637892492308518912269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2114425261661539012608179 3171637892492308518912269)
              ·
                refine ⟨1189364209684615694592101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3171637892492308518912269 1189364209684615694592101)
                ·
                  refine ⟨223005789315865442736019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1189364209684615694592101 223005789315865442736019)
                  ·
                    rfl

theorem cell20_488590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 3, 4].length) (baseStart_488590 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_488590 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_488590 prefixEnd_488590 := by exact prefixLift 488590
  have htrace : WordTrace (prefixWord ++ tailWord_488590) baseStart_488590 baseEnd_488590 := by
    simpa [prefixWord, tailWord_488590, baseEnd_488590] using wordTrace_append hprefix tailTrace_488590
  have hstable : (prefixWord ++ tailWord_488590).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488590).length < 2 ^ (prefixWord ++ tailWord_488590).sum := by decide
  have hdescent : baseEnd_488590 < baseStart_488590 := by decide
  rcases family_descends (prefixWord ++ tailWord_488590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488600 : List Nat := [2, 1, 2, 4, 2, 2, 3, 1, 3]
def baseStart_488600 : Nat := 118140960795 + 488600 * 2 ^ 59
def prefixEnd_488600 : Nat := 4983230072969 + 3 ^ 40 * 488600 * 2
def baseEnd_488600 : Nat := 223010353588349852402645

theorem tailTrace_488600 : CollatzResearch.WordTrace tailWord_488600 prefixEnd_488600 223010353588349852402645 := by
  unfold tailWord_488600
  simp only [CollatzResearch.WordTrace]
  refine ⟨8910353014946560540807627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11880470686595414054410169 8910353014946560540807627)
  ·
    refine ⟨13365529522419840811211441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8910353014946560540807627 13365529522419840811211441)
    ·
      refine ⟨10024147141814880608408581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13365529522419840811211441 10024147141814880608408581)
      ·
        refine ⟨1879527589090290114076609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10024147141814880608408581 1879527589090290114076609)
        ·
          refine ⟨1409645691817717585557457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1879527589090290114076609 1409645691817717585557457)
          ·
            refine ⟨1057234268863288189168093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1409645691817717585557457 1057234268863288189168093)
            ·
              refine ⟨396462850823733070938035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1057234268863288189168093 396462850823733070938035)
              ·
                refine ⟨594694276235599606407053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 396462850823733070938035 594694276235599606407053)
                ·
                  refine ⟨223010353588349852402645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 594694276235599606407053 223010353588349852402645)
                  ·
                    rfl

theorem cell20_488600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 3, 1, 3].length) (baseStart_488600 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_488600 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_488600 prefixEnd_488600 := by exact prefixLift 488600
  have htrace : WordTrace (prefixWord ++ tailWord_488600) baseStart_488600 baseEnd_488600 := by
    simpa [prefixWord, tailWord_488600, baseEnd_488600] using wordTrace_append hprefix tailTrace_488600
  have hstable : (prefixWord ++ tailWord_488600).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488600).length < 2 ^ (prefixWord ++ tailWord_488600).sum := by decide
  have hdescent : baseEnd_488600 < baseStart_488600 := by decide
  rcases family_descends (prefixWord ++ tailWord_488600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488610 : List Nat := [3, 3, 1, 3, 3, 1, 2, 4]
def baseStart_488610 : Nat := 118140960795 + 488610 * 2 ^ 59
def prefixEnd_488610 : Nat := 4983230072969 + 3 ^ 40 * 488610 * 2
def baseEnd_488610 : Nat := 74338305953611420689757

theorem tailTrace_488610 : CollatzResearch.WordTrace tailWord_488610 prefixEnd_488610 74338305953611420689757 := by
  unfold tailWord_488610
  simp only [CollatzResearch.WordTrace]
  refine ⟨4455267689964223197369821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11880713839904595192986189 4455267689964223197369821)
  ·
    refine ⟨1670725383736583699013683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4455267689964223197369821 1670725383736583699013683)
    ·
      refine ⟨2506088075604875548520525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1670725383736583699013683 2506088075604875548520525)
      ·
        refine ⟨939783028351828330695197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2506088075604875548520525 939783028351828330695197)
        ·
          refine ⟨352418635631935624010699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 939783028351828330695197 352418635631935624010699)
          ·
            refine ⟨528627953447903436016049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 352418635631935624010699 528627953447903436016049)
            ·
              refine ⟨396470965085927577012037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 528627953447903436016049 396470965085927577012037)
              ·
                refine ⟨74338305953611420689757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 396470965085927577012037 74338305953611420689757)
                ·
                  rfl

theorem cell20_488610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 2, 4].length) (baseStart_488610 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_488610 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_488610 prefixEnd_488610 := by exact prefixLift 488610
  have htrace : WordTrace (prefixWord ++ tailWord_488610) baseStart_488610 baseEnd_488610 := by
    simpa [prefixWord, tailWord_488610, baseEnd_488610] using wordTrace_append hprefix tailTrace_488610
  have hstable : (prefixWord ++ tailWord_488610).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488610).length < 2 ^ (prefixWord ++ tailWord_488610).sum := by decide
  have hdescent : baseEnd_488610 < baseStart_488610 := by decide
  rcases family_descends (prefixWord ++ tailWord_488610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488641 : List Nat := [1, 2, 6, 1, 1, 2, 3, 2, 2]
def baseStart_488641 : Nat := 118140960795 + 488641 * 2 ^ 59
def prefixEnd_488641 : Nat := 4983230072969 + 3 ^ 40 * 488641 * 2
def baseEnd_488641 : Nat := 223029067105535932035811

theorem tailTrace_488641 : CollatzResearch.WordTrace tailWord_488641 prefixEnd_488641 223029067105535932035811 := by
  unfold tailWord_488641
  simp only [CollatzResearch.WordTrace]
  refine ⟨17822201422744585083857777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11881467615163056722571851 17822201422744585083857777)
  ·
    refine ⟨13366651067058438812893333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17822201422744585083857777 13366651067058438812893333)
    ·
      refine ⟨626561768768364319354375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 13366651067058438812893333 626561768768364319354375)
      ·
        refine ⟨939842653152546479031563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 626561768768364319354375 939842653152546479031563)
        ·
          refine ⟨1409763979728819718547345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 939842653152546479031563 1409763979728819718547345)
          ·
            refine ⟨1057322984796614788910509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1409763979728819718547345 1057322984796614788910509)
            ·
              refine ⟨396496119298730545841441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1057322984796614788910509 396496119298730545841441)
              ·
                refine ⟨297372089474047909381081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 396496119298730545841441 297372089474047909381081)
                ·
                  refine ⟨223029067105535932035811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 297372089474047909381081 223029067105535932035811)
                  ·
                    rfl

theorem cell20_488641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 3, 2, 2].length) (baseStart_488641 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_488641 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_488641 prefixEnd_488641 := by exact prefixLift 488641
  have htrace : WordTrace (prefixWord ++ tailWord_488641) baseStart_488641 baseEnd_488641 := by
    simpa [prefixWord, tailWord_488641, baseEnd_488641] using wordTrace_append hprefix tailTrace_488641
  have hstable : (prefixWord ++ tailWord_488641).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488641).length < 2 ^ (prefixWord ++ tailWord_488641).sum := by decide
  have hdescent : baseEnd_488641 < baseStart_488641 := by decide
  rcases family_descends (prefixWord ++ tailWord_488641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488692 : List Nat := [2, 6, 1, 2, 2, 1, 2, 2, 2]
def baseStart_488692 : Nat := 118140960795 + 488692 * 2 ^ 59
def prefixEnd_488692 : Nat := 4983230072969 + 3 ^ 40 * 488692 * 2
def baseEnd_488692 : Nat := 223052344895206421335603

theorem tailTrace_488692 : CollatzResearch.WordTrace tailWord_488692 prefixEnd_488692 223052344895206421335603 := by
  unfold tailWord_488692
  simp only [CollatzResearch.WordTrace]
  refine ⟨8912030772779910396982165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11882707697039880529309553 8912030772779910396982165)
  ·
    refine ⟨417751442474058299858539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 8912030772779910396982165 417751442474058299858539)
    ·
      refine ⟨626627163711087449787809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 417751442474058299858539 626627163711087449787809)
      ·
        refine ⟨469970372783315587340857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 626627163711087449787809 469970372783315587340857)
        ·
          refine ⟨352477779587486690505643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 469970372783315587340857 352477779587486690505643)
          ·
            refine ⟨528716669381230035758465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 352477779587486690505643 528716669381230035758465)
            ·
              refine ⟨396537502035922526818849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 528716669381230035758465 396537502035922526818849)
              ·
                refine ⟨297403126526941895114137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 396537502035922526818849 297403126526941895114137)
                ·
                  refine ⟨223052344895206421335603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 297403126526941895114137 223052344895206421335603)
                  ·
                    rfl

theorem cell20_488692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 2, 2, 2].length) (baseStart_488692 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_488692 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_488692 prefixEnd_488692 := by exact prefixLift 488692
  have htrace : WordTrace (prefixWord ++ tailWord_488692) baseStart_488692 baseEnd_488692 := by
    simpa [prefixWord, tailWord_488692, baseEnd_488692] using wordTrace_append hprefix tailTrace_488692
  have hstable : (prefixWord ++ tailWord_488692).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488692).length < 2 ^ (prefixWord ++ tailWord_488692).sum := by decide
  have hdescent : baseEnd_488692 < baseStart_488692 := by decide
  rcases family_descends (prefixWord ++ tailWord_488692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488732 : List Nat := [2, 2, 3, 1, 1, 1, 2, 8]
def baseStart_488732 : Nat := 118140960795 + 488732 * 2 ^ 59
def prefixEnd_488732 : Nat := 4983230072969 + 3 ^ 40 * 488732 * 2
def baseEnd_488732 : Nat := 74356867328381353334035

theorem tailTrace_488732 : CollatzResearch.WordTrace tailWord_488732 prefixEnd_488732 74356867328381353334035 := by
  unfold tailWord_488732
  simp only [CollatzResearch.WordTrace]
  refine ⟨8912760232707453812710225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11883680310276605083613633 8912760232707453812710225)
  ·
    refine ⟨6684570174530590359532669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8912760232707453812710225 6684570174530590359532669)
    ·
      refine ⟨2506713815448971384824751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6684570174530590359532669 2506713815448971384824751)
      ·
        refine ⟨3760070723173457077237127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2506713815448971384824751 3760070723173457077237127)
        ·
          refine ⟨5640106084760185615855691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3760070723173457077237127 5640106084760185615855691)
          ·
            refine ⟨8460159127140278423783537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5640106084760185615855691 8460159127140278423783537)
            ·
              refine ⟨6345119345355208817837653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8460159127140278423783537 6345119345355208817837653)
              ·
                refine ⟨74356867328381353334035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6345119345355208817837653 74356867328381353334035)
                ·
                  rfl

theorem cell20_488732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 8].length) (baseStart_488732 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_488732 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_488732 prefixEnd_488732 := by exact prefixLift 488732
  have htrace : WordTrace (prefixWord ++ tailWord_488732) baseStart_488732 baseEnd_488732 := by
    simpa [prefixWord, tailWord_488732, baseEnd_488732] using wordTrace_append hprefix tailTrace_488732
  have hstable : (prefixWord ++ tailWord_488732).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488732).length < 2 ^ (prefixWord ++ tailWord_488732).sum := by decide
  have hdescent : baseEnd_488732 < baseStart_488732 := by decide
  rcases family_descends (prefixWord ++ tailWord_488732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488738 : List Nat := [3, 3, 1, 1, 4, 1, 2, 3, 2]
def baseStart_488738 : Nat := 118140960795 + 488738 * 2 ^ 59
def prefixEnd_488738 : Nat := 4983230072969 + 3 ^ 40 * 488738 * 2
def baseEnd_488738 : Nat := 223073340548634705802081

theorem tailTrace_488738 : CollatzResearch.WordTrace tailWord_488738 prefixEnd_488738 223073340548634705802081 := by
  unfold tailWord_488738
  simp only [CollatzResearch.WordTrace]
  refine ⟨4456434825848292662534717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11883826202262113766759245 4456434825848292662534717)
  ·
    refine ⟨1671163059693109748450519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4456434825848292662534717 1671163059693109748450519)
    ·
      refine ⟨2506744589539664622675779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1671163059693109748450519 2506744589539664622675779)
      ·
        refine ⟨3760116884309496934013669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2506744589539664622675779 3760116884309496934013669)
        ·
          refine ⟨705021915808030675127563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3760116884309496934013669 705021915808030675127563)
          ·
            refine ⟨1057532873712046012691345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 705021915808030675127563 1057532873712046012691345)
            ·
              refine ⟨793149655284034509518509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1057532873712046012691345 793149655284034509518509)
              ·
                refine ⟨297431120731512941069441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 793149655284034509518509 297431120731512941069441)
                ·
                  refine ⟨223073340548634705802081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 297431120731512941069441 223073340548634705802081)
                  ·
                    rfl

theorem cell20_488738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 2, 3, 2].length) (baseStart_488738 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_488738 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_488738 prefixEnd_488738 := by exact prefixLift 488738
  have htrace : WordTrace (prefixWord ++ tailWord_488738) baseStart_488738 baseEnd_488738 := by
    simpa [prefixWord, tailWord_488738, baseEnd_488738] using wordTrace_append hprefix tailTrace_488738
  have hstable : (prefixWord ++ tailWord_488738).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488738).length < 2 ^ (prefixWord ++ tailWord_488738).sum := by decide
  have hdescent : baseEnd_488738 < baseStart_488738 := by decide
  rcases family_descends (prefixWord ++ tailWord_488738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488814 : List Nat := [4, 1, 2, 4, 1, 2, 1, 1, 4]
def baseStart_488814 : Nat := 118140960795 + 488814 * 2 ^ 59
def prefixEnd_488814 : Nat := 4983230072969 + 3 ^ 40 * 488814 * 2
def baseEnd_488814 : Nat := 223108029019516219268437

theorem tailTrace_488814 : CollatzResearch.WordTrace tailWord_488814 prefixEnd_488814 223108029019516219268437 := by
  unfold tailWord_488814
  simp only [CollatzResearch.WordTrace]
  refine ⟨2228563906389729453738187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11885674167411890419936997 2228563906389729453738187)
  ·
    refine ⟨3342845859584594180607281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2228563906389729453738187 3342845859584594180607281)
    ·
      refine ⟨2507134394688445635455461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3342845859584594180607281 2507134394688445635455461)
      ·
        refine ⟨470087699004083556647899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2507134394688445635455461 470087699004083556647899)
        ·
          refine ⟨705131548506125334971849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 470087699004083556647899 705131548506125334971849)
          ·
            refine ⟨528848661379594001228887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 705131548506125334971849 528848661379594001228887)
            ·
              refine ⟨793272992069391001843331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 528848661379594001228887 793272992069391001843331)
              ·
                refine ⟨1189909488104086502764997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 793272992069391001843331 1189909488104086502764997)
                ·
                  refine ⟨223108029019516219268437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1189909488104086502764997 223108029019516219268437)
                  ·
                    rfl

theorem cell20_488814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 1, 1, 4].length) (baseStart_488814 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_488814 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_488814 prefixEnd_488814 := by exact prefixLift 488814
  have htrace : WordTrace (prefixWord ++ tailWord_488814) baseStart_488814 baseEnd_488814 := by
    simpa [prefixWord, tailWord_488814, baseEnd_488814] using wordTrace_append hprefix tailTrace_488814
  have hstable : (prefixWord ++ tailWord_488814).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488814).length < 2 ^ (prefixWord ++ tailWord_488814).sum := by decide
  have hdescent : baseEnd_488814 < baseStart_488814 := by decide
  rcases family_descends (prefixWord ++ tailWord_488814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488815 : List Nat := [1, 1, 2, 1, 3, 1, 3, 3, 5]
def baseStart_488815 : Nat := 118140960795 + 488815 * 2 ^ 59
def prefixEnd_488815 : Nat := 4983230072969 + 3 ^ 40 * 488815 * 2
def baseEnd_488815 : Nat := 223108485446764660235099

theorem tailTrace_488815 : CollatzResearch.WordTrace tailWord_488815 prefixEnd_488815 223108485446764660235099 := by
  unfold tailWord_488815
  simp only [CollatzResearch.WordTrace]
  refine ⟨17828547724114212800691899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11885698482742808533794599 17828547724114212800691899)
  ·
    refine ⟨26742821586171319201037849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17828547724114212800691899 26742821586171319201037849)
    ·
      refine ⟨20057116189628489400778387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26742821586171319201037849 20057116189628489400778387)
      ·
        refine ⟨30085674284442734101167581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20057116189628489400778387 30085674284442734101167581)
        ·
          refine ⟨11282127856666025287937843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30085674284442734101167581 11282127856666025287937843)
          ·
            refine ⟨16923191784999037931906765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11282127856666025287937843 16923191784999037931906765)
            ·
              refine ⟨6346196919374639224465037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16923191784999037931906765 6346196919374639224465037)
              ·
                refine ⟨2379823844765489709174389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6346196919374639224465037 2379823844765489709174389)
                ·
                  refine ⟨223108485446764660235099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2379823844765489709174389 223108485446764660235099)
                  ·
                    rfl

theorem cell20_488815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 3, 5].length) (baseStart_488815 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_488815 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_488815 prefixEnd_488815 := by exact prefixLift 488815
  have htrace : WordTrace (prefixWord ++ tailWord_488815) baseStart_488815 baseEnd_488815 := by
    simpa [prefixWord, tailWord_488815, baseEnd_488815] using wordTrace_append hprefix tailTrace_488815
  have hstable : (prefixWord ++ tailWord_488815).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488815).length < 2 ^ (prefixWord ++ tailWord_488815).sum := by decide
  have hdescent : baseEnd_488815 < baseStart_488815 := by decide
  rcases family_descends (prefixWord ++ tailWord_488815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488853 : List Nat := [1, 3, 2, 1, 1, 2, 2, 1, 7]
def baseStart_488853 : Nat := 118140960795 + 488853 * 2 ^ 59
def prefixEnd_488853 : Nat := 4983230072969 + 3 ^ 40 * 488853 * 2
def baseEnd_488853 : Nat := 223125829682205416968277

theorem tailTrace_488853 : CollatzResearch.WordTrace tailWord_488853 prefixEnd_488853 223125829682205416968277 := by
  unfold tailWord_488853
  simp only [CollatzResearch.WordTrace]
  refine ⟨17829933697976545290575213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11886622465317696860383475 17829933697976545290575213)
  ·
    refine ⟨6686225136741204483965705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17829933697976545290575213 6686225136741204483965705)
    ·
      refine ⟨5014668852555903362974279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6686225136741204483965705 5014668852555903362974279)
      ·
        refine ⟨7522003278833855044461419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5014668852555903362974279 7522003278833855044461419)
        ·
          refine ⟨11283004918250782566692129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7522003278833855044461419 11283004918250782566692129)
          ·
            refine ⟨8462253688688086925019097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11283004918250782566692129 8462253688688086925019097)
            ·
              refine ⟨6346690266516065193764323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8462253688688086925019097 6346690266516065193764323)
              ·
                refine ⟨9520035399774097790646485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6346690266516065193764323 9520035399774097790646485)
                ·
                  refine ⟨223125829682205416968277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9520035399774097790646485 223125829682205416968277)
                  ·
                    rfl

theorem cell20_488853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 1, 7].length) (baseStart_488853 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_488853 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_488853 prefixEnd_488853 := by exact prefixLift 488853
  have htrace : WordTrace (prefixWord ++ tailWord_488853) baseStart_488853 baseEnd_488853 := by
    simpa [prefixWord, tailWord_488853, baseEnd_488853] using wordTrace_append hprefix tailTrace_488853
  have hstable : (prefixWord ++ tailWord_488853).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488853).length < 2 ^ (prefixWord ++ tailWord_488853).sum := by decide
  have hdescent : baseEnd_488853 < baseStart_488853 := by decide
  rcases family_descends (prefixWord ++ tailWord_488853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488922 : List Nat := [3, 1, 1, 2, 3, 3, 7]
def baseStart_488922 : Nat := 118140960795 + 488922 * 2 ^ 59
def prefixEnd_488922 : Nat := 4983230072969 + 3 ^ 40 * 488922 * 2
def baseEnd_488922 : Nat := 24795258129149760407555

theorem tailTrace_488922 : CollatzResearch.WordTrace tailWord_488922 prefixEnd_488922 24795258129149760407555 := by
  unfold tailWord_488922
  simp only [CollatzResearch.WordTrace]
  refine ⟨4458112583681642518709255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11888300223151046716558013 4458112583681642518709255)
  ·
    refine ⟨6687168875522463778063883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4458112583681642518709255 6687168875522463778063883)
    ·
      refine ⟨10030753313283695667095825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6687168875522463778063883 10030753313283695667095825)
      ·
        refine ⟨7523064984962771750321869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10030753313283695667095825 7523064984962771750321869)
        ·
          refine ⟨2821149369361039406370701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7523064984962771750321869 2821149369361039406370701)
          ·
            refine ⟨1057931013510389777389013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2821149369361039406370701 1057931013510389777389013)
            ·
              refine ⟨24795258129149760407555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1057931013510389777389013 24795258129149760407555)
              ·
                rfl

theorem cell20_488922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 7].length) (baseStart_488922 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_488922 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_488922 prefixEnd_488922 := by exact prefixLift 488922
  have htrace : WordTrace (prefixWord ++ tailWord_488922) baseStart_488922 baseEnd_488922 := by
    simpa [prefixWord, tailWord_488922, baseEnd_488922] using wordTrace_append hprefix tailTrace_488922
  have hstable : (prefixWord ++ tailWord_488922).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488922).length < 2 ^ (prefixWord ++ tailWord_488922).sum := by decide
  have hdescent : baseEnd_488922 < baseStart_488922 := by decide
  rcases family_descends (prefixWord ++ tailWord_488922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488925 : List Nat := [1, 4, 3, 1, 1, 2, 3, 2, 3]
def baseStart_488925 : Nat := 118140960795 + 488925 * 2 ^ 59
def prefixEnd_488925 : Nat := 4983230072969 + 3 ^ 40 * 488925 * 2
def baseEnd_488925 : Nat := 223158692444093166567983

theorem tailTrace_488925 : CollatzResearch.WordTrace tailWord_488925 prefixEnd_488925 223158692444093166567983 := by
  unfold tailWord_488925
  simp only [CollatzResearch.WordTrace]
  refine ⟨17832559753715701587196229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11888373169143801058130819 17832559753715701587196229)
  ·
    refine ⟨3343604953821694047599293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17832559753715701587196229 3343604953821694047599293)
    ·
      refine ⟨1253851857683135267849735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3343604953821694047599293 1253851857683135267849735)
      ·
        refine ⟨1880777786524702901774603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1253851857683135267849735 1880777786524702901774603)
        ·
          refine ⟨2821166679787054352661905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1880777786524702901774603 2821166679787054352661905)
          ·
            refine ⟨2115875009840290764496429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2821166679787054352661905 2115875009840290764496429)
            ·
              refine ⟨793453128690109036686161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2115875009840290764496429 793453128690109036686161)
              ·
                refine ⟨595089846517581777514621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 793453128690109036686161 595089846517581777514621)
                ·
                  refine ⟨223158692444093166567983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 595089846517581777514621 223158692444093166567983)
                  ·
                    rfl

theorem cell20_488925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 3, 2, 3].length) (baseStart_488925 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_488925 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_488925 prefixEnd_488925 := by exact prefixLift 488925
  have htrace : WordTrace (prefixWord ++ tailWord_488925) baseStart_488925 baseEnd_488925 := by
    simpa [prefixWord, tailWord_488925, baseEnd_488925] using wordTrace_append hprefix tailTrace_488925
  have hstable : (prefixWord ++ tailWord_488925).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488925).length < 2 ^ (prefixWord ++ tailWord_488925).sum := by decide
  have hdescent : baseEnd_488925 < baseStart_488925 := by decide
  rcases family_descends (prefixWord ++ tailWord_488925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488973 : List Nat := [1, 7, 1, 1, 2, 2, 6]
def baseStart_488973 : Nat := 118140960795 + 488973 * 2 ^ 59
def prefixEnd_488973 : Nat := 4983230072969 + 3 ^ 40 * 488973 * 2
def baseEnd_488973 : Nat := 24797844550224259218643

theorem tailTrace_488973 : CollatzResearch.WordTrace tailWord_488973 prefixEnd_488973 24797844550224259218643 := by
  unfold tailWord_488973
  simp only [CollatzResearch.WordTrace]
  refine ⟨17834310457541805784943573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11889540305027870523295715 17834310457541805784943573)
  ·
    refine ⟨417991651348636073084615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 17834310457541805784943573 417991651348636073084615)
    ·
      refine ⟨626987477022954109626923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 417991651348636073084615 626987477022954109626923)
      ·
        refine ⟨940481215534431164440385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 626987477022954109626923 940481215534431164440385)
        ·
          refine ⟨705360911650823373330289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 940481215534431164440385 705360911650823373330289)
          ·
            refine ⟨529020683738117529997717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 705360911650823373330289 529020683738117529997717)
            ·
              refine ⟨24797844550224259218643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 529020683738117529997717 24797844550224259218643)
              ·
                rfl

theorem cell20_488973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 6].length) (baseStart_488973 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_488973 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_488973 prefixEnd_488973 := by exact prefixLift 488973
  have htrace : WordTrace (prefixWord ++ tailWord_488973) baseStart_488973 baseEnd_488973 := by
    simpa [prefixWord, tailWord_488973, baseEnd_488973] using wordTrace_append hprefix tailTrace_488973
  have hstable : (prefixWord ++ tailWord_488973).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488973).length < 2 ^ (prefixWord ++ tailWord_488973).sum := by decide
  have hdescent : baseEnd_488973 < baseStart_488973 := by decide
  rcases family_descends (prefixWord ++ tailWord_488973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488990 : List Nat := [4, 3, 3, 1, 1, 1, 2, 5]
def baseStart_488990 : Nat := 118140960795 + 488990 * 2 ^ 59
def prefixEnd_488990 : Nat := 4983230072969 + 3 ^ 40 * 488990 * 2
def baseEnd_488990 : Nat := 74396120071747276467017

theorem tailTrace_488990 : CollatzResearch.WordTrace tailWord_488990 prefixEnd_488990 74396120071747276467017 := by
  unfold tailWord_488990
  simp only [CollatzResearch.WordTrace]
  refine ⟨2229366312310027211039053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11889953665653478458874949 2229366312310027211039053)
  ·
    refine ⟨836012367116260204139645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2229366312310027211039053 836012367116260204139645)
    ·
      refine ⟨313504637668597576552367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 836012367116260204139645 313504637668597576552367)
      ·
        refine ⟨470256956502896364828551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313504637668597576552367 470256956502896364828551)
        ·
          refine ⟨705385434754344547242827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 470256956502896364828551 705385434754344547242827)
          ·
            refine ⟨1058078152131516820864241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 705385434754344547242827 1058078152131516820864241)
            ·
              refine ⟨793558614098637615648181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1058078152131516820864241 793558614098637615648181)
              ·
                refine ⟨74396120071747276467017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 793558614098637615648181 74396120071747276467017)
                ·
                  rfl

theorem cell20_488990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 2, 5].length) (baseStart_488990 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_488990 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_488990 prefixEnd_488990 := by exact prefixLift 488990
  have htrace : WordTrace (prefixWord ++ tailWord_488990) baseStart_488990 baseEnd_488990 := by
    simpa [prefixWord, tailWord_488990, baseEnd_488990] using wordTrace_append hprefix tailTrace_488990
  have hstable : (prefixWord ++ tailWord_488990).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488990).length < 2 ^ (prefixWord ++ tailWord_488990).sum := by decide
  have hdescent : baseEnd_488990 < baseStart_488990 := by decide
  rcases family_descends (prefixWord ++ tailWord_488990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488991 : List Nat := [1, 1, 2, 4, 1, 1, 5, 1, 4]
def baseStart_488991 : Nat := 118140960795 + 488991 * 2 ^ 59
def prefixEnd_488991 : Nat := 4983230072969 + 3 ^ 40 * 488991 * 2
def baseEnd_488991 : Nat := 223188816642490270367713

theorem tailTrace_488991 : CollatzResearch.WordTrace tailWord_488991 prefixEnd_488991 223188816642490270367713 := by
  unfold tailWord_488991
  simp only [CollatzResearch.WordTrace]
  refine ⟨17834966971476594859098827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11889977980984396572732551 17834966971476594859098827)
  ·
    refine ⟨26752450457214892288648241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17834966971476594859098827 26752450457214892288648241)
    ·
      refine ⟨20064337842911169216486181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26752450457214892288648241 20064337842911169216486181)
      ·
        refine ⟨3762063345545844228091159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20064337842911169216486181 3762063345545844228091159)
        ·
          refine ⟨5643095018318766342136739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3762063345545844228091159 5643095018318766342136739)
          ·
            refine ⟨8464642527478149513205109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5643095018318766342136739 8464642527478149513205109)
            ·
              refine ⟨793560236951076516862979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8464642527478149513205109 793560236951076516862979)
              ·
                refine ⟨1190340355426614775294469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 793560236951076516862979 1190340355426614775294469)
                ·
                  refine ⟨223188816642490270367713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1190340355426614775294469 223188816642490270367713)
                  ·
                    rfl

theorem cell20_488991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 5, 1, 4].length) (baseStart_488991 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_488991 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_488991 prefixEnd_488991 := by exact prefixLift 488991
  have htrace : WordTrace (prefixWord ++ tailWord_488991) baseStart_488991 baseEnd_488991 := by
    simpa [prefixWord, tailWord_488991, baseEnd_488991] using wordTrace_append hprefix tailTrace_488991
  have hstable : (prefixWord ++ tailWord_488991).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488991).length < 2 ^ (prefixWord ++ tailWord_488991).sum := by decide
  have hdescent : baseEnd_488991 < baseStart_488991 := by decide
  rcases family_descends (prefixWord ++ tailWord_488991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489042 : List Nat := [3, 2, 2, 1, 2, 4, 2, 2, 2]
def baseStart_489042 : Nat := 118140960795 + 489042 * 2 ^ 59
def prefixEnd_489042 : Nat := 4983230072969 + 3 ^ 40 * 489042 * 2
def baseEnd_489042 : Nat := 223212094432160759667505

theorem tailTrace_489042 : CollatzResearch.WordTrace tailWord_489042 prefixEnd_489042 223212094432160759667505 := by
  unfold tailWord_489042
  simp only [CollatzResearch.WordTrace]
  refine ⟨4459206773572957642301345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11891218062861220379470253 4459206773572957642301345)
  ·
    refine ⟨3344405080179718231726009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4459206773572957642301345 3344405080179718231726009)
    ·
      refine ⟨2508303810134788673794507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3344405080179718231726009 2508303810134788673794507)
      ·
        refine ⟨3762455715202183010691761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2508303810134788673794507 3762455715202183010691761)
        ·
          refine ⟨2821841786401637258018821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3762455715202183010691761 2821841786401637258018821)
          ·
            refine ⟨529095334950306985878529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2821841786401637258018821 529095334950306985878529)
            ·
              refine ⟨396821501212730239408897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 529095334950306985878529 396821501212730239408897)
              ·
                refine ⟨297616125909547679556673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 396821501212730239408897 297616125909547679556673)
                ·
                  refine ⟨223212094432160759667505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 297616125909547679556673 223212094432160759667505)
                  ·
                    rfl

theorem cell20_489042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 2, 2, 2].length) (baseStart_489042 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_489042 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_489042 prefixEnd_489042 := by exact prefixLift 489042
  have htrace : WordTrace (prefixWord ++ tailWord_489042) baseStart_489042 baseEnd_489042 := by
    simpa [prefixWord, tailWord_489042, baseEnd_489042] using wordTrace_append hprefix tailTrace_489042
  have hstable : (prefixWord ++ tailWord_489042).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489042).length < 2 ^ (prefixWord ++ tailWord_489042).sum := by decide
  have hdescent : baseEnd_489042 < baseStart_489042 := by decide
  rcases family_descends (prefixWord ++ tailWord_489042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489050 : List Nat := [3, 1, 1, 2, 1, 1, 1, 2, 8]
def baseStart_489050 : Nat := 118140960795 + 489050 * 2 ^ 59
def prefixEnd_489050 : Nat := 4983230072969 + 3 ^ 40 * 489050 * 2
def baseEnd_489050 : Nat := 223215745850148287400805

theorem tailTrace_489050 : CollatzResearch.WordTrace tailWord_489050 prefixEnd_489050 223215745850148287400805 := by
  unfold tailWord_489050
  simp only [CollatzResearch.WordTrace]
  refine ⟨4459279719565711983874151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11891412585508565290331069 4459279719565711983874151)
  ·
    refine ⟨6688919579348567975811227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4459279719565711983874151 6688919579348567975811227)
    ·
      refine ⟨10033379369022851963716841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6688919579348567975811227 10033379369022851963716841)
      ·
        refine ⟨7525034526767138972787631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10033379369022851963716841 7525034526767138972787631)
        ·
          refine ⟨11287551790150708459181447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7525034526767138972787631 11287551790150708459181447)
          ·
            refine ⟨16931327685226062688772171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11287551790150708459181447 16931327685226062688772171)
            ·
              refine ⟨25396991527839094033158257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16931327685226062688772171 25396991527839094033158257)
              ·
                refine ⟨19047743645879320524868693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25396991527839094033158257 19047743645879320524868693)
                ·
                  refine ⟨223215745850148287400805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19047743645879320524868693 223215745850148287400805)
                  ·
                    rfl

theorem cell20_489050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 2, 8].length) (baseStart_489050 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_489050 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_489050 prefixEnd_489050 := by exact prefixLift 489050
  have htrace : WordTrace (prefixWord ++ tailWord_489050) baseStart_489050 baseEnd_489050 := by
    simpa [prefixWord, tailWord_489050, baseEnd_489050] using wordTrace_append hprefix tailTrace_489050
  have hstable : (prefixWord ++ tailWord_489050).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489050).length < 2 ^ (prefixWord ++ tailWord_489050).sum := by decide
  have hdescent : baseEnd_489050 < baseStart_489050 := by decide
  rcases family_descends (prefixWord ++ tailWord_489050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489060 : List Nat := [2, 3, 1, 1, 2, 3, 2, 3, 3]
def baseStart_489060 : Nat := 118140960795 + 489060 * 2 ^ 59
def prefixEnd_489060 : Nat := 4983230072969 + 3 ^ 40 * 489060 * 2
def baseEnd_489060 : Nat := 223220310122632697067431

theorem tailTrace_489060 : CollatzResearch.WordTrace tailWord_489060 prefixEnd_489060 223220310122632697067431 := by
  unfold tailWord_489060
  simp only [CollatzResearch.WordTrace]
  refine ⟨8918741804113309821680317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11891655738817746428907089 8918741804113309821680317)
  ·
    refine ⟨3344528176542491183130119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8918741804113309821680317 3344528176542491183130119)
    ·
      refine ⟨5016792264813736774695179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3344528176542491183130119 5016792264813736774695179)
      ·
        refine ⟨7525188397220605162042769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5016792264813736774695179 7525188397220605162042769)
        ·
          refine ⟨5643891297915453871532077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7525188397220605162042769 5643891297915453871532077)
          ·
            refine ⟨2116459236718295201824529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5643891297915453871532077 2116459236718295201824529)
            ·
              refine ⟨1587344427538721401368397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2116459236718295201824529 1587344427538721401368397)
              ·
                refine ⟨595254160327020525513149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1587344427538721401368397 595254160327020525513149)
                ·
                  refine ⟨223220310122632697067431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 595254160327020525513149 223220310122632697067431)
                  ·
                    rfl

theorem cell20_489060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 3, 3].length) (baseStart_489060 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_489060 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_489060 prefixEnd_489060 := by exact prefixLift 489060
  have htrace : WordTrace (prefixWord ++ tailWord_489060) baseStart_489060 baseEnd_489060 := by
    simpa [prefixWord, tailWord_489060, baseEnd_489060] using wordTrace_append hprefix tailTrace_489060
  have hstable : (prefixWord ++ tailWord_489060).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489060).length < 2 ^ (prefixWord ++ tailWord_489060).sum := by decide
  have hdescent : baseEnd_489060 < baseStart_489060 := by decide
  rcases family_descends (prefixWord ++ tailWord_489060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489070 : List Nat := [4, 1, 2, 2, 3, 1, 3, 4]
def baseStart_489070 : Nat := 118140960795 + 489070 * 2 ^ 59
def prefixEnd_489070 : Nat := 4983230072969 + 3 ^ 40 * 489070 * 2
def baseEnd_489070 : Nat := 74408291465039035578019

theorem tailTrace_489070 : CollatzResearch.WordTrace tailWord_489070 prefixEnd_489070 74408291465039035578019 := by
  unfold tailWord_489070
  simp only [CollatzResearch.WordTrace]
  refine ⟨2229731042273798918903083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11891898892126927567483109 2229731042273798918903083)
  ·
    refine ⟨3344596563410698378354625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2229731042273798918903083 3344596563410698378354625)
    ·
      refine ⟨2508447422558023783765969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3344596563410698378354625 2508447422558023783765969)
      ·
        refine ⟨1881335566918517837824477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2508447422558023783765969 1881335566918517837824477)
        ·
          refine ⟨705500837594444189184179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1881335566918517837824477 705500837594444189184179)
          ·
            refine ⟨1058251256391666283776269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 705500837594444189184179 1058251256391666283776269)
            ·
              refine ⟨396844221146874856416101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1058251256391666283776269 396844221146874856416101)
              ·
                refine ⟨74408291465039035578019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 396844221146874856416101 74408291465039035578019)
                ·
                  rfl

theorem cell20_489070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 3, 4].length) (baseStart_489070 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_489070 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_489070 prefixEnd_489070 := by exact prefixLift 489070
  have htrace : WordTrace (prefixWord ++ tailWord_489070) baseStart_489070 baseEnd_489070 := by
    simpa [prefixWord, tailWord_489070, baseEnd_489070] using wordTrace_append hprefix tailTrace_489070
  have hstable : (prefixWord ++ tailWord_489070).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489070).length < 2 ^ (prefixWord ++ tailWord_489070).sum := by decide
  have hdescent : baseEnd_489070 < baseStart_489070 := by decide
  rcases family_descends (prefixWord ++ tailWord_489070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489081 : List Nat := [1, 2, 1, 3, 3, 1, 2, 2, 5]
def baseStart_489081 : Nat := 118140960795 + 489081 * 2 ^ 59
def prefixEnd_489081 : Nat := 4983230072969 + 3 ^ 40 * 489081 * 2
def baseEnd_489081 : Nat := 223229895094849957367345

theorem tailTrace_489081 : CollatzResearch.WordTrace tailWord_489081 prefixEnd_489081 223229895094849957367345 := by
  unfold tailWord_489081
  simp only [CollatzResearch.WordTrace]
  refine ⟨17838249541150540229875097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11892166360767026819916731 17838249541150540229875097)
  ·
    refine ⟨13378687155862905172406323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17838249541150540229875097 13378687155862905172406323)
    ·
      refine ⟨20068030733794357758609485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13378687155862905172406323 20068030733794357758609485)
      ·
        refine ⟨7525511525172884159478557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20068030733794357758609485 7525511525172884159478557)
        ·
          refine ⟨2822066821939831559804459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7525511525172884159478557 2822066821939831559804459)
          ·
            refine ⟨4233100232909747339706689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2822066821939831559804459 4233100232909747339706689)
            ·
              refine ⟨3174825174682310504780017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4233100232909747339706689 3174825174682310504780017)
              ·
                refine ⟨2381118881011732878585013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3174825174682310504780017 2381118881011732878585013)
                ·
                  refine ⟨223229895094849957367345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2381118881011732878585013 223229895094849957367345)
                  ·
                    rfl

theorem cell20_489081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 2, 5].length) (baseStart_489081 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_489081 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_489081 prefixEnd_489081 := by exact prefixLift 489081
  have htrace : WordTrace (prefixWord ++ tailWord_489081) baseStart_489081 baseEnd_489081 := by
    simpa [prefixWord, tailWord_489081, baseEnd_489081] using wordTrace_append hprefix tailTrace_489081
  have hstable : (prefixWord ++ tailWord_489081).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489081).length < 2 ^ (prefixWord ++ tailWord_489081).sum := by decide
  have hdescent : baseEnd_489081 < baseStart_489081 := by decide
  rcases family_descends (prefixWord ++ tailWord_489081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489088 : List Nat := [2, 1, 1, 2, 1, 4, 1, 2, 6]
def baseStart_489088 : Nat := 118140960795 + 489088 * 2 ^ 59
def prefixEnd_489088 : Nat := 4983230072969 + 3 ^ 40 * 489088 * 2
def baseEnd_489088 : Nat := 223233090085589044133983

theorem tailTrace_489088 : CollatzResearch.WordTrace tailWord_489088 prefixEnd_489088 223233090085589044133983 := by
  unfold tailWord_489088
  simp only [CollatzResearch.WordTrace]
  refine ⟨8919252426062590212689959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11892336568083453616919945 8919252426062590212689959)
  ·
    refine ⟨13378878639093885319034939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8919252426062590212689959 13378878639093885319034939)
    ·
      refine ⟨20068317958640827978552409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13378878639093885319034939 20068317958640827978552409)
      ·
        refine ⟨15051238468980620983914307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20068317958640827978552409 15051238468980620983914307)
        ·
          refine ⟨22576857703470931475871461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15051238468980620983914307 22576857703470931475871461)
          ·
            refine ⟨4233160819400799651725899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22576857703470931475871461 4233160819400799651725899)
            ·
              refine ⟨6349741229101199477588849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4233160819400799651725899 6349741229101199477588849)
              ·
                refine ⟨4762305921825899608191637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6349741229101199477588849 4762305921825899608191637)
                ·
                  refine ⟨223233090085589044133983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4762305921825899608191637 223233090085589044133983)
                  ·
                    rfl

theorem cell20_489088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 2, 6].length) (baseStart_489088 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_489088 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_489088 prefixEnd_489088 := by exact prefixLift 489088
  have htrace : WordTrace (prefixWord ++ tailWord_489088) baseStart_489088 baseEnd_489088 := by
    simpa [prefixWord, tailWord_489088, baseEnd_489088] using wordTrace_append hprefix tailTrace_489088
  have hstable : (prefixWord ++ tailWord_489088).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489088).length < 2 ^ (prefixWord ++ tailWord_489088).sum := by decide
  have hdescent : baseEnd_489088 < baseStart_489088 := by decide
  rcases family_descends (prefixWord ++ tailWord_489088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489098 : List Nat := [3, 1, 2, 3, 2, 2, 1, 1, 5]
def baseStart_489098 : Nat := 118140960795 + 489098 * 2 ^ 59
def prefixEnd_489098 : Nat := 4983230072969 + 3 ^ 40 * 489098 * 2
def baseEnd_489098 : Nat := 223237654358073453800609

theorem tailTrace_489098 : CollatzResearch.WordTrace tailWord_489098 prefixEnd_489098 223237654358073453800609 := by
  unfold tailWord_489098
  simp only [CollatzResearch.WordTrace]
  refine ⟨4459717395522238033310987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11892579721392634755495965 4459717395522238033310987)
  ·
    refine ⟨6689576093283357049966481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4459717395522238033310987 6689576093283357049966481)
    ·
      refine ⟨5017182069962517787474861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6689576093283357049966481 5017182069962517787474861)
      ·
        refine ⟨1881443276235944170303073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5017182069962517787474861 1881443276235944170303073)
        ·
          refine ⟨1411082457176958127727305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1881443276235944170303073 1411082457176958127727305)
          ·
            refine ⟨1058311842882718595795479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1411082457176958127727305 1058311842882718595795479)
            ·
              refine ⟨1587467764324077893693219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1058311842882718595795479 1587467764324077893693219)
              ·
                refine ⟨2381201646486116840539829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1587467764324077893693219 2381201646486116840539829)
                ·
                  refine ⟨223237654358073453800609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2381201646486116840539829 223237654358073453800609)
                  ·
                    rfl

theorem cell20_489098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 1, 5].length) (baseStart_489098 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_489098 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_489098 prefixEnd_489098 := by exact prefixLift 489098
  have htrace : WordTrace (prefixWord ++ tailWord_489098) baseStart_489098 baseEnd_489098 := by
    simpa [prefixWord, tailWord_489098, baseEnd_489098] using wordTrace_append hprefix tailTrace_489098
  have hstable : (prefixWord ++ tailWord_489098).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489098).length < 2 ^ (prefixWord ++ tailWord_489098).sum := by decide
  have hdescent : baseEnd_489098 < baseStart_489098 := by decide
  rcases family_descends (prefixWord ++ tailWord_489098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489150 : List Nat := [4, 2, 1, 1, 2, 2, 8]
def baseStart_489150 : Nat := 118140960795 + 489150 * 2 ^ 59
def prefixEnd_489150 : Nat := 4983230072969 + 3 ^ 40 * 489150 * 2
def baseEnd_489150 : Nat := 24806820952776931563007

theorem tailTrace_489150 : CollatzResearch.WordTrace tailWord_489150 prefixEnd_489150 24806820952776931563007 := by
  unfold tailWord_489150
  simp only [CollatzResearch.WordTrace]
  refine ⟨2230095772237570626767113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11893844118600376676091269 2230095772237570626767113)
  ·
    refine ⟨1672571829178177970075335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2230095772237570626767113 1672571829178177970075335)
    ·
      refine ⟨2508857743767266955113003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1672571829178177970075335 2508857743767266955113003)
      ·
        refine ⟨3763286615650900432669505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2508857743767266955113003 3763286615650900432669505)
        ·
          refine ⟨2822464961738175324502129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3763286615650900432669505 2822464961738175324502129)
          ·
            refine ⟨2116848721303631493376597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2822464961738175324502129 2116848721303631493376597)
            ·
              refine ⟨24806820952776931563007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2116848721303631493376597 24806820952776931563007)
              ·
                rfl

theorem cell20_489150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 8].length) (baseStart_489150 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_489150 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_489150 prefixEnd_489150 := by exact prefixLift 489150
  have htrace : WordTrace (prefixWord ++ tailWord_489150) baseStart_489150 baseEnd_489150 := by
    simpa [prefixWord, tailWord_489150, baseEnd_489150] using wordTrace_append hprefix tailTrace_489150
  have hstable : (prefixWord ++ tailWord_489150).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489150).length < 2 ^ (prefixWord ++ tailWord_489150).sum := by decide
  have hdescent : baseEnd_489150 < baseStart_489150 := by decide
  rcases family_descends (prefixWord ++ tailWord_489150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489170 : List Nat := [3, 2, 2, 2, 2, 3, 2, 1, 3]
def baseStart_489170 : Nat := 118140960795 + 489170 * 2 ^ 59
def prefixEnd_489170 : Nat := 4983230072969 + 3 ^ 40 * 489170 * 2
def baseEnd_489170 : Nat := 223270517119961203400315

theorem tailTrace_489170 : CollatzResearch.WordTrace tailWord_489170 prefixEnd_489170 223270517119961203400315 := by
  unfold tailWord_489170
  simp only [CollatzResearch.WordTrace]
  refine ⟨4460373909457027107466241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11894330425218738953243309 4460373909457027107466241)
  ·
    refine ⟨3345280432092770330599681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4460373909457027107466241 3345280432092770330599681)
    ·
      refine ⟨2508960324069577747949761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3345280432092770330599681 2508960324069577747949761)
      ·
        refine ⟨1881720243052183310962321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2508960324069577747949761 1881720243052183310962321)
        ·
          refine ⟨1411290182289137483221741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1881720243052183310962321 1411290182289137483221741)
          ·
            refine ⟨529233818358426556208153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1411290182289137483221741 529233818358426556208153)
            ·
              refine ⟨396925363768819917156115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 529233818358426556208153 396925363768819917156115)
              ·
                refine ⟨595388045653229875734173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 396925363768819917156115 595388045653229875734173)
                ·
                  refine ⟨223270517119961203400315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 595388045653229875734173 223270517119961203400315)
                  ·
                    rfl

theorem cell20_489170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 2, 1, 3].length) (baseStart_489170 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_489170 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_489170 prefixEnd_489170 := by exact prefixLift 489170
  have htrace : WordTrace (prefixWord ++ tailWord_489170) baseStart_489170 baseEnd_489170 := by
    simpa [prefixWord, tailWord_489170, baseEnd_489170] using wordTrace_append hprefix tailTrace_489170
  have hstable : (prefixWord ++ tailWord_489170).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489170).length < 2 ^ (prefixWord ++ tailWord_489170).sum := by decide
  have hdescent : baseEnd_489170 < baseStart_489170 := by decide
  rcases family_descends (prefixWord ++ tailWord_489170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489198 : List Nat := [4, 1, 2, 1, 1, 2, 2, 5, 2]
def baseStart_489198 : Nat := 118140960795 + 489198 * 2 ^ 59
def prefixEnd_489198 : Nat := 4983230072969 + 3 ^ 40 * 489198 * 2
def baseEnd_489198 : Nat := 223283297082917550466867

theorem tailTrace_489198 : CollatzResearch.WordTrace tailWord_489198 prefixEnd_489198 223283297082917550466867 := by
  unfold tailWord_489198
  simp only [CollatzResearch.WordTrace]
  refine ⟨2230314610215833651485531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11895011254484446141256165 2230314610215833651485531)
  ·
    refine ⟨3345471915323750477228297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2230314610215833651485531 3345471915323750477228297)
    ·
      refine ⟨2509103936492812857921223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3345471915323750477228297 2509103936492812857921223)
      ·
        refine ⟨3763655904739219286881835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2509103936492812857921223 3763655904739219286881835)
        ·
          refine ⟨5645483857108828930322753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3763655904739219286881835 5645483857108828930322753)
          ·
            refine ⟨4234112892831621697742065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5645483857108828930322753 4234112892831621697742065)
            ·
              refine ⟨3175584669623716273306549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4234112892831621697742065 3175584669623716273306549)
              ·
                refine ⟨297711062777223400622489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3175584669623716273306549 297711062777223400622489)
                ·
                  refine ⟨223283297082917550466867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 297711062777223400622489 223283297082917550466867)
                  ·
                    rfl

theorem cell20_489198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 5, 2].length) (baseStart_489198 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_489198 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_489198 prefixEnd_489198 := by exact prefixLift 489198
  have htrace : WordTrace (prefixWord ++ tailWord_489198) baseStart_489198 baseEnd_489198 := by
    simpa [prefixWord, tailWord_489198, baseEnd_489198] using wordTrace_append hprefix tailTrace_489198
  have hstable : (prefixWord ++ tailWord_489198).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489198).length < 2 ^ (prefixWord ++ tailWord_489198).sum := by decide
  have hdescent : baseEnd_489198 < baseStart_489198 := by decide
  rcases family_descends (prefixWord ++ tailWord_489198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489212 : List Nat := [2, 2, 2, 1, 3, 1, 4, 2, 3]
def baseStart_489212 : Nat := 118140960795 + 489212 * 2 ^ 59
def prefixEnd_489212 : Nat := 4983230072969 + 3 ^ 40 * 489212 * 2
def baseEnd_489212 : Nat := 223289687064395724000143

theorem tailTrace_489212 : CollatzResearch.WordTrace tailWord_489212 prefixEnd_489212 223289687064395724000143 := by
  unfold tailWord_489212
  simp only [CollatzResearch.WordTrace]
  refine ⟨8921513751837974801446945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11895351669117299735262593 8921513751837974801446945)
  ·
    refine ⟨6691135313878481101085209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8921513751837974801446945 6691135313878481101085209)
    ·
      refine ⟨5018351485408860825813907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6691135313878481101085209 5018351485408860825813907)
      ·
        refine ⟨7527527228113291238720861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5018351485408860825813907 7527527228113291238720861)
        ·
          refine ⟨2822822710542484214520323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7527527228113291238720861 2822822710542484214520323)
          ·
            refine ⟨4234234065813726321780485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2822822710542484214520323 4234234065813726321780485)
            ·
              refine ⟨793918887340073685333841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4234234065813726321780485 793918887340073685333841)
              ·
                refine ⟨595439165505055264000381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 793918887340073685333841 595439165505055264000381)
                ·
                  refine ⟨223289687064395724000143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 595439165505055264000381 223289687064395724000143)
                  ·
                    rfl

theorem cell20_489212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 4, 2, 3].length) (baseStart_489212 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_489212 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_489212 prefixEnd_489212 := by exact prefixLift 489212
  have htrace : WordTrace (prefixWord ++ tailWord_489212) baseStart_489212 baseEnd_489212 := by
    simpa [prefixWord, tailWord_489212, baseEnd_489212] using wordTrace_append hprefix tailTrace_489212
  have hstable : (prefixWord ++ tailWord_489212).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489212).length < 2 ^ (prefixWord ++ tailWord_489212).sum := by decide
  have hdescent : baseEnd_489212 < baseStart_489212 := by decide
  rcases family_descends (prefixWord ++ tailWord_489212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489226 : List Nat := [3, 1, 2, 2, 1, 3, 3, 5]
def baseStart_489226 : Nat := 118140960795 + 489226 * 2 ^ 59
def prefixEnd_489226 : Nat := 4983230072969 + 3 ^ 40 * 489226 * 2
def baseEnd_489226 : Nat := 74432025681957965844473

theorem tailTrace_489226 : CollatzResearch.WordTrace tailWord_489226 prefixEnd_489226 74432025681957965844473 := by
  unfold tailWord_489226
  simp only [CollatzResearch.WordTrace]
  refine ⟨4460884531406307498475883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11895692083750153329269021 4460884531406307498475883)
  ·
    refine ⟨6691326797109461247713825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4460884531406307498475883 6691326797109461247713825)
    ·
      refine ⟨5018495097832095935785369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6691326797109461247713825 5018495097832095935785369)
      ·
        refine ⟨3763871323374071951839027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5018495097832095935785369 3763871323374071951839027)
        ·
          refine ⟨5645806985061107927758541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3763871323374071951839027 5645806985061107927758541)
          ·
            refine ⟨2117177619397915472909453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5645806985061107927758541 2117177619397915472909453)
            ·
              refine ⟨793941607274218302341045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2117177619397915472909453 793941607274218302341045)
              ·
                refine ⟨74432025681957965844473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 793941607274218302341045 74432025681957965844473)
                ·
                  rfl

theorem cell20_489226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 3, 5].length) (baseStart_489226 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_489226 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_489226 prefixEnd_489226 := by exact prefixLift 489226
  have htrace : WordTrace (prefixWord ++ tailWord_489226) baseStart_489226 baseEnd_489226 := by
    simpa [prefixWord, tailWord_489226, baseEnd_489226] using wordTrace_append hprefix tailTrace_489226
  have hstable : (prefixWord ++ tailWord_489226).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489226).length < 2 ^ (prefixWord ++ tailWord_489226).sum := by decide
  have hdescent : baseEnd_489226 < baseStart_489226 := by decide
  rcases family_descends (prefixWord ++ tailWord_489226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489240 : List Nat := [2, 1, 2, 3, 1, 1, 3, 1, 6]
def baseStart_489240 : Nat := 118140960795 + 489240 * 2 ^ 59
def prefixEnd_489240 : Nat := 4983230072969 + 3 ^ 40 * 489240 * 2
def baseEnd_489240 : Nat := 223302467027352071066695

theorem tailTrace_489240 : CollatzResearch.WordTrace tailWord_489240 prefixEnd_489240 223302467027352071066695 := by
  unfold tailWord_489240
  simp only [CollatzResearch.WordTrace]
  refine ⟨8922024373787255192456587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11896032498383006923275449 8922024373787255192456587)
  ·
    refine ⟨13383036560680882788684881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8922024373787255192456587 13383036560680882788684881)
    ·
      refine ⟨10037277420510662091513661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13383036560680882788684881 10037277420510662091513661)
      ·
        refine ⟨3763979032691498284317623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10037277420510662091513661 3763979032691498284317623)
        ·
          refine ⟨5645968549037247426476435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3763979032691498284317623 5645968549037247426476435)
          ·
            refine ⟨8468952823555871139714653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5645968549037247426476435 8468952823555871139714653)
            ·
              refine ⟨3175857308833451677392995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8468952823555871139714653 3175857308833451677392995)
              ·
                refine ⟨4763785963250177516089493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3175857308833451677392995 4763785963250177516089493)
                ·
                  refine ⟨223302467027352071066695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4763785963250177516089493 223302467027352071066695)
                  ·
                    rfl

theorem cell20_489240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 1, 6].length) (baseStart_489240 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_489240 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_489240 prefixEnd_489240 := by exact prefixLift 489240
  have htrace : WordTrace (prefixWord ++ tailWord_489240) baseStart_489240 baseEnd_489240 := by
    simpa [prefixWord, tailWord_489240, baseEnd_489240] using wordTrace_append hprefix tailTrace_489240
  have hstable : (prefixWord ++ tailWord_489240).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489240).length < 2 ^ (prefixWord ++ tailWord_489240).sum := by decide
  have hdescent : baseEnd_489240 < baseStart_489240 := by decide
  rcases family_descends (prefixWord ++ tailWord_489240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489267 : List Nat := [1, 1, 1, 2, 7, 2, 1, 2, 3]
def baseStart_489267 : Nat := 118140960795 + 489267 * 2 ^ 59
def prefixEnd_489267 : Nat := 4983230072969 + 3 ^ 40 * 489267 * 2
def baseEnd_489267 : Nat := 223314790563059977166585

theorem tailTrace_489267 : CollatzResearch.WordTrace tailWord_489267 prefixEnd_489267 223314790563059977166585 := by
  unfold tailWord_489267
  simp only [CollatzResearch.WordTrace]
  refine ⟨17845033518476693996146055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11896689012317795997430703 17845033518476693996146055)
  ·
    refine ⟨26767550277715040994219083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17845033518476693996146055 26767550277715040994219083)
    ·
      refine ⟨40151325416572561491328625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26767550277715040994219083 40151325416572561491328625)
      ·
        refine ⟨30113494062429421118496469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40151325416572561491328625 30113494062429421118496469)
        ·
          refine ⟨705785017088189557464761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 30113494062429421118496469 705785017088189557464761)
          ·
            refine ⟨529338762816142168098571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 705785017088189557464761 529338762816142168098571)
            ·
              refine ⟨794008144224213252147857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 529338762816142168098571 794008144224213252147857)
              ·
                refine ⟨595506108168159939110893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 794008144224213252147857 595506108168159939110893)
                ·
                  refine ⟨223314790563059977166585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 595506108168159939110893 223314790563059977166585)
                  ·
                    rfl

theorem cell20_489267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 1, 2, 3].length) (baseStart_489267 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_489267 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_489267 prefixEnd_489267 := by exact prefixLift 489267
  have htrace : WordTrace (prefixWord ++ tailWord_489267) baseStart_489267 baseEnd_489267 := by
    simpa [prefixWord, tailWord_489267, baseEnd_489267] using wordTrace_append hprefix tailTrace_489267
  have hstable : (prefixWord ++ tailWord_489267).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489267).length < 2 ^ (prefixWord ++ tailWord_489267).sum := by decide
  have hdescent : baseEnd_489267 < baseStart_489267 := by decide
  rcases family_descends (prefixWord ++ tailWord_489267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489271 : List Nat := [1, 1, 3, 1, 2, 1, 2, 6, 3]
def baseStart_489271 : Nat := 118140960795 + 489271 * 2 ^ 59
def prefixEnd_489271 : Nat := 4983230072969 + 3 ^ 40 * 489271 * 2
def baseEnd_489271 : Nat := 223316616272053741033235

theorem tailTrace_489271 : CollatzResearch.WordTrace tailWord_489271 prefixEnd_489271 223316616272053741033235 := by
  unfold tailWord_489271
  simp only [CollatzResearch.WordTrace]
  refine ⟨17845179410462202679291667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11896786273641468452861111 17845179410462202679291667)
  ·
    refine ⟨26767769115693304018937501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17845179410462202679291667 26767769115693304018937501)
    ·
      refine ⟨10037913418384989007101563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26767769115693304018937501 10037913418384989007101563)
      ·
        refine ⟨15056870127577483510652345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10037913418384989007101563 15056870127577483510652345)
        ·
          refine ⟨11292652595683112632989259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15056870127577483510652345 11292652595683112632989259)
          ·
            refine ⟨16938978893524668949483889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11292652595683112632989259 16938978893524668949483889)
            ·
              refine ⟨12704234170143501712112917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16938978893524668949483889 12704234170143501712112917)
              ·
                refine ⟨595510976725476642755293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 12704234170143501712112917 595510976725476642755293)
                ·
                  refine ⟨223316616272053741033235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 595510976725476642755293 223316616272053741033235)
                  ·
                    rfl

theorem cell20_489271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 6, 3].length) (baseStart_489271 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_489271 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_489271 prefixEnd_489271 := by exact prefixLift 489271
  have htrace : WordTrace (prefixWord ++ tailWord_489271) baseStart_489271 baseEnd_489271 := by
    simpa [prefixWord, tailWord_489271, baseEnd_489271] using wordTrace_append hprefix tailTrace_489271
  have hstable : (prefixWord ++ tailWord_489271).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489271).length < 2 ^ (prefixWord ++ tailWord_489271).sum := by decide
  have hdescent : baseEnd_489271 < baseStart_489271 := by decide
  rcases family_descends (prefixWord ++ tailWord_489271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489274 : List Nat := [3, 1, 1, 1, 5, 1, 2, 4, 2]
def baseStart_489274 : Nat := 118140960795 + 489274 * 2 ^ 59
def prefixEnd_489274 : Nat := 4983230072969 + 3 ^ 40 * 489274 * 2
def baseEnd_489274 : Nat := 223317985553799063933223

theorem tailTrace_489274 : CollatzResearch.WordTrace tailWord_489274 prefixEnd_489274 223317985553799063933223 := by
  unfold tailWord_489274
  simp only [CollatzResearch.WordTrace]
  refine ⟨4461322207362833547912719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11896859219634222794433917 4461322207362833547912719)
  ·
    refine ⟨6691983311044250321869079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4461322207362833547912719 6691983311044250321869079)
    ·
      refine ⟨10037974966566375482803619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6691983311044250321869079 10037974966566375482803619)
      ·
        refine ⟨15056962449849563224205429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10037974966566375482803619 15056962449849563224205429)
        ·
          refine ⟨1411590229673396552269259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15056962449849563224205429 1411590229673396552269259)
          ·
            refine ⟨2117385344510094828403889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1411590229673396552269259 2117385344510094828403889)
            ·
              refine ⟨1588039008382571121302917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2117385344510094828403889 1588039008382571121302917)
              ·
                refine ⟨297757314071732085244297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1588039008382571121302917 297757314071732085244297)
                ·
                  refine ⟨223317985553799063933223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 297757314071732085244297 223317985553799063933223)
                  ·
                    rfl

theorem cell20_489274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 4, 2].length) (baseStart_489274 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_489274 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_489274 prefixEnd_489274 := by exact prefixLift 489274
  have htrace : WordTrace (prefixWord ++ tailWord_489274) baseStart_489274 baseEnd_489274 := by
    simpa [prefixWord, tailWord_489274, baseEnd_489274] using wordTrace_append hprefix tailTrace_489274
  have hstable : (prefixWord ++ tailWord_489274).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489274).length < 2 ^ (prefixWord ++ tailWord_489274).sum := by decide
  have hdescent : baseEnd_489274 < baseStart_489274 := by decide
  rcases family_descends (prefixWord ++ tailWord_489274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489285 : List Nat := [1, 3, 1, 1, 1, 2, 4, 7]
def baseStart_489285 : Nat := 118140960795 + 489285 * 2 ^ 59
def prefixEnd_489285 : Nat := 4983230072969 + 3 ^ 40 * 489285 * 2
def baseEnd_489285 : Nat := 74441002084510638188837

theorem tailTrace_489285 : CollatzResearch.WordTrace tailWord_489285 prefixEnd_489285 74441002084510638188837 := by
  unfold tailWord_489285
  simp only [CollatzResearch.WordTrace]
  refine ⟨17845690032411483070301309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11897126688274322046867539 17845690032411483070301309)
  ·
    refine ⟨6692133762154306151362991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17845690032411483070301309 6692133762154306151362991)
    ·
      refine ⟨10038200643231459227044487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6692133762154306151362991 10038200643231459227044487)
      ·
        refine ⟨15057300964847188840566731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10038200643231459227044487 15057300964847188840566731)
        ·
          refine ⟨22585951447270783260850097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15057300964847188840566731 22585951447270783260850097)
          ·
            refine ⟨16939463585453087445637573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22585951447270783260850097 16939463585453087445637573)
            ·
              refine ⟨3176149422272453896057045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16939463585453087445637573 3176149422272453896057045)
              ·
                refine ⟨74441002084510638188837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3176149422272453896057045 74441002084510638188837)
                ·
                  rfl

theorem cell20_489285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 7].length) (baseStart_489285 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_489285 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_489285 prefixEnd_489285 := by exact prefixLift 489285
  have htrace : WordTrace (prefixWord ++ tailWord_489285) baseStart_489285 baseEnd_489285 := by
    simpa [prefixWord, tailWord_489285, baseEnd_489285] using wordTrace_append hprefix tailTrace_489285
  have hstable : (prefixWord ++ tailWord_489285).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489285).length < 2 ^ (prefixWord ++ tailWord_489285).sum := by decide
  have hdescent : baseEnd_489285 < baseStart_489285 := by decide
  rcases family_descends (prefixWord ++ tailWord_489285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489308 : List Nat := [2, 2, 4, 2, 2, 2, 1, 3, 2]
def baseStart_489308 : Nat := 118140960795 + 489308 * 2 ^ 59
def prefixEnd_489308 : Nat := 4983230072969 + 3 ^ 40 * 489308 * 2
def baseEnd_489308 : Nat := 223333504080246056799751

theorem tailTrace_489308 : CollatzResearch.WordTrace tailWord_489308 prefixEnd_489308 223333504080246056799751 := by
  unfold tailWord_489308
  simp only [CollatzResearch.WordTrace]
  refine ⟨8923264455664078999194289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11897685940885438665592385 8923264455664078999194289)
  ·
    refine ⟨6692448341748059249395717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8923264455664078999194289 6692448341748059249395717)
    ·
      refine ⟨1254834064077761109261697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6692448341748059249395717 1254834064077761109261697)
      ·
        refine ⟨941125548058320831946273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1254834064077761109261697 941125548058320831946273)
        ·
          refine ⟨705844161043740623959705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 941125548058320831946273 705844161043740623959705)
          ·
            refine ⟨529383120782805467969779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 705844161043740623959705 529383120782805467969779)
            ·
              refine ⟨794074681174208201954669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 529383120782805467969779 794074681174208201954669)
              ·
                refine ⟨297778005440328075733001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 794074681174208201954669 297778005440328075733001)
                ·
                  refine ⟨223333504080246056799751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 297778005440328075733001 223333504080246056799751)
                  ·
                    rfl

theorem cell20_489308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 1, 3, 2].length) (baseStart_489308 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_489308 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_489308 prefixEnd_489308 := by exact prefixLift 489308
  have htrace : WordTrace (prefixWord ++ tailWord_489308) baseStart_489308 baseEnd_489308 := by
    simpa [prefixWord, tailWord_489308, baseEnd_489308] using wordTrace_append hprefix tailTrace_489308
  have hstable : (prefixWord ++ tailWord_489308).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489308).length < 2 ^ (prefixWord ++ tailWord_489308).sum := by decide
  have hdescent : baseEnd_489308 < baseStart_489308 := by decide
  rcases family_descends (prefixWord ++ tailWord_489308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489312 : List Nat := [2, 1, 1, 3, 3, 2, 3, 3, 2]
def baseStart_489312 : Nat := 118140960795 + 489312 * 2 ^ 59
def prefixEnd_489312 : Nat := 4983230072969 + 3 ^ 40 * 489312 * 2
def baseEnd_489312 : Nat := 223335329789239820666401

theorem tailTrace_489312 : CollatzResearch.WordTrace tailWord_489312 prefixEnd_489312 223335329789239820666401 := by
  unfold tailWord_489312
  simp only [CollatzResearch.WordTrace]
  refine ⟨8923337401656833340767095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11897783202209111121022793 8923337401656833340767095)
  ·
    refine ⟨13385006102485250011150643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8923337401656833340767095 13385006102485250011150643)
    ·
      refine ⟨20077509153727875016725965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13385006102485250011150643 20077509153727875016725965)
      ·
        refine ⟨7529065932647953131272237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20077509153727875016725965 7529065932647953131272237)
        ·
          refine ⟨2823399724742982424227089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7529065932647953131272237 2823399724742982424227089)
          ·
            refine ⟨2117549793557236818170317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2823399724742982424227089 2117549793557236818170317)
            ·
              refine ⟨794081172583963806813869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2117549793557236818170317 794081172583963806813869)
              ·
                refine ⟨297780439718986427555201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 794081172583963806813869 297780439718986427555201)
                ·
                  refine ⟨223335329789239820666401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 297780439718986427555201 223335329789239820666401)
                  ·
                    rfl

theorem cell20_489312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 3, 3, 2].length) (baseStart_489312 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_489312 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_489312 prefixEnd_489312 := by exact prefixLift 489312
  have htrace : WordTrace (prefixWord ++ tailWord_489312) baseStart_489312 baseEnd_489312 := by
    simpa [prefixWord, tailWord_489312, baseEnd_489312] using wordTrace_append hprefix tailTrace_489312
  have hstable : (prefixWord ++ tailWord_489312).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489312).length < 2 ^ (prefixWord ++ tailWord_489312).sum := by decide
  have hdescent : baseEnd_489312 < baseStart_489312 := by decide
  rcases family_descends (prefixWord ++ tailWord_489312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489326 : List Nat := [4, 1, 2, 3, 1, 1, 2, 1, 5]
def baseStart_489326 : Nat := 118140960795 + 489326 * 2 ^ 59
def prefixEnd_489326 : Nat := 4983230072969 + 3 ^ 40 * 489326 * 2
def baseEnd_489326 : Nat := 223341719770717994199677

theorem tailTrace_489326 : CollatzResearch.WordTrace tailWord_489326 prefixEnd_489326 223341719770717994199677 := by
  unfold tailWord_489326
  simp only [CollatzResearch.WordTrace]
  refine ⟨2230898178157868384067979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11898123616841964715029221 2230898178157868384067979)
  ·
    refine ⟨3346347267236802576101969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2230898178157868384067979 3346347267236802576101969)
    ·
      refine ⟨2509760450427601932076477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3346347267236802576101969 2509760450427601932076477)
      ·
        refine ⟨941160168910350724528679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2509760450427601932076477 941160168910350724528679)
        ·
          refine ⟨1411740253365526086793019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 941160168910350724528679 1411740253365526086793019)
          ·
            refine ⟨2117610380048289130189529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1411740253365526086793019 2117610380048289130189529)
            ·
              refine ⟨1588207785036216847642147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2117610380048289130189529 1588207785036216847642147)
              ·
                refine ⟨2382311677554325271463221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1588207785036216847642147 2382311677554325271463221)
                ·
                  refine ⟨223341719770717994199677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2382311677554325271463221 223341719770717994199677)
                  ·
                    rfl

theorem cell20_489326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 1, 5].length) (baseStart_489326 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_489326 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_489326 prefixEnd_489326 := by exact prefixLift 489326
  have htrace : WordTrace (prefixWord ++ tailWord_489326) baseStart_489326 baseEnd_489326 := by
    simpa [prefixWord, tailWord_489326, baseEnd_489326] using wordTrace_append hprefix tailTrace_489326
  have hstable : (prefixWord ++ tailWord_489326).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489326).length < 2 ^ (prefixWord ++ tailWord_489326).sum := by decide
  have hdescent : baseEnd_489326 < baseStart_489326 := by decide
  rcases family_descends (prefixWord ++ tailWord_489326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489361 : List Nat := [1, 2, 2, 1, 1, 1, 6, 6]
def baseStart_489361 : Nat := 118140960795 + 489361 * 2 ^ 59
def prefixEnd_489361 : Nat := 4983230072969 + 3 ^ 40 * 489361 * 2
def baseEnd_489361 : Nat := 74452564908137809344289

theorem tailTrace_489361 : CollatzResearch.WordTrace tailWord_489361 prefixEnd_489361 74452564908137809344289 := by
  unfold tailWord_489361
  simp only [CollatzResearch.WordTrace]
  refine ⟨17848461980136148050067937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11898974653424098700045291 17848461980136148050067937)
  ·
    refine ⟨13386346485102111037550953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17848461980136148050067937 13386346485102111037550953)
    ·
      refine ⟨10039759863826583278163215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13386346485102111037550953 10039759863826583278163215)
      ·
        refine ⟨15059639795739874917244823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10039759863826583278163215 15059639795739874917244823)
        ·
          refine ⟨22589459693609812375867235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15059639795739874917244823 22589459693609812375867235)
          ·
            refine ⟨33884189540414718563800853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22589459693609812375867235 33884189540414718563800853)
            ·
              refine ⟨1588321384706939932678165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 33884189540414718563800853 1588321384706939932678165)
              ·
                refine ⟨74452564908137809344289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1588321384706939932678165 74452564908137809344289)
                ·
                  rfl

theorem cell20_489361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 6].length) (baseStart_489361 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_489361 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_489361 prefixEnd_489361 := by exact prefixLift 489361
  have htrace : WordTrace (prefixWord ++ tailWord_489361) baseStart_489361 baseEnd_489361 := by
    simpa [prefixWord, tailWord_489361, baseEnd_489361] using wordTrace_append hprefix tailTrace_489361
  have hstable : (prefixWord ++ tailWord_489361).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489361).length < 2 ^ (prefixWord ++ tailWord_489361).sum := by decide
  have hdescent : baseEnd_489361 < baseStart_489361 := by decide
  rcases family_descends (prefixWord ++ tailWord_489361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489374 : List Nat := [4, 3, 1, 3, 2, 7]
def baseStart_489374 : Nat := 118140960795 + 489374 * 2 ^ 59
def prefixEnd_489374 : Nat := 4983230072969 + 3 ^ 40 * 489374 * 2
def baseEnd_489374 : Nat := 8272726973283080022203

theorem tailTrace_489374 : CollatzResearch.WordTrace tailWord_489374 prefixEnd_489374 8272726973283080022203 := by
  unfold tailWord_489374
  simp only [CollatzResearch.WordTrace]
  refine ⟨2231117016136131408786397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11899290752726034180194117 2231117016136131408786397)
  ·
    refine ⟨836668881051049278294899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2231117016136131408786397 836668881051049278294899)
    ·
      refine ⟨1255003321576573917442349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 836668881051049278294899 1255003321576573917442349)
      ·
        refine ⟨470626245591215219040881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1255003321576573917442349 470626245591215219040881)
        ·
          refine ⟨352969684193411414280661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 470626245591215219040881 352969684193411414280661)
          ·
            refine ⟨8272726973283080022203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 352969684193411414280661 8272726973283080022203)
            ·
              rfl

theorem cell20_489374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 7].length) (baseStart_489374 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_489374 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_489374 prefixEnd_489374 := by exact prefixLift 489374
  have htrace : WordTrace (prefixWord ++ tailWord_489374) baseStart_489374 baseEnd_489374 := by
    simpa [prefixWord, tailWord_489374, baseEnd_489374] using wordTrace_append hprefix tailTrace_489374
  have hstable : (prefixWord ++ tailWord_489374).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489374).length < 2 ^ (prefixWord ++ tailWord_489374).sum := by decide
  have hdescent : baseEnd_489374 < baseStart_489374 := by decide
  rcases family_descends (prefixWord ++ tailWord_489374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489378 : List Nat := [3, 3, 1, 2, 3, 8]
def baseStart_489378 : Nat := 118140960795 + 489378 * 2 ^ 59
def prefixEnd_489378 : Nat := 4983230072969 + 3 ^ 40 * 489378 * 2
def baseEnd_489378 : Nat := 8272794592134700906153

theorem tailTrace_489378 : CollatzResearch.WordTrace tailWord_489378 prefixEnd_489378 8272794592134700906153 := by
  unfold tailWord_489378
  simp only [CollatzResearch.WordTrace]
  refine ⟨4462270505268639988359197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11899388014049706635624525 4462270505268639988359197)
  ·
    refine ⟨1673351439475739995634699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4462270505268639988359197 1673351439475739995634699)
    ·
      refine ⟨2510027159213609993452049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1673351439475739995634699 2510027159213609993452049)
      ·
        refine ⟨1882520369410207495089037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2510027159213609993452049 1882520369410207495089037)
        ·
          refine ⟨705945138528827810658389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1882520369410207495089037 705945138528827810658389)
          ·
            refine ⟨8272794592134700906153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 705945138528827810658389 8272794592134700906153)
            ·
              rfl

theorem cell20_489378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 8].length) (baseStart_489378 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_489378 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_489378 prefixEnd_489378 := by exact prefixLift 489378
  have htrace : WordTrace (prefixWord ++ tailWord_489378) baseStart_489378 baseEnd_489378 := by
    simpa [prefixWord, tailWord_489378, baseEnd_489378] using wordTrace_append hprefix tailTrace_489378
  have hstable : (prefixWord ++ tailWord_489378).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489378).length < 2 ^ (prefixWord ++ tailWord_489378).sum := by decide
  have hdescent : baseEnd_489378 < baseStart_489378 := by decide
  rcases family_descends (prefixWord ++ tailWord_489378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489384 : List Nat := [2, 1, 6, 2, 1, 1, 1, 4, 2]
def baseStart_489384 : Nat := 118140960795 + 489384 * 2 ^ 59
def prefixEnd_489384 : Nat := 4983230072969 + 3 ^ 40 * 489384 * 2
def baseEnd_489384 : Nat := 223368192551127570266107

theorem tailTrace_489384 : CollatzResearch.WordTrace tailWord_489384 prefixEnd_489384 223368192551127570266107 := by
  unfold tailWord_489384
  simp only [CollatzResearch.WordTrace]
  refine ⟨8924650429526411489077603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11899533906035215318770137 8924650429526411489077603)
  ·
    refine ⟨13386975644289617233616405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8924650429526411489077603 13386975644289617233616405)
    ·
      refine ⟨627514483326075807825769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 13386975644289617233616405 627514483326075807825769)
      ·
        refine ⟨470635862494556855869327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 627514483326075807825769 470635862494556855869327)
        ·
          refine ⟨705953793741835283803991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 470635862494556855869327 705953793741835283803991)
          ·
            refine ⟨1058930690612752925705987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 705953793741835283803991 1058930690612752925705987)
            ·
              refine ⟨1588396035919129388558981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1058930690612752925705987 1588396035919129388558981)
              ·
                refine ⟨297824256734836760354809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1588396035919129388558981 297824256734836760354809)
                ·
                  refine ⟨223368192551127570266107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 297824256734836760354809 223368192551127570266107)
                  ·
                    rfl

theorem cell20_489384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 4, 2].length) (baseStart_489384 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_489384 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_489384 prefixEnd_489384 := by exact prefixLift 489384
  have htrace : WordTrace (prefixWord ++ tailWord_489384) baseStart_489384 baseEnd_489384 := by
    simpa [prefixWord, tailWord_489384, baseEnd_489384] using wordTrace_append hprefix tailTrace_489384
  have hstable : (prefixWord ++ tailWord_489384).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489384).length < 2 ^ (prefixWord ++ tailWord_489384).sum := by decide
  have hdescent : baseEnd_489384 < baseStart_489384 := by decide
  rcases family_descends (prefixWord ++ tailWord_489384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489436 : List Nat := [2, 2, 6, 1, 1, 1, 1, 1, 5]
def baseStart_489436 : Nat := 118140960795 + 489436 * 2 ^ 59
def prefixEnd_489436 : Nat := 4983230072969 + 3 ^ 40 * 489436 * 2
def baseEnd_489436 : Nat := 223391926768046500532561

theorem tailTrace_489436 : CollatzResearch.WordTrace tailWord_489436 prefixEnd_489436 223391926768046500532561 := by
  unfold tailWord_489436
  simp only [CollatzResearch.WordTrace]
  refine ⟨8925598727432217929524081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11900798303242957239365441 8925598727432217929524081)
  ·
    refine ⟨6694199045574163447143061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8925598727432217929524081 6694199045574163447143061)
    ·
      refine ⟨313790580261288911584831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 6694199045574163447143061 313790580261288911584831)
      ·
        refine ⟨470685870391933367377247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313790580261288911584831 470685870391933367377247)
        ·
          refine ⟨706028805587900051065871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 470685870391933367377247 706028805587900051065871)
          ·
            refine ⟨1059043208381850076598807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 706028805587900051065871 1059043208381850076598807)
            ·
              refine ⟨1588564812572775114898211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1059043208381850076598807 1588564812572775114898211)
              ·
                refine ⟨2382847218859162672347317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1588564812572775114898211 2382847218859162672347317)
                ·
                  refine ⟨223391926768046500532561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2382847218859162672347317 223391926768046500532561)
                  ·
                    rfl

theorem cell20_489436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 1, 5].length) (baseStart_489436 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_489436 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_489436 prefixEnd_489436 := by exact prefixLift 489436
  have htrace : WordTrace (prefixWord ++ tailWord_489436) baseStart_489436 baseEnd_489436 := by
    simpa [prefixWord, tailWord_489436, baseEnd_489436] using wordTrace_append hprefix tailTrace_489436
  have hstable : (prefixWord ++ tailWord_489436).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489436).length < 2 ^ (prefixWord ++ tailWord_489436).sum := by decide
  have hdescent : baseEnd_489436 < baseStart_489436 := by decide
  rcases family_descends (prefixWord ++ tailWord_489436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489457 : List Nat := [1, 2, 2, 2, 5, 1, 3, 1, 3]
def baseStart_489457 : Nat := 118140960795 + 489457 * 2 ^ 59
def prefixEnd_489457 : Nat := 4983230072969 + 3 ^ 40 * 489457 * 2
def baseEnd_489457 : Nat := 223401511740263760832475

theorem tailTrace_489457 : CollatzResearch.WordTrace tailWord_489457 prefixEnd_489457 223401511740263760832475 := by
  unfold tailWord_489457
  simp only [CollatzResearch.WordTrace]
  refine ⟨17851963387788356445562625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11901308925192237630375083 17851963387788356445562625)
  ·
    refine ⟨13388972540841267334171969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17851963387788356445562625 13388972540841267334171969)
    ·
      refine ⟨10041729405630950500628977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13388972540841267334171969 10041729405630950500628977)
      ·
        refine ⟨7531297054223212875471733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10041729405630950500628977 7531297054223212875471733)
        ·
          refine ⟨706059098833426207075475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7531297054223212875471733 706059098833426207075475)
          ·
            refine ⟨1059088648250139310613213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 706059098833426207075475 1059088648250139310613213)
            ·
              refine ⟨397158243093802241479955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1059088648250139310613213 397158243093802241479955)
              ·
                refine ⟨595737364640703362219933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 397158243093802241479955 595737364640703362219933)
                ·
                  refine ⟨223401511740263760832475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 595737364640703362219933 223401511740263760832475)
                  ·
                    rfl

theorem cell20_489457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 3, 1, 3].length) (baseStart_489457 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_489457 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_489457 prefixEnd_489457 := by exact prefixLift 489457
  have htrace : WordTrace (prefixWord ++ tailWord_489457) baseStart_489457 baseEnd_489457 := by
    simpa [prefixWord, tailWord_489457, baseEnd_489457] using wordTrace_append hprefix tailTrace_489457
  have hstable : (prefixWord ++ tailWord_489457).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489457).length < 2 ^ (prefixWord ++ tailWord_489457).sum := by decide
  have hdescent : baseEnd_489457 < baseStart_489457 := by decide
  rcases family_descends (prefixWord ++ tailWord_489457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489468 : List Nat := [2, 2, 2, 1, 2, 2, 1, 4, 4]
def baseStart_489468 : Nat := 118140960795 + 489468 * 2 ^ 59
def prefixEnd_489468 : Nat := 4983230072969 + 3 ^ 40 * 489468 * 2
def baseEnd_489468 : Nat := 223406532439996611465763

theorem tailTrace_489468 : CollatzResearch.WordTrace tailWord_489468 prefixEnd_489468 223406532439996611465763 := by
  unfold tailWord_489468
  simp only [CollatzResearch.WordTrace]
  refine ⟨8926182295374252662106529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11901576393832336882808705 8926182295374252662106529)
  ·
    refine ⟨6694636721530689496579897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8926182295374252662106529 6694636721530689496579897)
    ·
      refine ⟨5020977541148017122434923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6694636721530689496579897 5020977541148017122434923)
      ·
        refine ⟨7531466311722025683652385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5020977541148017122434923 7531466311722025683652385)
        ·
          refine ⟨5648599733791519262739289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7531466311722025683652385 5648599733791519262739289)
          ·
            refine ⟨4236449800343639447054467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5648599733791519262739289 4236449800343639447054467)
            ·
              refine ⟨6354674700515459170581701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4236449800343639447054467 6354674700515459170581701)
              ·
                refine ⟨1191501506346648594484069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6354674700515459170581701 1191501506346648594484069)
                ·
                  refine ⟨223406532439996611465763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1191501506346648594484069 223406532439996611465763)
                  ·
                    rfl

theorem cell20_489468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 4, 4].length) (baseStart_489468 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_489468 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_489468 prefixEnd_489468 := by exact prefixLift 489468
  have htrace : WordTrace (prefixWord ++ tailWord_489468) baseStart_489468 baseEnd_489468 := by
    simpa [prefixWord, tailWord_489468, baseEnd_489468] using wordTrace_append hprefix tailTrace_489468
  have hstable : (prefixWord ++ tailWord_489468).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489468).length < 2 ^ (prefixWord ++ tailWord_489468).sum := by decide
  have hdescent : baseEnd_489468 < baseStart_489468 := by decide
  rcases family_descends (prefixWord ++ tailWord_489468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489557 : List Nat := [1, 3, 2, 2, 1, 5, 2, 2, 2]
def baseStart_489557 : Nat := 118140960795 + 489557 * 2 ^ 59
def prefixEnd_489557 : Nat := 4983230072969 + 3 ^ 40 * 489557 * 2
def baseEnd_489557 : Nat := 223447154465107857498733

theorem tailTrace_489557 : CollatzResearch.WordTrace tailWord_489557 prefixEnd_489557 223447154465107857498733 := by
  unfold tailWord_489557
  simp only [CollatzResearch.WordTrace]
  refine ⟨17855610687426073524202925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11903740458284049016135283 17855610687426073524202925)
  ·
    refine ⟨6695854007784777571576097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17855610687426073524202925 6695854007784777571576097)
    ·
      refine ⟨5021890505838583178682073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6695854007784777571576097 5021890505838583178682073)
      ·
        refine ⟨3766417879378937384011555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5021890505838583178682073 3766417879378937384011555)
        ·
          refine ⟨5649626819068406076017333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3766417879378937384011555 5649626819068406076017333)
          ·
            refine ⟨529652514287663069626625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5649626819068406076017333 529652514287663069626625)
            ·
              refine ⟨397239385715747302219969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 529652514287663069626625 397239385715747302219969)
              ·
                refine ⟨297929539286810476664977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 397239385715747302219969 297929539286810476664977)
                ·
                  refine ⟨223447154465107857498733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 297929539286810476664977 223447154465107857498733)
                  ·
                    rfl

theorem cell20_489557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 2, 2, 2].length) (baseStart_489557 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_489557 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_489557 prefixEnd_489557 := by exact prefixLift 489557
  have htrace : WordTrace (prefixWord ++ tailWord_489557) baseStart_489557 baseEnd_489557 := by
    simpa [prefixWord, tailWord_489557, baseEnd_489557] using wordTrace_append hprefix tailTrace_489557
  have hstable : (prefixWord ++ tailWord_489557).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489557).length < 2 ^ (prefixWord ++ tailWord_489557).sum := by decide
  have hdescent : baseEnd_489557 < baseStart_489557 := by decide
  rcases family_descends (prefixWord ++ tailWord_489557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489561 : List Nat := [1, 2, 1, 2, 2, 1, 5, 4, 2]
def baseStart_489561 : Nat := 118140960795 + 489561 * 2 ^ 59
def prefixEnd_489561 : Nat := 4983230072969 + 3 ^ 40 * 489561 * 2
def baseEnd_489561 : Nat := 223448980174101621365383

theorem tailTrace_489561 : CollatzResearch.WordTrace tailWord_489561 prefixEnd_489561 223448980174101621365383 := by
  unfold tailWord_489561
  simp only [CollatzResearch.WordTrace]
  refine ⟨17855756579411582207348537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11903837719607721471565691 17855756579411582207348537)
  ·
    refine ⟨13391817434558686655511403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17855756579411582207348537 13391817434558686655511403)
    ·
      refine ⟨20087726151838029983267105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13391817434558686655511403 20087726151838029983267105)
      ·
        refine ⟨15065794613878522487450329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20087726151838029983267105 15065794613878522487450329)
        ·
          refine ⟨11299345960408891865587747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15065794613878522487450329 11299345960408891865587747)
          ·
            refine ⟨16949018940613337798381621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11299345960408891865587747 16949018940613337798381621)
            ·
              refine ⟨1588970525682500418598277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16949018940613337798381621 1588970525682500418598277)
              ·
                refine ⟨297931973565468828487177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1588970525682500418598277 297931973565468828487177)
                ·
                  refine ⟨223448980174101621365383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 297931973565468828487177 223448980174101621365383)
                  ·
                    rfl

theorem cell20_489561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 4, 2].length) (baseStart_489561 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_489561 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_489561 prefixEnd_489561 := by exact prefixLift 489561
  have htrace : WordTrace (prefixWord ++ tailWord_489561) baseStart_489561 baseEnd_489561 := by
    simpa [prefixWord, tailWord_489561, baseEnd_489561] using wordTrace_append hprefix tailTrace_489561
  have hstable : (prefixWord ++ tailWord_489561).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489561).length < 2 ^ (prefixWord ++ tailWord_489561).sum := by decide
  have hdescent : baseEnd_489561 < baseStart_489561 := by decide
  rcases family_descends (prefixWord ++ tailWord_489561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489568 : List Nat := [2, 1, 1, 3, 2, 5, 1, 5]
def baseStart_489568 : Nat := 118140960795 + 489568 * 2 ^ 59
def prefixEnd_489568 : Nat := 4983230072969 + 3 ^ 40 * 489568 * 2
def baseEnd_489568 : Nat := 74484058388280236044007

theorem tailTrace_489568 : CollatzResearch.WordTrace tailWord_489568 prefixEnd_489568 74484058388280236044007 := by
  unfold tailWord_489568
  simp only [CollatzResearch.WordTrace]
  refine ⟨8928005945193111201426679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11904007926924148268568905 8928005945193111201426679)
  ·
    refine ⟨13392008917789666802140019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8928005945193111201426679 13392008917789666802140019)
    ·
      refine ⟨20088013376684500203210029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13392008917789666802140019 20088013376684500203210029)
      ·
        refine ⟨7533005016256687576203761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20088013376684500203210029 7533005016256687576203761)
        ·
          refine ⟨5649753762192515682152821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7533005016256687576203761 5649753762192515682152821)
          ·
            refine ⟨529664415205548345201827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5649753762192515682152821 529664415205548345201827)
            ·
              refine ⟨794496622808322517802741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 529664415205548345201827 794496622808322517802741)
              ·
                refine ⟨74484058388280236044007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 794496622808322517802741 74484058388280236044007)
                ·
                  rfl

theorem cell20_489568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 1, 5].length) (baseStart_489568 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_489568 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_489568 prefixEnd_489568 := by exact prefixLift 489568
  have htrace : WordTrace (prefixWord ++ tailWord_489568) baseStart_489568 baseEnd_489568 := by
    simpa [prefixWord, tailWord_489568, baseEnd_489568] using wordTrace_append hprefix tailTrace_489568
  have hstable : (prefixWord ++ tailWord_489568).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489568).length < 2 ^ (prefixWord ++ tailWord_489568).sum := by decide
  have hdescent : baseEnd_489568 < baseStart_489568 := by decide
  rcases family_descends (prefixWord ++ tailWord_489568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489575 : List Nat := [1, 1, 5, 1, 1, 2, 1, 5, 3]
def baseStart_489575 : Nat := 118140960795 + 489575 * 2 ^ 59
def prefixEnd_489575 : Nat := 4983230072969 + 3 ^ 40 * 489575 * 2
def baseEnd_489575 : Nat := 223455370155579794898659

theorem tailTrace_489575 : CollatzResearch.WordTrace tailWord_489575 prefixEnd_489575 223455370155579794898659 := by
  unfold tailWord_489575
  simp only [CollatzResearch.WordTrace]
  refine ⟨17856267201360862598358179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11904178134240575065572119 17856267201360862598358179)
  ·
    refine ⟨26784400802041293897537269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17856267201360862598358179 26784400802041293897537269)
    ·
      refine ⟨2511037575191371302894119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 26784400802041293897537269 2511037575191371302894119)
      ·
        refine ⟨3766556362787056954341179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2511037575191371302894119 3766556362787056954341179)
        ·
          refine ⟨5649834544180585431511769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3766556362787056954341179 5649834544180585431511769)
          ·
            refine ⟨4237375908135439073633827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5649834544180585431511769 4237375908135439073633827)
            ·
              refine ⟨6356063862203158610450741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4237375908135439073633827 6356063862203158610450741)
              ·
                refine ⟨595880987081546119729757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6356063862203158610450741 595880987081546119729757)
                ·
                  refine ⟨223455370155579794898659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 595880987081546119729757 223455370155579794898659)
                  ·
                    rfl

theorem cell20_489575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 5, 3].length) (baseStart_489575 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_489575 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_489575 prefixEnd_489575 := by exact prefixLift 489575
  have htrace : WordTrace (prefixWord ++ tailWord_489575) baseStart_489575 baseEnd_489575 := by
    simpa [prefixWord, tailWord_489575, baseEnd_489575] using wordTrace_append hprefix tailTrace_489575
  have hstable : (prefixWord ++ tailWord_489575).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489575).length < 2 ^ (prefixWord ++ tailWord_489575).sum := by decide
  have hdescent : baseEnd_489575 < baseStart_489575 := by decide
  rcases family_descends (prefixWord ++ tailWord_489575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489682 : List Nat := [3, 2, 2, 2, 1, 3, 2, 5]
def baseStart_489682 : Nat := 118140960795 + 489682 * 2 ^ 59
def prefixEnd_489682 : Nat := 4983230072969 + 3 ^ 40 * 489682 * 2
def baseEnd_489682 : Nat := 74501402623720992777185

theorem tailTrace_489682 : CollatzResearch.WordTrace tailWord_489682 prefixEnd_489682 74501402623720992777185 := by
  unfold tailWord_489682
  simp only [CollatzResearch.WordTrace]
  refine ⟨4465042452993304968125825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11906779874648813248335533 4465042452993304968125825)
  ·
    refine ⟨3348781839744978726094369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4465042452993304968125825 3348781839744978726094369)
    ·
      refine ⟨2511586379808734044570777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3348781839744978726094369 2511586379808734044570777)
      ·
        refine ⟨1883689784856550533428083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2511586379808734044570777 1883689784856550533428083)
        ·
          refine ⟨2825534677284825800142125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1883689784856550533428083 2825534677284825800142125)
          ·
            refine ⟨1059575503981809675053297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2825534677284825800142125 1059575503981809675053297)
            ·
              refine ⟨794681627986357256289973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1059575503981809675053297 794681627986357256289973)
              ·
                refine ⟨74501402623720992777185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 794681627986357256289973 74501402623720992777185)
                ·
                  rfl

theorem cell20_489682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 2, 5].length) (baseStart_489682 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_489682 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_489682 prefixEnd_489682 := by exact prefixLift 489682
  have htrace : WordTrace (prefixWord ++ tailWord_489682) baseStart_489682 baseEnd_489682 := by
    simpa [prefixWord, tailWord_489682, baseEnd_489682] using wordTrace_append hprefix tailTrace_489682
  have hstable : (prefixWord ++ tailWord_489682).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489682).length < 2 ^ (prefixWord ++ tailWord_489682).sum := by decide
  have hdescent : baseEnd_489682 < baseStart_489682 := by decide
  rcases family_descends (prefixWord ++ tailWord_489682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489727 : List Nat := [1, 1, 2, 2, 1, 4, 4, 2, 3]
def baseStart_489727 : Nat := 118140960795 + 489727 * 2 ^ 59
def prefixEnd_489727 : Nat := 4983230072969 + 3 ^ 40 * 489727 * 2
def baseEnd_489727 : Nat := 223524747097342821831371

theorem tailTrace_489727 : CollatzResearch.WordTrace tailWord_489727 prefixEnd_489727 223524747097342821831371 := by
  unfold tailWord_489727
  simp only [CollatzResearch.WordTrace]
  refine ⟨17861811096810192557891435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11907874064540128371927623 17861811096810192557891435)
  ·
    refine ⟨26792716645215288836837153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17861811096810192557891435 26792716645215288836837153)
    ·
      refine ⟨20094537483911466627627865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26792716645215288836837153 20094537483911466627627865)
      ·
        refine ⟨15070903112933599970720899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20094537483911466627627865 15070903112933599970720899)
        ·
          refine ⟨22606354669400399956081349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15070903112933599970720899 22606354669400399956081349)
          ·
            refine ⟨4238691500512574991765253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22606354669400399956081349 4238691500512574991765253)
            ·
              refine ⟨794754656346107810955985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4238691500512574991765253 794754656346107810955985)
              ·
                refine ⟨596065992259580858216989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 794754656346107810955985 596065992259580858216989)
                ·
                  refine ⟨223524747097342821831371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 596065992259580858216989 223524747097342821831371)
                  ·
                    rfl

theorem cell20_489727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 4, 2, 3].length) (baseStart_489727 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_489727 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_489727 prefixEnd_489727 := by exact prefixLift 489727
  have htrace : WordTrace (prefixWord ++ tailWord_489727) baseStart_489727 baseEnd_489727 := by
    simpa [prefixWord, tailWord_489727, baseEnd_489727] using wordTrace_append hprefix tailTrace_489727
  have hstable : (prefixWord ++ tailWord_489727).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489727).length < 2 ^ (prefixWord ++ tailWord_489727).sum := by decide
  have hdescent : baseEnd_489727 < baseStart_489727 := by decide
  rcases family_descends (prefixWord ++ tailWord_489727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489755 : List Nat := [1, 1, 1, 1, 1, 1, 7, 1, 6]
def baseStart_489755 : Nat := 118140960795 + 489755 * 2 ^ 59
def prefixEnd_489755 : Nat := 4983230072969 + 3 ^ 40 * 489755 * 2
def baseEnd_489755 : Nat := 223537527060299168897923

theorem tailTrace_489755 : CollatzResearch.WordTrace tailWord_489755 prefixEnd_489755 223537527060299168897923 := by
  unfold tailWord_489755
  simp only [CollatzResearch.WordTrace]
  refine ⟨17862832340708753339910719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11908554893805835559940479 17862832340708753339910719)
  ·
    refine ⟨26794248511063130009866079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17862832340708753339910719 26794248511063130009866079)
    ·
      refine ⟨40191372766594695014799119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26794248511063130009866079 40191372766594695014799119)
      ·
        refine ⟨60287059149892042522198679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40191372766594695014799119 60287059149892042522198679)
        ·
          refine ⟨90430588724838063783298019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60287059149892042522198679 90430588724838063783298019)
          ·
            refine ⟨135645883087257095674947029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90430588724838063783298019 135645883087257095674947029)
            ·
              refine ⟨3179200384857588179881571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 135645883087257095674947029 3179200384857588179881571)
              ·
                refine ⟨4768800577286382269822357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3179200384857588179881571 4768800577286382269822357)
                ·
                  refine ⟨223537527060299168897923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4768800577286382269822357 223537527060299168897923)
                  ·
                    rfl

theorem cell20_489755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 1, 6].length) (baseStart_489755 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_489755 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_489755 prefixEnd_489755 := by exact prefixLift 489755
  have htrace : WordTrace (prefixWord ++ tailWord_489755) baseStart_489755 baseEnd_489755 := by
    simpa [prefixWord, tailWord_489755, baseEnd_489755] using wordTrace_append hprefix tailTrace_489755
  have hstable : (prefixWord ++ tailWord_489755).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489755).length < 2 ^ (prefixWord ++ tailWord_489755).sum := by decide
  have hdescent : baseEnd_489755 < baseStart_489755 := by decide
  rcases family_descends (prefixWord ++ tailWord_489755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489810 : List Nat := [3, 2, 2, 1, 1, 1, 4, 2, 4]
def baseStart_489810 : Nat := 118140960795 + 489810 * 2 ^ 59
def prefixEnd_489810 : Nat := 4983230072969 + 3 ^ 40 * 489810 * 2
def baseEnd_489810 : Nat := 223562630558963422064365

theorem tailTrace_489810 : CollatzResearch.WordTrace tailWord_489810 prefixEnd_489810 223562630558963422064365 := by
  unfold tailWord_489810
  simp only [CollatzResearch.WordTrace]
  refine ⟨4466209588877374433290721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11909892237006331822108589 4466209588877374433290721)
  ·
    refine ⟨3349657191658030824968041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4466209588877374433290721 3349657191658030824968041)
    ·
      refine ⟨2512242893743523118726031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3349657191658030824968041 2512242893743523118726031)
      ·
        refine ⟨3768364340615284678089047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2512242893743523118726031 3768364340615284678089047)
        ·
          refine ⟨5652546510922927017133571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3768364340615284678089047 5652546510922927017133571)
          ·
            refine ⟨8478819766384390525700357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5652546510922927017133571 8478819766384390525700357)
            ·
              refine ⟨1589778706197073223568817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8478819766384390525700357 1589778706197073223568817)
              ·
                refine ⟨1192334029647804917676613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1589778706197073223568817 1192334029647804917676613)
                ·
                  refine ⟨223562630558963422064365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1192334029647804917676613 223562630558963422064365)
                  ·
                    rfl

theorem cell20_489810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 2, 4].length) (baseStart_489810 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_489810 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_489810 prefixEnd_489810 := by exact prefixLift 489810
  have htrace : WordTrace (prefixWord ++ tailWord_489810) baseStart_489810 baseEnd_489810 := by
    simpa [prefixWord, tailWord_489810, baseEnd_489810] using wordTrace_append hprefix tailTrace_489810
  have hstable : (prefixWord ++ tailWord_489810).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489810).length < 2 ^ (prefixWord ++ tailWord_489810).sum := by decide
  have hdescent : baseEnd_489810 < baseStart_489810 := by decide
  rcases family_descends (prefixWord ++ tailWord_489810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489813 : List Nat := [1, 3, 2, 2, 4, 2, 2, 4]
def baseStart_489813 : Nat := 118140960795 + 489813 * 2 ^ 59
def prefixEnd_489813 : Nat := 4983230072969 + 3 ^ 40 * 489813 * 2
def baseEnd_489813 : Nat := 74521333280236248321451

theorem tailTrace_489813 : CollatzResearch.WordTrace tailWord_489813 prefixEnd_489813 74521333280236248321451 := by
  unfold tailWord_489813
  simp only [CollatzResearch.WordTrace]
  refine ⟨17864947774498629245522093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11909965182999086163681395 17864947774498629245522093)
  ·
    refine ⟨6699355415436985967070785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17864947774498629245522093 6699355415436985967070785)
    ·
      refine ⟨5024516561577739475303089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6699355415436985967070785 5024516561577739475303089)
      ·
        refine ⟨3768387421183304606477317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5024516561577739475303089 3768387421183304606477317)
        ·
          refine ⟨706572641471869613714497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3768387421183304606477317 706572641471869613714497)
          ·
            refine ⟨529929481103902210285873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 706572641471869613714497 529929481103902210285873)
            ·
              refine ⟨397447110827926657714405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 529929481103902210285873 397447110827926657714405)
              ·
                refine ⟨74521333280236248321451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 397447110827926657714405 74521333280236248321451)
                ·
                  rfl

theorem cell20_489813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 2, 4].length) (baseStart_489813 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_489813 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_489813 prefixEnd_489813 := by exact prefixLift 489813
  have htrace : WordTrace (prefixWord ++ tailWord_489813) baseStart_489813 baseEnd_489813 := by
    simpa [prefixWord, tailWord_489813, baseEnd_489813] using wordTrace_append hprefix tailTrace_489813
  have hstable : (prefixWord ++ tailWord_489813).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489813).length < 2 ^ (prefixWord ++ tailWord_489813).sum := by decide
  have hdescent : baseEnd_489813 < baseStart_489813 := by decide
  rcases family_descends (prefixWord ++ tailWord_489813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489834 : List Nat := [3, 1, 3, 3, 1, 3, 6]
def baseStart_489834 : Nat := 118140960795 + 489834 * 2 ^ 59
def prefixEnd_489834 : Nat := 4983230072969 + 3 ^ 40 * 489834 * 2
def baseEnd_489834 : Nat := 24841509423658445029363

theorem tailTrace_489834 : CollatzResearch.WordTrace tailWord_489834 prefixEnd_489834 24841509423658445029363 := by
  unfold tailWord_489834
  simp only [CollatzResearch.WordTrace]
  refine ⟨4466428426855637458009139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11910475804948366554691037 4466428426855637458009139)
  ·
    refine ⟨6699642640283456187013709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4466428426855637458009139 6699642640283456187013709)
    ·
      refine ⟨2512365990106296070130141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6699642640283456187013709 2512365990106296070130141)
      ·
        refine ⟨942137246289861026298803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2512365990106296070130141 942137246289861026298803)
        ·
          refine ⟨1413205869434791539448205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 942137246289861026298803 1413205869434791539448205)
          ·
            refine ⟨529952201038046827293077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1413205869434791539448205 529952201038046827293077)
            ·
              refine ⟨24841509423658445029363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 529952201038046827293077 24841509423658445029363)
              ·
                rfl

theorem cell20_489834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 6].length) (baseStart_489834 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_489834 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_489834 prefixEnd_489834 := by exact prefixLift 489834
  have htrace : WordTrace (prefixWord ++ tailWord_489834) baseStart_489834 baseEnd_489834 := by
    simpa [prefixWord, tailWord_489834, baseEnd_489834] using wordTrace_append hprefix tailTrace_489834
  have hstable : (prefixWord ++ tailWord_489834).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489834).length < 2 ^ (prefixWord ++ tailWord_489834).sum := by decide
  have hdescent : baseEnd_489834 < baseStart_489834 := by decide
  rcases family_descends (prefixWord ++ tailWord_489834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489896 : List Nat := [2, 1, 6, 1, 1, 1, 1, 4, 3]
def baseStart_489896 : Nat := 118140960795 + 489896 * 2 ^ 59
def prefixEnd_489896 : Nat := 4983230072969 + 3 ^ 40 * 489896 * 2
def baseEnd_489896 : Nat := 223601883302329345197347

theorem tailTrace_489896 : CollatzResearch.WordTrace tailWord_489896 prefixEnd_489896 223601883302329345197347 := by
  unfold tailWord_489896
  simp only [CollatzResearch.WordTrace]
  refine ⟨8933987516598967210396771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11911983355465289613862361 8933987516598967210396771)
  ·
    refine ⟨13400981274898450815595157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8933987516598967210396771 13400981274898450815595157)
    ·
      refine ⟨628170997260864881981023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 13400981274898450815595157 628170997260864881981023)
      ·
        refine ⟨942256495891297322971535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 628170997260864881981023 942256495891297322971535)
        ·
          refine ⟨1413384743836945984457303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 942256495891297322971535 1413384743836945984457303)
          ·
            refine ⟨2120077115755418976685955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1413384743836945984457303 2120077115755418976685955)
            ·
              refine ⟨3180115673633128465028933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2120077115755418976685955 3180115673633128465028933)
              ·
                refine ⟨596271688806211587192925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3180115673633128465028933 596271688806211587192925)
                ·
                  refine ⟨223601883302329345197347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 596271688806211587192925 223601883302329345197347)
                  ·
                    rfl

theorem cell20_489896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 4, 3].length) (baseStart_489896 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_489896 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_489896 prefixEnd_489896 := by exact prefixLift 489896
  have htrace : WordTrace (prefixWord ++ tailWord_489896) baseStart_489896 baseEnd_489896 := by
    simpa [prefixWord, tailWord_489896, baseEnd_489896] using wordTrace_append hprefix tailTrace_489896
  have hstable : (prefixWord ++ tailWord_489896).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489896).length < 2 ^ (prefixWord ++ tailWord_489896).sum := by decide
  have hdescent : baseEnd_489896 < baseStart_489896 := by decide
  rcases family_descends (prefixWord ++ tailWord_489896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489917 : List Nat := [1, 4, 1, 2, 2, 2, 2, 3, 3]
def baseStart_489917 : Nat := 118140960795 + 489917 * 2 ^ 59
def prefixEnd_489917 : Nat := 4983230072969 + 3 ^ 40 * 489917 * 2
def baseEnd_489917 : Nat := 223611468274546605497261

theorem tailTrace_489917 : CollatzResearch.WordTrace tailWord_489917 prefixEnd_489917 223611468274546605497261 := by
  unfold tailWord_489917
  simp only [CollatzResearch.WordTrace]
  refine ⟨17868740966121855007308005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11912493977414570004872003 17868740966121855007308005)
  ·
    refine ⟨3350388931147847813870251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17868740966121855007308005 3350388931147847813870251)
    ·
      refine ⟨5025583396721771720805377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3350388931147847813870251 5025583396721771720805377)
      ·
        refine ⟨3769187547541328790604033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5025583396721771720805377 3769187547541328790604033)
        ·
          refine ⟨2826890660655996592953025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3769187547541328790604033 2826890660655996592953025)
          ·
            refine ⟨2120167995491997444714769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2826890660655996592953025 2120167995491997444714769)
            ·
              refine ⟨1590125996618998083536077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2120167995491997444714769 1590125996618998083536077)
              ·
                refine ⟨596297248732124281326029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1590125996618998083536077 596297248732124281326029)
                ·
                  refine ⟨223611468274546605497261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 596297248732124281326029 223611468274546605497261)
                  ·
                    rfl

theorem cell20_489917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 3, 3].length) (baseStart_489917 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_489917 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_489917 prefixEnd_489917 := by exact prefixLift 489917
  have htrace : WordTrace (prefixWord ++ tailWord_489917) baseStart_489917 baseEnd_489917 := by
    simpa [prefixWord, tailWord_489917, baseEnd_489917] using wordTrace_append hprefix tailTrace_489917
  have hstable : (prefixWord ++ tailWord_489917).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489917).length < 2 ^ (prefixWord ++ tailWord_489917).sum := by decide
  have hdescent : baseEnd_489917 < baseStart_489917 := by decide
  rcases family_descends (prefixWord ++ tailWord_489917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489941 : List Nat := [1, 3, 2, 3, 1, 2, 1, 5, 2]
def baseStart_489941 : Nat := 118140960795 + 489941 * 2 ^ 59
def prefixEnd_489941 : Nat := 4983230072969 + 3 ^ 40 * 489941 * 2
def baseEnd_489941 : Nat := 223622422528509188697163

theorem tailTrace_489941 : CollatzResearch.WordTrace tailWord_489941 prefixEnd_489941 223622422528509188697163 := by
  unfold tailWord_489941
  simp only [CollatzResearch.WordTrace]
  refine ⟨17869616318034907106181677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11913077545356604737454451 17869616318034907106181677)
  ·
    refine ⟨6701106119263090164818129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17869616318034907106181677 6701106119263090164818129)
    ·
      refine ⟨5025829589447317623613597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6701106119263090164818129 5025829589447317623613597)
      ·
        refine ⟨1884686096042744108855099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5025829589447317623613597 1884686096042744108855099)
        ·
          refine ⟨2827029144064116163282649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1884686096042744108855099 2827029144064116163282649)
          ·
            refine ⟨2120271858048087122461987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2827029144064116163282649 2120271858048087122461987)
            ·
              refine ⟨3180407787072130683692981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2120271858048087122461987 3180407787072130683692981)
              ·
                refine ⟨298163230038012251596217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3180407787072130683692981 298163230038012251596217)
                ·
                  refine ⟨223622422528509188697163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 298163230038012251596217 223622422528509188697163)
                  ·
                    rfl

theorem cell20_489941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 5, 2].length) (baseStart_489941 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_489941 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_489941 prefixEnd_489941 := by exact prefixLift 489941
  have htrace : WordTrace (prefixWord ++ tailWord_489941) baseStart_489941 baseEnd_489941 := by
    simpa [prefixWord, tailWord_489941, baseEnd_489941] using wordTrace_append hprefix tailTrace_489941
  have hstable : (prefixWord ++ tailWord_489941).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489941).length < 2 ^ (prefixWord ++ tailWord_489941).sum := by decide
  have hdescent : baseEnd_489941 < baseStart_489941 := by decide
  rcases family_descends (prefixWord ++ tailWord_489941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489945 : List Nat := [1, 2, 1, 2, 4, 1, 1, 2, 6]
def baseStart_489945 : Nat := 118140960795 + 489945 * 2 ^ 59
def prefixEnd_489945 : Nat := 4983230072969 + 3 ^ 40 * 489945 * 2
def baseEnd_489945 : Nat := 223624248237502952563813

theorem tailTrace_489945 : CollatzResearch.WordTrace tailWord_489945 prefixEnd_489945 223624248237502952563813 := by
  unfold tailWord_489945
  simp only [CollatzResearch.WordTrace]
  refine ⟨17869762210020415789327289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11913174806680277192884859 17869762210020415789327289)
  ·
    refine ⟨13402321657515311841995467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17869762210020415789327289 13402321657515311841995467)
    ·
      refine ⟨20103482486272967762993201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13402321657515311841995467 20103482486272967762993201)
      ·
        refine ⟨15077611864704725822244901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20103482486272967762993201 15077611864704725822244901)
        ·
          refine ⟨2827052224632136091670919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15077611864704725822244901 2827052224632136091670919)
          ·
            refine ⟨4240578336948204137506379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2827052224632136091670919 4240578336948204137506379)
            ·
              refine ⟨6360867505422306206259569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4240578336948204137506379 6360867505422306206259569)
              ·
                refine ⟨4770650629066729654694677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6360867505422306206259569 4770650629066729654694677)
                ·
                  refine ⟨223624248237502952563813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4770650629066729654694677 223624248237502952563813)
                  ·
                    rfl

theorem cell20_489945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 2, 6].length) (baseStart_489945 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_489945 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_489945 prefixEnd_489945 := by exact prefixLift 489945
  have htrace : WordTrace (prefixWord ++ tailWord_489945) baseStart_489945 baseEnd_489945 := by
    simpa [prefixWord, tailWord_489945, baseEnd_489945] using wordTrace_append hprefix tailTrace_489945
  have hstable : (prefixWord ++ tailWord_489945).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489945).length < 2 ^ (prefixWord ++ tailWord_489945).sum := by decide
  have hdescent : baseEnd_489945 < baseStart_489945 := by decide
  rcases family_descends (prefixWord ++ tailWord_489945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489952 : List Nat := [2, 1, 1, 3, 1, 1, 11]
def baseStart_489952 : Nat := 118140960795 + 489952 * 2 ^ 59
def prefixEnd_489952 : Nat := 4983230072969 + 3 ^ 40 * 489952 * 2
def baseEnd_489952 : Nat := 24847493692026893258939

theorem tailTrace_489952 : CollatzResearch.WordTrace tailWord_489952 prefixEnd_489952 24847493692026893258939 := by
  unfold tailWord_489952
  simp only [CollatzResearch.WordTrace]
  refine ⟨8935008760497527992416055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11913345013996703989888073 8935008760497527992416055)
  ·
    refine ⟨13402513140746291988624083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8935008760497527992416055 13402513140746291988624083)
    ·
      refine ⟨20103769711119437982936125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13402513140746291988624083 20103769711119437982936125)
      ·
        refine ⟨7538913641669789243601047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20103769711119437982936125 7538913641669789243601047)
        ·
          refine ⟨11308370462504683865401571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7538913641669789243601047 11308370462504683865401571)
          ·
            refine ⟨16962555693757025798102357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11308370462504683865401571 16962555693757025798102357)
            ·
              refine ⟨24847493692026893258939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 16962555693757025798102357 24847493692026893258939)
              ·
                rfl

theorem cell20_489952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 11].length) (baseStart_489952 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_489952 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_489952 prefixEnd_489952 := by exact prefixLift 489952
  have htrace : WordTrace (prefixWord ++ tailWord_489952) baseStart_489952 baseEnd_489952 := by
    simpa [prefixWord, tailWord_489952, baseEnd_489952] using wordTrace_append hprefix tailTrace_489952
  have hstable : (prefixWord ++ tailWord_489952).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489952).length < 2 ^ (prefixWord ++ tailWord_489952).sum := by decide
  have hdescent : baseEnd_489952 < baseStart_489952 := by decide
  rcases family_descends (prefixWord ++ tailWord_489952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489955 : List Nat := [1, 1, 1, 6, 3, 1, 1, 1, 5]
def baseStart_489955 : Nat := 118140960795 + 489955 * 2 ^ 59
def prefixEnd_489955 : Nat := 4983230072969 + 3 ^ 40 * 489955 * 2
def baseEnd_489955 : Nat := 223628812509987362230439

theorem tailTrace_489955 : CollatzResearch.WordTrace tailWord_489955 prefixEnd_489955 223628812509987362230439 := by
  unfold tailWord_489955
  simp only [CollatzResearch.WordTrace]
  refine ⟨17870126939984187497191319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11913417959989458331460879 17870126939984187497191319)
  ·
    refine ⟨26805190409976281245786979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17870126939984187497191319 26805190409976281245786979)
    ·
      refine ⟨40207785614964421868680469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26805190409976281245786979 40207785614964421868680469)
      ·
        refine ⟨1884739950701457275094397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 40207785614964421868680469 1884739950701457275094397)
        ·
          refine ⟨706777481513046478160399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1884739950701457275094397 706777481513046478160399)
          ·
            refine ⟨1060166222269569717240599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 706777481513046478160399 1060166222269569717240599)
            ·
              refine ⟨1590249333404354575860899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1060166222269569717240599 1590249333404354575860899)
              ·
                refine ⟨2385374000106531863791349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1590249333404354575860899 2385374000106531863791349)
                ·
                  refine ⟨223628812509987362230439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2385374000106531863791349 223628812509987362230439)
                  ·
                    rfl

theorem cell20_489955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 1, 5].length) (baseStart_489955 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_489955 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_489955 prefixEnd_489955 := by exact prefixLift 489955
  have htrace : WordTrace (prefixWord ++ tailWord_489955) baseStart_489955 baseEnd_489955 := by
    simpa [prefixWord, tailWord_489955, baseEnd_489955] using wordTrace_append hprefix tailTrace_489955
  have hstable : (prefixWord ++ tailWord_489955).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489955).length < 2 ^ (prefixWord ++ tailWord_489955).sum := by decide
  have hdescent : baseEnd_489955 < baseStart_489955 := by decide
  rcases family_descends (prefixWord ++ tailWord_489955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489962 : List Nat := [3, 1, 3, 1, 3, 1, 1, 3, 4]
def baseStart_489962 : Nat := 118140960795 + 489962 * 2 ^ 59
def prefixEnd_489962 : Nat := 4983230072969 + 3 ^ 40 * 489962 * 2
def baseEnd_489962 : Nat := 223632007500726448997077

theorem tailTrace_489962 : CollatzResearch.WordTrace tailWord_489962 prefixEnd_489962 223632007500726448997077 := by
  unfold tailWord_489962
  simp only [CollatzResearch.WordTrace]
  refine ⟨4467595562739706923174035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11913588167305885128464093 4467595562739706923174035)
  ·
    refine ⟨6701393344109560384761053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4467595562739706923174035 6701393344109560384761053)
    ·
      refine ⟨2513022504041085144285395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6701393344109560384761053 2513022504041085144285395)
      ·
        refine ⟨3769533756061627716428093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2513022504041085144285395 3769533756061627716428093)
        ·
          refine ⟨1413575158523110393660535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3769533756061627716428093 1413575158523110393660535)
          ·
            refine ⟨2120362737784665590490803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1413575158523110393660535 2120362737784665590490803)
            ·
              refine ⟨3180544106676998385736205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2120362737784665590490803 3180544106676998385736205)
              ·
                refine ⟨1192704040003874394651077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3180544106676998385736205 1192704040003874394651077)
                ·
                  refine ⟨223632007500726448997077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1192704040003874394651077 223632007500726448997077)
                  ·
                    rfl

theorem cell20_489962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 3, 4].length) (baseStart_489962 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_489962 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_489962 prefixEnd_489962 := by exact prefixLift 489962
  have htrace : WordTrace (prefixWord ++ tailWord_489962) baseStart_489962 baseEnd_489962 := by
    simpa [prefixWord, tailWord_489962, baseEnd_489962] using wordTrace_append hprefix tailTrace_489962
  have hstable : (prefixWord ++ tailWord_489962).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489962).length < 2 ^ (prefixWord ++ tailWord_489962).sum := by decide
  have hdescent : baseEnd_489962 < baseStart_489962 := by decide
  rcases family_descends (prefixWord ++ tailWord_489962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489983 : List Nat := [1, 1, 2, 2, 1, 2, 3, 4, 4]
def baseStart_489983 : Nat := 118140960795 + 489983 * 2 ^ 59
def prefixEnd_489983 : Nat := 4983230072969 + 3 ^ 40 * 489983 * 2
def baseEnd_489983 : Nat := 223641592472943709296991

theorem tailTrace_489983 : CollatzResearch.WordTrace tailWord_489983 prefixEnd_489983 223641592472943709296991 := by
  unfold tailWord_489983
  simp only [CollatzResearch.WordTrace]
  refine ⟨17871148183882748279210603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11914098789255165519473735 17871148183882748279210603)
  ·
    refine ⟨26806722275824122418815905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17871148183882748279210603 26806722275824122418815905)
    ·
      refine ⟨20105041706868091814111929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26806722275824122418815905 20105041706868091814111929)
      ·
        refine ⟨15078781280151068860583947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20105041706868091814111929 15078781280151068860583947)
        ·
          refine ⟨22618171920226603290875921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15078781280151068860583947 22618171920226603290875921)
          ·
            refine ⟨16963628940169952468156941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22618171920226603290875921 16963628940169952468156941)
            ·
              refine ⟨6361360852563732175558853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16963628940169952468156941 6361360852563732175558853)
              ·
                refine ⟨1192755159855699782917285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6361360852563732175558853 1192755159855699782917285)
                ·
                  refine ⟨223641592472943709296991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1192755159855699782917285 223641592472943709296991)
                  ·
                    rfl

theorem cell20_489983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 4, 4].length) (baseStart_489983 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_489983 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_489983 prefixEnd_489983 := by exact prefixLift 489983
  have htrace : WordTrace (prefixWord ++ tailWord_489983) baseStart_489983 baseEnd_489983 := by
    simpa [prefixWord, tailWord_489983, baseEnd_489983] using wordTrace_append hprefix tailTrace_489983
  have hstable : (prefixWord ++ tailWord_489983).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489983).length < 2 ^ (prefixWord ++ tailWord_489983).sum := by decide
  have hdescent : baseEnd_489983 < baseStart_489983 := by decide
  rcases family_descends (prefixWord ++ tailWord_489983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489996 : List Nat := [2, 2, 1, 2, 4, 3, 1, 3, 2]
def baseStart_489996 : Nat := 118140960795 + 489996 * 2 ^ 59
def prefixEnd_489996 : Nat := 4983230072969 + 3 ^ 40 * 489996 * 2
def baseEnd_489996 : Nat := 223647526027173441863605

theorem tailTrace_489996 : CollatzResearch.WordTrace tailWord_489996 prefixEnd_489996 223647526027173441863605 := by
  unfold tailWord_489996
  simp only [CollatzResearch.WordTrace]
  refine ⟨8935811166417825749716921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11914414888557100999622561 8935811166417825749716921)
  ·
    refine ⟨6701858374813369312287691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8935811166417825749716921 6701858374813369312287691)
    ·
      refine ⟨10052787562220053968431537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6701858374813369312287691 10052787562220053968431537)
      ·
        refine ⟨7539590671665040476323653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10052787562220053968431537 7539590671665040476323653)
        ·
          refine ⟨1413673250937195089310685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7539590671665040476323653 1413673250937195089310685)
          ·
            refine ⟨530127469101448158491507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1413673250937195089310685 530127469101448158491507)
            ·
              refine ⟨795191203652172237737261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 530127469101448158491507 795191203652172237737261)
              ·
                refine ⟨298196701369564589151473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 795191203652172237737261 298196701369564589151473)
                ·
                  refine ⟨223647526027173441863605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 298196701369564589151473 223647526027173441863605)
                  ·
                    rfl

theorem cell20_489996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 1, 3, 2].length) (baseStart_489996 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_489996 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_489996 prefixEnd_489996 := by exact prefixLift 489996
  have htrace : WordTrace (prefixWord ++ tailWord_489996) baseStart_489996 baseEnd_489996 := by
    simpa [prefixWord, tailWord_489996, baseEnd_489996] using wordTrace_append hprefix tailTrace_489996
  have hstable : (prefixWord ++ tailWord_489996).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489996).length < 2 ^ (prefixWord ++ tailWord_489996).sum := by decide
  have hdescent : baseEnd_489996 < baseStart_489996 := by decide
  rcases family_descends (prefixWord ++ tailWord_489996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490023 : List Nat := [1, 1, 7, 2, 2, 1, 2, 1, 3]
def baseStart_490023 : Nat := 118140960795 + 490023 * 2 ^ 59
def prefixEnd_490023 : Nat := 4983230072969 + 3 ^ 40 * 490023 * 2
def baseEnd_490023 : Nat := 223659849562881347963495

theorem tailTrace_490023 : CollatzResearch.WordTrace tailWord_490023 prefixEnd_490023 223659849562881347963495 := by
  unfold tailWord_490023
  simp only [CollatzResearch.WordTrace]
  refine ⟨17872607103737835110666723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11915071402491890073777815 17872607103737835110666723)
  ·
    refine ⟨26808910655606752666000085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17872607103737835110666723 26808910655606752666000085)
    ·
      refine ⟨628333843490783265609377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 26808910655606752666000085 628333843490783265609377)
      ·
        refine ⟨471250382618087449207033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 628333843490783265609377 471250382618087449207033)
        ·
          refine ⟨353437786963565586905275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 471250382618087449207033 353437786963565586905275)
          ·
            refine ⟨530156680445348380357913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 353437786963565586905275 530156680445348380357913)
            ·
              refine ⟨397617510334011285268435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 530156680445348380357913 397617510334011285268435)
              ·
                refine ⟨596426265501016927902653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 397617510334011285268435 596426265501016927902653)
                ·
                  refine ⟨223659849562881347963495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 596426265501016927902653 223659849562881347963495)
                  ·
                    rfl

theorem cell20_490023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 2, 1, 3].length) (baseStart_490023 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_490023 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_490023 prefixEnd_490023 := by exact prefixLift 490023
  have htrace : WordTrace (prefixWord ++ tailWord_490023) baseStart_490023 baseEnd_490023 := by
    simpa [prefixWord, tailWord_490023, baseEnd_490023] using wordTrace_append hprefix tailTrace_490023
  have hstable : (prefixWord ++ tailWord_490023).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490023).length < 2 ^ (prefixWord ++ tailWord_490023).sum := by decide
  have hdescent : baseEnd_490023 < baseStart_490023 := by decide
  rcases family_descends (prefixWord ++ tailWord_490023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490024 : List Nat := [2, 1, 5, 2, 1, 2, 2, 5]
def baseStart_490024 : Nat := 118140960795 + 490024 * 2 ^ 59
def prefixEnd_490024 : Nat := 4983230072969 + 3 ^ 40 * 490024 * 2
def baseEnd_490024 : Nat := 74553435330043262976719

theorem tailTrace_490024 : CollatzResearch.WordTrace tailWord_490024 prefixEnd_490024 74553435330043262976719 := by
  unfold tailWord_490024
  simp only [CollatzResearch.WordTrace]
  refine ⟨8936321788367106140726563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11915095717822808187635417 8936321788367106140726563)
  ·
    refine ⟨13404482682550659211089845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8936321788367106140726563 13404482682550659211089845)
    ·
      refine ⟨1256670251489124301039673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13404482682550659211089845 1256670251489124301039673)
      ·
        refine ⟨942502688616843225779755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1256670251489124301039673 942502688616843225779755)
        ·
          refine ⟨1413754032925264838669633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 942502688616843225779755 1413754032925264838669633)
          ·
            refine ⟨1060315524693948629002225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1413754032925264838669633 1060315524693948629002225)
            ·
              refine ⟨795236643520461471751669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1060315524693948629002225 795236643520461471751669)
              ·
                refine ⟨74553435330043262976719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 795236643520461471751669 74553435330043262976719)
                ·
                  rfl

theorem cell20_490024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 2, 5].length) (baseStart_490024 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_490024 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_490024 prefixEnd_490024 := by exact prefixLift 490024
  have htrace : WordTrace (prefixWord ++ tailWord_490024) baseStart_490024 baseEnd_490024 := by
    simpa [prefixWord, tailWord_490024, baseEnd_490024] using wordTrace_append hprefix tailTrace_490024
  have hstable : (prefixWord ++ tailWord_490024).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490024).length < 2 ^ (prefixWord ++ tailWord_490024).sum := by decide
  have hdescent : baseEnd_490024 < baseStart_490024 := by decide
  rcases family_descends (prefixWord ++ tailWord_490024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490045 : List Nat := [1, 4, 1, 3, 2, 1, 2, 6]
def baseStart_490045 : Nat := 118140960795 + 490045 * 2 ^ 59
def prefixEnd_490045 : Nat := 4983230072969 + 3 ^ 40 * 490045 * 2
def baseEnd_490045 : Nat := 74556630320782349743357

theorem tailTrace_490045 : CollatzResearch.WordTrace tailWord_490045 prefixEnd_490045 74556630320782349743357 := by
  unfold tailWord_490045
  simp only [CollatzResearch.WordTrace]
  refine ⟨17873409509658132867967589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11915606339772088578645059 17873409509658132867967589)
  ·
    refine ⟨3351264283060899912743923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17873409509658132867967589 3351264283060899912743923)
    ·
      refine ⟨5026896424591349869115885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3351264283060899912743923 5026896424591349869115885)
      ·
        refine ⟨1885086159221756200918457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5026896424591349869115885 1885086159221756200918457)
        ·
          refine ⟨1413814619416317150688843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1885086159221756200918457 1413814619416317150688843)
          ·
            refine ⟨2120721929124475726033265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1413814619416317150688843 2120721929124475726033265)
            ·
              refine ⟨1590541446843356794524949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2120721929124475726033265 1590541446843356794524949)
              ·
                refine ⟨74556630320782349743357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1590541446843356794524949 74556630320782349743357)
                ·
                  rfl

theorem cell20_490045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 6].length) (baseStart_490045 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_490045 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_490045 prefixEnd_490045 := by exact prefixLift 490045
  have htrace : WordTrace (prefixWord ++ tailWord_490045) baseStart_490045 baseEnd_490045 := by
    simpa [prefixWord, tailWord_490045, baseEnd_490045] using wordTrace_append hprefix tailTrace_490045
  have hstable : (prefixWord ++ tailWord_490045).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490045).length < 2 ^ (prefixWord ++ tailWord_490045).sum := by decide
  have hdescent : baseEnd_490045 < baseStart_490045 := by decide
  rcases family_descends (prefixWord ++ tailWord_490045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490159 : List Nat := [1, 1, 2, 1, 2, 5, 4, 4]
def baseStart_490159 : Nat := 118140960795 + 490159 * 2 ^ 59
def prefixEnd_490159 : Nat := 4983230072969 + 3 ^ 40 * 490159 * 2
def baseEnd_490159 : Nat := 74573974556223106476535

theorem tailTrace_490159 : CollatzResearch.WordTrace tailWord_490159 prefixEnd_490159 74573974556223106476535 := by
  unfold tailWord_490159
  simp only [CollatzResearch.WordTrace]
  refine ⟨17877567431245130337617531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11918378287496753558411687 17877567431245130337617531)
  ·
    refine ⟨26816351146867695506426297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17877567431245130337617531 26816351146867695506426297)
    ·
      refine ⟨20112263360150771629819723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26816351146867695506426297 20112263360150771629819723)
      ·
        refine ⟨30168395040226157444729585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20112263360150771629819723 30168395040226157444729585)
        ·
          refine ⟨22626296280169618083547189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30168395040226157444729585 22626296280169618083547189)
          ·
            refine ⟨2121215276265901695332549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22626296280169618083547189 2121215276265901695332549)
            ·
              refine ⟨397727864299856567874853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2121215276265901695332549 397727864299856567874853)
              ·
                refine ⟨74573974556223106476535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 397727864299856567874853 74573974556223106476535)
                ·
                  rfl

theorem cell20_490159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 4, 4].length) (baseStart_490159 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_490159 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_490159 prefixEnd_490159 := by exact prefixLift 490159
  have htrace : WordTrace (prefixWord ++ tailWord_490159) baseStart_490159 baseEnd_490159 := by
    simpa [prefixWord, tailWord_490159, baseEnd_490159] using wordTrace_append hprefix tailTrace_490159
  have hstable : (prefixWord ++ tailWord_490159).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490159).length < 2 ^ (prefixWord ++ tailWord_490159).sum := by decide
  have hdescent : baseEnd_490159 < baseStart_490159 := by decide
  rcases family_descends (prefixWord ++ tailWord_490159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490182 : List Nat := [6, 1, 2, 1, 3, 1, 1, 1, 4]
def baseStart_490182 : Nat := 118140960795 + 490182 * 2 ^ 59
def prefixEnd_490182 : Nat := 4983230072969 + 3 ^ 40 * 490182 * 2
def baseEnd_490182 : Nat := 223732421495383461662845

theorem tailTrace_490182 : CollatzResearch.WordTrace tailWord_490182 prefixEnd_490182 223732421495383461662845 := by
  unfold tailWord_490182
  simp only [CollatzResearch.WordTrace]
  refine ⟨558700197192556414553275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 11918937540107870177136533 558700197192556414553275)
  ·
    refine ⟨838050295788834621829913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 558700197192556414553275 838050295788834621829913)
    ·
      refine ⟨628537721841625966372435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 838050295788834621829913 628537721841625966372435)
      ·
        refine ⟨942806582762438949558653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 628537721841625966372435 942806582762438949558653)
        ·
          refine ⟨353552468535914606084495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 942806582762438949558653 353552468535914606084495)
          ·
            refine ⟨530328702803871909126743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 353552468535914606084495 530328702803871909126743)
            ·
              refine ⟨795493054205807863690115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 530328702803871909126743 795493054205807863690115)
              ·
                refine ⟨1193239581308711795535173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 795493054205807863690115 1193239581308711795535173)
                ·
                  refine ⟨223732421495383461662845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1193239581308711795535173 223732421495383461662845)
                  ·
                    rfl

theorem cell20_490182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 1, 1, 4].length) (baseStart_490182 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_490182 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_490182 prefixEnd_490182 := by exact prefixLift 490182
  have htrace : WordTrace (prefixWord ++ tailWord_490182) baseStart_490182 baseEnd_490182 := by
    simpa [prefixWord, tailWord_490182, baseEnd_490182] using wordTrace_append hprefix tailTrace_490182
  have hstable : (prefixWord ++ tailWord_490182).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490182).length < 2 ^ (prefixWord ++ tailWord_490182).sum := by decide
  have hdescent : baseEnd_490182 < baseStart_490182 := by decide
  rcases family_descends (prefixWord ++ tailWord_490182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490186 : List Nat := [3, 1, 2, 1, 4, 2, 3, 2, 2]
def baseStart_490186 : Nat := 118140960795 + 490186 * 2 ^ 59
def prefixEnd_490186 : Nat := 4983230072969 + 3 ^ 40 * 490186 * 2
def baseEnd_490186 : Nat := 223734247204377225529495

theorem tailTrace_490186 : CollatzResearch.WordTrace tailWord_490186 prefixEnd_490186 223734247204377225529495 := by
  unfold tailWord_490186
  simp only [CollatzResearch.WordTrace]
  refine ⟨4469638050536828487212603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11919034801431542632566941 4469638050536828487212603)
  ·
    refine ⟨6704457075805242730818905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4469638050536828487212603 6704457075805242730818905)
    ·
      refine ⟨5028342806853932048114179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6704457075805242730818905 5028342806853932048114179)
      ·
        refine ⟨7542514210280898072171269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5028342806853932048114179 7542514210280898072171269)
        ·
          refine ⟨1414221414427668388532113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7542514210280898072171269 1414221414427668388532113)
          ·
            refine ⟨1060666060820751291399085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1414221414427668388532113 1060666060820751291399085)
            ·
              refine ⟨397749772807781734274657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1060666060820751291399085 397749772807781734274657)
              ·
                refine ⟨298312329605836300705993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 397749772807781734274657 298312329605836300705993)
                ·
                  refine ⟨223734247204377225529495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 298312329605836300705993 223734247204377225529495)
                  ·
                    rfl

theorem cell20_490186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 3, 2, 2].length) (baseStart_490186 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_490186 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_490186 prefixEnd_490186 := by exact prefixLift 490186
  have htrace : WordTrace (prefixWord ++ tailWord_490186) baseStart_490186 baseEnd_490186 := by
    simpa [prefixWord, tailWord_490186, baseEnd_490186] using wordTrace_append hprefix tailTrace_490186
  have hstable : (prefixWord ++ tailWord_490186).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490186).length < 2 ^ (prefixWord ++ tailWord_490186).sum := by decide
  have hdescent : baseEnd_490186 < baseStart_490186 := by decide
  rcases family_descends (prefixWord ++ tailWord_490186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490190 : List Nat := [4, 1, 1, 1, 3, 2, 3, 1, 4]
def baseStart_490190 : Nat := 118140960795 + 490190 * 2 ^ 59
def prefixEnd_490190 : Nat := 4983230072969 + 3 ^ 40 * 490190 * 2
def baseEnd_490190 : Nat := 223736072913370989396145

theorem tailTrace_490190 : CollatzResearch.WordTrace tailWord_490190 prefixEnd_490190 223736072913370989396145 := by
  unfold tailWord_490190
  simp only [CollatzResearch.WordTrace]
  refine ⟨2234837261766602828999503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11919132062755215087997349 2234837261766602828999503)
  ·
    refine ⟨3352255892649904243499255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2234837261766602828999503 3352255892649904243499255)
    ·
      refine ⟨5028383838974856365248883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3352255892649904243499255 5028383838974856365248883)
      ·
        refine ⟨7542575758462284547873325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5028383838974856365248883 7542575758462284547873325)
        ·
          refine ⟨2828465909423356705452497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7542575758462284547873325 2828465909423356705452497)
          ·
            refine ⟨2121349432067517529089373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2828465909423356705452497 2121349432067517529089373)
            ·
              refine ⟨795506037025319073408515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2121349432067517529089373 795506037025319073408515)
              ·
                refine ⟨1193259055537978610112773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 795506037025319073408515 1193259055537978610112773)
                ·
                  refine ⟨223736072913370989396145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1193259055537978610112773 223736072913370989396145)
                  ·
                    rfl

theorem cell20_490190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 3, 1, 4].length) (baseStart_490190 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_490190 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_490190 prefixEnd_490190 := by exact prefixLift 490190
  have htrace : WordTrace (prefixWord ++ tailWord_490190) baseStart_490190 baseEnd_490190 := by
    simpa [prefixWord, tailWord_490190, baseEnd_490190] using wordTrace_append hprefix tailTrace_490190
  have hstable : (prefixWord ++ tailWord_490190).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490190).length < 2 ^ (prefixWord ++ tailWord_490190).sum := by decide
  have hdescent : baseEnd_490190 < baseStart_490190 := by decide
  rcases family_descends (prefixWord ++ tailWord_490190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490196 : List Nat := [2, 4, 1, 3, 3, 1, 2, 1, 3]
def baseStart_490196 : Nat := 118140960795 + 490196 * 2 ^ 59
def prefixEnd_490196 : Nat := 4983230072969 + 3 ^ 40 * 490196 * 2
def baseEnd_490196 : Nat := 223738811476861635196121

theorem tailTrace_490196 : CollatzResearch.WordTrace tailWord_490196 prefixEnd_490196 223738811476861635196121 := by
  unfold tailWord_490196
  simp only [CollatzResearch.WordTrace]
  refine ⟨8939458466055542828357221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11919277954740723771142961 8939458466055542828357221)
  ·
    refine ⟨1676148462385414280316979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8939458466055542828357221 1676148462385414280316979)
    ·
      refine ⟨2514222693578121420475469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1676148462385414280316979 2514222693578121420475469)
      ·
        refine ⟨942833510091795532678301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2514222693578121420475469 942833510091795532678301)
        ·
          refine ⟨353562566284423324754363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 942833510091795532678301 353562566284423324754363)
          ·
            refine ⟨530343849426634987131545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 353562566284423324754363 530343849426634987131545)
            ·
              refine ⟨397757887069976240348659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 530343849426634987131545 397757887069976240348659)
              ·
                refine ⟨596636830604964360522989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 397757887069976240348659 596636830604964360522989)
                ·
                  refine ⟨223738811476861635196121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 596636830604964360522989 223738811476861635196121)
                  ·
                    rfl

theorem cell20_490196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 2, 1, 3].length) (baseStart_490196 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_490196 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_490196 prefixEnd_490196 := by exact prefixLift 490196
  have htrace : WordTrace (prefixWord ++ tailWord_490196) baseStart_490196 baseEnd_490196 := by
    simpa [prefixWord, tailWord_490196, baseEnd_490196] using wordTrace_append hprefix tailTrace_490196
  have hstable : (prefixWord ++ tailWord_490196).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490196).length < 2 ^ (prefixWord ++ tailWord_490196).sum := by decide
  have hdescent : baseEnd_490196 < baseStart_490196 := by decide
  rcases family_descends (prefixWord ++ tailWord_490196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490200 : List Nat := [2, 1, 2, 2, 3, 4, 2, 1, 3]
def baseStart_490200 : Nat := 118140960795 + 490200 * 2 ^ 59
def prefixEnd_490200 : Nat := 4983230072969 + 3 ^ 40 * 490200 * 2
def baseEnd_490200 : Nat := 223740637185855399062771

theorem tailTrace_490200 : CollatzResearch.WordTrace tailWord_490200 prefixEnd_490200 223740637185855399062771 := by
  unfold tailWord_490200
  simp only [CollatzResearch.WordTrace]
  refine ⟨8939531412048297169930027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11919375216064396226573369 8939531412048297169930027)
  ·
    refine ⟨13409297118072445754895041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8939531412048297169930027 13409297118072445754895041)
    ·
      refine ⟨10056972838554334316171281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13409297118072445754895041 10056972838554334316171281)
      ·
        refine ⟨7542729628915750737128461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10056972838554334316171281 7542729628915750737128461)
        ·
          refine ⟨2828523610843406526423173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7542729628915750737128461 2828523610843406526423173)
          ·
            refine ⟨530348177033138723704345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2828523610843406526423173 530348177033138723704345)
            ·
              refine ⟨397761132774854042778259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 530348177033138723704345 397761132774854042778259)
              ·
                refine ⟨596641699162281064167389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 397761132774854042778259 596641699162281064167389)
                ·
                  refine ⟨223740637185855399062771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 596641699162281064167389 223740637185855399062771)
                  ·
                    rfl

theorem cell20_490200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 2, 1, 3].length) (baseStart_490200 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_490200 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_490200 prefixEnd_490200 := by exact prefixLift 490200
  have htrace : WordTrace (prefixWord ++ tailWord_490200) baseStart_490200 baseEnd_490200 := by
    simpa [prefixWord, tailWord_490200, baseEnd_490200] using wordTrace_append hprefix tailTrace_490200
  have hstable : (prefixWord ++ tailWord_490200).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490200).length < 2 ^ (prefixWord ++ tailWord_490200).sum := by decide
  have hdescent : baseEnd_490200 < baseStart_490200 := by decide
  rcases family_descends (prefixWord ++ tailWord_490200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490238 : List Nat := [4, 2, 2, 1, 2, 2, 2, 2, 3]
def baseStart_490238 : Nat := 118140960795 + 490238 * 2 ^ 59
def prefixEnd_490238 : Nat := 4983230072969 + 3 ^ 40 * 490238 * 2
def baseEnd_490238 : Nat := 223757981421296155795949

theorem tailTrace_490238 : CollatzResearch.WordTrace tailWord_490238 prefixEnd_490238 223757981421296155795949 := by
  unfold tailWord_490238
  simp only [CollatzResearch.WordTrace]
  refine ⟨2235056099744865853717921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11920299198639284553162245 2235056099744865853717921)
  ·
    refine ⟨1676292074808649390288441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2235056099744865853717921 1676292074808649390288441)
    ·
      refine ⟨1257219056106487042716331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1676292074808649390288441 1257219056106487042716331)
      ·
        refine ⟨1885828584159730564074497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1257219056106487042716331 1885828584159730564074497)
        ·
          refine ⟨1414371438119797923055873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1885828584159730564074497 1414371438119797923055873)
          ·
            refine ⟨1060778578589848442291905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1414371438119797923055873 1060778578589848442291905)
            ·
              refine ⟨795583933942386331718929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1060778578589848442291905 795583933942386331718929)
              ·
                refine ⟨596687950456789748789197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 795583933942386331718929 596687950456789748789197)
                ·
                  refine ⟨223757981421296155795949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 596687950456789748789197 223757981421296155795949)
                  ·
                    rfl

theorem cell20_490238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 2, 2, 3].length) (baseStart_490238 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_490238 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_490238 prefixEnd_490238 := by exact prefixLift 490238
  have htrace : WordTrace (prefixWord ++ tailWord_490238) baseStart_490238 baseEnd_490238 := by
    simpa [prefixWord, tailWord_490238, baseEnd_490238] using wordTrace_append hprefix tailTrace_490238
  have hstable : (prefixWord ++ tailWord_490238).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490238).length < 2 ^ (prefixWord ++ tailWord_490238).sum := by decide
  have hdescent : baseEnd_490238 < baseStart_490238 := by decide
  rcases family_descends (prefixWord ++ tailWord_490238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490269 : List Nat := [1, 4, 2, 4, 1, 1, 3, 4]
def baseStart_490269 : Nat := 118140960795 + 490269 * 2 ^ 59
def prefixEnd_490269 : Nat := 4983230072969 + 3 ^ 40 * 490269 * 2
def baseEnd_490269 : Nat := 74590710221999275254163

theorem tailTrace_490269 : CollatzResearch.WordTrace tailWord_490269 prefixEnd_490269 74590710221999275254163 := by
  unfold tailWord_490269
  simp only [CollatzResearch.WordTrace]
  refine ⟨17881579460846619124121861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11921052973897746082747907 17881579460846619124121861)
  ·
    refine ⟨3352796148908741085772849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17881579460846619124121861 3352796148908741085772849)
    ·
      refine ⟨2514597111681555814329637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3352796148908741085772849 2514597111681555814329637)
      ·
        refine ⟨471486958440291715186807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2514597111681555814329637 471486958440291715186807)
        ·
          refine ⟨707230437660437572780211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 471486958440291715186807 707230437660437572780211)
          ·
            refine ⟨1060845656490656359170317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 707230437660437572780211 1060845656490656359170317)
            ·
              refine ⟨397817121183996134688869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1060845656490656359170317 397817121183996134688869)
              ·
                refine ⟨74590710221999275254163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 397817121183996134688869 74590710221999275254163)
                ·
                  rfl

theorem cell20_490269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 3, 4].length) (baseStart_490269 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_490269 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_490269 prefixEnd_490269 := by exact prefixLift 490269
  have htrace : WordTrace (prefixWord ++ tailWord_490269) baseStart_490269 baseEnd_490269 := by
    simpa [prefixWord, tailWord_490269, baseEnd_490269] using wordTrace_append hprefix tailTrace_490269
  have hstable : (prefixWord ++ tailWord_490269).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490269).length < 2 ^ (prefixWord ++ tailWord_490269).sum := by decide
  have hdescent : baseEnd_490269 < baseStart_490269 := by decide
  rcases family_descends (prefixWord ++ tailWord_490269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490273 : List Nat := [1, 2, 3, 2, 1, 2, 5, 4]
def baseStart_490273 : Nat := 118140960795 + 490273 * 2 ^ 59
def prefixEnd_490273 : Nat := 4983230072969 + 3 ^ 40 * 490273 * 2
def baseEnd_490273 : Nat := 74591318791663863209713

theorem tailTrace_490273 : CollatzResearch.WordTrace tailWord_490273 prefixEnd_490273 74591318791663863209713 := by
  unfold tailWord_490273
  simp only [CollatzResearch.WordTrace]
  refine ⟨17881725352832127807267473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11921150235221418538178315 17881725352832127807267473)
  ·
    refine ⟨13411294014624095855450605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17881725352832127807267473 13411294014624095855450605)
    ·
      refine ⟨5029235255484035945793977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13411294014624095855450605 5029235255484035945793977)
      ·
        refine ⟨3771926441613026959345483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5029235255484035945793977 3771926441613026959345483)
        ·
          refine ⟨5657889662419540439018225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3771926441613026959345483 5657889662419540439018225)
          ·
            refine ⟨4243417246814655329263669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5657889662419540439018225 4243417246814655329263669)
            ·
              refine ⟨397820366888873937118469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4243417246814655329263669 397820366888873937118469)
              ·
                refine ⟨74591318791663863209713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 397820366888873937118469 74591318791663863209713)
                ·
                  rfl

theorem cell20_490273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 5, 4].length) (baseStart_490273 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_490273 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_490273 prefixEnd_490273 := by exact prefixLift 490273
  have htrace : WordTrace (prefixWord ++ tailWord_490273) baseStart_490273 baseEnd_490273 := by
    simpa [prefixWord, tailWord_490273, baseEnd_490273] using wordTrace_append hprefix tailTrace_490273
  have hstable : (prefixWord ++ tailWord_490273).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490273).length < 2 ^ (prefixWord ++ tailWord_490273).sum := by decide
  have hdescent : baseEnd_490273 < baseStart_490273 := by decide
  rcases family_descends (prefixWord ++ tailWord_490273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490280 : List Nat := [2, 1, 5, 1, 1, 1, 2, 2, 5]
def baseStart_490280 : Nat := 118140960795 + 490280 * 2 ^ 59
def prefixEnd_490280 : Nat := 4983230072969 + 3 ^ 40 * 490280 * 2
def baseEnd_490280 : Nat := 223777151365730676395777

theorem tailTrace_490280 : CollatzResearch.WordTrace tailWord_490280 prefixEnd_490280 223777151365730676395777 := by
  unfold tailWord_490280
  simp only [CollatzResearch.WordTrace]
  refine ⟨8940990331903384001386147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11921320442537845335181529 8940990331903384001386147)
  ·
    refine ⟨13411485497855076002079221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8940990331903384001386147 13411485497855076002079221)
    ·
      refine ⟨1257326765423913375194927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13411485497855076002079221 1257326765423913375194927)
      ·
        refine ⟨1885990148135870062792391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1257326765423913375194927 1885990148135870062792391)
        ·
          refine ⟨2828985222203805094188587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1885990148135870062792391 2828985222203805094188587)
          ·
            refine ⟨4243477833305707641282881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2828985222203805094188587 4243477833305707641282881)
            ·
              refine ⟨3182608374979280730962161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4243477833305707641282881 3182608374979280730962161)
              ·
                refine ⟨2386956281234460548221621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3182608374979280730962161 2386956281234460548221621)
                ·
                  refine ⟨223777151365730676395777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2386956281234460548221621 223777151365730676395777)
                  ·
                    rfl

theorem cell20_490280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 2, 5].length) (baseStart_490280 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_490280 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_490280 prefixEnd_490280 := by exact prefixLift 490280
  have htrace : WordTrace (prefixWord ++ tailWord_490280) baseStart_490280 baseEnd_490280 := by
    simpa [prefixWord, tailWord_490280, baseEnd_490280] using wordTrace_append hprefix tailTrace_490280
  have hstable : (prefixWord ++ tailWord_490280).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490280).length < 2 ^ (prefixWord ++ tailWord_490280).sum := by decide
  have hdescent : baseEnd_490280 < baseStart_490280 := by decide
  rcases family_descends (prefixWord ++ tailWord_490280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490310 : List Nat := [6, 1, 1, 2, 2, 1, 3, 1, 3]
def baseStart_490310 : Nat := 118140960795 + 490310 * 2 ^ 59
def prefixEnd_490310 : Nat := 4983230072969 + 3 ^ 40 * 490310 * 2
def baseEnd_490310 : Nat := 223790844183183905395655

theorem tailTrace_490310 : CollatzResearch.WordTrace tailWord_490310 prefixEnd_490310 223790844183183905395655 := by
  unfold tailWord_490310
  simp only [CollatzResearch.WordTrace]
  refine ⟨558846089178065097698887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 11922049902465388750909589 558846089178065097698887)
  ·
    refine ⟨838269133767097646548331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 558846089178065097698887 838269133767097646548331)
    ·
      refine ⟨1257403700650646469822497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 838269133767097646548331 1257403700650646469822497)
      ·
        refine ⟨943052775487984852366873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1257403700650646469822497 943052775487984852366873)
        ·
          refine ⟨707289581615988639275155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 943052775487984852366873 707289581615988639275155)
          ·
            refine ⟨1060934372423982958912733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 707289581615988639275155 1060934372423982958912733)
            ·
              refine ⟨397850389658993609592275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1060934372423982958912733 397850389658993609592275)
              ·
                refine ⟨596775584488490414388413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 397850389658993609592275 596775584488490414388413)
                ·
                  refine ⟨223790844183183905395655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 596775584488490414388413 223790844183183905395655)
                  ·
                    rfl

theorem cell20_490310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 3, 1, 3].length) (baseStart_490310 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_490310 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_490310 prefixEnd_490310 := by exact prefixLift 490310
  have htrace : WordTrace (prefixWord ++ tailWord_490310) baseStart_490310 baseEnd_490310 := by
    simpa [prefixWord, tailWord_490310, baseEnd_490310] using wordTrace_append hprefix tailTrace_490310
  have hstable : (prefixWord ++ tailWord_490310).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490310).length < 2 ^ (prefixWord ++ tailWord_490310).sum := by decide
  have hdescent : baseEnd_490310 < baseStart_490310 := by decide
  rcases family_descends (prefixWord ++ tailWord_490310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490318 : List Nat := [4, 1, 1, 1, 1, 1, 1, 7, 3]
def baseStart_490318 : Nat := 118140960795 + 490318 * 2 ^ 59
def prefixEnd_490318 : Nat := 4983230072969 + 3 ^ 40 * 490318 * 2
def baseEnd_490318 : Nat := 223794495601171433128955

theorem tailTrace_490318 : CollatzResearch.WordTrace tailWord_490318 prefixEnd_490318 223794495601171433128955 := by
  unfold tailWord_490318
  simp only [CollatzResearch.WordTrace]
  refine ⟨2235420829708637561581951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11922244425112733661770405 2235420829708637561581951)
  ·
    refine ⟨3353131244562956342372927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2235420829708637561581951 3353131244562956342372927)
    ·
      refine ⟨5029696866844434513559391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3353131244562956342372927 5029696866844434513559391)
      ·
        refine ⟨7544545300266651770339087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5029696866844434513559391 7544545300266651770339087)
        ·
          refine ⟨11316817950399977655508631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7544545300266651770339087 11316817950399977655508631)
          ·
            refine ⟨16975226925599966483262947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11316817950399977655508631 16975226925599966483262947)
            ·
              refine ⟨25462840388399949724894421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16975226925599966483262947 25462840388399949724894421)
              ·
                refine ⟨596785321603123821677213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 25462840388399949724894421 596785321603123821677213)
                ·
                  refine ⟨223794495601171433128955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 596785321603123821677213 223794495601171433128955)
                  ·
                    rfl

theorem cell20_490318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 7, 3].length) (baseStart_490318 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_490318 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_490318 prefixEnd_490318 := by exact prefixLift 490318
  have htrace : WordTrace (prefixWord ++ tailWord_490318) baseStart_490318 baseEnd_490318 := by
    simpa [prefixWord, tailWord_490318, baseEnd_490318] using wordTrace_append hprefix tailTrace_490318
  have hstable : (prefixWord ++ tailWord_490318).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490318).length < 2 ^ (prefixWord ++ tailWord_490318).sum := by decide
  have hdescent : baseEnd_490318 < baseStart_490318 := by decide
  rcases family_descends (prefixWord ++ tailWord_490318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490325 : List Nat := [1, 3, 2, 2, 2, 1, 1, 4, 4]
def baseStart_490325 : Nat := 118140960795 + 490325 * 2 ^ 59
def prefixEnd_490325 : Nat := 4983230072969 + 3 ^ 40 * 490325 * 2
def baseEnd_490325 : Nat := 223797690591910519895593

theorem tailTrace_490325 : CollatzResearch.WordTrace tailWord_490325 prefixEnd_490325 223797690591910519895593 := by
  unfold tailWord_490325
  simp only [CollatzResearch.WordTrace]
  refine ⟨17883621948643740688160429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11922414632429160458773619 17883621948643740688160429)
  ·
    refine ⟨6706358230741402758060161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17883621948643740688160429 6706358230741402758060161)
    ·
      refine ⟨5029768673056052068545121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6706358230741402758060161 5029768673056052068545121)
      ·
        refine ⟨3772326504792039051408841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5029768673056052068545121 3772326504792039051408841)
        ·
          refine ⟨2829244878594029288556631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3772326504792039051408841 2829244878594029288556631)
          ·
            refine ⟨4243867317891043932834947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2829244878594029288556631 4243867317891043932834947)
            ·
              refine ⟨6365800976836565899252421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4243867317891043932834947 6365800976836565899252421)
              ·
                refine ⟨1193587683156856106109829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6365800976836565899252421 1193587683156856106109829)
                ·
                  refine ⟨223797690591910519895593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1193587683156856106109829 223797690591910519895593)
                  ·
                    rfl

theorem cell20_490325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 4, 4].length) (baseStart_490325 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_490325 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_490325 prefixEnd_490325 := by exact prefixLift 490325
  have htrace : WordTrace (prefixWord ++ tailWord_490325) baseStart_490325 baseEnd_490325 := by
    simpa [prefixWord, tailWord_490325, baseEnd_490325] using wordTrace_append hprefix tailTrace_490325
  have hstable : (prefixWord ++ tailWord_490325).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490325).length < 2 ^ (prefixWord ++ tailWord_490325).sum := by decide
  have hdescent : baseEnd_490325 < baseStart_490325 := by decide
  rcases family_descends (prefixWord ++ tailWord_490325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490363 : List Nat := [1, 1, 1, 1, 1, 5, 5, 1, 4]
def baseStart_490363 : Nat := 118140960795 + 490363 * 2 ^ 59
def prefixEnd_490363 : Nat := 4983230072969 + 3 ^ 40 * 490363 * 2
def baseEnd_490363 : Nat := 223815034827351276628771

theorem tailTrace_490363 : CollatzResearch.WordTrace tailWord_490363 prefixEnd_490363 223815034827351276628771 := by
  unfold tailWord_490363
  simp only [CollatzResearch.WordTrace]
  refine ⟨17885007922506073178043743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11923338615004048785362495 17885007922506073178043743)
  ·
    refine ⟨26827511883759109767065615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17885007922506073178043743 26827511883759109767065615)
    ·
      refine ⟨40241267825638664650598423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26827511883759109767065615 40241267825638664650598423)
      ·
        refine ⟨60361901738457996975897635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40241267825638664650598423 60361901738457996975897635)
        ·
          refine ⟨90542852607686995463846453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60361901738457996975897635 90542852607686995463846453)
          ·
            refine ⟨8488392431970655824735605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 90542852607686995463846453 8488392431970655824735605)
            ·
              refine ⟨795786790497248983568963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8488392431970655824735605 795786790497248983568963)
              ·
                refine ⟨1193680185745873475353445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 795786790497248983568963 1193680185745873475353445)
                ·
                  refine ⟨223815034827351276628771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1193680185745873475353445 223815034827351276628771)
                  ·
                    rfl

theorem cell20_490363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 5, 1, 4].length) (baseStart_490363 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_490363 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_490363 prefixEnd_490363 := by exact prefixLift 490363
  have htrace : WordTrace (prefixWord ++ tailWord_490363) baseStart_490363 baseEnd_490363 := by
    simpa [prefixWord, tailWord_490363, baseEnd_490363] using wordTrace_append hprefix tailTrace_490363
  have hstable : (prefixWord ++ tailWord_490363).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490363).length < 2 ^ (prefixWord ++ tailWord_490363).sum := by decide
  have hdescent : baseEnd_490363 < baseStart_490363 := by decide
  rcases family_descends (prefixWord ++ tailWord_490363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490373 : List Nat := [1, 3, 1, 1, 3, 3, 4, 1, 3]
def baseStart_490373 : Nat := 118140960795 + 490373 * 2 ^ 59
def prefixEnd_490373 : Nat := 4983230072969 + 3 ^ 40 * 490373 * 2
def baseEnd_490373 : Nat := 223819599099835686295397

theorem tailTrace_490373 : CollatzResearch.WordTrace tailWord_490373 prefixEnd_490373 223819599099835686295397 := by
  unfold tailWord_490373
  simp only [CollatzResearch.WordTrace]
  refine ⟨17885372652469844885907773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11923581768313229923938515 17885372652469844885907773)
  ·
    refine ⟨6707014744676191832215415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17885372652469844885907773 6707014744676191832215415)
    ·
      refine ⟨10060522117014287748323123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6707014744676191832215415 10060522117014287748323123)
      ·
        refine ⟨15090783175521431622484685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10060522117014287748323123 15090783175521431622484685)
        ·
          refine ⟨5659043690820536858431757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15090783175521431622484685 5659043690820536858431757)
          ·
            refine ⟨2122141384057701321911909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5659043690820536858431757 2122141384057701321911909)
            ·
              refine ⟨397901509510818997858483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2122141384057701321911909 397901509510818997858483)
              ·
                refine ⟨596852264266228496787725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 397901509510818997858483 596852264266228496787725)
                ·
                  refine ⟨223819599099835686295397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 596852264266228496787725 223819599099835686295397)
                  ·
                    rfl

theorem cell20_490373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 4, 1, 3].length) (baseStart_490373 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_490373 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_490373 prefixEnd_490373 := by exact prefixLift 490373
  have htrace : WordTrace (prefixWord ++ tailWord_490373) baseStart_490373 baseEnd_490373 := by
    simpa [prefixWord, tailWord_490373, baseEnd_490373] using wordTrace_append hprefix tailTrace_490373
  have hstable : (prefixWord ++ tailWord_490373).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490373).length < 2 ^ (prefixWord ++ tailWord_490373).sum := by decide
  have hdescent : baseEnd_490373 < baseStart_490373 := by decide
  rcases family_descends (prefixWord ++ tailWord_490373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490408 : List Nat := [2, 1, 6, 11]
def baseStart_490408 : Nat := 118140960795 + 490408 * 2 ^ 59
def prefixEnd_490408 : Nat := 4983230072969 + 3 ^ 40 * 490408 * 2
def baseEnd_490408 : Nat := 921134049603008724809

theorem tailTrace_490408 : CollatzResearch.WordTrace tailWord_490408 prefixEnd_490408 921134049603008724809 := by
  unfold tailWord_490408
  simp only [CollatzResearch.WordTrace]
  refine ⟨8943324603671522931715939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11924432804895363908954585 8943324603671522931715939)
  ·
    refine ⟨13414986905507284397573909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8943324603671522931715939 13414986905507284397573909)
    ·
      refine ⟨628827511195653956136277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 13414986905507284397573909 628827511195653956136277)
      ·
        refine ⟨921134049603008724809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 11 628827511195653956136277 921134049603008724809)
        ·
          rfl

theorem cell20_490408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 11].length) (baseStart_490408 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_490408 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_490408 prefixEnd_490408 := by exact prefixLift 490408
  have htrace : WordTrace (prefixWord ++ tailWord_490408) baseStart_490408 baseEnd_490408 := by
    simpa [prefixWord, tailWord_490408, baseEnd_490408] using wordTrace_append hprefix tailTrace_490408
  have hstable : (prefixWord ++ tailWord_490408).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490408).length < 2 ^ (prefixWord ++ tailWord_490408).sum := by decide
  have hdescent : baseEnd_490408 < baseStart_490408 := by decide
  rcases family_descends (prefixWord ++ tailWord_490408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490425 : List Nat := [1, 2, 1, 4, 2, 4, 1, 5]
def baseStart_490425 : Nat := 118140960795 + 490425 * 2 ^ 59
def prefixEnd_490425 : Nat := 4983230072969 + 3 ^ 40 * 490425 * 2
def baseEnd_490425 : Nat := 74614444438918205520617

theorem tailTrace_490425 : CollatzResearch.WordTrace tailWord_490425 prefixEnd_490425 74614444438918205520617 := by
  unfold tailWord_490425
  simp only [CollatzResearch.WordTrace]
  refine ⟨17887269248281457766800729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11924846165520971844533819 17887269248281457766800729)
  ·
    refine ⟨13415451936211093325100547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17887269248281457766800729 13415451936211093325100547)
    ·
      refine ⟨20123177904316639987650821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13415451936211093325100547 20123177904316639987650821)
      ·
        refine ⟨3773095857059369997684529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20123177904316639987650821 3773095857059369997684529)
        ·
          refine ⟨2829821892794527498263397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3773095857059369997684529 2829821892794527498263397)
          ·
            refine ⟨530591604898973905924387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2829821892794527498263397 530591604898973905924387)
            ·
              refine ⟨795887407348460858886581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 530591604898973905924387 795887407348460858886581)
              ·
                refine ⟨74614444438918205520617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 795887407348460858886581 74614444438918205520617)
                ·
                  rfl

theorem cell20_490425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 1, 5].length) (baseStart_490425 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_490425 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_490425 prefixEnd_490425 := by exact prefixLift 490425
  have htrace : WordTrace (prefixWord ++ tailWord_490425) baseStart_490425 baseEnd_490425 := by
    simpa [prefixWord, tailWord_490425, baseEnd_490425] using wordTrace_append hprefix tailTrace_490425
  have hstable : (prefixWord ++ tailWord_490425).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490425).length < 2 ^ (prefixWord ++ tailWord_490425).sum := by decide
  have hdescent : baseEnd_490425 < baseStart_490425 := by decide
  rcases family_descends (prefixWord ++ tailWord_490425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490432 : List Nat := [2, 1, 1, 2, 3, 3, 2, 3, 3]
def baseStart_490432 : Nat := 118140960795 + 490432 * 2 ^ 59
def prefixEnd_490432 : Nat := 4983230072969 + 3 ^ 40 * 490432 * 2
def baseEnd_490432 : Nat := 223846528307493703328489

theorem tailTrace_490432 : CollatzResearch.WordTrace tailWord_490432 prefixEnd_490432 223846528307493703328489 := by
  unfold tailWord_490432
  simp only [CollatzResearch.WordTrace]
  refine ⟨8943762279628048981152775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11925016372837398641537033 8943762279628048981152775)
  ·
    refine ⟨13415643419442073471729163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8943762279628048981152775 13415643419442073471729163)
    ·
      refine ⟨20123465129163110207593745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13415643419442073471729163 20123465129163110207593745)
      ·
        refine ⟨15092598846872332655695309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20123465129163110207593745 15092598846872332655695309)
        ·
          refine ⟨5659724567577124745885741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15092598846872332655695309 5659724567577124745885741)
          ·
            refine ⟨2122396712841421779707153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5659724567577124745885741 2122396712841421779707153)
            ·
              refine ⟨1591797534631066334780365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2122396712841421779707153 1591797534631066334780365)
              ·
                refine ⟨596924075486649875542637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1591797534631066334780365 596924075486649875542637)
                ·
                  refine ⟨223846528307493703328489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 596924075486649875542637 223846528307493703328489)
                  ·
                    rfl

theorem cell20_490432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 3, 3].length) (baseStart_490432 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_490432 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_490432 prefixEnd_490432 := by exact prefixLift 490432
  have htrace : WordTrace (prefixWord ++ tailWord_490432) baseStart_490432 baseEnd_490432 := by
    simpa [prefixWord, tailWord_490432, baseEnd_490432] using wordTrace_append hprefix tailTrace_490432
  have hstable : (prefixWord ++ tailWord_490432).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490432).length < 2 ^ (prefixWord ++ tailWord_490432).sum := by decide
  have hdescent : baseEnd_490432 < baseStart_490432 := by decide
  rcases family_descends (prefixWord ++ tailWord_490432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490456 : List Nat := [2, 1, 2, 2, 2, 3, 1, 5, 2]
def baseStart_490456 : Nat := 118140960795 + 490456 * 2 ^ 59
def prefixEnd_490456 : Nat := 4983230072969 + 3 ^ 40 * 490456 * 2
def baseEnd_490456 : Nat := 223857482561456286528391

theorem tailTrace_490456 : CollatzResearch.WordTrace tailWord_490456 prefixEnd_490456 223857482561456286528391 := by
  unfold tailWord_490456
  simp only [CollatzResearch.WordTrace]
  refine ⟨8944199955584575030589611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11925599940779433374119481 8944199955584575030589611)
  ·
    refine ⟨13416299933376862545884417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8944199955584575030589611 13416299933376862545884417)
    ·
      refine ⟨10062224950032646909413313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13416299933376862545884417 10062224950032646909413313)
      ·
        refine ⟨7546668712524485182059985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10062224950032646909413313 7546668712524485182059985)
        ·
          refine ⟨5660001534393363886544989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7546668712524485182059985 5660001534393363886544989)
          ·
            refine ⟨2122500575397511457454371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5660001534393363886544989 2122500575397511457454371)
            ·
              refine ⟨3183750863096267186181557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2122500575397511457454371 3183750863096267186181557)
              ·
                refine ⟨298476643415275048704521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3183750863096267186181557 298476643415275048704521)
                ·
                  refine ⟨223857482561456286528391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 298476643415275048704521 223857482561456286528391)
                  ·
                    rfl

theorem cell20_490456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 5, 2].length) (baseStart_490456 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_490456 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_490456 prefixEnd_490456 := by exact prefixLift 490456
  have htrace : WordTrace (prefixWord ++ tailWord_490456) baseStart_490456 baseEnd_490456 := by
    simpa [prefixWord, tailWord_490456, baseEnd_490456] using wordTrace_append hprefix tailTrace_490456
  have hstable : (prefixWord ++ tailWord_490456).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490456).length < 2 ^ (prefixWord ++ tailWord_490456).sum := by decide
  have hdescent : baseEnd_490456 < baseStart_490456 := by decide
  rcases family_descends (prefixWord ++ tailWord_490456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490466 : List Nat := [3, 3, 3, 1, 1, 1, 3, 2, 3]
def baseStart_490466 : Nat := 118140960795 + 490466 * 2 ^ 59
def prefixEnd_490466 : Nat := 4983230072969 + 3 ^ 40 * 490466 * 2
def baseEnd_490466 : Nat := 223862046833940696195017

theorem tailTrace_490466 : CollatzResearch.WordTrace tailWord_490466 prefixEnd_490466 223862046833940696195017 := by
  unfold tailWord_490466
  simp only [CollatzResearch.WordTrace]
  refine ⟨4472191160283230442260813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11925843094088614512695501 4472191160283230442260813)
  ·
    refine ⟨1677071685106211415847805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4472191160283230442260813 1677071685106211415847805)
    ·
      refine ⟨628901881914829280942927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1677071685106211415847805 628901881914829280942927)
      ·
        refine ⟨943352822872243921414391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 628901881914829280942927 943352822872243921414391)
        ·
          refine ⟨1415029234308365882121587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 943352822872243921414391 1415029234308365882121587)
          ·
            refine ⟨2122543851462548823182381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1415029234308365882121587 2122543851462548823182381)
            ·
              refine ⟨795953944298455808693393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2122543851462548823182381 795953944298455808693393)
              ·
                refine ⟨596965458223841856520045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 795953944298455808693393 596965458223841856520045)
                ·
                  refine ⟨223862046833940696195017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 596965458223841856520045 223862046833940696195017)
                  ·
                    rfl

theorem cell20_490466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 3, 2, 3].length) (baseStart_490466 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_490466 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_490466 prefixEnd_490466 := by exact prefixLift 490466
  have htrace : WordTrace (prefixWord ++ tailWord_490466) baseStart_490466 baseEnd_490466 := by
    simpa [prefixWord, tailWord_490466, baseEnd_490466] using wordTrace_append hprefix tailTrace_490466
  have hstable : (prefixWord ++ tailWord_490466).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490466).length < 2 ^ (prefixWord ++ tailWord_490466).sum := by decide
  have hdescent : baseEnd_490466 < baseStart_490466 := by decide
  rcases family_descends (prefixWord ++ tailWord_490466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490514 : List Nat := [3, 2, 5, 1, 2, 1, 6]
def baseStart_490514 : Nat := 118140960795 + 490514 * 2 ^ 59
def prefixEnd_490514 : Nat := 4983230072969 + 3 ^ 40 * 490514 * 2
def baseEnd_490514 : Nat := 24875995037985095843869

theorem tailTrace_490514 : CollatzResearch.WordTrace tailWord_490514 prefixEnd_490514 24875995037985095843869 := by
  unfold tailWord_490514
  simp only [CollatzResearch.WordTrace]
  refine ⟨4472628836239756491697649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11927010229972683977860397 4472628836239756491697649)
  ·
    refine ⟨3354471627179817368773237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4472628836239756491697649 3354471627179817368773237)
    ·
      refine ⟨314481715048107878322491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3354471627179817368773237 314481715048107878322491)
      ·
        refine ⟨471722572572161817483737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314481715048107878322491 471722572572161817483737)
        ·
          refine ⟨353791929429121363112803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 471722572572161817483737 353791929429121363112803)
          ·
            refine ⟨530687894143682044669205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 353791929429121363112803 530687894143682044669205)
            ·
              refine ⟨24875995037985095843869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 530687894143682044669205 24875995037985095843869)
              ·
                rfl

theorem cell20_490514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 6].length) (baseStart_490514 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_490514 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_490514 prefixEnd_490514 := by exact prefixLift 490514
  have htrace : WordTrace (prefixWord ++ tailWord_490514) baseStart_490514 baseEnd_490514 := by
    simpa [prefixWord, tailWord_490514, baseEnd_490514] using wordTrace_append hprefix tailTrace_490514
  have hstable : (prefixWord ++ tailWord_490514).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490514).length < 2 ^ (prefixWord ++ tailWord_490514).sum := by decide
  have hdescent : baseEnd_490514 < baseStart_490514 := by decide
  rcases family_descends (prefixWord ++ tailWord_490514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490528 : List Nat := [2, 1, 1, 7, 2, 1, 1, 1, 4]
def baseStart_490528 : Nat := 118140960795 + 490528 * 2 ^ 59
def prefixEnd_490528 : Nat := 4983230072969 + 3 ^ 40 * 490528 * 2
def baseEnd_490528 : Nat := 223890345323344036128097

theorem tailTrace_490528 : CollatzResearch.WordTrace tailWord_490528 prefixEnd_490528 223890345323344036128097 := by
  unfold tailWord_490528
  simp only [CollatzResearch.WordTrace]
  refine ⟨8945512983454153178900119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11927350644605537571866825 8945512983454153178900119)
  ·
    refine ⟨13418269475181229768350179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8945512983454153178900119 13418269475181229768350179)
    ·
      refine ⟨20127404212771844652525269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13418269475181229768350179 20127404212771844652525269)
      ·
        refine ⟨471736036236840109043561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 20127404212771844652525269 471736036236840109043561)
        ·
          refine ⟨353802027177630081782671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 471736036236840109043561 353802027177630081782671)
          ·
            refine ⟨530703040766445122674007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 353802027177630081782671 530703040766445122674007)
            ·
              refine ⟨796054561149667684011011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 530703040766445122674007 796054561149667684011011)
              ·
                refine ⟨1194081841724501526016517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 796054561149667684011011 1194081841724501526016517)
                ·
                  refine ⟨223890345323344036128097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1194081841724501526016517 223890345323344036128097)
                  ·
                    rfl

theorem cell20_490528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 1, 1, 4].length) (baseStart_490528 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_490528 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_490528 prefixEnd_490528 := by exact prefixLift 490528
  have htrace : WordTrace (prefixWord ++ tailWord_490528) baseStart_490528 baseEnd_490528 := by
    simpa [prefixWord, tailWord_490528, baseEnd_490528] using wordTrace_append hprefix tailTrace_490528
  have hstable : (prefixWord ++ tailWord_490528).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490528).length < 2 ^ (prefixWord ++ tailWord_490528).sum := by decide
  have hdescent : baseEnd_490528 < baseStart_490528 := by decide
  rcases family_descends (prefixWord ++ tailWord_490528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490532 : List Nat := [2, 3, 1, 4, 1, 1, 3, 1, 4]
def baseStart_490532 : Nat := 118140960795 + 490532 * 2 ^ 59
def prefixEnd_490532 : Nat := 4983230072969 + 3 ^ 40 * 490532 * 2
def baseEnd_490532 : Nat := 223892171032337799994747

theorem tailTrace_490532 : CollatzResearch.WordTrace tailWord_490532 prefixEnd_490532 223892171032337799994747 := by
  unfold tailWord_490532
  simp only [CollatzResearch.WordTrace]
  refine ⟨8945585929446907520472925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11927447905929210027297233 8945585929446907520472925)
  ·
    refine ⟨3354594723542590320177347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8945585929446907520472925 3354594723542590320177347)
    ·
      refine ⟨5031892085313885480266021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3354594723542590320177347 5031892085313885480266021)
      ·
        refine ⟨943479765996353527549879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5031892085313885480266021 943479765996353527549879)
        ·
          refine ⟨1415219648994530291324819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 943479765996353527549879 1415219648994530291324819)
          ·
            refine ⟨2122829473491795436987229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1415219648994530291324819 2122829473491795436987229)
            ·
              refine ⟨796061052559423288870211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2122829473491795436987229 796061052559423288870211)
              ·
                refine ⟨1194091578839134933305317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 796061052559423288870211 1194091578839134933305317)
                ·
                  refine ⟨223892171032337799994747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1194091578839134933305317 223892171032337799994747)
                  ·
                    rfl

theorem cell20_490532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 3, 1, 4].length) (baseStart_490532 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_490532 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_490532 prefixEnd_490532 := by exact prefixLift 490532
  have htrace : WordTrace (prefixWord ++ tailWord_490532) baseStart_490532 baseEnd_490532 := by
    simpa [prefixWord, tailWord_490532, baseEnd_490532] using wordTrace_append hprefix tailTrace_490532
  have hstable : (prefixWord ++ tailWord_490532).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490532).length < 2 ^ (prefixWord ++ tailWord_490532).sum := by decide
  have hdescent : baseEnd_490532 < baseStart_490532 := by decide
  rcases family_descends (prefixWord ++ tailWord_490532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490546 : List Nat := [3, 2, 1, 1, 2, 2, 3, 3, 3]
def baseStart_490546 : Nat := 118140960795 + 490546 * 2 ^ 59
def prefixEnd_490546 : Nat := 4983230072969 + 3 ^ 40 * 490546 * 2
def baseEnd_490546 : Nat := 223898561013815973528023

theorem tailTrace_490546 : CollatzResearch.WordTrace tailWord_490546 prefixEnd_490546 223898561013815973528023 := by
  unfold tailWord_490546
  simp only [CollatzResearch.WordTrace]
  refine ⟨4472920620210773857988873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11927788320562063621303661 4472920620210773857988873)
  ·
    refine ⟨3354690465158080393491655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4472920620210773857988873 3354690465158080393491655)
    ·
      refine ⟨5032035697737120590237483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3354690465158080393491655 5032035697737120590237483)
      ·
        refine ⟨7548053546605680885356225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5032035697737120590237483 7548053546605680885356225)
        ·
          refine ⟨5661040159954260664017169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7548053546605680885356225 5661040159954260664017169)
          ·
            refine ⟨4245780119965695498012877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5661040159954260664017169 4245780119965695498012877)
            ·
              refine ⟨1592167544987135811754829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4245780119965695498012877 1592167544987135811754829)
              ·
                refine ⟨597062829370175929408061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1592167544987135811754829 597062829370175929408061)
                ·
                  refine ⟨223898561013815973528023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 597062829370175929408061 223898561013815973528023)
                  ·
                    rfl

theorem cell20_490546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 3, 3].length) (baseStart_490546 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_490546 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_490546 prefixEnd_490546 := by exact prefixLift 490546
  have htrace : WordTrace (prefixWord ++ tailWord_490546) baseStart_490546 baseEnd_490546 := by
    simpa [prefixWord, tailWord_490546, baseEnd_490546] using wordTrace_append hprefix tailTrace_490546
  have hstable : (prefixWord ++ tailWord_490546).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490546).length < 2 ^ (prefixWord ++ tailWord_490546).sum := by decide
  have hdescent : baseEnd_490546 < baseStart_490546 := by decide
  rcases family_descends (prefixWord ++ tailWord_490546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490584 : List Nat := [2, 1, 2, 2, 1, 3, 4, 2, 3]
def baseStart_490584 : Nat := 118140960795 + 490584 * 2 ^ 59
def prefixEnd_490584 : Nat := 4983230072969 + 3 ^ 40 * 490584 * 2
def baseEnd_490584 : Nat := 223915905249256730261201

theorem tailTrace_490584 : CollatzResearch.WordTrace tailWord_490584 prefixEnd_490584 223915905249256730261201 := by
  unfold tailWord_490584
  simp only [CollatzResearch.WordTrace]
  refine ⟨8946534227352713960919403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11928712303136951947892537 8946534227352713960919403)
  ·
    refine ⟨13419801341029070941379105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8946534227352713960919403 13419801341029070941379105)
    ·
      refine ⟨10064851005771803206034329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13419801341029070941379105 10064851005771803206034329)
      ·
        refine ⟨7548638254328852404525747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10064851005771803206034329 7548638254328852404525747)
        ·
          refine ⟨11322957381493278606788621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7548638254328852404525747 11322957381493278606788621)
          ·
            refine ⟨4246109018059979477545733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11322957381493278606788621 4246109018059979477545733)
            ·
              refine ⟨796145440886246152039825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4246109018059979477545733 796145440886246152039825)
              ·
                refine ⟨597109080664684614029869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 796145440886246152039825 597109080664684614029869)
                ·
                  refine ⟨223915905249256730261201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 597109080664684614029869 223915905249256730261201)
                  ·
                    rfl

theorem cell20_490584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 4, 2, 3].length) (baseStart_490584 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_490584 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_490584 prefixEnd_490584 := by exact prefixLift 490584
  have htrace : WordTrace (prefixWord ++ tailWord_490584) baseStart_490584 baseEnd_490584 := by
    simpa [prefixWord, tailWord_490584, baseEnd_490584] using wordTrace_append hprefix tailTrace_490584
  have hstable : (prefixWord ++ tailWord_490584).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490584).length < 2 ^ (prefixWord ++ tailWord_490584).sum := by decide
  have hdescent : baseEnd_490584 < baseStart_490584 := by decide
  rcases family_descends (prefixWord ++ tailWord_490584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490594 : List Nat := [3, 3, 2, 2, 1, 3, 1, 5]
def baseStart_490594 : Nat := 118140960795 + 490594 * 2 ^ 59
def prefixEnd_490594 : Nat := 4983230072969 + 3 ^ 40 * 490594 * 2
def baseEnd_490594 : Nat := 74640156507247046642609

theorem tailTrace_490594 : CollatzResearch.WordTrace tailWord_490594 prefixEnd_490594 74640156507247046642609 := by
  unfold tailWord_490594
  simp only [CollatzResearch.WordTrace]
  refine ⟨4473358296167299907425709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11928955456446133086468557 4473358296167299907425709)
  ·
    refine ⟨1677509361062737465284641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4473358296167299907425709 1677509361062737465284641)
    ·
      refine ⟨1258132020797053098963481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1677509361062737465284641 1258132020797053098963481)
      ·
        refine ⟨943599015597789824222611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1258132020797053098963481 943599015597789824222611)
        ·
          refine ⟨1415398523396684736333917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 943599015597789824222611 1415398523396684736333917)
          ·
            refine ⟨530774446273756776125219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1415398523396684736333917 530774446273756776125219)
            ·
              refine ⟨796161669410635164187829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 530774446273756776125219 796161669410635164187829)
              ·
                refine ⟨74640156507247046642609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 796161669410635164187829 74640156507247046642609)
                ·
                  rfl

theorem cell20_490594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 1, 5].length) (baseStart_490594 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_490594 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_490594 prefixEnd_490594 := by exact prefixLift 490594
  have htrace : WordTrace (prefixWord ++ tailWord_490594) baseStart_490594 baseEnd_490594 := by
    simpa [prefixWord, tailWord_490594, baseEnd_490594] using wordTrace_append hprefix tailTrace_490594
  have hstable : (prefixWord ++ tailWord_490594).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490594).length < 2 ^ (prefixWord ++ tailWord_490594).sum := by decide
  have hdescent : baseEnd_490594 < baseStart_490594 := by decide
  rcases family_descends (prefixWord ++ tailWord_490594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490619 : List Nat := [1, 1, 1, 1, 1, 4, 1, 10]
def baseStart_490619 : Nat := 118140960795 + 490619 * 2 ^ 59
def prefixEnd_490619 : Nat := 4983230072969 + 3 ^ 40 * 490619 * 2
def baseEnd_490619 : Nat := 74643960067650721364797

theorem tailTrace_490619 : CollatzResearch.WordTrace tailWord_490619 prefixEnd_490619 74643960067650721364797 := by
  unfold tailWord_490619
  simp only [CollatzResearch.WordTrace]
  refine ⟨17894345009578628899362911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11929563339719085932908607 17894345009578628899362911)
  ·
    refine ⟨26841517514367943349044367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17894345009578628899362911 26841517514367943349044367)
    ·
      refine ⟨40262276271551915023566551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26841517514367943349044367 40262276271551915023566551)
      ·
        refine ⟨60393414407327872535349827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40262276271551915023566551 60393414407327872535349827)
        ·
          refine ⟨90590121610991808803024741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60393414407327872535349827 90590121610991808803024741)
          ·
            refine ⟨16985647802060964150567139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90590121610991808803024741 16985647802060964150567139)
            ·
              refine ⟨25478471703091446225850709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16985647802060964150567139 25478471703091446225850709)
              ·
                refine ⟨74643960067650721364797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 25478471703091446225850709 74643960067650721364797)
                ·
                  rfl

theorem cell20_490619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 10].length) (baseStart_490619 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_490619 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_490619 prefixEnd_490619 := by exact prefixLift 490619
  have htrace : WordTrace (prefixWord ++ tailWord_490619) baseStart_490619 baseEnd_490619 := by
    simpa [prefixWord, tailWord_490619, baseEnd_490619] using wordTrace_append hprefix tailTrace_490619
  have hstable : (prefixWord ++ tailWord_490619).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490619).length < 2 ^ (prefixWord ++ tailWord_490619).sum := by decide
  have hdescent : baseEnd_490619 < baseStart_490619 := by decide
  rcases family_descends (prefixWord ++ tailWord_490619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490625 : List Nat := [1, 2, 4, 2, 2, 2, 2, 3, 2]
def baseStart_490625 : Nat := 118140960795 + 490625 * 2 ^ 59
def prefixEnd_490625 : Nat := 4983230072969 + 3 ^ 40 * 490625 * 2
def baseEnd_490625 : Nat := 223934618766442809894367

theorem tailTrace_490625 : CollatzResearch.WordTrace tailWord_490625 prefixEnd_490625 223934618766442809894367 := by
  unfold tailWord_490625
  simp only [CollatzResearch.WordTrace]
  refine ⟨17894563847556891924081329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11929709231704594616054219 17894563847556891924081329)
  ·
    refine ⟨13420922885667668943060997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17894563847556891924081329 13420922885667668943060997)
    ·
      refine ⟨2516423041062687926823937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13420922885667668943060997 2516423041062687926823937)
      ·
        refine ⟨1887317280797015945117953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2516423041062687926823937 1887317280797015945117953)
        ·
          refine ⟨1415487960597761958838465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1887317280797015945117953 1415487960597761958838465)
          ·
            refine ⟨1061615970448321469128849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1415487960597761958838465 1061615970448321469128849)
            ·
              refine ⟨796211977836241101846637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1061615970448321469128849 796211977836241101846637)
              ·
                refine ⟨298579491688590413192489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 796211977836241101846637 298579491688590413192489)
                ·
                  refine ⟨223934618766442809894367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 298579491688590413192489 223934618766442809894367)
                  ·
                    rfl

theorem cell20_490625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 2, 3, 2].length) (baseStart_490625 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_490625 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_490625 prefixEnd_490625 := by exact prefixLift 490625
  have htrace : WordTrace (prefixWord ++ tailWord_490625) baseStart_490625 baseEnd_490625 := by
    simpa [prefixWord, tailWord_490625, baseEnd_490625] using wordTrace_append hprefix tailTrace_490625
  have hstable : (prefixWord ++ tailWord_490625).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490625).length < 2 ^ (prefixWord ++ tailWord_490625).sum := by decide
  have hdescent : baseEnd_490625 < baseStart_490625 := by decide
  rcases family_descends (prefixWord ++ tailWord_490625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490674 : List Nat := [3, 2, 1, 1, 1, 5, 1, 6]
def baseStart_490674 : Nat := 118140960795 + 490674 * 2 ^ 59
def prefixEnd_490674 : Nat := 4983230072969 + 3 ^ 40 * 490674 * 2
def baseEnd_490674 : Nat := 74652327900538805753611

theorem tailTrace_490674 : CollatzResearch.WordTrace tailWord_490674 prefixEnd_490674 74652327900538805753611 := by
  unfold tailWord_490674
  simp only [CollatzResearch.WordTrace]
  refine ⟨4474087756094843323153769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11930900682919582195076717 4474087756094843323153769)
  ·
    refine ⟨3355565817071132492365327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4474087756094843323153769 3355565817071132492365327)
    ·
      refine ⟨5033348725606698738547991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3355565817071132492365327 5033348725606698738547991)
      ·
        refine ⟨7550023088410048107821987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5033348725606698738547991 7550023088410048107821987)
        ·
          refine ⟨11325034632615072161732981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7550023088410048107821987 11325034632615072161732981)
          ·
            refine ⟨1061721996807663015162467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11325034632615072161732981 1061721996807663015162467)
            ·
              refine ⟨1592582995211494522743701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1061721996807663015162467 1592582995211494522743701)
              ·
                refine ⟨74652327900538805753611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1592582995211494522743701 74652327900538805753611)
                ·
                  rfl

theorem cell20_490674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 6].length) (baseStart_490674 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_490674 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_490674 prefixEnd_490674 := by exact prefixLift 490674
  have htrace : WordTrace (prefixWord ++ tailWord_490674) baseStart_490674 baseEnd_490674 := by
    simpa [prefixWord, tailWord_490674, baseEnd_490674] using wordTrace_append hprefix tailTrace_490674
  have hstable : (prefixWord ++ tailWord_490674).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490674).length < 2 ^ (prefixWord ++ tailWord_490674).sum := by decide
  have hdescent : baseEnd_490674 < baseStart_490674 := by decide
  rcases family_descends (prefixWord ++ tailWord_490674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490681 : List Nat := [1, 2, 1, 4, 1, 3, 1, 2, 5]
def baseStart_490681 : Nat := 118140960795 + 490681 * 2 ^ 59
def prefixEnd_490681 : Nat := 4983230072969 + 3 ^ 40 * 490681 * 2
def baseEnd_490681 : Nat := 223960178692355504027471

theorem tailTrace_490681 : CollatzResearch.WordTrace tailWord_490681 prefixEnd_490681 223960178692355504027471 := by
  unfold tailWord_490681
  simp only [CollatzResearch.WordTrace]
  refine ⟨17896606335354013488119897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11931070890236008992079931 17896606335354013488119897)
  ·
    refine ⟨13422454751515510116089923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17896606335354013488119897 13422454751515510116089923)
    ·
      refine ⟨20133682127273265174134885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13422454751515510116089923 20133682127273265174134885)
      ·
        refine ⟨3775065398863737220150291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20133682127273265174134885 3775065398863737220150291)
        ·
          refine ⟨5662598098295605830225437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3775065398863737220150291 5662598098295605830225437)
          ·
            refine ⟨2123474286860852186334539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5662598098295605830225437 2123474286860852186334539)
            ·
              refine ⟨3185211430291278279501809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2123474286860852186334539 3185211430291278279501809)
              ·
                refine ⟨2388908572718458709626357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3185211430291278279501809 2388908572718458709626357)
                ·
                  refine ⟨223960178692355504027471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2388908572718458709626357 223960178692355504027471)
                  ·
                    rfl

theorem cell20_490681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 2, 5].length) (baseStart_490681 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_490681 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_490681 prefixEnd_490681 := by exact prefixLift 490681
  have htrace : WordTrace (prefixWord ++ tailWord_490681) baseStart_490681 baseEnd_490681 := by
    simpa [prefixWord, tailWord_490681, baseEnd_490681] using wordTrace_append hprefix tailTrace_490681
  have hstable : (prefixWord ++ tailWord_490681).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490681).length < 2 ^ (prefixWord ++ tailWord_490681).sum := by decide
  have hdescent : baseEnd_490681 < baseStart_490681 := by decide
  rcases family_descends (prefixWord ++ tailWord_490681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490708 : List Nat := [2, 4, 1, 4, 1, 1, 2, 5]
def baseStart_490708 : Nat := 118140960795 + 490708 * 2 ^ 59
def prefixEnd_490708 : Nat := 4983230072969 + 3 ^ 40 * 490708 * 2
def baseEnd_490708 : Nat := 74657500742687803375787

theorem tailTrace_490708 : CollatzResearch.WordTrace tailWord_490708 prefixEnd_490708 74657500742687803375787 := by
  unfold tailWord_490708
  simp only [CollatzResearch.WordTrace]
  refine ⟨8948795553128098549676389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11931727404170798066235185 8948795553128098549676389)
  ·
    refine ⟨1677899166211518478064323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8948795553128098549676389 1677899166211518478064323)
    ·
      refine ⟨2516848749317277717096485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1677899166211518478064323 2516848749317277717096485)
      ·
        refine ⟨471909140496989571955591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2516848749317277717096485 471909140496989571955591)
        ·
          refine ⟨707863710745484357933387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 471909140496989571955591 707863710745484357933387)
          ·
            refine ⟨1061795566118226536900081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 707863710745484357933387 1061795566118226536900081)
            ·
              refine ⟨796346674588669902675061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1061795566118226536900081 796346674588669902675061)
              ·
                refine ⟨74657500742687803375787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 796346674588669902675061 74657500742687803375787)
                ·
                  rfl

theorem cell20_490708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 2, 5].length) (baseStart_490708 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_490708 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_490708 prefixEnd_490708 := by exact prefixLift 490708
  have htrace : WordTrace (prefixWord ++ tailWord_490708) baseStart_490708 baseEnd_490708 := by
    simpa [prefixWord, tailWord_490708, baseEnd_490708] using wordTrace_append hprefix tailTrace_490708
  have hstable : (prefixWord ++ tailWord_490708).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490708).length < 2 ^ (prefixWord ++ tailWord_490708).sum := by decide
  have hdescent : baseEnd_490708 < baseStart_490708 := by decide
  rcases family_descends (prefixWord ++ tailWord_490708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490750 : List Nat := [4, 2, 2, 1, 1, 10]
def baseStart_490750 : Nat := 118140960795 + 490750 * 2 ^ 59
def prefixEnd_490750 : Nat := 4983230072969 + 3 ^ 40 * 490750 * 2
def baseEnd_490750 : Nat := 8295987858240664101007

theorem tailTrace_490750 : CollatzResearch.WordTrace tailWord_490750 prefixEnd_490750 8295987858240664101007 := by
  unfold tailWord_490750
  simp only [CollatzResearch.WordTrace]
  refine ⟨2237390371513004784047713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11932748648069358848254469 2237390371513004784047713)
  ·
    refine ⟨1678042778634753588035785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2237390371513004784047713 1678042778634753588035785)
    ·
      refine ⟨1258532083976065191026839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1678042778634753588035785 1258532083976065191026839)
      ·
        refine ⟨1887798125964097786540259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1258532083976065191026839 1887798125964097786540259)
        ·
          refine ⟨2831697188946146679810389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1887798125964097786540259 2831697188946146679810389)
          ·
            refine ⟨8295987858240664101007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2831697188946146679810389 8295987858240664101007)
            ·
              rfl

theorem cell20_490750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 10].length) (baseStart_490750 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_490750 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_490750 prefixEnd_490750 := by exact prefixLift 490750
  have htrace : WordTrace (prefixWord ++ tailWord_490750) baseStart_490750 baseEnd_490750 := by
    simpa [prefixWord, tailWord_490750, baseEnd_490750] using wordTrace_append hprefix tailTrace_490750
  have hstable : (prefixWord ++ tailWord_490750).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490750).length < 2 ^ (prefixWord ++ tailWord_490750).sum := by decide
  have hdescent : baseEnd_490750 < baseStart_490750 := by decide
  rcases family_descends (prefixWord ++ tailWord_490750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490756 : List Nat := [2, 3, 2, 2, 2, 3, 2, 2, 2]
def baseStart_490756 : Nat := 118140960795 + 490756 * 2 ^ 59
def prefixEnd_490756 : Nat := 4983230072969 + 3 ^ 40 * 490756 * 2
def baseEnd_490756 : Nat := 223994410735988576527165

theorem tailTrace_490756 : CollatzResearch.WordTrace tailWord_490756 prefixEnd_490756 223994410735988576527165 := by
  unfold tailWord_490756
  simp only [CollatzResearch.WordTrace]
  refine ⟨8949670905041150648550061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11932894540054867531400081 8949670905041150648550061)
  ·
    refine ⟨3356126589390431493206273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8949670905041150648550061 3356126589390431493206273)
    ·
      refine ⟨2517094942042823619904705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3356126589390431493206273 2517094942042823619904705)
      ·
        refine ⟨1887821206532117714928529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2517094942042823619904705 1887821206532117714928529)
        ·
          refine ⟨1415865904899088286196397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1887821206532117714928529 1415865904899088286196397)
          ·
            refine ⟨530949714337158107323649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1415865904899088286196397 530949714337158107323649)
            ·
              refine ⟨398212285752868580492737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 530949714337158107323649 398212285752868580492737)
              ·
                refine ⟨298659214314651435369553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 398212285752868580492737 298659214314651435369553)
                ·
                  refine ⟨223994410735988576527165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 298659214314651435369553 223994410735988576527165)
                  ·
                    rfl

theorem cell20_490756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 2, 2, 2].length) (baseStart_490756 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_490756 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_490756 prefixEnd_490756 := by exact prefixLift 490756
  have htrace : WordTrace (prefixWord ++ tailWord_490756) baseStart_490756 baseEnd_490756 := by
    simpa [prefixWord, tailWord_490756, baseEnd_490756] using wordTrace_append hprefix tailTrace_490756
  have hstable : (prefixWord ++ tailWord_490756).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490756).length < 2 ^ (prefixWord ++ tailWord_490756).sum := by decide
  have hdescent : baseEnd_490756 < baseStart_490756 := by decide
  rcases family_descends (prefixWord ++ tailWord_490756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490781 : List Nat := [1, 4, 2, 3, 1, 1, 1, 1, 6]
def baseStart_490781 : Nat := 118140960795 + 490781 * 2 ^ 59
def prefixEnd_490781 : Nat := 4983230072969 + 3 ^ 40 * 490781 * 2
def baseEnd_490781 : Nat := 224005821417199600693729

theorem tailTrace_490781 : CollatzResearch.WordTrace tailWord_490781 prefixEnd_490781 224005821417199600693729 := by
  unfold tailWord_490781
  simp only [CollatzResearch.WordTrace]
  refine ⟨17900253634991730566760197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11933502423327820377840131 17900253634991730566760197)
  ·
    refine ⟨3356297556560949481267537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17900253634991730566760197 3356297556560949481267537)
    ·
      refine ⟨2517223167420712110950653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3356297556560949481267537 2517223167420712110950653)
      ·
        refine ⟨943958687782767041606495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2517223167420712110950653 943958687782767041606495)
        ·
          refine ⟨1415938031674150562409743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 943958687782767041606495 1415938031674150562409743)
          ·
            refine ⟨2123907047511225843614615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1415938031674150562409743 2123907047511225843614615)
            ·
              refine ⟨3185860571266838765421923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2123907047511225843614615 3185860571266838765421923)
              ·
                refine ⟨4778790856900258148132885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3185860571266838765421923 4778790856900258148132885)
                ·
                  refine ⟨224005821417199600693729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4778790856900258148132885 224005821417199600693729)
                  ·
                    rfl

theorem cell20_490781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 1, 6].length) (baseStart_490781 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_490781 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_490781 prefixEnd_490781 := by exact prefixLift 490781
  have htrace : WordTrace (prefixWord ++ tailWord_490781) baseStart_490781 baseEnd_490781 := by
    simpa [prefixWord, tailWord_490781, baseEnd_490781] using wordTrace_append hprefix tailTrace_490781
  have hstable : (prefixWord ++ tailWord_490781).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490781).length < 2 ^ (prefixWord ++ tailWord_490781).sum := by decide
  have hdescent : baseEnd_490781 < baseStart_490781 := by decide
  rcases family_descends (prefixWord ++ tailWord_490781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490812 : List Nat := [2, 2, 2, 2, 1, 3, 3, 2, 3]
def baseStart_490812 : Nat := 118140960795 + 490812 * 2 ^ 59
def prefixEnd_490812 : Nat := 4983230072969 + 3 ^ 40 * 490812 * 2
def baseEnd_490812 : Nat := 224019970661901270660269

theorem tailTrace_490812 : CollatzResearch.WordTrace tailWord_490812 prefixEnd_490812 224019970661901270660269 := by
  unfold tailWord_490812
  simp only [CollatzResearch.WordTrace]
  refine ⟨8950692148939711430569345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11934256198586281907425793 8950692148939711430569345)
  ·
    refine ⟨6713019111704783572927009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8950692148939711430569345 6713019111704783572927009)
    ·
      refine ⟨5034764333778587679695257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6713019111704783572927009 5034764333778587679695257)
      ·
        refine ⟨3776073250333940759771443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5034764333778587679695257 3776073250333940759771443)
        ·
          refine ⟨5664109875500911139657165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3776073250333940759771443 5664109875500911139657165)
          ·
            refine ⟨2124041203312841677371437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5664109875500911139657165 2124041203312841677371437)
            ·
              refine ⟨796515451242315629014289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2124041203312841677371437 796515451242315629014289)
              ·
                refine ⟨597386588431736721760717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 796515451242315629014289 597386588431736721760717)
                ·
                  refine ⟨224019970661901270660269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 597386588431736721760717 224019970661901270660269)
                  ·
                    rfl

theorem cell20_490812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 3, 2, 3].length) (baseStart_490812 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_490812 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_490812 prefixEnd_490812 := by exact prefixLift 490812
  have htrace : WordTrace (prefixWord ++ tailWord_490812) baseStart_490812 baseEnd_490812 := by
    simpa [prefixWord, tailWord_490812, baseEnd_490812] using wordTrace_append hprefix tailTrace_490812
  have hstable : (prefixWord ++ tailWord_490812).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490812).length < 2 ^ (prefixWord ++ tailWord_490812).sum := by decide
  have hdescent : baseEnd_490812 < baseStart_490812 := by decide
  rcases family_descends (prefixWord ++ tailWord_490812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490840 : List Nat := [2, 1, 2, 2, 1, 1, 3, 4, 4]
def baseStart_490840 : Nat := 118140960795 + 490840 * 2 ^ 59
def prefixEnd_490840 : Nat := 4983230072969 + 3 ^ 40 * 490840 * 2
def baseEnd_490840 : Nat := 224032750624857617726821

theorem tailTrace_490840 : CollatzResearch.WordTrace tailWord_490840 prefixEnd_490840 224032750624857617726821 := by
  unfold tailWord_490840
  simp only [CollatzResearch.WordTrace]
  refine ⟨8951202770888991821578987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11934937027851989095438649 8951202770888991821578987)
  ·
    refine ⟨13426804156333487732368481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8951202770888991821578987 13426804156333487732368481)
    ·
      refine ⟨10070103117250115799276361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13426804156333487732368481 10070103117250115799276361)
      ·
        refine ⟨7552577337937586849457271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10070103117250115799276361 7552577337937586849457271)
        ·
          refine ⟨11328866006906380274185907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7552577337937586849457271 11328866006906380274185907)
          ·
            refine ⟨16993299010359570411278861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11328866006906380274185907 16993299010359570411278861)
            ·
              refine ⟨6372487128884838904229573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16993299010359570411278861 6372487128884838904229573)
              ·
                refine ⟨1194841336665907294543045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6372487128884838904229573 1194841336665907294543045)
                ·
                  refine ⟨224032750624857617726821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1194841336665907294543045 224032750624857617726821)
                  ·
                    rfl

theorem cell20_490840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 4, 4].length) (baseStart_490840 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_490840 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_490840 prefixEnd_490840 := by exact prefixLift 490840
  have htrace : WordTrace (prefixWord ++ tailWord_490840) baseStart_490840 baseEnd_490840 := by
    simpa [prefixWord, tailWord_490840, baseEnd_490840] using wordTrace_append hprefix tailTrace_490840
  have hstable : (prefixWord ++ tailWord_490840).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490840).length < 2 ^ (prefixWord ++ tailWord_490840).sum := by decide
  have hdescent : baseEnd_490840 < baseStart_490840 := by decide
  rcases family_descends (prefixWord ++ tailWord_490840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490857 : List Nat := [1, 2, 1, 1, 1, 3, 2, 7, 2]
def baseStart_490857 : Nat := 118140960795 + 490857 * 2 ^ 59
def prefixEnd_490857 : Nat := 4983230072969 + 3 ^ 40 * 490857 * 2
def baseEnd_490857 : Nat := 224040509888081114160085

theorem tailTrace_490857 : CollatzResearch.WordTrace tailWord_490857 prefixEnd_490857 224040509888081114160085 := by
  unfold tailWord_490857
  simp only [CollatzResearch.WordTrace]
  refine ⟨17903025582716395546526825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11935350388477597031017883 17903025582716395546526825)
  ·
    refine ⟨13427269187037296659895119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17903025582716395546526825 13427269187037296659895119)
    ·
      refine ⟨20140903780555944989842679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13427269187037296659895119 20140903780555944989842679)
      ·
        refine ⟨30211355670833917484764019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20140903780555944989842679 30211355670833917484764019)
        ·
          refine ⟨45317033506250876227146029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30211355670833917484764019 45317033506250876227146029)
          ·
            refine ⟨16993887564844078585179761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45317033506250876227146029 16993887564844078585179761)
            ·
              refine ⟨12745415673633058938884821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16993887564844078585179761 12745415673633058938884821)
              ·
                refine ⟨298720679850774818880113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 12745415673633058938884821 298720679850774818880113)
                ·
                  refine ⟨224040509888081114160085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 298720679850774818880113 224040509888081114160085)
                  ·
                    rfl

theorem cell20_490857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 7, 2].length) (baseStart_490857 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_490857 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_490857 prefixEnd_490857 := by exact prefixLift 490857
  have htrace : WordTrace (prefixWord ++ tailWord_490857) baseStart_490857 baseEnd_490857 := by
    simpa [prefixWord, tailWord_490857, baseEnd_490857] using wordTrace_append hprefix tailTrace_490857
  have hstable : (prefixWord ++ tailWord_490857).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490857).length < 2 ^ (prefixWord ++ tailWord_490857).sum := by decide
  have hdescent : baseEnd_490857 < baseStart_490857 := by decide
  rcases family_descends (prefixWord ++ tailWord_490857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490871 : List Nat := [1, 1, 3, 1, 1, 2, 4, 4, 3]
def baseStart_490871 : Nat := 118140960795 + 490871 * 2 ^ 59
def prefixEnd_490871 : Nat := 4983230072969 + 3 ^ 40 * 490871 * 2
def baseEnd_490871 : Nat := 224046899869559287693361

theorem tailTrace_490871 : CollatzResearch.WordTrace tailWord_490871 prefixEnd_490871 224046899869559287693361 := by
  unfold tailWord_490871
  simp only [CollatzResearch.WordTrace]
  refine ⟨17903536204665675937536467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11935690803110450625024311 17903536204665675937536467)
  ·
    refine ⟨26855304306998513906304701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17903536204665675937536467 26855304306998513906304701)
    ·
      refine ⟨10070739115124442714864263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26855304306998513906304701 10070739115124442714864263)
      ·
        refine ⟨15106108672686664072296395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10070739115124442714864263 15106108672686664072296395)
        ·
          refine ⟨22659163009029996108444593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15106108672686664072296395 22659163009029996108444593)
          ·
            refine ⟨16994372256772497081333445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22659163009029996108444593 16994372256772497081333445)
            ·
              refine ⟨3186444798144843202750021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16994372256772497081333445 3186444798144843202750021)
              ·
                refine ⟨597458399652158100515629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3186444798144843202750021 597458399652158100515629)
                ·
                  refine ⟨224046899869559287693361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 597458399652158100515629 224046899869559287693361)
                  ·
                    rfl

theorem cell20_490871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 4, 3].length) (baseStart_490871 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_490871 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_490871 prefixEnd_490871 := by exact prefixLift 490871
  have htrace : WordTrace (prefixWord ++ tailWord_490871) baseStart_490871 baseEnd_490871 := by
    simpa [prefixWord, tailWord_490871, baseEnd_490871] using wordTrace_append hprefix tailTrace_490871
  have hstable : (prefixWord ++ tailWord_490871).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490871).length < 2 ^ (prefixWord ++ tailWord_490871).sum := by decide
  have hdescent : baseEnd_490871 < baseStart_490871 := by decide
  rcases family_descends (prefixWord ++ tailWord_490871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490881 : List Nat := [1, 2, 4, 3, 2, 1, 2, 5]
def baseStart_490881 : Nat := 118140960795 + 490881 * 2 ^ 59
def prefixEnd_490881 : Nat := 4983230072969 + 3 ^ 40 * 490881 * 2
def baseEnd_490881 : Nat := 74683821380681232453329

theorem tailTrace_490881 : CollatzResearch.WordTrace tailWord_490881 prefixEnd_490881 74683821380681232453329 := by
  unfold tailWord_490881
  simp only [CollatzResearch.WordTrace]
  refine ⟨17903900934629447645400497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11935933956419631763600331 17903900934629447645400497)
  ·
    refine ⟨13427925700972085734050373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17903900934629447645400497 13427925700972085734050373)
    ·
      refine ⟨2517736068932266075134445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13427925700972085734050373 2517736068932266075134445)
      ·
        refine ⟨944151025849599778175417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2517736068932266075134445 944151025849599778175417)
        ·
          refine ⟨708113269387199833631563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 944151025849599778175417 708113269387199833631563)
          ·
            refine ⟨1062169904080799750447345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 708113269387199833631563 1062169904080799750447345)
            ·
              refine ⟨796627428060599812835509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1062169904080799750447345 796627428060599812835509)
              ·
                refine ⟨74683821380681232453329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 796627428060599812835509 74683821380681232453329)
                ·
                  rfl

theorem cell20_490881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 2, 5].length) (baseStart_490881 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_490881 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_490881 prefixEnd_490881 := by exact prefixLift 490881
  have htrace : WordTrace (prefixWord ++ tailWord_490881) baseStart_490881 baseEnd_490881 := by
    simpa [prefixWord, tailWord_490881, baseEnd_490881] using wordTrace_append hprefix tailTrace_490881
  have hstable : (prefixWord ++ tailWord_490881).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490881).length < 2 ^ (prefixWord ++ tailWord_490881).sum := by decide
  have hdescent : baseEnd_490881 < baseStart_490881 := by decide
  rcases family_descends (prefixWord ++ tailWord_490881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490885 : List Nat := [1, 3, 1, 1, 3, 1, 3, 7]
def baseStart_490885 : Nat := 118140960795 + 490885 * 2 ^ 59
def prefixEnd_490885 : Nat := 4983230072969 + 3 ^ 40 * 490885 * 2
def baseEnd_490885 : Nat := 74684429950345820408879

theorem tailTrace_490885 : CollatzResearch.WordTrace tailWord_490885 prefixEnd_490885 74684429950345820408879 := by
  unfold tailWord_490885
  simp only [CollatzResearch.WordTrace]
  refine ⟨17904046826614956328546109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11936031217743304219030739 17904046826614956328546109)
  ·
    refine ⟨6714017559980608623204791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17904046826614956328546109 6714017559980608623204791)
    ·
      refine ⟨10071026339970912934807187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6714017559980608623204791 10071026339970912934807187)
      ·
        refine ⟨15106539509956369402210781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10071026339970912934807187 15106539509956369402210781)
        ·
          refine ⟨5664952316233638525829043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15106539509956369402210781 5664952316233638525829043)
          ·
            refine ⟨8497428474350457788743565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5664952316233638525829043 8497428474350457788743565)
            ·
              refine ⟨3186535677881421670778837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8497428474350457788743565 3186535677881421670778837)
              ·
                refine ⟨74684429950345820408879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3186535677881421670778837 74684429950345820408879)
                ·
                  rfl

theorem cell20_490885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 7].length) (baseStart_490885 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_490885 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_490885 prefixEnd_490885 := by exact prefixLift 490885
  have htrace : WordTrace (prefixWord ++ tailWord_490885) baseStart_490885 baseEnd_490885 := by
    simpa [prefixWord, tailWord_490885, baseEnd_490885] using wordTrace_append hprefix tailTrace_490885
  have hstable : (prefixWord ++ tailWord_490885).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490885).length < 2 ^ (prefixWord ++ tailWord_490885).sum := by decide
  have hdescent : baseEnd_490885 < baseStart_490885 := by decide
  rcases family_descends (prefixWord ++ tailWord_490885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490888 : List Nat := [2, 1, 3, 3, 1, 3, 1, 3, 3]
def baseStart_490888 : Nat := 118140960795 + 490888 * 2 ^ 59
def prefixEnd_490888 : Nat := 4983230072969 + 3 ^ 40 * 490888 * 2
def baseEnd_490888 : Nat := 224054659132782784126625

theorem tailTrace_490888 : CollatzResearch.WordTrace tailWord_490888 prefixEnd_490888 224054659132782784126625 := by
  unfold tailWord_490888
  simp only [CollatzResearch.WordTrace]
  refine ⟨8952078122802043920452659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11936104163736058560603545 8952078122802043920452659)
  ·
    refine ⟨13428117184203065880678989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8952078122802043920452659 13428117184203065880678989)
    ·
      refine ⟨5035543944076149705254621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13428117184203065880678989 5035543944076149705254621)
      ·
        refine ⟨1888328979028556139470483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5035543944076149705254621 1888328979028556139470483)
        ·
          refine ⟨2832493468542834209205725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1888328979028556139470483 2832493468542834209205725)
          ·
            refine ⟨1062185050703562828452147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2832493468542834209205725 1062185050703562828452147)
            ·
              refine ⟨1593277576055344242678221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1062185050703562828452147 1593277576055344242678221)
              ·
                refine ⟨597479091020754091004333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1593277576055344242678221 597479091020754091004333)
                ·
                  refine ⟨224054659132782784126625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 597479091020754091004333 224054659132782784126625)
                  ·
                    rfl

theorem cell20_490888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 3, 3].length) (baseStart_490888 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_490888 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_490888 prefixEnd_490888 := by exact prefixLift 490888
  have htrace : WordTrace (prefixWord ++ tailWord_490888) baseStart_490888 baseEnd_490888 := by
    simpa [prefixWord, tailWord_490888, baseEnd_490888] using wordTrace_append hprefix tailTrace_490888
  have hstable : (prefixWord ++ tailWord_490888).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490888).length < 2 ^ (prefixWord ++ tailWord_490888).sum := by decide
  have hdescent : baseEnd_490888 < baseStart_490888 := by decide
  rcases family_descends (prefixWord ++ tailWord_490888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490947 : List Nat := [1, 1, 1, 3, 1, 1, 6, 3, 3]
def baseStart_490947 : Nat := 118140960795 + 490947 * 2 ^ 59
def prefixEnd_490947 : Nat := 4983230072969 + 3 ^ 40 * 490947 * 2
def baseEnd_490947 : Nat := 224081588340440801159717

theorem tailTrace_490947 : CollatzResearch.WordTrace tailWord_490947 prefixEnd_490947 224081588340440801159717 := by
  unfold tailWord_490947
  simp only [CollatzResearch.WordTrace]
  refine ⟨17906308152390340917303095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11937538768260227278202063 17906308152390340917303095)
  ·
    refine ⟨26859462228585511375954643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17906308152390340917303095 26859462228585511375954643)
    ·
      refine ⟨40289193342878267063931965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26859462228585511375954643 40289193342878267063931965)
      ·
        refine ⟨15108447503579350148974487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40289193342878267063931965 15108447503579350148974487)
        ·
          refine ⟨22662671255369025223461731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15108447503579350148974487 22662671255369025223461731)
          ·
            refine ⟨33994006883053537835192597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22662671255369025223461731 33994006883053537835192597)
            ·
              refine ⟨1593469072643134586024653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 33994006883053537835192597 1593469072643134586024653)
              ·
                refine ⟨597550902241175469759245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1593469072643134586024653 597550902241175469759245)
                ·
                  refine ⟨224081588340440801159717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 597550902241175469759245 224081588340440801159717)
                  ·
                    rfl

theorem cell20_490947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 3, 3].length) (baseStart_490947 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_490947 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_490947 prefixEnd_490947 := by exact prefixLift 490947
  have htrace : WordTrace (prefixWord ++ tailWord_490947) baseStart_490947 baseEnd_490947 := by
    simpa [prefixWord, tailWord_490947, baseEnd_490947] using wordTrace_append hprefix tailTrace_490947
  have hstable : (prefixWord ++ tailWord_490947).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490947).length < 2 ^ (prefixWord ++ tailWord_490947).sum := by decide
  have hdescent : baseEnd_490947 < baseStart_490947 := by decide
  rcases family_descends (prefixWord ++ tailWord_490947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490954 : List Nat := [3, 1, 2, 1, 2, 3, 1, 1, 6]
def baseStart_490954 : Nat := 118140960795 + 490954 * 2 ^ 59
def prefixEnd_490954 : Nat := 4983230072969 + 3 ^ 40 * 490954 * 2
def baseEnd_490954 : Nat := 224084783331179887926355

theorem tailTrace_490954 : CollatzResearch.WordTrace tailWord_490954 prefixEnd_490954 224084783331179887926355 := by
  unfold tailWord_490954
  simp only [CollatzResearch.WordTrace]
  refine ⟨4476640865841245278201979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11937708975576654075205277 4476640865841245278201979)
  ·
    refine ⟨6714961298761867917302969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4476640865841245278201979 6714961298761867917302969)
    ·
      refine ⟨5036220974071400937977227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6714961298761867917302969 5036220974071400937977227)
      ·
        refine ⟨7554331461107101406965841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5036220974071400937977227 7554331461107101406965841)
        ·
          refine ⟨5665748595830326055224381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7554331461107101406965841 5665748595830326055224381)
          ·
            refine ⟨2124655723436372270709143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5665748595830326055224381 2124655723436372270709143)
            ·
              refine ⟨3186983585154558406063715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2124655723436372270709143 3186983585154558406063715)
              ·
                refine ⟨4780475377731837609095573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3186983585154558406063715 4780475377731837609095573)
                ·
                  refine ⟨224084783331179887926355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4780475377731837609095573 224084783331179887926355)
                  ·
                    rfl

theorem cell20_490954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 1, 6].length) (baseStart_490954 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_490954 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_490954 prefixEnd_490954 := by exact prefixLift 490954
  have htrace : WordTrace (prefixWord ++ tailWord_490954) baseStart_490954 baseEnd_490954 := by
    simpa [prefixWord, tailWord_490954, baseEnd_490954] using wordTrace_append hprefix tailTrace_490954
  have hstable : (prefixWord ++ tailWord_490954).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490954).length < 2 ^ (prefixWord ++ tailWord_490954).sum := by decide
  have hdescent : baseEnd_490954 < baseStart_490954 := by decide
  rcases family_descends (prefixWord ++ tailWord_490954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490981 : List Nat := [1, 3, 1, 5, 1, 3, 1, 2, 3]
def baseStart_490981 : Nat := 118140960795 + 490981 * 2 ^ 59
def prefixEnd_490981 : Nat := 4983230072969 + 3 ^ 40 * 490981 * 2
def baseEnd_490981 : Nat := 224097106866887794026245

theorem tailTrace_490981 : CollatzResearch.WordTrace tailWord_490981 prefixEnd_490981 224097106866887794026245 := by
  unfold tailWord_490981
  simp only [CollatzResearch.WordTrace]
  refine ⟨17907548234267164724040797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11938365489511443149360531 17907548234267164724040797)
  ·
    refine ⟨6715330587850186771515299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17907548234267164724040797 6715330587850186771515299)
    ·
      refine ⟨10072995881775280157272949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6715330587850186771515299 10072995881775280157272949)
      ·
        refine ⟨944343363916432514744339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10072995881775280157272949 944343363916432514744339)
        ·
          refine ⟨1416515045874648772116509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 944343363916432514744339 1416515045874648772116509)
          ·
            refine ⟨531193142202993289543691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1416515045874648772116509 531193142202993289543691)
            ·
              refine ⟨796789713304489934315537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 531193142202993289543691 796789713304489934315537)
              ·
                refine ⟨597592284978367450736653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 796789713304489934315537 597592284978367450736653)
                ·
                  refine ⟨224097106866887794026245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 597592284978367450736653 224097106866887794026245)
                  ·
                    rfl

theorem cell20_490981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 1, 2, 3].length) (baseStart_490981 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_490981 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_490981 prefixEnd_490981 := by exact prefixLift 490981
  have htrace : WordTrace (prefixWord ++ tailWord_490981) baseStart_490981 baseEnd_490981 := by
    simpa [prefixWord, tailWord_490981, baseEnd_490981] using wordTrace_append hprefix tailTrace_490981
  have hstable : (prefixWord ++ tailWord_490981).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490981).length < 2 ^ (prefixWord ++ tailWord_490981).sum := by decide
  have hdescent : baseEnd_490981 < baseStart_490981 := by decide
  rcases family_descends (prefixWord ++ tailWord_490981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490992 : List Nat := [2, 1, 1, 1, 3, 4, 1, 3, 4]
def baseStart_490992 : Nat := 118140960795 + 490992 * 2 ^ 59
def prefixEnd_490992 : Nat := 4983230072969 + 3 ^ 40 * 490992 * 2
def baseEnd_490992 : Nat := 224102127566620644659533

theorem tailTrace_490992 : CollatzResearch.WordTrace tailWord_490992 prefixEnd_490992 224102127566620644659533 := by
  unfold tailWord_490992
  simp only [CollatzResearch.WordTrace]
  refine ⟨8953974718613656801345615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11938632958151542401794153 8953974718613656801345615)
  ·
    refine ⟨13430962077920485202018423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8953974718613656801345615 13430962077920485202018423)
    ·
      refine ⟨20146443116880727803027635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13430962077920485202018423 20146443116880727803027635)
      ·
        refine ⟨30219664675321091704541453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20146443116880727803027635 30219664675321091704541453)
        ·
          refine ⟨11332374253245409389203045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30219664675321091704541453 11332374253245409389203045)
          ·
            refine ⟨2124820172483514260475571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11332374253245409389203045 2124820172483514260475571)
            ·
              refine ⟨3187230258725271390713357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2124820172483514260475571 3187230258725271390713357)
              ·
                refine ⟨1195211347021976771517509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3187230258725271390713357 1195211347021976771517509)
                ·
                  refine ⟨224102127566620644659533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1195211347021976771517509 224102127566620644659533)
                  ·
                    rfl

theorem cell20_490992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 3, 4].length) (baseStart_490992 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_490992 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_490992 prefixEnd_490992 := by exact prefixLift 490992
  have htrace : WordTrace (prefixWord ++ tailWord_490992) baseStart_490992 baseEnd_490992 := by
    simpa [prefixWord, tailWord_490992, baseEnd_490992] using wordTrace_append hprefix tailTrace_490992
  have hstable : (prefixWord ++ tailWord_490992).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490992).length < 2 ^ (prefixWord ++ tailWord_490992).sum := by decide
  have hdescent : baseEnd_490992 < baseStart_490992 := by decide
  rcases family_descends (prefixWord ++ tailWord_490992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491002 : List Nat := [3, 1, 1, 1, 1, 2, 7, 1, 3]
def baseStart_491002 : Nat := 118140960795 + 491002 * 2 ^ 59
def prefixEnd_491002 : Nat := 4983230072969 + 3 ^ 40 * 491002 * 2
def baseEnd_491002 : Nat := 224106691839105054326159

theorem tailTrace_491002 : CollatzResearch.WordTrace tailWord_491002 prefixEnd_491002 224106691839105054326159 := by
  unfold tailWord_491002
  simp only [CollatzResearch.WordTrace]
  refine ⟨4477078541797771327638815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11938876111460723540370173 4477078541797771327638815)
  ·
    refine ⟨6715617812696656991458223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4477078541797771327638815 6715617812696656991458223)
    ·
      refine ⟨10073426719044985487187335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6715617812696656991458223 10073426719044985487187335)
      ·
        refine ⟨15110140078567478230781003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10073426719044985487187335 15110140078567478230781003)
        ·
          refine ⟨22665210117851217346171505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15110140078567478230781003 22665210117851217346171505)
          ·
            refine ⟨16998907588388413009628629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22665210117851217346171505 16998907588388413009628629)
            ·
              refine ⟨398411896602853429913171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 16998907588388413009628629 398411896602853429913171)
              ·
                refine ⟨597617844904280144869757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 398411896602853429913171 597617844904280144869757)
                ·
                  refine ⟨224106691839105054326159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 597617844904280144869757 224106691839105054326159)
                  ·
                    rfl

theorem cell20_491002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 7, 1, 3].length) (baseStart_491002 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_491002 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_491002 prefixEnd_491002 := by exact prefixLift 491002
  have htrace : WordTrace (prefixWord ++ tailWord_491002) baseStart_491002 baseEnd_491002 := by
    simpa [prefixWord, tailWord_491002, baseEnd_491002] using wordTrace_append hprefix tailTrace_491002
  have hstable : (prefixWord ++ tailWord_491002).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491002).length < 2 ^ (prefixWord ++ tailWord_491002).sum := by decide
  have hdescent : baseEnd_491002 < baseStart_491002 := by decide
  rcases family_descends (prefixWord ++ tailWord_491002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491012 : List Nat := [2, 3, 2, 3, 2, 2, 2, 4]
def baseStart_491012 : Nat := 118140960795 + 491012 * 2 ^ 59
def prefixEnd_491012 : Nat := 4983230072969 + 3 ^ 40 * 491012 * 2
def baseEnd_491012 : Nat := 74703752037196487997595

theorem tailTrace_491012 : CollatzResearch.WordTrace tailWord_491012 prefixEnd_491012 74703752037196487997595 := by
  unfold tailWord_491012
  simp only [CollatzResearch.WordTrace]
  refine ⟨8954339448577428509209645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11939119264769904678946193 8954339448577428509209645)
  ·
    refine ⟨3357877293216535690953617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8954339448577428509209645 3357877293216535690953617)
    ·
      refine ⟨2518407969912401768215213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3357877293216535690953617 2518407969912401768215213)
      ·
        refine ⟨944402988717150663080705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2518407969912401768215213 944402988717150663080705)
        ·
          refine ⟨708302241537862997310529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 944402988717150663080705 708302241537862997310529)
          ·
            refine ⟨531226681153397247982897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 708302241537862997310529 531226681153397247982897)
            ·
              refine ⟨398420010865047935987173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 531226681153397247982897 398420010865047935987173)
              ·
                refine ⟨74703752037196487997595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 398420010865047935987173 74703752037196487997595)
                ·
                  rfl

theorem cell20_491012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 2, 4].length) (baseStart_491012 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_491012 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_491012 prefixEnd_491012 := by exact prefixLift 491012
  have htrace : WordTrace (prefixWord ++ tailWord_491012) baseStart_491012 baseEnd_491012 := by
    simpa [prefixWord, tailWord_491012, baseEnd_491012] using wordTrace_append hprefix tailTrace_491012
  have hstable : (prefixWord ++ tailWord_491012).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491012).length < 2 ^ (prefixWord ++ tailWord_491012).sum := by decide
  have hdescent : baseEnd_491012 < baseStart_491012 := by decide
  rcases family_descends (prefixWord ++ tailWord_491012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491016 : List Nat := [2, 1, 3, 2, 1, 1, 6, 4]
def baseStart_491016 : Nat := 118140960795 + 491016 * 2 ^ 59
def prefixEnd_491016 : Nat := 4983230072969 + 3 ^ 40 * 491016 * 2
def baseEnd_491016 : Nat := 74704360606861075953145

theorem tailTrace_491016 : CollatzResearch.WordTrace tailWord_491016 prefixEnd_491016 74704360606861075953145 := by
  unfold tailWord_491016
  simp only [CollatzResearch.WordTrace]
  refine ⟨8954412394570182850782451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11939216526093577134376601 8954412394570182850782451)
  ·
    refine ⟨13431618591855274276173677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8954412394570182850782451 13431618591855274276173677)
    ·
      refine ⟨5036856971945727853565129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13431618591855274276173677 5036856971945727853565129)
      ·
        refine ⟨3777642728959295890173847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5036856971945727853565129 3777642728959295890173847)
        ·
          refine ⟨5666464093438943835260771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3777642728959295890173847 5666464093438943835260771)
          ·
            refine ⟨8499696140158415752891157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5666464093438943835260771 8499696140158415752891157)
            ·
              refine ⟨398423256569925738416773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 8499696140158415752891157 398423256569925738416773)
              ·
                refine ⟨74704360606861075953145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 398423256569925738416773 74704360606861075953145)
                ·
                  rfl

theorem cell20_491016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 6, 4].length) (baseStart_491016 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_491016 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_491016 prefixEnd_491016 := by exact prefixLift 491016
  have htrace : WordTrace (prefixWord ++ tailWord_491016) baseStart_491016 baseEnd_491016 := by
    simpa [prefixWord, tailWord_491016, baseEnd_491016] using wordTrace_append hprefix tailTrace_491016
  have hstable : (prefixWord ++ tailWord_491016).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491016).length < 2 ^ (prefixWord ++ tailWord_491016).sum := by decide
  have hdescent : baseEnd_491016 < baseStart_491016 := by decide
  rcases family_descends (prefixWord ++ tailWord_491016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491022 : List Nat := [4, 1, 1, 2, 5, 1, 1, 3, 2]
def baseStart_491022 : Nat := 118140960795 + 491022 * 2 ^ 59
def prefixEnd_491022 : Nat := 4983230072969 + 3 ^ 40 * 491022 * 2
def baseEnd_491022 : Nat := 224115820384073873659411

theorem tailTrace_491022 : CollatzResearch.WordTrace tailWord_491022 prefixEnd_491022 224115820384073873659411 := by
  unfold tailWord_491022
  simp only [CollatzResearch.WordTrace]
  refine ⟨2238630453389828590785415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11939362418079085817522213 2238630453389828590785415)
  ·
    refine ⟨3357945680084742886178123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2238630453389828590785415 3357945680084742886178123)
    ·
      refine ⟨5036918520127114329267185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3357945680084742886178123 5036918520127114329267185)
      ·
        refine ⟨3777688890095335746950389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5036918520127114329267185 3777688890095335746950389)
        ·
          refine ⟨354158333446437726276599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3777688890095335746950389 354158333446437726276599)
          ·
            refine ⟨531237500169656589414899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 354158333446437726276599 531237500169656589414899)
            ·
              refine ⟨796856250254484884122349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 531237500169656589414899 796856250254484884122349)
              ·
                refine ⟨298821093845431831545881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 796856250254484884122349 298821093845431831545881)
                ·
                  refine ⟨224115820384073873659411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 298821093845431831545881 224115820384073873659411)
                  ·
                    rfl

theorem cell20_491022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 1, 3, 2].length) (baseStart_491022 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_491022 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_491022 prefixEnd_491022 := by exact prefixLift 491022
  have htrace : WordTrace (prefixWord ++ tailWord_491022) baseStart_491022 baseEnd_491022 := by
    simpa [prefixWord, tailWord_491022, baseEnd_491022] using wordTrace_append hprefix tailTrace_491022
  have hstable : (prefixWord ++ tailWord_491022).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491022).length < 2 ^ (prefixWord ++ tailWord_491022).sum := by decide
  have hdescent : baseEnd_491022 < baseStart_491022 := by decide
  rcases family_descends (prefixWord ++ tailWord_491022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491043 : List Nat := [1, 1, 1, 4, 5, 1, 3, 2, 2]
def baseStart_491043 : Nat := 118140960795 + 491043 * 2 ^ 59
def prefixEnd_491043 : Nat := 4983230072969 + 3 ^ 40 * 491043 * 2
def baseEnd_491043 : Nat := 224125405356291133959325

theorem tailTrace_491043 : CollatzResearch.WordTrace tailWord_491043 prefixEnd_491043 224125405356291133959325 := by
  unfold tailWord_491043
  simp only [CollatzResearch.WordTrace]
  refine ⟨17909809560042549312797783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11939873040028366208531855 17909809560042549312797783)
  ·
    refine ⟨26864714340063823969196675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17909809560042549312797783 26864714340063823969196675)
    ·
      refine ⟨40297071510095735953795013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26864714340063823969196675 40297071510095735953795013)
      ·
        refine ⟨7555700908142950491336565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40297071510095735953795013 7555700908142950491336565)
        ·
          refine ⟨708346960138401608562803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7555700908142950491336565 708346960138401608562803)
          ·
            refine ⟨1062520440207602412844205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 708346960138401608562803 1062520440207602412844205)
            ·
              refine ⟨398445165077850904816577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1062520440207602412844205 398445165077850904816577)
              ·
                refine ⟨298833873808388178612433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 398445165077850904816577 298833873808388178612433)
                ·
                  refine ⟨224125405356291133959325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 298833873808388178612433 224125405356291133959325)
                  ·
                    rfl

theorem cell20_491043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 3, 2, 2].length) (baseStart_491043 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_491043 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_491043 prefixEnd_491043 := by exact prefixLift 491043
  have htrace : WordTrace (prefixWord ++ tailWord_491043) baseStart_491043 baseEnd_491043 := by
    simpa [prefixWord, tailWord_491043, baseEnd_491043] using wordTrace_append hprefix tailTrace_491043
  have hstable : (prefixWord ++ tailWord_491043).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491043).length < 2 ^ (prefixWord ++ tailWord_491043).sum := by decide
  have hdescent : baseEnd_491043 < baseStart_491043 := by decide
  rcases family_descends (prefixWord ++ tailWord_491043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491054 : List Nat := [4, 1, 3, 1, 2, 1, 1, 7]
def baseStart_491054 : Nat := 118140960795 + 491054 * 2 ^ 59
def prefixEnd_491054 : Nat := 4983230072969 + 3 ^ 40 * 491054 * 2
def baseEnd_491054 : Nat := 74710142018674661530871

theorem tailTrace_491054 : CollatzResearch.WordTrace tailWord_491054 prefixEnd_491054 74710142018674661530871 := by
  unfold tailWord_491054
  simp only [CollatzResearch.WordTrace]
  refine ⟨2238776345375337273931027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11940140508668465460965477 2238776345375337273931027)
  ·
    refine ⟨3358164518063005910896541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2238776345375337273931027 3358164518063005910896541)
    ·
      refine ⟨1259311694273627216586203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3358164518063005910896541 1259311694273627216586203)
      ·
        refine ⟨1888967541410440824879305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1259311694273627216586203 1888967541410440824879305)
        ·
          refine ⟨1416725656057830618659479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1888967541410440824879305 1416725656057830618659479)
          ·
            refine ⟨2125088484086745927989219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1416725656057830618659479 2125088484086745927989219)
            ·
              refine ⟨3187632726130118891983829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2125088484086745927989219 3187632726130118891983829)
              ·
                refine ⟨74710142018674661530871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3187632726130118891983829 74710142018674661530871)
                ·
                  rfl

theorem cell20_491054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 7].length) (baseStart_491054 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_491054 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_491054 prefixEnd_491054 := by exact prefixLift 491054
  have htrace : WordTrace (prefixWord ++ tailWord_491054) baseStart_491054 baseEnd_491054 := by
    simpa [prefixWord, tailWord_491054, baseEnd_491054] using wordTrace_append hprefix tailTrace_491054
  have hstable : (prefixWord ++ tailWord_491054).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491054).length < 2 ^ (prefixWord ++ tailWord_491054).sum := by decide
  have hdescent : baseEnd_491054 < baseStart_491054 := by decide
  rcases family_descends (prefixWord ++ tailWord_491054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491094 : List Nat := [5, 2, 2, 2, 1, 2, 2, 2, 2]
def baseStart_491094 : Nat := 118140960795 + 491094 * 2 ^ 59
def prefixEnd_491094 : Nat := 4983230072969 + 3 ^ 40 * 491094 * 2
def baseEnd_491094 : Nat := 224148683145961623259117

theorem tailTrace_491094 : CollatzResearch.WordTrace tailWord_491094 prefixEnd_491094 224148683145961623259117 := by
  unfold tailWord_491094
  simp only [CollatzResearch.WordTrace]
  refine ⟨1119479355178611563931521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11941113121905190015269557 1119479355178611563931521)
  ·
    refine ⟨839609516383958672948641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1119479355178611563931521 839609516383958672948641)
    ·
      refine ⟨629707137287969004711481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 839609516383958672948641 629707137287969004711481)
      ·
        refine ⟨472280352965976753533611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 629707137287969004711481 472280352965976753533611)
        ·
          refine ⟨708420529448965130300417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 472280352965976753533611 708420529448965130300417)
          ·
            refine ⟨531315397086723847725313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 708420529448965130300417 531315397086723847725313)
            ·
              refine ⟨398486547815042885793985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 531315397086723847725313 398486547815042885793985)
              ·
                refine ⟨298864910861282164345489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 398486547815042885793985 298864910861282164345489)
                ·
                  refine ⟨224148683145961623259117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 298864910861282164345489 224148683145961623259117)
                  ·
                    rfl

theorem cell20_491094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 2, 2, 2].length) (baseStart_491094 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_491094 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_491094 prefixEnd_491094 := by exact prefixLift 491094
  have htrace : WordTrace (prefixWord ++ tailWord_491094) baseStart_491094 baseEnd_491094 := by
    simpa [prefixWord, tailWord_491094, baseEnd_491094] using wordTrace_append hprefix tailTrace_491094
  have hstable : (prefixWord ++ tailWord_491094).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491094).length < 2 ^ (prefixWord ++ tailWord_491094).sum := by decide
  have hdescent : baseEnd_491094 < baseStart_491094 := by decide
  rcases family_descends (prefixWord ++ tailWord_491094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491113 : List Nat := [1, 2, 1, 1, 1, 4, 5, 5]
def baseStart_491113 : Nat := 118140960795 + 491113 * 2 ^ 59
def prefixEnd_491113 : Nat := 4983230072969 + 3 ^ 40 * 491113 * 2
def baseEnd_491113 : Nat := 74719118421227333875235

theorem tailTrace_491113 : CollatzResearch.WordTrace tailWord_491113 prefixEnd_491113 74719118421227333875235 := by
  unfold tailWord_491113
  simp only [CollatzResearch.WordTrace]
  refine ⟨17912362669788951267845993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11941575113192634178563995 17912362669788951267845993)
  ·
    refine ⟨13434272002341713450884495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17912362669788951267845993 13434272002341713450884495)
    ·
      refine ⟨20151408003512570176326743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13434272002341713450884495 20151408003512570176326743)
      ·
        refine ⟨30227112005268855264490115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20151408003512570176326743 30227112005268855264490115)
        ·
          refine ⟨45340668007903282896735173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30227112005268855264490115 45340668007903282896735173)
          ·
            refine ⟨8501375251481865543137845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45340668007903282896735173 8501375251481865543137845)
            ·
              refine ⟨797003929826424894669173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8501375251481865543137845 797003929826424894669173)
              ·
                refine ⟨74719118421227333875235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 797003929826424894669173 74719118421227333875235)
                ·
                  rfl

theorem cell20_491113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 5, 5].length) (baseStart_491113 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_491113 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_491113 prefixEnd_491113 := by exact prefixLift 491113
  have htrace : WordTrace (prefixWord ++ tailWord_491113) baseStart_491113 baseEnd_491113 := by
    simpa [prefixWord, tailWord_491113, baseEnd_491113] using wordTrace_append hprefix tailTrace_491113
  have hstable : (prefixWord ++ tailWord_491113).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491113).length < 2 ^ (prefixWord ++ tailWord_491113).sum := by decide
  have hdescent : baseEnd_491113 < baseStart_491113 := by decide
  rcases family_descends (prefixWord ++ tailWord_491113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491154 : List Nat := [3, 2, 3, 1, 3, 1, 1, 1, 5]
def baseStart_491154 : Nat := 118140960795 + 491154 * 2 ^ 59
def prefixEnd_491154 : Nat := 4983230072969 + 3 ^ 40 * 491154 * 2
def baseEnd_491154 : Nat := 224176068780868081258871

theorem tailTrace_491154 : CollatzResearch.WordTrace tailWord_491154 prefixEnd_491154 224176068780868081258871 := by
  unfold tailWord_491154
  simp only [CollatzResearch.WordTrace]
  refine ⟨4478464515660103817522129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11942572041760276846725677 4478464515660103817522129)
  ·
    refine ⟨3358848386745077863141597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4478464515660103817522129 3358848386745077863141597)
    ·
      refine ⟨1259568145029404198678099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3358848386745077863141597 1259568145029404198678099)
      ·
        refine ⟨1889352217544106298017149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1259568145029404198678099 1889352217544106298017149)
        ·
          refine ⟨708507081579039861756431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1889352217544106298017149 708507081579039861756431)
          ·
            refine ⟨1062760622368559792634647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 708507081579039861756431 1062760622368559792634647)
            ·
              refine ⟨1594140933552839688951971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1062760622368559792634647 1594140933552839688951971)
              ·
                refine ⟨2391211400329259533427957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1594140933552839688951971 2391211400329259533427957)
                ·
                  refine ⟨224176068780868081258871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2391211400329259533427957 224176068780868081258871)
                  ·
                    rfl

theorem cell20_491154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 1, 5].length) (baseStart_491154 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_491154 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_491154 prefixEnd_491154 := by exact prefixLift 491154
  have htrace : WordTrace (prefixWord ++ tailWord_491154) baseStart_491154 baseEnd_491154 := by
    simpa [prefixWord, tailWord_491154, baseEnd_491154] using wordTrace_append hprefix tailTrace_491154
  have hstable : (prefixWord ++ tailWord_491154).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491154).length < 2 ^ (prefixWord ++ tailWord_491154).sum := by decide
  have hdescent : baseEnd_491154 < baseStart_491154 := by decide
  rcases family_descends (prefixWord ++ tailWord_491154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491222 : List Nat := [5, 2, 1, 3, 2, 1, 2, 1, 3]
def baseStart_491222 : Nat := 118140960795 + 491222 * 2 ^ 59
def prefixEnd_491222 : Nat := 4983230072969 + 3 ^ 40 * 491222 * 2
def baseEnd_491222 : Nat := 224207105833762066991927

theorem tailTrace_491222 : CollatzResearch.WordTrace tailWord_491222 prefixEnd_491222 224207105833762066991927 := by
  unfold tailWord_491222
  simp only [CollatzResearch.WordTrace]
  refine ⟨1119771139149628930222745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11944225484262708589042613 1119771139149628930222745)
  ·
    refine ⟨839828354362221697667059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1119771139149628930222745 839828354362221697667059)
    ·
      refine ⟨1259742531543332546500589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 839828354362221697667059 1259742531543332546500589)
      ·
        refine ⟨472403449328749704937721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1259742531543332546500589 472403449328749704937721)
        ·
          refine ⟨354302586996562278703291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 472403449328749704937721 354302586996562278703291)
          ·
            refine ⟨531453880494843418054937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 354302586996562278703291 531453880494843418054937)
            ·
              refine ⟨398590410371132563541203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 531453880494843418054937 398590410371132563541203)
              ·
                refine ⟨597885615556698845311805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 398590410371132563541203 597885615556698845311805)
                ·
                  refine ⟨224207105833762066991927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 597885615556698845311805 224207105833762066991927)
                  ·
                    rfl

theorem cell20_491222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 2, 1, 3].length) (baseStart_491222 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_491222 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_491222 prefixEnd_491222 := by exact prefixLift 491222
  have htrace : WordTrace (prefixWord ++ tailWord_491222) baseStart_491222 baseEnd_491222 := by
    simpa [prefixWord, tailWord_491222, baseEnd_491222] using wordTrace_append hprefix tailTrace_491222
  have hstable : (prefixWord ++ tailWord_491222).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491222).length < 2 ^ (prefixWord ++ tailWord_491222).sum := by decide
  have hdescent : baseEnd_491222 < baseStart_491222 := by decide
  rcases family_descends (prefixWord ++ tailWord_491222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491241 : List Nat := [1, 2, 1, 1, 1, 2, 3, 3, 6]
def baseStart_491241 : Nat := 118140960795 + 491241 * 2 ^ 59
def prefixEnd_491241 : Nat := 4983230072969 + 3 ^ 40 * 491241 * 2
def baseEnd_491241 : Nat := 224215777951482445358515

theorem tailTrace_491241 : CollatzResearch.WordTrace tailWord_491241 prefixEnd_491241 224215777951482445358515 := by
  unfold tailWord_491241
  simp only [CollatzResearch.WordTrace]
  refine ⟨17917031213325229128505577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11944687475550152752337051 17917031213325229128505577)
  ·
    refine ⟨13437773409993921846379183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17917031213325229128505577 13437773409993921846379183)
    ·
      refine ⟨20156660114990882769568775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13437773409993921846379183 20156660114990882769568775)
      ·
        refine ⟨30234990172486324154353163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20156660114990882769568775 30234990172486324154353163)
        ·
          refine ⟨45352485258729486231529745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30234990172486324154353163 45352485258729486231529745)
          ·
            refine ⟨34014363944047114673647309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45352485258729486231529745 34014363944047114673647309)
            ·
              refine ⟨12755386479017668002617741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34014363944047114673647309 12755386479017668002617741)
              ·
                refine ⟨4783269929631625500981653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12755386479017668002617741 4783269929631625500981653)
                ·
                  refine ⟨224215777951482445358515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4783269929631625500981653 224215777951482445358515)
                  ·
                    rfl

theorem cell20_491241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 3, 6].length) (baseStart_491241 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_491241 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_491241 prefixEnd_491241 := by exact prefixLift 491241
  have htrace : WordTrace (prefixWord ++ tailWord_491241) baseStart_491241 baseEnd_491241 := by
    simpa [prefixWord, tailWord_491241, baseEnd_491241] using wordTrace_append hprefix tailTrace_491241
  have hstable : (prefixWord ++ tailWord_491241).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491241).length < 2 ^ (prefixWord ++ tailWord_491241).sum := by decide
  have hdescent : baseEnd_491241 < baseStart_491241 := by decide
  rcases family_descends (prefixWord ++ tailWord_491241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491268 : List Nat := [2, 3, 2, 2, 1, 3, 2, 2, 3]
def baseStart_491268 : Nat := 118140960795 + 491268 * 2 ^ 59
def prefixEnd_491268 : Nat := 4983230072969 + 3 ^ 40 * 491268 * 2
def baseEnd_491268 : Nat := 224228101487190351458405

theorem tailTrace_491268 : CollatzResearch.WordTrace tailWord_491268 prefixEnd_491268 224228101487190351458405 := by
  unfold tailWord_491268
  simp only [CollatzResearch.WordTrace]
  refine ⟨8959007992113706369869229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11945343989484941826492305 8959007992113706369869229)
  ·
    refine ⟨3359627997042639888700961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8959007992113706369869229 3359627997042639888700961)
    ·
      refine ⟨2519720997781979916525721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3359627997042639888700961 2519720997781979916525721)
      ·
        refine ⟨1889790748336484937394291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2519720997781979916525721 1889790748336484937394291)
        ·
          refine ⟨2834686122504727406091437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1889790748336484937394291 2834686122504727406091437)
          ·
            refine ⟨1063007295939272777284289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2834686122504727406091437 1063007295939272777284289)
            ·
              refine ⟨797255471954454582963217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1063007295939272777284289 797255471954454582963217)
              ·
                refine ⟨597941603965840937222413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 797255471954454582963217 597941603965840937222413)
                ·
                  refine ⟨224228101487190351458405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 597941603965840937222413 224228101487190351458405)
                  ·
                    rfl

theorem cell20_491268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 2, 2, 3].length) (baseStart_491268 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_491268 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_491268 prefixEnd_491268 := by exact prefixLift 491268
  have htrace : WordTrace (prefixWord ++ tailWord_491268) baseStart_491268 baseEnd_491268 := by
    simpa [prefixWord, tailWord_491268, baseEnd_491268] using wordTrace_append hprefix tailTrace_491268
  have hstable : (prefixWord ++ tailWord_491268).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491268).length < 2 ^ (prefixWord ++ tailWord_491268).sum := by decide
  have hdescent : baseEnd_491268 < baseStart_491268 := by decide
  rcases family_descends (prefixWord ++ tailWord_491268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491296 : List Nat := [2, 1, 1, 5, 1, 1, 3, 2, 4]
def baseStart_491296 : Nat := 118140960795 + 491296 * 2 ^ 59
def prefixEnd_491296 : Nat := 4983230072969 + 3 ^ 40 * 491296 * 2
def baseEnd_491296 : Nat := 224240881450146698524957

theorem tailTrace_491296 : CollatzResearch.WordTrace tailWord_491296 prefixEnd_491296 224240881450146698524957 := by
  unfold tailWord_491296
  simp only [CollatzResearch.WordTrace]
  refine ⟨8959518614062986760878871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11946024818750649014505161 8959518614062986760878871)
  ·
    refine ⟨13439277921094480141318307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8959518614062986760878871 13439277921094480141318307)
    ·
      refine ⟨20158916881641720211977461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13439277921094480141318307 20158916881641720211977461)
      ·
        refine ⟨1889898457653911269872887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20158916881641720211977461 1889898457653911269872887)
        ·
          refine ⟨2834847686480866904809331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1889898457653911269872887 2834847686480866904809331)
          ·
            refine ⟨4252271529721300357213997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2834847686480866904809331 4252271529721300357213997)
            ·
              refine ⟨1594601823645487633955249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4252271529721300357213997 1594601823645487633955249)
              ·
                refine ⟨1195951367734115725466437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1594601823645487633955249 1195951367734115725466437)
                ·
                  refine ⟨224240881450146698524957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1195951367734115725466437 224240881450146698524957)
                  ·
                    rfl

theorem cell20_491296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 2, 4].length) (baseStart_491296 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_491296 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_491296 prefixEnd_491296 := by exact prefixLift 491296
  have htrace : WordTrace (prefixWord ++ tailWord_491296) baseStart_491296 baseEnd_491296 := by
    simpa [prefixWord, tailWord_491296, baseEnd_491296] using wordTrace_append hprefix tailTrace_491296
  have hstable : (prefixWord ++ tailWord_491296).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491296).length < 2 ^ (prefixWord ++ tailWord_491296).sum := by decide
  have hdescent : baseEnd_491296 < baseStart_491296 := by decide
  rcases family_descends (prefixWord ++ tailWord_491296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491313 : List Nat := [1, 2, 2, 3, 2, 2, 1, 5, 2]
def baseStart_491313 : Nat := 118140960795 + 491313 * 2 ^ 59
def prefixEnd_491313 : Nat := 4983230072969 + 3 ^ 40 * 491313 * 2
def baseEnd_491313 : Nat := 224248640713370194958221

theorem tailTrace_491313 : CollatzResearch.WordTrace tailWord_491313 prefixEnd_491313 224248640713370194958221 := by
  unfold tailWord_491313
  simp only [CollatzResearch.WordTrace]
  refine ⟨17919657269064385425126593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11946438179376256950084395 17919657269064385425126593)
  ·
    refine ⟨13439742951798289068844945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17919657269064385425126593 13439742951798289068844945)
    ·
      refine ⟨10079807213848716801633709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13439742951798289068844945 10079807213848716801633709)
      ·
        refine ⟨3779927705193268800612641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10079807213848716801633709 3779927705193268800612641)
        ·
          refine ⟨2834945778894951600459481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3779927705193268800612641 2834945778894951600459481)
          ·
            refine ⟨2126209334171213700344611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2834945778894951600459481 2126209334171213700344611)
            ·
              refine ⟨3189314001256820550516917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2126209334171213700344611 3189314001256820550516917)
              ·
                refine ⟨298998187617826926610961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3189314001256820550516917 298998187617826926610961)
                ·
                  refine ⟨224248640713370194958221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 298998187617826926610961 224248640713370194958221)
                  ·
                    rfl

theorem cell20_491313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 5, 2].length) (baseStart_491313 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_491313 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_491313 prefixEnd_491313 := by exact prefixLift 491313
  have htrace : WordTrace (prefixWord ++ tailWord_491313) baseStart_491313 baseEnd_491313 := by
    simpa [prefixWord, tailWord_491313, baseEnd_491313] using wordTrace_append hprefix tailTrace_491313
  have hstable : (prefixWord ++ tailWord_491313).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491313).length < 2 ^ (prefixWord ++ tailWord_491313).sum := by decide
  have hdescent : baseEnd_491313 < baseStart_491313 := by decide
  rcases family_descends (prefixWord ++ tailWord_491313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491327 : List Nat := [1, 1, 2, 2, 6, 1, 1, 1, 5]
def baseStart_491327 : Nat := 118140960795 + 491327 * 2 ^ 59
def prefixEnd_491327 : Nat := 4983230072969 + 3 ^ 40 * 491327 * 2
def baseEnd_491327 : Nat := 224255030694848368491497

theorem tailTrace_491327 : CollatzResearch.WordTrace tailWord_491327 prefixEnd_491327 224255030694848368491497 := by
  unfold tailWord_491327
  simp only [CollatzResearch.WordTrace]
  refine ⟨17920167891013665816136235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11946778594009110544090823 17920167891013665816136235)
  ·
    refine ⟨26880251836520498724204353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17920167891013665816136235 26880251836520498724204353)
    ·
      refine ⟨20160188877390374043153265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26880251836520498724204353 20160188877390374043153265)
      ·
        refine ⟨15120141658042780532364949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20160188877390374043153265 15120141658042780532364949)
        ·
          refine ⟨708756640220755337454607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 15120141658042780532364949 708756640220755337454607)
          ·
            refine ⟨1063134960331133006181911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 708756640220755337454607 1063134960331133006181911)
            ·
              refine ⟨1594702440496699509272867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1063134960331133006181911 1594702440496699509272867)
              ·
                refine ⟨2392053660745049263909301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1594702440496699509272867 2392053660745049263909301)
                ·
                  refine ⟨224255030694848368491497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2392053660745049263909301 224255030694848368491497)
                  ·
                    rfl

theorem cell20_491327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 1, 5].length) (baseStart_491327 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_491327 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_491327 prefixEnd_491327 := by exact prefixLift 491327
  have htrace : WordTrace (prefixWord ++ tailWord_491327) baseStart_491327 baseEnd_491327 := by
    simpa [prefixWord, tailWord_491327, baseEnd_491327] using wordTrace_append hprefix tailTrace_491327
  have hstable : (prefixWord ++ tailWord_491327).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491327).length < 2 ^ (prefixWord ++ tailWord_491327).sum := by decide
  have hdescent : baseEnd_491327 < baseStart_491327 := by decide
  rcases family_descends (prefixWord ++ tailWord_491327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491386 : List Nat := [3, 1, 1, 1, 1, 1, 6, 1, 5]
def baseStart_491386 : Nat := 118140960795 + 491386 * 2 ^ 59
def prefixEnd_491386 : Nat := 4983230072969 + 3 ^ 40 * 491386 * 2
def baseEnd_491386 : Nat := 224281959902506385524589

theorem tailTrace_491386 : CollatzResearch.WordTrace tailWord_491386 prefixEnd_491386 224281959902506385524589 := by
  unfold tailWord_491386
  simp only [CollatzResearch.WordTrace]
  refine ⟨4480579949449979723133503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11948213198533279261689341 4480579949449979723133503)
  ·
    refine ⟨6720869924174969584700255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4480579949449979723133503 6720869924174969584700255)
    ·
      refine ⟨10081304886262454377050383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6720869924174969584700255 10081304886262454377050383)
      ·
        refine ⟨15121957329393681565575575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10081304886262454377050383 15121957329393681565575575)
        ·
          refine ⟨22682935994090522348363363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15121957329393681565575575 22682935994090522348363363)
          ·
            refine ⟨34024403991135783522545045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22682935994090522348363363 34024403991135783522545045)
            ·
              refine ⟨1594893937084489852619299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 34024403991135783522545045 1594893937084489852619299)
              ·
                refine ⟨2392340905626734778928949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1594893937084489852619299 2392340905626734778928949)
                ·
                  refine ⟨224281959902506385524589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2392340905626734778928949 224281959902506385524589)
                  ·
                    rfl

theorem cell20_491386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 1, 5].length) (baseStart_491386 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_491386 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_491386 prefixEnd_491386 := by exact prefixLift 491386
  have htrace : WordTrace (prefixWord ++ tailWord_491386) baseStart_491386 baseEnd_491386 := by
    simpa [prefixWord, tailWord_491386, baseEnd_491386] using wordTrace_append hprefix tailTrace_491386
  have hstable : (prefixWord ++ tailWord_491386).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491386).length < 2 ^ (prefixWord ++ tailWord_491386).sum := by decide
  have hdescent : baseEnd_491386 < baseStart_491386 := by decide
  rcases family_descends (prefixWord ++ tailWord_491386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491399 : List Nat := [1, 1, 4, 2, 4, 2, 2, 1, 3]
def baseStart_491399 : Nat := 118140960795 + 491399 * 2 ^ 59
def prefixEnd_491399 : Nat := 4983230072969 + 3 ^ 40 * 491399 * 2
def baseEnd_491399 : Nat := 224287893456736118091203

theorem tailTrace_491399 : CollatzResearch.WordTrace tailWord_491399 prefixEnd_491399 224287893456736118091203 := by
  unfold tailWord_491399
  simp only [CollatzResearch.WordTrace]
  refine ⟨17922793946752822112757251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11948529297835214741838167 17922793946752822112757251)
  ·
    refine ⟨26884190920129233169135877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17922793946752822112757251 26884190920129233169135877)
    ·
      refine ⟨5040785797524231219212977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26884190920129233169135877 5040785797524231219212977)
      ·
        refine ⟨3780589348143173414409733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5040785797524231219212977 3780589348143173414409733)
        ·
          refine ⟨708860502776845015201825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3780589348143173414409733 708860502776845015201825)
          ·
            refine ⟨531645377082633761401369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 708860502776845015201825 531645377082633761401369)
            ·
              refine ⟨398734032811975321051027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 531645377082633761401369 398734032811975321051027)
              ·
                refine ⟨598101049217962981576541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 398734032811975321051027 598101049217962981576541)
                ·
                  refine ⟨224287893456736118091203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 598101049217962981576541 224287893456736118091203)
                  ·
                    rfl

theorem cell20_491399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 2, 1, 3].length) (baseStart_491399 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_491399 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_491399 prefixEnd_491399 := by exact prefixLift 491399
  have htrace : WordTrace (prefixWord ++ tailWord_491399) baseStart_491399 baseEnd_491399 := by
    simpa [prefixWord, tailWord_491399, baseEnd_491399] using wordTrace_append hprefix tailTrace_491399
  have hstable : (prefixWord ++ tailWord_491399).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491399).length < 2 ^ (prefixWord ++ tailWord_491399).sum := by decide
  have hdescent : baseEnd_491399 < baseStart_491399 := by decide
  rcases family_descends (prefixWord ++ tailWord_491399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491441 : List Nat := [1, 2, 2, 4, 2, 1, 1, 4, 3]
def baseStart_491441 : Nat := 118140960795 + 491441 * 2 ^ 59
def prefixEnd_491441 : Nat := 4983230072969 + 3 ^ 40 * 491441 * 2
def baseEnd_491441 : Nat := 224307063401170638691031

theorem tailTrace_491441 : CollatzResearch.WordTrace tailWord_491441 prefixEnd_491441 224307063401170638691031 := by
  unfold tailWord_491441
  simp only [CollatzResearch.WordTrace]
  refine ⟨17924325812600663285786177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11949550541733775523857451 17924325812600663285786177)
  ·
    refine ⟨13443244359450497464339633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17924325812600663285786177 13443244359450497464339633)
    ·
      refine ⟨10082433269587873098254725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13443244359450497464339633 10082433269587873098254725)
      ·
        refine ⟨1890456238047726205922761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10082433269587873098254725 1890456238047726205922761)
        ·
          refine ⟨1417842178535794654442071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1890456238047726205922761 1417842178535794654442071)
          ·
            refine ⟨2126763267803691981663107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1417842178535794654442071 2126763267803691981663107)
            ·
              refine ⟨3190144901705537972494661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2126763267803691981663107 3190144901705537972494661)
              ·
                refine ⟨598152169069788369842749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3190144901705537972494661 598152169069788369842749)
                ·
                  refine ⟨224307063401170638691031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 598152169069788369842749 224307063401170638691031)
                  ·
                    rfl

theorem cell20_491441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 4, 3].length) (baseStart_491441 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_491441 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_491441 prefixEnd_491441 := by exact prefixLift 491441
  have htrace : WordTrace (prefixWord ++ tailWord_491441) baseStart_491441 baseEnd_491441 := by
    simpa [prefixWord, tailWord_491441, baseEnd_491441] using wordTrace_append hprefix tailTrace_491441
  have hstable : (prefixWord ++ tailWord_491441).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491441).length < 2 ^ (prefixWord ++ tailWord_491441).sum := by decide
  have hdescent : baseEnd_491441 < baseStart_491441 := by decide
  rcases family_descends (prefixWord ++ tailWord_491441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491482 : List Nat := [3, 1, 1, 2, 5, 1, 2, 3, 2]
def baseStart_491482 : Nat := 118140960795 + 491482 * 2 ^ 59
def prefixEnd_491482 : Nat := 4983230072969 + 3 ^ 40 * 491482 * 2
def baseEnd_491482 : Nat := 224325776918356718324197

theorem tailTrace_491482 : CollatzResearch.WordTrace tailWord_491482 prefixEnd_491482 224325776918356718324197 := by
  unfold tailWord_491482
  simp only [CollatzResearch.WordTrace]
  refine ⟨4481455301363031822007175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11950547470301418192019133 4481455301363031822007175)
  ·
    refine ⟨6722182952044547733010763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4481455301363031822007175 6722182952044547733010763)
    ·
      refine ⟨10083274428066821599516145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6722182952044547733010763 10083274428066821599516145)
      ·
        refine ⟨7562455821050116199637109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10083274428066821599516145 7562455821050116199637109)
        ·
          refine ⟨708980233223448393715979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7562455821050116199637109 708980233223448393715979)
          ·
            refine ⟨1063470349835172590573969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 708980233223448393715979 1063470349835172590573969)
            ·
              refine ⟨797602762376379442930477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1063470349835172590573969 797602762376379442930477)
              ·
                refine ⟨299101035891142291098929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 797602762376379442930477 299101035891142291098929)
                ·
                  refine ⟨224325776918356718324197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 299101035891142291098929 224325776918356718324197)
                  ·
                    rfl

theorem cell20_491482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 2, 3, 2].length) (baseStart_491482 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_491482 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_491482 prefixEnd_491482 := by exact prefixLift 491482
  have htrace : WordTrace (prefixWord ++ tailWord_491482) baseStart_491482 baseEnd_491482 := by
    simpa [prefixWord, tailWord_491482, baseEnd_491482] using wordTrace_append hprefix tailTrace_491482
  have hstable : (prefixWord ++ tailWord_491482).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491482).length < 2 ^ (prefixWord ++ tailWord_491482).sum := by decide
  have hdescent : baseEnd_491482 < baseStart_491482 := by decide
  rcases family_descends (prefixWord ++ tailWord_491482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491533 : List Nat := [1, 7, 1, 2, 1, 2, 1, 3, 2]
def baseStart_491533 : Nat := 118140960795 + 491533 * 2 ^ 59
def prefixEnd_491533 : Nat := 4983230072969 + 3 ^ 40 * 491533 * 2
def baseEnd_491533 : Nat := 224349054708027207623989

theorem tailTrace_491533 : CollatzResearch.WordTrace tailWord_491533 prefixEnd_491533 224349054708027207623989 := by
  unfold tailWord_491533
  simp only [CollatzResearch.WordTrace]
  refine ⟨17927681328267362998135253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11951787552178241998756835 17927681328267362998135253)
  ·
    refine ⟨420180031131266320268795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 17927681328267362998135253 420180031131266320268795)
    ·
      refine ⟨630270046696899480403193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 420180031131266320268795 630270046696899480403193)
      ·
        refine ⟨472702535022674610302395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 630270046696899480403193 472702535022674610302395)
        ·
          refine ⟨709053802534011915453593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 472702535022674610302395 709053802534011915453593)
          ·
            refine ⟨531790351900508936590195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 709053802534011915453593 531790351900508936590195)
            ·
              refine ⟨797685527850763404885293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 531790351900508936590195 797685527850763404885293)
              ·
                refine ⟨299132072944036276831985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 797685527850763404885293 299132072944036276831985)
                ·
                  refine ⟨224349054708027207623989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 299132072944036276831985 224349054708027207623989)
                  ·
                    rfl

theorem cell20_491533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 1, 3, 2].length) (baseStart_491533 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_491533 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_491533 prefixEnd_491533 := by exact prefixLift 491533
  have htrace : WordTrace (prefixWord ++ tailWord_491533) baseStart_491533 baseEnd_491533 := by
    simpa [prefixWord, tailWord_491533, baseEnd_491533] using wordTrace_append hprefix tailTrace_491533
  have hstable : (prefixWord ++ tailWord_491533).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491533).length < 2 ^ (prefixWord ++ tailWord_491533).sum := by decide
  have hdescent : baseEnd_491533 < baseStart_491533 := by decide
  rcases family_descends (prefixWord ++ tailWord_491533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491569 : List Nat := [1, 2, 2, 3, 1, 4, 2, 5]
def baseStart_491569 : Nat := 118140960795 + 491569 * 2 ^ 59
def prefixEnd_491569 : Nat := 4983230072969 + 3 ^ 40 * 491569 * 2
def baseEnd_491569 : Nat := 74788495362990360807947

theorem tailTrace_491569 : CollatzResearch.WordTrace tailWord_491569 prefixEnd_491569 74788495362990360807947 := by
  unfold tailWord_491569
  simp only [CollatzResearch.WordTrace]
  refine ⟨17928994356136941146445761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11952662904091294097630507 17928994356136941146445761)
  ·
    refine ⟨13446745767102705859834321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17928994356136941146445761 13446745767102705859834321)
    ·
      refine ⟨10085059325327029394875741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13446745767102705859834321 10085059325327029394875741)
      ·
        refine ⟨3781897246997636023078403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10085059325327029394875741 3781897246997636023078403)
        ·
          refine ⟨5672845870496454034617605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3781897246997636023078403 5672845870496454034617605)
          ·
            refine ⟨1063658600718085131490801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5672845870496454034617605 1063658600718085131490801)
            ·
              refine ⟨797743950538563848618101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1063658600718085131490801 797743950538563848618101)
              ·
                refine ⟨74788495362990360807947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 797743950538563848618101 74788495362990360807947)
                ·
                  rfl

theorem cell20_491569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 2, 5].length) (baseStart_491569 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_491569 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_491569 prefixEnd_491569 := by exact prefixLift 491569
  have htrace : WordTrace (prefixWord ++ tailWord_491569) baseStart_491569 baseEnd_491569 := by
    simpa [prefixWord, tailWord_491569, baseEnd_491569] using wordTrace_append hprefix tailTrace_491569
  have hstable : (prefixWord ++ tailWord_491569).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491569).length < 2 ^ (prefixWord ++ tailWord_491569).sum := by decide
  have hdescent : baseEnd_491569 < baseStart_491569 := by decide
  rcases family_descends (prefixWord ++ tailWord_491569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491583 : List Nat := [1, 1, 2, 2, 3, 1, 2, 4, 4]
def baseStart_491583 : Nat := 118140960795 + 491583 * 2 ^ 59
def prefixEnd_491583 : Nat := 4983230072969 + 3 ^ 40 * 491583 * 2
def baseEnd_491583 : Nat := 224371876070449255957117

theorem tailTrace_491583 : CollatzResearch.WordTrace tailWord_491583 prefixEnd_491583 224371876070449255957117 := by
  unfold tailWord_491583
  simp only [CollatzResearch.WordTrace]
  refine ⟨17929504978086221537455403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11953003318724147691636935 17929504978086221537455403)
  ·
    refine ⟨26894257467129332306183105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17929504978086221537455403 26894257467129332306183105)
    ·
      refine ⟨20170693100346999229637329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26894257467129332306183105 20170693100346999229637329)
      ·
        refine ⟨15128019825260249422227997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20170693100346999229637329 15128019825260249422227997)
        ·
          refine ⟨5673007434472593533335499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15128019825260249422227997 5673007434472593533335499)
          ·
            refine ⟨8509511151708890300003249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5673007434472593533335499 8509511151708890300003249)
            ·
              refine ⟨6382133363781667725002437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8509511151708890300003249 6382133363781667725002437)
              ·
                refine ⟨1196650005709062698437957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6382133363781667725002437 1196650005709062698437957)
                ·
                  refine ⟨224371876070449255957117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1196650005709062698437957 224371876070449255957117)
                  ·
                    rfl

theorem cell20_491583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 4, 4].length) (baseStart_491583 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_491583 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_491583 prefixEnd_491583 := by exact prefixLift 491583
  have htrace : WordTrace (prefixWord ++ tailWord_491583) baseStart_491583 baseEnd_491583 := by
    simpa [prefixWord, tailWord_491583, baseEnd_491583] using wordTrace_append hprefix tailTrace_491583
  have hstable : (prefixWord ++ tailWord_491583).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491583).length < 2 ^ (prefixWord ++ tailWord_491583).sum := by decide
  have hdescent : baseEnd_491583 < baseStart_491583 := by decide
  rcases family_descends (prefixWord ++ tailWord_491583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491613 : List Nat := [1, 4, 4, 1, 1, 1, 4, 2, 2]
def baseStart_491613 : Nat := 118140960795 + 491613 * 2 ^ 59
def prefixEnd_491613 : Nat := 4983230072969 + 3 ^ 40 * 491613 * 2
def baseEnd_491613 : Nat := 224385568887902484956995

theorem tailTrace_491613 : CollatzResearch.WordTrace tailWord_491613 prefixEnd_491613 224385568887902484956995 := by
  unfold tailWord_491613
  simp only [CollatzResearch.WordTrace]
  refine ⟨17930599167977536661047493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11953732778651691107364995 17930599167977536661047493)
  ·
    refine ⟨3361987343995788123946405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17930599167977536661047493 3361987343995788123946405)
    ·
      refine ⟨630372626999210273239951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3361987343995788123946405 630372626999210273239951)
      ·
        refine ⟨945558940498815409859927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 630372626999210273239951 945558940498815409859927)
        ·
          refine ⟨1418338410748223114789891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 945558940498815409859927 1418338410748223114789891)
          ·
            refine ⟨2127507616122334672184837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1418338410748223114789891 2127507616122334672184837)
            ·
              refine ⟨398907678022937751034657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2127507616122334672184837 398907678022937751034657)
              ·
                refine ⟨299180758517203313275993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 398907678022937751034657 299180758517203313275993)
                ·
                  refine ⟨224385568887902484956995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 299180758517203313275993 224385568887902484956995)
                  ·
                    rfl

theorem cell20_491613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 4, 2, 2].length) (baseStart_491613 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_491613 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_491613 prefixEnd_491613 := by exact prefixLift 491613
  have htrace : WordTrace (prefixWord ++ tailWord_491613) baseStart_491613 baseEnd_491613 := by
    simpa [prefixWord, tailWord_491613, baseEnd_491613] using wordTrace_append hprefix tailTrace_491613
  have hstable : (prefixWord ++ tailWord_491613).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491613).length < 2 ^ (prefixWord ++ tailWord_491613).sum := by decide
  have hdescent : baseEnd_491613 < baseStart_491613 := by decide
  rcases family_descends (prefixWord ++ tailWord_491613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491638 : List Nat := [5, 1, 1, 2, 1, 2, 1, 1, 6]
def baseStart_491638 : Nat := 118140960795 + 491638 * 2 ^ 59
def prefixEnd_491638 : Nat := 4983230072969 + 3 ^ 40 * 491638 * 2
def baseEnd_491638 : Nat := 224396979569113509123559

theorem tailTrace_491638 : CollatzResearch.WordTrace tailWord_491638 prefixEnd_491638 224396979569113509123559 := by
  unfold tailWord_491638
  simp only [CollatzResearch.WordTrace]
  refine ⟨1120719437055435370669223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11954340661924643953805045 1120719437055435370669223)
  ·
    refine ⟨1681079155583153056003835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1120719437055435370669223 1681079155583153056003835)
    ·
      refine ⟨2521618733374729584005753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1681079155583153056003835 2521618733374729584005753)
      ·
        refine ⟨1891214050031047188004315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2521618733374729584005753 1891214050031047188004315)
        ·
          refine ⟨2836821075046570782006473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1891214050031047188004315 2836821075046570782006473)
          ·
            refine ⟨2127615806284928086504855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2836821075046570782006473 2127615806284928086504855)
            ·
              refine ⟨3191423709427392129757283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2127615806284928086504855 3191423709427392129757283)
              ·
                refine ⟨4787135564141088194635925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3191423709427392129757283 4787135564141088194635925)
                ·
                  refine ⟨224396979569113509123559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4787135564141088194635925 224396979569113509123559)
                  ·
                    rfl

theorem cell20_491638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 1, 6].length) (baseStart_491638 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_491638 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_491638 prefixEnd_491638 := by exact prefixLift 491638
  have htrace : WordTrace (prefixWord ++ tailWord_491638) baseStart_491638 baseEnd_491638 := by
    simpa [prefixWord, tailWord_491638, baseEnd_491638] using wordTrace_append hprefix tailTrace_491638
  have hstable : (prefixWord ++ tailWord_491638).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491638).length < 2 ^ (prefixWord ++ tailWord_491638).sum := by decide
  have hdescent : baseEnd_491638 < baseStart_491638 := by decide
  rcases family_descends (prefixWord ++ tailWord_491638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491652 : List Nat := [2, 3, 2, 1, 2, 1, 2, 2, 5]
def baseStart_491652 : Nat := 118140960795 + 491652 * 2 ^ 59
def prefixEnd_491652 : Nat := 4983230072969 + 3 ^ 40 * 491652 * 2
def baseEnd_491652 : Nat := 224403369550591682656835

theorem tailTrace_491652 : CollatzResearch.WordTrace tailWord_491652 prefixEnd_491652 224403369550591682656835 := by
  unfold tailWord_491652
  simp only [CollatzResearch.WordTrace]
  refine ⟨8966010807418123160858605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11954681076557497547811473 8966010807418123160858605)
  ·
    refine ⟨3362254052781796185321977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8966010807418123160858605 3362254052781796185321977)
    ·
      refine ⟨2521690539586347138991483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3362254052781796185321977 2521690539586347138991483)
      ·
        refine ⟨3782535809379520708487225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2521690539586347138991483 3782535809379520708487225)
        ·
          refine ⟨2836901857034640531365419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3782535809379520708487225 2836901857034640531365419)
          ·
            refine ⟨4255352785551960797048129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2836901857034640531365419 4255352785551960797048129)
            ·
              refine ⟨3191514589163970597786097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4255352785551960797048129 3191514589163970597786097)
              ·
                refine ⟨2393635941872977948339573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3191514589163970597786097 2393635941872977948339573)
                ·
                  refine ⟨224403369550591682656835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2393635941872977948339573 224403369550591682656835)
                  ·
                    rfl

theorem cell20_491652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 2, 5].length) (baseStart_491652 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_491652 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_491652 prefixEnd_491652 := by exact prefixLift 491652
  have htrace : WordTrace (prefixWord ++ tailWord_491652) baseStart_491652 baseEnd_491652 := by
    simpa [prefixWord, tailWord_491652, baseEnd_491652] using wordTrace_append hprefix tailTrace_491652
  have hstable : (prefixWord ++ tailWord_491652).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491652).length < 2 ^ (prefixWord ++ tailWord_491652).sum := by decide
  have hdescent : baseEnd_491652 < baseStart_491652 := by decide
  rcases family_descends (prefixWord ++ tailWord_491652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491676 : List Nat := [2, 2, 3, 2, 1, 1, 4, 1, 4]
def baseStart_491676 : Nat := 118140960795 + 491676 * 2 ^ 59
def prefixEnd_491676 : Nat := 4983230072969 + 3 ^ 40 * 491676 * 2
def baseEnd_491676 : Nat := 224414323804554265856737

theorem tailTrace_491676 : CollatzResearch.WordTrace tailWord_491676 prefixEnd_491676 224414323804554265856737 := by
  unfold tailWord_491676
  simp only [CollatzResearch.WordTrace]
  refine ⟨8966448483374649210295441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11955264644499532280393921 8966448483374649210295441)
  ·
    refine ⟨6724836362530986907721581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8966448483374649210295441 6724836362530986907721581)
    ·
      refine ⟨2521813635949120090395593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6724836362530986907721581 2521813635949120090395593)
      ·
        refine ⟨1891360226961840067796695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2521813635949120090395593 1891360226961840067796695)
        ·
          refine ⟨2837040340442760101695043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1891360226961840067796695 2837040340442760101695043)
          ·
            refine ⟨4255560510664140152542565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2837040340442760101695043 4255560510664140152542565)
            ·
              refine ⟨797917595749526278601731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4255560510664140152542565 797917595749526278601731)
              ·
                refine ⟨1196876393624289417902597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 797917595749526278601731 1196876393624289417902597)
                ·
                  refine ⟨224414323804554265856737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1196876393624289417902597 224414323804554265856737)
                  ·
                    rfl

theorem cell20_491676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 4, 1, 4].length) (baseStart_491676 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_491676 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_491676 prefixEnd_491676 := by exact prefixLift 491676
  have htrace : WordTrace (prefixWord ++ tailWord_491676) baseStart_491676 baseEnd_491676 := by
    simpa [prefixWord, tailWord_491676, baseEnd_491676] using wordTrace_append hprefix tailTrace_491676
  have hstable : (prefixWord ++ tailWord_491676).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491676).length < 2 ^ (prefixWord ++ tailWord_491676).sum := by decide
  have hdescent : baseEnd_491676 < baseStart_491676 := by decide
  rcases family_descends (prefixWord ++ tailWord_491676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491704 : List Nat := [2, 1, 2, 1, 2, 1, 5, 6]
def baseStart_491704 : Nat := 118140960795 + 491704 * 2 ^ 59
def prefixEnd_491704 : Nat := 4983230072969 + 3 ^ 40 * 491704 * 2
def baseEnd_491704 : Nat := 74809034589170204307763

theorem tailTrace_491704 : CollatzResearch.WordTrace tailWord_491704 prefixEnd_491704 74809034589170204307763 := by
  unfold tailWord_491704
  simp only [CollatzResearch.WordTrace]
  refine ⟨8966959105323929601305083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11955945473765239468406777 8966959105323929601305083)
  ·
    refine ⟨13450438657985894401957625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8966959105323929601305083 13450438657985894401957625)
    ·
      refine ⟨10087828993489420801468219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13450438657985894401957625 10087828993489420801468219)
      ·
        refine ⟨15131743490234131202202329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10087828993489420801468219 15131743490234131202202329)
        ·
          refine ⟨11348807617675598401651747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15131743490234131202202329 11348807617675598401651747)
          ·
            refine ⟨17023211426513397602477621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11348807617675598401651747 17023211426513397602477621)
            ·
              refine ⟨1595926071235631025232277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17023211426513397602477621 1595926071235631025232277)
              ·
                refine ⟨74809034589170204307763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1595926071235631025232277 74809034589170204307763)
                ·
                  rfl

theorem cell20_491704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 6].length) (baseStart_491704 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_491704 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_491704 prefixEnd_491704 := by exact prefixLift 491704
  have htrace : WordTrace (prefixWord ++ tailWord_491704) baseStart_491704 baseEnd_491704 := by
    simpa [prefixWord, tailWord_491704, baseEnd_491704] using wordTrace_append hprefix tailTrace_491704
  have hstable : (prefixWord ++ tailWord_491704).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491704).length < 2 ^ (prefixWord ++ tailWord_491704).sum := by decide
  have hdescent : baseEnd_491704 < baseStart_491704 := by decide
  rcases family_descends (prefixWord ++ tailWord_491704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491741 : List Nat := [1, 4, 3, 2, 1, 3, 2, 1, 3]
def baseStart_491741 : Nat := 118140960795 + 491741 * 2 ^ 59
def prefixEnd_491741 : Nat := 4983230072969 + 3 ^ 40 * 491741 * 2
def baseEnd_491741 : Nat := 224443991575702928689805

theorem tailTrace_491741 : CollatzResearch.WordTrace tailWord_491741 prefixEnd_491741 224443991575702928689805 := by
  unfold tailWord_491741
  simp only [CollatzResearch.WordTrace]
  refine ⟨17935267711513814521707077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11956845141009209681138051 17935267711513814521707077)
  ·
    refine ⟨3362862695908840222820077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17935267711513814521707077 3362862695908840222820077)
    ·
      refine ⟨1261073510965815083557529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3362862695908840222820077 1261073510965815083557529)
      ·
        refine ⟨945805133224361312668147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1261073510965815083557529 945805133224361312668147)
        ·
          refine ⟨1418707699836541969002221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 945805133224361312668147 1418707699836541969002221)
          ·
            refine ⟨532015387438703238375833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1418707699836541969002221 532015387438703238375833)
            ·
              refine ⟨399011540579027428781875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 532015387438703238375833 399011540579027428781875)
              ·
                refine ⟨598517310868541143172813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 399011540579027428781875 598517310868541143172813)
                ·
                  refine ⟨224443991575702928689805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 598517310868541143172813 224443991575702928689805)
                  ·
                    rfl

theorem cell20_491741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 2, 1, 3].length) (baseStart_491741 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_491741 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_491741 prefixEnd_491741 := by exact prefixLift 491741
  have htrace : WordTrace (prefixWord ++ tailWord_491741) baseStart_491741 baseEnd_491741 := by
    simpa [prefixWord, tailWord_491741, baseEnd_491741] using wordTrace_append hprefix tailTrace_491741
  have hstable : (prefixWord ++ tailWord_491741).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491741).length < 2 ^ (prefixWord ++ tailWord_491741).sum := by decide
  have hdescent : baseEnd_491741 < baseStart_491741 := by decide
  rcases family_descends (prefixWord ++ tailWord_491741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491766 : List Nat := [5, 1, 1, 1, 1, 1, 2, 1, 7]
def baseStart_491766 : Nat := 118140960795 + 491766 * 2 ^ 59
def prefixEnd_491766 : Nat := 4983230072969 + 3 ^ 40 * 491766 * 2
def baseEnd_491766 : Nat := 224455402256913952856369

theorem tailTrace_491766 : CollatzResearch.WordTrace tailWord_491766 prefixEnd_491766 224455402256913952856369 := by
  unfold tailWord_491766
  simp only [CollatzResearch.WordTrace]
  refine ⟨1121011221026452736960447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11957453024282162527578101 1121011221026452736960447)
  ·
    refine ⟨1681516831539679105440671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1121011221026452736960447 1681516831539679105440671)
    ·
      refine ⟨2522275247309518658161007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1681516831539679105440671 2522275247309518658161007)
      ·
        refine ⟨3783412870964277987241511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2522275247309518658161007 3783412870964277987241511)
        ·
          refine ⟨5675119306446416980862267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3783412870964277987241511 5675119306446416980862267)
          ·
            refine ⟨8512678959669625471293401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5675119306446416980862267 8512678959669625471293401)
            ·
              refine ⟨6384509219752219103470051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8512678959669625471293401 6384509219752219103470051)
              ·
                refine ⟨9576763829628328655205077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6384509219752219103470051 9576763829628328655205077)
                ·
                  refine ⟨224455402256913952856369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9576763829628328655205077 224455402256913952856369)
                  ·
                    rfl

theorem cell20_491766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 1, 7].length) (baseStart_491766 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_491766 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_491766 prefixEnd_491766 := by exact prefixLift 491766
  have htrace : WordTrace (prefixWord ++ tailWord_491766) baseStart_491766 baseEnd_491766 := by
    simpa [prefixWord, tailWord_491766, baseEnd_491766] using wordTrace_append hprefix tailTrace_491766
  have hstable : (prefixWord ++ tailWord_491766).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491766).length < 2 ^ (prefixWord ++ tailWord_491766).sum := by decide
  have hdescent : baseEnd_491766 < baseStart_491766 := by decide
  rcases family_descends (prefixWord ++ tailWord_491766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491780 : List Nat := [2, 3, 2, 2, 11]
def baseStart_491780 : Nat := 118140960795 + 491780 * 2 ^ 59
def prefixEnd_491780 : Nat := 4983230072969 + 3 ^ 40 * 491780 * 2
def baseEnd_491780 : Nat := 2771133237511013906045

theorem tailTrace_491780 : CollatzResearch.WordTrace tailWord_491780 prefixEnd_491780 2771133237511013906045 := by
  unfold tailWord_491780
  simp only [CollatzResearch.WordTrace]
  refine ⟨8968345079186262091188397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11957793438915016121584529 8968345079186262091188397)
  ·
    refine ⟨3363129404694848284195649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8968345079186262091188397 3363129404694848284195649)
    ·
      refine ⟨2522347053521136213146737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3363129404694848284195649 2522347053521136213146737)
      ·
        refine ⟨1891760290140852159860053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2522347053521136213146737 1891760290140852159860053)
        ·
          refine ⟨2771133237511013906045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 1891760290140852159860053 2771133237511013906045)
          ·
            rfl

theorem cell20_491780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 11].length) (baseStart_491780 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_491780 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_491780 prefixEnd_491780 := by exact prefixLift 491780
  have htrace : WordTrace (prefixWord ++ tailWord_491780) baseStart_491780 baseEnd_491780 := by
    simpa [prefixWord, tailWord_491780, baseEnd_491780] using wordTrace_append hprefix tailTrace_491780
  have hstable : (prefixWord ++ tailWord_491780).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491780).length < 2 ^ (prefixWord ++ tailWord_491780).sum := by decide
  have hdescent : baseEnd_491780 < baseStart_491780 := by decide
  rcases family_descends (prefixWord ++ tailWord_491780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491811 : List Nat := [1, 1, 1, 4, 2, 2, 3, 2, 4]
def baseStart_491811 : Nat := 118140960795 + 491811 * 2 ^ 59
def prefixEnd_491811 : Nat := 4983230072969 + 3 ^ 40 * 491811 * 2
def baseEnd_491811 : Nat := 224475941483093796356185

theorem tailTrace_491811 : CollatzResearch.WordTrace tailWord_491811 prefixEnd_491811 224475941483093796356185 := by
  unfold tailWord_491811
  simp only [CollatzResearch.WordTrace]
  refine ⟨17937820821260216476755287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11958547214173477651170191 17937820821260216476755287)
  ·
    refine ⟨26906731231890324715132931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17937820821260216476755287 26906731231890324715132931)
    ·
      refine ⟨40360096847835487072699397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26906731231890324715132931 40360096847835487072699397)
      ·
        refine ⟨7567518158969153826131137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40360096847835487072699397 7567518158969153826131137)
        ·
          refine ⟨5675638619226865369598353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7567518158969153826131137 5675638619226865369598353)
          ·
            refine ⟨4256728964420149027198765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5675638619226865369598353 4256728964420149027198765)
            ·
              refine ⟨1596273361657555885199537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4256728964420149027198765 1596273361657555885199537)
              ·
                refine ⟨1197205021243166913899653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1596273361657555885199537 1197205021243166913899653)
                ·
                  refine ⟨224475941483093796356185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1197205021243166913899653 224475941483093796356185)
                  ·
                    rfl

theorem cell20_491811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 2, 4].length) (baseStart_491811 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_491811 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_491811 prefixEnd_491811 := by exact prefixLift 491811
  have htrace : WordTrace (prefixWord ++ tailWord_491811) baseStart_491811 baseEnd_491811 := by
    simpa [prefixWord, tailWord_491811, baseEnd_491811] using wordTrace_append hprefix tailTrace_491811
  have hstable : (prefixWord ++ tailWord_491811).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491811).length < 2 ^ (prefixWord ++ tailWord_491811).sum := by decide
  have hdescent : baseEnd_491811 < baseStart_491811 := by decide
  rcases family_descends (prefixWord ++ tailWord_491811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491838 : List Nat := [4, 2, 1, 2, 1, 4, 1, 2, 3]
def baseStart_491838 : Nat := 118140960795 + 491838 * 2 ^ 59
def prefixEnd_491838 : Nat := 4983230072969 + 3 ^ 40 * 491838 * 2
def baseEnd_491838 : Nat := 224488265018801702456075

theorem tailTrace_491838 : CollatzResearch.WordTrace tailWord_491838 prefixEnd_491838 224488265018801702456075 := by
  unfold tailWord_491838
  simp only [CollatzResearch.WordTrace]
  refine ⟨2242350699020300010998521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11959203728108266725325445 2242350699020300010998521)
  ·
    refine ⟨1681763024265225008248891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2242350699020300010998521 1681763024265225008248891)
    ·
      refine ⟨2522644536397837512373337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1681763024265225008248891 2522644536397837512373337)
      ·
        refine ⟨1891983402298378134280003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2522644536397837512373337 1891983402298378134280003)
        ·
          refine ⟨2837975103447567201420005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1891983402298378134280003 2837975103447567201420005)
          ·
            refine ⟨532120331896418850266251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2837975103447567201420005 532120331896418850266251)
            ·
              refine ⟨798180497844628275399377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 532120331896418850266251 798180497844628275399377)
              ·
                refine ⟨598635373383471206549533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 798180497844628275399377 598635373383471206549533)
                ·
                  refine ⟨224488265018801702456075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 598635373383471206549533 224488265018801702456075)
                  ·
                    rfl

theorem cell20_491838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 1, 2, 3].length) (baseStart_491838 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_491838 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_491838 prefixEnd_491838 := by exact prefixLift 491838
  have htrace : WordTrace (prefixWord ++ tailWord_491838) baseStart_491838 baseEnd_491838 := by
    simpa [prefixWord, tailWord_491838, baseEnd_491838] using wordTrace_append hprefix tailTrace_491838
  have hstable : (prefixWord ++ tailWord_491838).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491838).length < 2 ^ (prefixWord ++ tailWord_491838).sum := by decide
  have hdescent : baseEnd_491838 < baseStart_491838 := by decide
  rcases family_descends (prefixWord ++ tailWord_491838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491880 : List Nat := [2, 1, 4, 2, 2, 1, 1, 2, 5]
def baseStart_491880 : Nat := 118140960795 + 491880 * 2 ^ 59
def prefixEnd_491880 : Nat := 4983230072969 + 3 ^ 40 * 491880 * 2
def baseEnd_491880 : Nat := 224507434963236223055903

theorem tailTrace_491880 : CollatzResearch.WordTrace tailWord_491880 prefixEnd_491880 224507434963236223055903 := by
  unfold tailWord_491880
  simp only [CollatzResearch.WordTrace]
  refine ⟨8970168729005120630508547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11960224972006827507344729 8970168729005120630508547)
  ·
    refine ⟨13455253093507680945762821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8970168729005120630508547 13455253093507680945762821)
    ·
      refine ⟨2522859955032690177330529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13455253093507680945762821 2522859955032690177330529)
      ·
        refine ⟨1892144966274517632997897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2522859955032690177330529 1892144966274517632997897)
        ·
          refine ⟨1419108724705888224748423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1892144966274517632997897 1419108724705888224748423)
          ·
            refine ⟨2128663087058832337122635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1419108724705888224748423 2128663087058832337122635)
            ·
              refine ⟨3192994630588248505683953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2128663087058832337122635 3192994630588248505683953)
              ·
                refine ⟨2394745972941186379262965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3192994630588248505683953 2394745972941186379262965)
                ·
                  refine ⟨224507434963236223055903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2394745972941186379262965 224507434963236223055903)
                  ·
                    rfl

theorem cell20_491880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 2, 5].length) (baseStart_491880 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_491880 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_491880 prefixEnd_491880 := by exact prefixLift 491880
  have htrace : WordTrace (prefixWord ++ tailWord_491880) baseStart_491880 baseEnd_491880 := by
    simpa [prefixWord, tailWord_491880, baseEnd_491880] using wordTrace_append hprefix tailTrace_491880
  have hstable : (prefixWord ++ tailWord_491880).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491880).length < 2 ^ (prefixWord ++ tailWord_491880).sum := by decide
  have hdescent : baseEnd_491880 < baseStart_491880 := by decide
  rcases family_descends (prefixWord ++ tailWord_491880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491914 : List Nat := [3, 1, 2, 5, 1, 1, 1, 3, 3]
def baseStart_491914 : Nat := 118140960795 + 491914 * 2 ^ 59
def prefixEnd_491914 : Nat := 4983230072969 + 3 ^ 40 * 491914 * 2
def baseEnd_491914 : Nat := 224522953489683215922431

theorem tailTrace_491914 : CollatzResearch.WordTrace tailWord_491914 prefixEnd_491914 224522953489683215922431 := by
  unfold tailWord_491914
  simp only [CollatzResearch.WordTrace]
  refine ⟨4485394384971766266938699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11961051693258043378503197 4485394384971766266938699)
  ·
    refine ⟨6728091577457649400408049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4485394384971766266938699 6728091577457649400408049)
    ·
      refine ⟨5046068683093237050306037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6728091577457649400408049 5046068683093237050306037)
      ·
        refine ⟨473068939039990973466191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5046068683093237050306037 473068939039990973466191)
        ·
          refine ⟨709603408559986460199287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 473068939039990973466191 709603408559986460199287)
          ·
            refine ⟨1064405112839979690298931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 709603408559986460199287 1064405112839979690298931)
            ·
              refine ⟨1596607669259969535448397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1064405112839979690298931 1596607669259969535448397)
              ·
                refine ⟨598727875972488575793149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1596607669259969535448397 598727875972488575793149)
                ·
                  refine ⟨224522953489683215922431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 598727875972488575793149 224522953489683215922431)
                  ·
                    rfl

theorem cell20_491914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 3, 3].length) (baseStart_491914 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_491914 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_491914 prefixEnd_491914 := by exact prefixLift 491914
  have htrace : WordTrace (prefixWord ++ tailWord_491914) baseStart_491914 baseEnd_491914 := by
    simpa [prefixWord, tailWord_491914, baseEnd_491914] using wordTrace_append hprefix tailTrace_491914
  have hstable : (prefixWord ++ tailWord_491914).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491914).length < 2 ^ (prefixWord ++ tailWord_491914).sum := by decide
  have hdescent : baseEnd_491914 < baseStart_491914 := by decide
  rcases family_descends (prefixWord ++ tailWord_491914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491949 : List Nat := [1, 5, 2, 2, 2, 8]
def baseStart_491949 : Nat := 118140960795 + 491949 * 2 ^ 59
def prefixEnd_491949 : Nat := 4983230072969 + 3 ^ 40 * 491949 * 2
def baseEnd_491949 : Nat := 8316256609014024065023

theorem tailTrace_491949 : CollatzResearch.WordTrace tailWord_491949 prefixEnd_491949 8316256609014024065023 := by
  unfold tailWord_491949
  simp only [CollatzResearch.WordTrace]
  refine ⟨17942854094760266045278901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11961902729840177363519267 17942854094760266045278901)
  ·
    refine ⟨1682142571383774941744897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17942854094760266045278901 1682142571383774941744897)
    ·
      refine ⟨1261606928537831206308673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1682142571383774941744897 1261606928537831206308673)
      ·
        refine ⟨946205196403373404731505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1261606928537831206308673 946205196403373404731505)
        ·
          refine ⟨709653897302530053548629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 946205196403373404731505 709653897302530053548629)
          ·
            refine ⟨8316256609014024065023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 709653897302530053548629 8316256609014024065023)
            ·
              rfl

theorem cell20_491949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 8].length) (baseStart_491949 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_491949 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_491949 prefixEnd_491949 := by exact prefixLift 491949
  have htrace : WordTrace (prefixWord ++ tailWord_491949) baseStart_491949 baseEnd_491949 := by
    simpa [prefixWord, tailWord_491949, baseEnd_491949] using wordTrace_append hprefix tailTrace_491949
  have hstable : (prefixWord ++ tailWord_491949).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491949).length < 2 ^ (prefixWord ++ tailWord_491949).sum := by decide
  have hdescent : baseEnd_491949 < baseStart_491949 := by decide
  rcases family_descends (prefixWord ++ tailWord_491949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491959 : List Nat := [1, 1, 3, 1, 3, 3, 4, 2, 2]
def baseStart_491959 : Nat := 118140960795 + 491959 * 2 ^ 59
def prefixEnd_491959 : Nat := 4983230072969 + 3 ^ 40 * 491959 * 2
def baseEnd_491959 : Nat := 224543492715863059422247

theorem tailTrace_491959 : CollatzResearch.WordTrace tailWord_491959 prefixEnd_491959 224543492715863059422247 := by
  unfold tailWord_491959
  simp only [CollatzResearch.WordTrace]
  refine ⟨17943218824724037753142931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11962145883149358502095287 17943218824724037753142931)
  ·
    refine ⟨26914828237086056629714397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17943218824724037753142931 26914828237086056629714397)
    ·
      refine ⟨10093060588907271236142899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26914828237086056629714397 10093060588907271236142899)
      ·
        refine ⟨15139590883360906854214349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10093060588907271236142899 15139590883360906854214349)
        ·
          refine ⟨5677346581260340070330381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15139590883360906854214349 5677346581260340070330381)
          ·
            refine ⟨2129004967972627526373893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5677346581260340070330381 2129004967972627526373893)
            ·
              refine ⟨399188431494867661195105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2129004967972627526373893 399188431494867661195105)
              ·
                refine ⟨299391323621150745896329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 399188431494867661195105 299391323621150745896329)
                ·
                  refine ⟨224543492715863059422247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 299391323621150745896329 224543492715863059422247)
                  ·
                    rfl

theorem cell20_491959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 4, 2, 2].length) (baseStart_491959 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_491959 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_491959 prefixEnd_491959 := by exact prefixLift 491959
  have htrace : WordTrace (prefixWord ++ tailWord_491959) baseStart_491959 baseEnd_491959 := by
    simpa [prefixWord, tailWord_491959, baseEnd_491959] using wordTrace_append hprefix tailTrace_491959
  have hstable : (prefixWord ++ tailWord_491959).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491959).length < 2 ^ (prefixWord ++ tailWord_491959).sum := by decide
  have hdescent : baseEnd_491959 < baseStart_491959 := by decide
  rcases family_descends (prefixWord ++ tailWord_491959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491980 : List Nat := [2, 2, 1, 4, 3, 1, 1, 2, 4]
def baseStart_491980 : Nat := 118140960795 + 491980 * 2 ^ 59
def prefixEnd_491980 : Nat := 4983230072969 + 3 ^ 40 * 491980 * 2
def baseEnd_491980 : Nat := 224553077688080319722161

theorem tailTrace_491980 : CollatzResearch.WordTrace tailWord_491980 prefixEnd_491980 224553077688080319722161 := by
  unfold tailWord_491980
  simp only [CollatzResearch.WordTrace]
  refine ⟨8971992378823979169828697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11962656505098638893104929 8971992378823979169828697)
  ·
    refine ⟨6728994284117984377371523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8971992378823979169828697 6728994284117984377371523)
    ·
      refine ⟨10093491426176976566057285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6728994284117984377371523 10093491426176976566057285)
      ·
        refine ⟨1892529642408183106135741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10093491426176976566057285 1892529642408183106135741)
        ·
          refine ⟨709698615903068664800903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1892529642408183106135741 709698615903068664800903)
          ·
            refine ⟨1064547923854602997201355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 709698615903068664800903 1064547923854602997201355)
            ·
              refine ⟨1596821885781904495802033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1064547923854602997201355 1596821885781904495802033)
              ·
                refine ⟨1197616414336428371851525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1596821885781904495802033 1197616414336428371851525)
                ·
                  refine ⟨224553077688080319722161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1197616414336428371851525 224553077688080319722161)
                  ·
                    rfl

theorem cell20_491980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 2, 4].length) (baseStart_491980 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_491980 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_491980 prefixEnd_491980 := by exact prefixLift 491980
  have htrace : WordTrace (prefixWord ++ tailWord_491980) baseStart_491980 baseEnd_491980 := by
    simpa [prefixWord, tailWord_491980, baseEnd_491980] using wordTrace_append hprefix tailTrace_491980
  have hstable : (prefixWord ++ tailWord_491980).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491980).length < 2 ^ (prefixWord ++ tailWord_491980).sum := by decide
  have hdescent : baseEnd_491980 < baseStart_491980 := by decide
  rcases family_descends (prefixWord ++ tailWord_491980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491997 : List Nat := [1, 4, 3, 1, 1, 1, 4, 3, 2]
def baseStart_491997 : Nat := 118140960795 + 491997 * 2 ^ 59
def prefixEnd_491997 : Nat := 4983230072969 + 3 ^ 40 * 491997 * 2
def baseEnd_491997 : Nat := 224560836951303816155425

theorem tailTrace_491997 : CollatzResearch.WordTrace tailWord_491997 prefixEnd_491997 224560836951303816155425 := by
  unfold tailWord_491997
  simp only [CollatzResearch.WordTrace]
  refine ⟨17944604798586370243026245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11963069865724246828684163 17944604798586370243026245)
  ·
    refine ⟨3364613399734944420567421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17944604798586370243026245 3364613399734944420567421)
    ·
      refine ⟨1261730024900604157712783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3364613399734944420567421 1261730024900604157712783)
      ·
        refine ⟨1892595037350906236569175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1261730024900604157712783 1892595037350906236569175)
        ·
          refine ⟨2838892556026359354853763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1892595037350906236569175 2838892556026359354853763)
          ·
            refine ⟨4258338834039539032280645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2838892556026359354853763 4258338834039539032280645)
            ·
              refine ⟨798438531382413568552621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4258338834039539032280645 798438531382413568552621)
              ·
                refine ⟨299414449268405088207233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 798438531382413568552621 299414449268405088207233)
                ·
                  refine ⟨224560836951303816155425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 299414449268405088207233 224560836951303816155425)
                  ·
                    rfl

theorem cell20_491997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 4, 3, 2].length) (baseStart_491997 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_491997 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_491997 prefixEnd_491997 := by exact prefixLift 491997
  have htrace : WordTrace (prefixWord ++ tailWord_491997) baseStart_491997 baseEnd_491997 := by
    simpa [prefixWord, tailWord_491997, baseEnd_491997] using wordTrace_append hprefix tailTrace_491997
  have hstable : (prefixWord ++ tailWord_491997).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491997).length < 2 ^ (prefixWord ++ tailWord_491997).sum := by decide
  have hdescent : baseEnd_491997 < baseStart_491997 := by decide
  rcases family_descends (prefixWord ++ tailWord_491997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492008 : List Nat := [2, 1, 4, 1, 1, 4, 7]
def baseStart_492008 : Nat := 118140960795 + 492008 * 2 ^ 59
def prefixEnd_492008 : Nat := 4983230072969 + 3 ^ 40 * 492008 * 2
def baseEnd_492008 : Nat := 24951761961226296309857

theorem tailTrace_492008 : CollatzResearch.WordTrace tailWord_492008 prefixEnd_492008 24951761961226296309857 := by
  unfold tailWord_492008
  simp only [CollatzResearch.WordTrace]
  refine ⟨8972503000773259560838339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11963337334364346081117785 8972503000773259560838339)
  ·
    refine ⟨13458754501159889341257509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8972503000773259560838339 13458754501159889341257509)
    ·
      refine ⟨2523516468967479251485783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13458754501159889341257509 2523516468967479251485783)
      ·
        refine ⟨3785274703451218877228675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2523516468967479251485783 3785274703451218877228675)
        ·
          refine ⟨5677912055176828315843013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3785274703451218877228675 5677912055176828315843013)
          ·
            refine ⟨1064608510345655309220565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5677912055176828315843013 1064608510345655309220565)
            ·
              refine ⟨24951761961226296309857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1064608510345655309220565 24951761961226296309857)
              ·
                rfl

theorem cell20_492008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 7].length) (baseStart_492008 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_492008 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_492008 prefixEnd_492008 := by exact prefixLift 492008
  have htrace : WordTrace (prefixWord ++ tailWord_492008) baseStart_492008 baseEnd_492008 := by
    simpa [prefixWord, tailWord_492008, baseEnd_492008] using wordTrace_append hprefix tailTrace_492008
  have hstable : (prefixWord ++ tailWord_492008).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492008).length < 2 ^ (prefixWord ++ tailWord_492008).sum := by decide
  have hdescent : baseEnd_492008 < baseStart_492008 := by decide
  rcases family_descends (prefixWord ++ tailWord_492008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492038 : List Nat := [6, 2, 1, 1, 1, 1, 4, 4]
def baseStart_492038 : Nat := 118140960795 + 492038 * 2 ^ 59
def prefixEnd_492038 : Nat := 4983230072969 + 3 ^ 40 * 492038 * 2
def baseEnd_492038 : Nat := 74859850156163298596197

theorem tailTrace_492038 : CollatzResearch.WordTrace tailWord_492038 prefixEnd_492038 74859850156163298596197 := by
  unfold tailWord_492038
  simp only [CollatzResearch.WordTrace]
  refine ⟨560815630982432320164649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 11964066794291889496845845 560815630982432320164649)
  ·
    refine ⟨420611723236824240123487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 560815630982432320164649 420611723236824240123487)
    ·
      refine ⟨630917584855236360185231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 420611723236824240123487 630917584855236360185231)
      ·
        refine ⟨946376377282854540277847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 630917584855236360185231 946376377282854540277847)
        ·
          refine ⟨1419564565924281810416771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 946376377282854540277847 1419564565924281810416771)
          ·
            refine ⟨2129346848886422715625157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1419564565924281810416771 2129346848886422715625157)
            ·
              refine ⟨399252534166204259179717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2129346848886422715625157 399252534166204259179717)
              ·
                refine ⟨74859850156163298596197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 399252534166204259179717 74859850156163298596197)
                ·
                  rfl

theorem cell20_492038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 4, 4].length) (baseStart_492038 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_492038 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_492038 prefixEnd_492038 := by exact prefixLift 492038
  have htrace : WordTrace (prefixWord ++ tailWord_492038) baseStart_492038 baseEnd_492038 := by
    simpa [prefixWord, tailWord_492038, baseEnd_492038] using wordTrace_append hprefix tailTrace_492038
  have hstable : (prefixWord ++ tailWord_492038).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492038).length < 2 ^ (prefixWord ++ tailWord_492038).sum := by decide
  have hdescent : baseEnd_492038 < baseStart_492038 := by decide
  rcases family_descends (prefixWord ++ tailWord_492038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492052 : List Nat := [2, 4, 3, 1, 1, 1, 3, 3, 2]
def baseStart_492052 : Nat := 118140960795 + 492052 * 2 ^ 59
def prefixEnd_492052 : Nat := 4983230072969 + 3 ^ 40 * 492052 * 2
def baseEnd_492052 : Nat := 224585940449968069321867

theorem tailTrace_492052 : CollatzResearch.WordTrace tailWord_492052 prefixEnd_492052 224585940449968069321867 := by
  unfold tailWord_492052
  simp only [CollatzResearch.WordTrace]
  refine ⟨8973305406693557318139205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11964407208924743090852273 8973305406693557318139205)
  ·
    refine ⟨1682494763755041997151101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8973305406693557318139205 1682494763755041997151101)
    ·
      refine ⟨630935536408140748931663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1682494763755041997151101 630935536408140748931663)
      ·
        refine ⟨946403304612211123397495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 630935536408140748931663 946403304612211123397495)
        ·
          refine ⟨1419604956918316685096243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 946403304612211123397495 1419604956918316685096243)
          ·
            refine ⟨2129407435377475027644365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1419604956918316685096243 2129407435377475027644365)
            ·
              refine ⟨798527788266553135366637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2129407435377475027644365 798527788266553135366637)
              ·
                refine ⟨299447920599957425762489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 798527788266553135366637 299447920599957425762489)
                ·
                  refine ⟨224585940449968069321867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 299447920599957425762489 224585940449968069321867)
                  ·
                    rfl

theorem cell20_492052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 3, 3, 2].length) (baseStart_492052 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_492052 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_492052 prefixEnd_492052 := by exact prefixLift 492052
  have htrace : WordTrace (prefixWord ++ tailWord_492052) baseStart_492052 baseEnd_492052 := by
    simpa [prefixWord, tailWord_492052, baseEnd_492052] using wordTrace_append hprefix tailTrace_492052
  have hstable : (prefixWord ++ tailWord_492052).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492052).length < 2 ^ (prefixWord ++ tailWord_492052).sum := by decide
  have hdescent : baseEnd_492052 < baseStart_492052 := by decide
  rcases family_descends (prefixWord ++ tailWord_492052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492053 : List Nat := [1, 3, 2, 1, 3, 1, 1, 1, 7]
def baseStart_492053 : Nat := 118140960795 + 492053 * 2 ^ 59
def prefixEnd_492053 : Nat := 4983230072969 + 3 ^ 40 * 492053 * 2
def baseEnd_492053 : Nat := 224586396877216510288529

theorem tailTrace_492053 : CollatzResearch.WordTrace tailWord_492053 prefixEnd_492053 224586396877216510288529 := by
  unfold tailWord_492053
  simp only [CollatzResearch.WordTrace]
  refine ⟨17946647286383491807064813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11964431524255661204709875 17946647286383491807064813)
  ·
    refine ⟨6729992732393809427649305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17946647286383491807064813 6729992732393809427649305)
    ·
      refine ⟨5047494549295357070736979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6729992732393809427649305 5047494549295357070736979)
      ·
        refine ⟨7571241823943035606105469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5047494549295357070736979 7571241823943035606105469)
        ·
          refine ⟨2839215683978638352289551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7571241823943035606105469 2839215683978638352289551)
          ·
            refine ⟨4258823525967957528434327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2839215683978638352289551 4258823525967957528434327)
            ·
              refine ⟨6388235288951936292651491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4258823525967957528434327 6388235288951936292651491)
              ·
                refine ⟨9582352933427904438977237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6388235288951936292651491 9582352933427904438977237)
                ·
                  refine ⟨224586396877216510288529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9582352933427904438977237 224586396877216510288529)
                  ·
                    rfl

theorem cell20_492053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 1, 7].length) (baseStart_492053 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_492053 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_492053 prefixEnd_492053 := by exact prefixLift 492053
  have htrace : WordTrace (prefixWord ++ tailWord_492053) baseStart_492053 baseEnd_492053 := by
    simpa [prefixWord, tailWord_492053, baseEnd_492053] using wordTrace_append hprefix tailTrace_492053
  have hstable : (prefixWord ++ tailWord_492053).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492053).length < 2 ^ (prefixWord ++ tailWord_492053).sum := by decide
  have hdescent : baseEnd_492053 < baseStart_492053 := by decide
  rcases family_descends (prefixWord ++ tailWord_492053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492132 : List Nat := [2, 3, 1, 1, 2, 2, 3, 4, 2]
def baseStart_492132 : Nat := 118140960795 + 492132 * 2 ^ 59
def prefixEnd_492132 : Nat := 4983230072969 + 3 ^ 40 * 492132 * 2
def baseEnd_492132 : Nat := 224622454629843346654873

theorem tailTrace_492132 : CollatzResearch.WordTrace tailWord_492132 prefixEnd_492132 224622454629843346654873 := by
  unfold tailWord_492132
  simp only [CollatzResearch.WordTrace]
  refine ⟨8974764326548644149595325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11966352435398192199460433 8974764326548644149595325)
  ·
    refine ⟨3365536622455741556098247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8974764326548644149595325 3365536622455741556098247)
    ·
      refine ⟨5048304933683612334147371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3365536622455741556098247 5048304933683612334147371)
      ·
        refine ⟨7572457400525418501221057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5048304933683612334147371 7572457400525418501221057)
        ·
          refine ⟨5679343050394063875915793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7572457400525418501221057 5679343050394063875915793)
          ·
            refine ⟨4259507287795547906936845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5679343050394063875915793 4259507287795547906936845)
            ·
              refine ⟨1597315232923330465101317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4259507287795547906936845 1597315232923330465101317)
              ·
                refine ⟨299496606173124462206497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1597315232923330465101317 299496606173124462206497)
                ·
                  refine ⟨224622454629843346654873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 299496606173124462206497 224622454629843346654873)
                  ·
                    rfl

theorem cell20_492132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 4, 2].length) (baseStart_492132 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_492132 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_492132 prefixEnd_492132 := by exact prefixLift 492132
  have htrace : WordTrace (prefixWord ++ tailWord_492132) baseStart_492132 baseEnd_492132 := by
    simpa [prefixWord, tailWord_492132, baseEnd_492132] using wordTrace_append hprefix tailTrace_492132
  have hstable : (prefixWord ++ tailWord_492132).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492132).length < 2 ^ (prefixWord ++ tailWord_492132).sum := by decide
  have hdescent : baseEnd_492132 < baseStart_492132 := by decide
  rcases family_descends (prefixWord ++ tailWord_492132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492153 : List Nat := [1, 2, 1, 3, 3, 3, 1, 2, 4]
def baseStart_492153 : Nat := 118140960795 + 492153 * 2 ^ 59
def prefixEnd_492153 : Nat := 4983230072969 + 3 ^ 40 * 492153 * 2
def baseEnd_492153 : Nat := 224632039602060606954787

theorem tailTrace_492153 : CollatzResearch.WordTrace tailWord_492153 prefixEnd_492153 224632039602060606954787 := by
  unfold tailWord_492153
  simp only [CollatzResearch.WordTrace]
  refine ⟨17950294586021208885705113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11966863057347472590470075 17950294586021208885705113)
  ·
    refine ⟨13462720939515906664278835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17950294586021208885705113 13462720939515906664278835)
    ·
      refine ⟨20194081409273859996418253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13462720939515906664278835 20194081409273859996418253)
      ·
        refine ⟨7572780528477697498656845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20194081409273859996418253 7572780528477697498656845)
        ·
          refine ⟨2839792698179136561996317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7572780528477697498656845 2839792698179136561996317)
          ·
            refine ⟨1064922261817176210748619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2839792698179136561996317 1064922261817176210748619)
            ·
              refine ⟨1597383392725764316122929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1064922261817176210748619 1597383392725764316122929)
              ·
                refine ⟨1198037544544323237092197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1597383392725764316122929 1198037544544323237092197)
                ·
                  refine ⟨224632039602060606954787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1198037544544323237092197 224632039602060606954787)
                  ·
                    rfl

theorem cell20_492153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 2, 4].length) (baseStart_492153 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_492153 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_492153 prefixEnd_492153 := by exact prefixLift 492153
  have htrace : WordTrace (prefixWord ++ tailWord_492153) baseStart_492153 baseEnd_492153 := by
    simpa [prefixWord, tailWord_492153, baseEnd_492153] using wordTrace_append hprefix tailTrace_492153
  have hstable : (prefixWord ++ tailWord_492153).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492153).length < 2 ^ (prefixWord ++ tailWord_492153).sum := by decide
  have hdescent : baseEnd_492153 < baseStart_492153 := by decide
  rcases family_descends (prefixWord ++ tailWord_492153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492162 : List Nat := [3, 4, 3, 1, 1, 1, 2, 3, 2]
def baseStart_492162 : Nat := 118140960795 + 492162 * 2 ^ 59
def prefixEnd_492162 : Nat := 4983230072969 + 3 ^ 40 * 492162 * 2
def baseEnd_492162 : Nat := 224636147447296575654751

theorem tailTrace_492162 : CollatzResearch.WordTrace tailWord_492162 prefixEnd_492162 224636147447296575654751 := by
  unfold tailWord_492162
  simp only [CollatzResearch.WordTrace]
  refine ⟨4487655710747150855695685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11967081895325735615188493 4487655710747150855695685)
  ·
    refine ⟨841435445765090785442941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4487655710747150855695685 841435445765090785442941)
    ·
      refine ⟨315538292161909044541103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 841435445765090785442941 315538292161909044541103)
      ·
        refine ⟨473307438242863566811655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315538292161909044541103 473307438242863566811655)
        ·
          refine ⟨709961157364295350217483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 473307438242863566811655 709961157364295350217483)
          ·
            refine ⟨1064941736046443025326225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 709961157364295350217483 1064941736046443025326225)
            ·
              refine ⟨798706302034832268994669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1064941736046443025326225 798706302034832268994669)
              ·
                refine ⟨299514863263062100873001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 798706302034832268994669 299514863263062100873001)
                ·
                  refine ⟨224636147447296575654751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 299514863263062100873001 224636147447296575654751)
                  ·
                    rfl

theorem cell20_492162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 2, 3, 2].length) (baseStart_492162 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_492162 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_492162 prefixEnd_492162 := by exact prefixLift 492162
  have htrace : WordTrace (prefixWord ++ tailWord_492162) baseStart_492162 baseEnd_492162 := by
    simpa [prefixWord, tailWord_492162, baseEnd_492162] using wordTrace_append hprefix tailTrace_492162
  have hstable : (prefixWord ++ tailWord_492162).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492162).length < 2 ^ (prefixWord ++ tailWord_492162).sum := by decide
  have hdescent : baseEnd_492162 < baseStart_492162 := by decide
  rcases family_descends (prefixWord ++ tailWord_492162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492167 : List Nat := [1, 1, 4, 2, 1, 2, 2, 2, 5]
def baseStart_492167 : Nat := 118140960795 + 492167 * 2 ^ 59
def prefixEnd_492167 : Nat := 4983230072969 + 3 ^ 40 * 492167 * 2
def baseEnd_492167 : Nat := 224638429583538780488063

theorem tailTrace_492167 : CollatzResearch.WordTrace tailWord_492167 prefixEnd_492167 224638429583538780488063 := by
  unfold tailWord_492167
  simp only [CollatzResearch.WordTrace]
  refine ⟨17950805207970489276714755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11967203471980326184476503 17950805207970489276714755)
  ·
    refine ⟨26926207811955733915072133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17950805207970489276714755 26926207811955733915072133)
    ·
      refine ⟨5048663964741700109076025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26926207811955733915072133 5048663964741700109076025)
      ·
        refine ⟨3786497973556275081807019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5048663964741700109076025 3786497973556275081807019)
        ·
          refine ⟨5679746960334412622710529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3786497973556275081807019 5679746960334412622710529)
          ·
            refine ⟨4259810220250809467032897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5679746960334412622710529 4259810220250809467032897)
            ·
              refine ⟨3194857665188107100274673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4259810220250809467032897 3194857665188107100274673)
              ·
                refine ⟨2396143248891080325206005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3194857665188107100274673 2396143248891080325206005)
                ·
                  refine ⟨224638429583538780488063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2396143248891080325206005 224638429583538780488063)
                  ·
                    rfl

theorem cell20_492167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 2, 5].length) (baseStart_492167 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_492167 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_492167 prefixEnd_492167 := by exact prefixLift 492167
  have htrace : WordTrace (prefixWord ++ tailWord_492167) baseStart_492167 baseEnd_492167 := by
    simpa [prefixWord, tailWord_492167, baseEnd_492167] using wordTrace_append hprefix tailTrace_492167
  have hstable : (prefixWord ++ tailWord_492167).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492167).length < 2 ^ (prefixWord ++ tailWord_492167).sum := by decide
  have hdescent : baseEnd_492167 < baseStart_492167 := by decide
  rcases family_descends (prefixWord ++ tailWord_492167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492180 : List Nat := [2, 4, 2, 2, 1, 3, 1, 2, 3]
def baseStart_492180 : Nat := 118140960795 + 492180 * 2 ^ 59
def prefixEnd_492180 : Nat := 4983230072969 + 3 ^ 40 * 492180 * 2
def baseEnd_492180 : Nat := 224644363137768513054677

theorem tailTrace_492180 : CollatzResearch.WordTrace tailWord_492180 prefixEnd_492180 224644363137768513054677 := by
  unfold tailWord_492180
  simp only [CollatzResearch.WordTrace]
  refine ⟨8975639678461696248468997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11967519571282261664625329 8975639678461696248468997)
  ·
    refine ⟨1682932439711568046587937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8975639678461696248468997 1682932439711568046587937)
    ·
      refine ⟨1262199329783676034940953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1682932439711568046587937 1262199329783676034940953)
      ·
        refine ⟨946649497337757026205715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1262199329783676034940953 946649497337757026205715)
        ·
          refine ⟨1419974246006635539308573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 946649497337757026205715 1419974246006635539308573)
          ·
            refine ⟨532490342252488327240715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1419974246006635539308573 532490342252488327240715)
            ·
              refine ⟨798735513378732490861073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 532490342252488327240715 798735513378732490861073)
              ·
                refine ⟨599051635034049368145805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 798735513378732490861073 599051635034049368145805)
                ·
                  refine ⟨224644363137768513054677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 599051635034049368145805 224644363137768513054677)
                  ·
                    rfl

theorem cell20_492180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 1, 2, 3].length) (baseStart_492180 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_492180 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_492180 prefixEnd_492180 := by exact prefixLift 492180
  have htrace : WordTrace (prefixWord ++ tailWord_492180) baseStart_492180 baseEnd_492180 := by
    simpa [prefixWord, tailWord_492180, baseEnd_492180] using wordTrace_append hprefix tailTrace_492180
  have hstable : (prefixWord ++ tailWord_492180).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492180).length < 2 ^ (prefixWord ++ tailWord_492180).sum := by decide
  have hdescent : baseEnd_492180 < baseStart_492180 := by decide
  rcases family_descends (prefixWord ++ tailWord_492180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492236 : List Nat := [2, 2, 1, 5, 1, 1, 8]
def baseStart_492236 : Nat := 118140960795 + 492236 * 2 ^ 59
def prefixEnd_492236 : Nat := 4983230072969 + 3 ^ 40 * 492236 * 2
def baseEnd_492236 : Nat := 24963324784853467465309

theorem tailTrace_492236 : CollatzResearch.WordTrace tailWord_492236 prefixEnd_492236 24963324784853467465309 := by
  unfold tailWord_492236
  simp only [CollatzResearch.WordTrace]
  refine ⟨8976660922360257030488281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11968881229813676040651041 8976660922360257030488281)
  ·
    refine ⟨6732495691770192772866211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8976660922360257030488281 6732495691770192772866211)
    ·
      refine ⟨10098743537655289159299317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6732495691770192772866211 10098743537655289159299317)
      ·
        refine ⟨946757206655183358684311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10098743537655289159299317 946757206655183358684311)
        ·
          refine ⟨1420135809982775038026467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 946757206655183358684311 1420135809982775038026467)
          ·
            refine ⟨2130203714974162557039701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1420135809982775038026467 2130203714974162557039701)
            ·
              refine ⟨24963324784853467465309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2130203714974162557039701 24963324784853467465309)
              ·
                rfl

theorem cell20_492236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 8].length) (baseStart_492236 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_492236 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_492236 prefixEnd_492236 := by exact prefixLift 492236
  have htrace : WordTrace (prefixWord ++ tailWord_492236) baseStart_492236 baseEnd_492236 := by
    simpa [prefixWord, tailWord_492236, baseEnd_492236] using wordTrace_append hprefix tailTrace_492236
  have hstable : (prefixWord ++ tailWord_492236).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492236).length < 2 ^ (prefixWord ++ tailWord_492236).sum := by decide
  have hdescent : baseEnd_492236 < baseStart_492236 := by decide
  rcases family_descends (prefixWord ++ tailWord_492236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492242 : List Nat := [3, 2, 2, 2, 3, 1, 3, 2, 2]
def baseStart_492242 : Nat := 118140960795 + 492242 * 2 ^ 59
def prefixEnd_492242 : Nat := 4983230072969 + 3 ^ 40 * 492242 * 2
def baseEnd_492242 : Nat := 224672661627171852987757

theorem tailTrace_492242 : CollatzResearch.WordTrace tailWord_492242 prefixEnd_492242 224672661627171852987757 := by
  unfold tailWord_492242
  simp only [CollatzResearch.WordTrace]
  refine ⟨4488385170674694271423745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11969027121799184723796653 4488385170674694271423745)
  ·
    refine ⟨3366288878006020703567809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4488385170674694271423745 3366288878006020703567809)
    ·
      refine ⟨2524716658504515527675857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3366288878006020703567809 2524716658504515527675857)
      ·
        refine ⟨1893537493878386645756893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2524716658504515527675857 1893537493878386645756893)
        ·
          refine ⟨710076560204394992158835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1893537493878386645756893 710076560204394992158835)
          ·
            refine ⟨1065114840306592488238253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 710076560204394992158835 1065114840306592488238253)
            ·
              refine ⟨399418065114972183089345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1065114840306592488238253 399418065114972183089345)
              ·
                refine ⟨299563548836229137317009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 399418065114972183089345 299563548836229137317009)
                ·
                  refine ⟨224672661627171852987757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 299563548836229137317009 224672661627171852987757)
                  ·
                    rfl

theorem cell20_492242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 3, 2, 2].length) (baseStart_492242 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_492242 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_492242 prefixEnd_492242 := by exact prefixLift 492242
  have htrace : WordTrace (prefixWord ++ tailWord_492242) baseStart_492242 baseEnd_492242 := by
    simpa [prefixWord, tailWord_492242, baseEnd_492242] using wordTrace_append hprefix tailTrace_492242
  have hstable : (prefixWord ++ tailWord_492242).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492242).length < 2 ^ (prefixWord ++ tailWord_492242).sum := by decide
  have hdescent : baseEnd_492242 < baseStart_492242 := by decide
  rcases family_descends (prefixWord ++ tailWord_492242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492260 : List Nat := [2, 3, 1, 1, 1, 5, 1, 3, 3]
def baseStart_492260 : Nat := 118140960795 + 492260 * 2 ^ 59
def prefixEnd_492260 : Nat := 4983230072969 + 3 ^ 40 * 492260 * 2
def baseEnd_492260 : Nat := 224680877317643790387683

theorem tailTrace_492260 : CollatzResearch.WordTrace tailWord_492260 prefixEnd_492260 224680877317643790387683 := by
  unfold tailWord_492260
  simp only [CollatzResearch.WordTrace]
  refine ⟨8977098598316783079925117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11969464797755710773233489 8977098598316783079925117)
  ·
    refine ⟨3366411974368793654971919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8977098598316783079925117 3366411974368793654971919)
    ·
      refine ⟨5049617961553190482457879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3366411974368793654971919 5049617961553190482457879)
      ·
        refine ⟨7574426942329785723686819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5049617961553190482457879 7574426942329785723686819)
        ·
          refine ⟨11361640413494678585530229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7574426942329785723686819 11361640413494678585530229)
          ·
            refine ⟨1065153788765126117393459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11361640413494678585530229 1065153788765126117393459)
            ·
              refine ⟨1597730683147689176090189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1065153788765126117393459 1597730683147689176090189)
              ·
                refine ⟨599149006180383441033821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1597730683147689176090189 599149006180383441033821)
                ·
                  refine ⟨224680877317643790387683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 599149006180383441033821 224680877317643790387683)
                  ·
                    rfl

theorem cell20_492260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 3, 3].length) (baseStart_492260 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_492260 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_492260 prefixEnd_492260 := by exact prefixLift 492260
  have htrace : WordTrace (prefixWord ++ tailWord_492260) baseStart_492260 baseEnd_492260 := by
    simpa [prefixWord, tailWord_492260, baseEnd_492260] using wordTrace_append hprefix tailTrace_492260
  have hstable : (prefixWord ++ tailWord_492260).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492260).length < 2 ^ (prefixWord ++ tailWord_492260).sum := by decide
  have hdescent : baseEnd_492260 < baseStart_492260 := by decide
  rcases family_descends (prefixWord ++ tailWord_492260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492274 : List Nat := [3, 2, 1, 3, 1, 2, 2, 6]
def baseStart_492274 : Nat := 118140960795 + 492274 * 2 ^ 59
def prefixEnd_492274 : Nat := 4983230072969 + 3 ^ 40 * 492274 * 2
def baseEnd_492274 : Nat := 74895755766373987973653

theorem tailTrace_492274 : CollatzResearch.WordTrace tailWord_492274 prefixEnd_492274 74895755766373987973653 := by
  unfold tailWord_492274
  simp only [CollatzResearch.WordTrace]
  refine ⟨4488676954645711637714969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11969805212388564367239917 4488676954645711637714969)
  ·
    refine ⟨3366507715984283728286227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4488676954645711637714969 3366507715984283728286227)
    ·
      refine ⟨5049761573976425592429341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3366507715984283728286227 5049761573976425592429341)
      ·
        refine ⟨1893660590241159597161003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5049761573976425592429341 1893660590241159597161003)
        ·
          refine ⟨2840490885361739395741505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1893660590241159597161003 2840490885361739395741505)
          ·
            refine ⟨2130368164021304546806129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2840490885361739395741505 2130368164021304546806129)
            ·
              refine ⟨1597776123015978410104597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2130368164021304546806129 1597776123015978410104597)
              ·
                refine ⟨74895755766373987973653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1597776123015978410104597 74895755766373987973653)
                ·
                  rfl

theorem cell20_492274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 6].length) (baseStart_492274 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_492274 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_492274 prefixEnd_492274 := by exact prefixLift 492274
  have htrace : WordTrace (prefixWord ++ tailWord_492274) baseStart_492274 baseEnd_492274 := by
    simpa [prefixWord, tailWord_492274, baseEnd_492274] using wordTrace_append hprefix tailTrace_492274
  have hstable : (prefixWord ++ tailWord_492274).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492274).length < 2 ^ (prefixWord ++ tailWord_492274).sum := by decide
  have hdescent : baseEnd_492274 < baseStart_492274 := by decide
  rcases family_descends (prefixWord ++ tailWord_492274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492298 : List Nat := [3, 1, 2, 2, 1, 2, 4, 2, 3]
def baseStart_492298 : Nat := 118140960795 + 492298 * 2 ^ 59
def prefixEnd_492298 : Nat := 4983230072969 + 3 ^ 40 * 492298 * 2
def baseEnd_492298 : Nat := 224698221553084547120861

theorem tailTrace_492298 : CollatzResearch.WordTrace tailWord_492298 prefixEnd_492298 224698221553084547120861 := by
  unfold tailWord_492298
  simp only [CollatzResearch.WordTrace]
  refine ⟨4488895792623974662433387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11970388780330599099822365 4488895792623974662433387)
  ·
    refine ⟨6733343688935961993650081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4488895792623974662433387 6733343688935961993650081)
    ·
      refine ⟨5050007766701971495237561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6733343688935961993650081 5050007766701971495237561)
      ·
        refine ⟨3787505825026478621428171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5050007766701971495237561 3787505825026478621428171)
        ·
          refine ⟨5681258737539717932142257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3787505825026478621428171 5681258737539717932142257)
          ·
            refine ⟨4260944053154788449106693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5681258737539717932142257 4260944053154788449106693)
            ·
              refine ⟨798927009966522834207505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4260944053154788449106693 798927009966522834207505)
              ·
                refine ⟨599195257474892125655629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 798927009966522834207505 599195257474892125655629)
                ·
                  refine ⟨224698221553084547120861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 599195257474892125655629 224698221553084547120861)
                  ·
                    rfl

theorem cell20_492298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 4, 2, 3].length) (baseStart_492298 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_492298 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_492298 prefixEnd_492298 := by exact prefixLift 492298
  have htrace : WordTrace (prefixWord ++ tailWord_492298) baseStart_492298 baseEnd_492298 := by
    simpa [prefixWord, tailWord_492298, baseEnd_492298] using wordTrace_append hprefix tailTrace_492298
  have hstable : (prefixWord ++ tailWord_492298).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492298).length < 2 ^ (prefixWord ++ tailWord_492298).sum := by decide
  have hdescent : baseEnd_492298 < baseStart_492298 := by decide
  rcases family_descends (prefixWord ++ tailWord_492298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492353 : List Nat := [1, 2, 5, 3, 1, 1, 1, 1, 5]
def baseStart_492353 : Nat := 118140960795 + 492353 * 2 ^ 59
def prefixEnd_492353 : Nat := 4983230072969 + 3 ^ 40 * 492353 * 2
def baseEnd_492353 : Nat := 224723325051748800287303

theorem tailTrace_492353 : CollatzResearch.WordTrace tailWord_492353 prefixEnd_492353 224723325051748800287303 := by
  unfold tailWord_492353
  simp only [CollatzResearch.WordTrace]
  refine ⟨17957589185296643042985713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11971726123531095361990475 17957589185296643042985713)
  ·
    refine ⟨13468191888972482282239285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17957589185296643042985713 13468191888972482282239285)
    ·
      refine ⟨1262642989591170213959933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13468191888972482282239285 1262642989591170213959933)
      ·
        refine ⟨473491121096688830234975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1262642989591170213959933 473491121096688830234975)
        ·
          refine ⟨710236681645033245352463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 473491121096688830234975 710236681645033245352463)
          ·
            refine ⟨1065355022467549868028695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 710236681645033245352463 1065355022467549868028695)
            ·
              refine ⟨1598032533701324802043043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1065355022467549868028695 1598032533701324802043043)
              ·
                refine ⟨2397048800551987203064565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1598032533701324802043043 2397048800551987203064565)
                ·
                  refine ⟨224723325051748800287303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2397048800551987203064565 224723325051748800287303)
                  ·
                    rfl

theorem cell20_492353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 1, 5].length) (baseStart_492353 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_492353 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_492353 prefixEnd_492353 := by exact prefixLift 492353
  have htrace : WordTrace (prefixWord ++ tailWord_492353) baseStart_492353 baseEnd_492353 := by
    simpa [prefixWord, tailWord_492353, baseEnd_492353] using wordTrace_append hprefix tailTrace_492353
  have hstable : (prefixWord ++ tailWord_492353).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492353).length < 2 ^ (prefixWord ++ tailWord_492353).sum := by decide
  have hdescent : baseEnd_492353 < baseStart_492353 := by decide
  rcases family_descends (prefixWord ++ tailWord_492353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492357 : List Nat := [1, 3, 1, 1, 1, 2, 2, 6, 3]
def baseStart_492357 : Nat := 118140960795 + 492357 * 2 ^ 59
def prefixEnd_492357 : Nat := 4983230072969 + 3 ^ 40 * 492357 * 2
def baseEnd_492357 : Nat := 224725150760742564153953

theorem tailTrace_492357 : CollatzResearch.WordTrace tailWord_492357 prefixEnd_492357 224725150760742564153953 := by
  unfold tailWord_492357
  simp only [CollatzResearch.WordTrace]
  refine ⟨17957735077282151726131325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11971823384854767817420883 17957735077282151726131325)
  ·
    refine ⟨6734150653980806897299247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17957735077282151726131325 6734150653980806897299247)
    ·
      refine ⟨10101225980971210345948871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6734150653980806897299247 10101225980971210345948871)
      ·
        refine ⟨15151838971456815518923307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10101225980971210345948871 15151838971456815518923307)
        ·
          refine ⟨22727758457185223278384961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15151838971456815518923307 22727758457185223278384961)
          ·
            refine ⟨17045818842888917458788721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22727758457185223278384961 17045818842888917458788721)
            ·
              refine ⟨12784364132166688094091541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17045818842888917458788721 12784364132166688094091541)
              ·
                refine ⟨599267068695313504410541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 12784364132166688094091541 599267068695313504410541)
                ·
                  refine ⟨224725150760742564153953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 599267068695313504410541 224725150760742564153953)
                  ·
                    rfl

theorem cell20_492357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 6, 3].length) (baseStart_492357 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_492357 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_492357 prefixEnd_492357 := by exact prefixLift 492357
  have htrace : WordTrace (prefixWord ++ tailWord_492357) baseStart_492357 baseEnd_492357 := by
    simpa [prefixWord, tailWord_492357, baseEnd_492357] using wordTrace_append hprefix tailTrace_492357
  have hstable : (prefixWord ++ tailWord_492357).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492357).length < 2 ^ (prefixWord ++ tailWord_492357).sum := by decide
  have hdescent : baseEnd_492357 < baseStart_492357 := by decide
  rcases family_descends (prefixWord ++ tailWord_492357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492388 : List Nat := [2, 3, 1, 1, 4, 2, 1, 6]
def baseStart_492388 : Nat := 118140960795 + 492388 * 2 ^ 59
def prefixEnd_492388 : Nat := 4983230072969 + 3 ^ 40 * 492388 * 2
def baseEnd_492388 : Nat := 74913100001814744706831

theorem tailTrace_492388 : CollatzResearch.WordTrace tailWord_492388 prefixEnd_492388 74913100001814744706831 := by
  unfold tailWord_492388
  simp only [CollatzResearch.WordTrace]
  refine ⟨8979432870084922010254909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11972577160113229347006545 8979432870084922010254909)
  ·
    refine ⟨3367287326281845753845591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8979432870084922010254909 3367287326281845753845591)
    ·
      refine ⟨5050930989422768630768387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3367287326281845753845591 5050930989422768630768387)
      ·
        refine ⟨7576396484134152946152581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5050930989422768630768387 7576396484134152946152581)
        ·
          refine ⟨1420574340775153677403609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7576396484134152946152581 1420574340775153677403609)
          ·
            refine ⟨1065430755581365258052707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1420574340775153677403609 1065430755581365258052707)
            ·
              refine ⟨1598146133372047887079061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1065430755581365258052707 1598146133372047887079061)
              ·
                refine ⟨74913100001814744706831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1598146133372047887079061 74913100001814744706831)
                ·
                  rfl

theorem cell20_492388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 6].length) (baseStart_492388 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_492388 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_492388 prefixEnd_492388 := by exact prefixLift 492388
  have htrace : WordTrace (prefixWord ++ tailWord_492388) baseStart_492388 baseEnd_492388 := by
    simpa [prefixWord, tailWord_492388, baseEnd_492388] using wordTrace_append hprefix tailTrace_492388
  have hstable : (prefixWord ++ tailWord_492388).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492388).length < 2 ^ (prefixWord ++ tailWord_492388).sum := by decide
  have hdescent : baseEnd_492388 < baseStart_492388 := by decide
  rcases family_descends (prefixWord ++ tailWord_492388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492402 : List Nat := [3, 2, 1, 2, 1, 1, 2, 2, 6]
def baseStart_492402 : Nat := 118140960795 + 492402 * 2 ^ 59
def prefixEnd_492402 : Nat := 4983230072969 + 3 ^ 40 * 492402 * 2
def baseEnd_492402 : Nat := 224745689986922407653769

theorem tailTrace_492402 : CollatzResearch.WordTrace tailWord_492402 prefixEnd_492402 224745689986922407653769 := by
  unfold tailWord_492402
  simp only [CollatzResearch.WordTrace]
  refine ⟨4489844090529781102879865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11972917574746082941012973 4489844090529781102879865)
  ·
    refine ⟨3367383067897335827159899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4489844090529781102879865 3367383067897335827159899)
    ·
      refine ⟨5051074601846003740739849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3367383067897335827159899 5051074601846003740739849)
      ·
        refine ⟨3788305951384502805554887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5051074601846003740739849 3788305951384502805554887)
        ·
          refine ⟨5682458927076754208332331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3788305951384502805554887 5682458927076754208332331)
          ·
            refine ⟨8523688390615131312498497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5682458927076754208332331 8523688390615131312498497)
            ·
              refine ⟨6392766292961348484373873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8523688390615131312498497 6392766292961348484373873)
              ·
                refine ⟨4794574719721011363280405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6392766292961348484373873 4794574719721011363280405)
                ·
                  refine ⟨224745689986922407653769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4794574719721011363280405 224745689986922407653769)
                  ·
                    rfl

theorem cell20_492402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 2, 6].length) (baseStart_492402 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_492402 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_492402 prefixEnd_492402 := by exact prefixLift 492402
  have htrace : WordTrace (prefixWord ++ tailWord_492402) baseStart_492402 baseEnd_492402 := by
    simpa [prefixWord, tailWord_492402, baseEnd_492402] using wordTrace_append hprefix tailTrace_492402
  have hstable : (prefixWord ++ tailWord_492402).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492402).length < 2 ^ (prefixWord ++ tailWord_492402).sum := by decide
  have hdescent : baseEnd_492402 < baseStart_492402 := by decide
  rcases family_descends (prefixWord ++ tailWord_492402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492409 : List Nat := [1, 2, 1, 3, 2, 3, 8]
def baseStart_492409 : Nat := 118140960795 + 492409 * 2 ^ 59
def prefixEnd_492409 : Nat := 4983230072969 + 3 ^ 40 * 492409 * 2
def baseEnd_492409 : Nat := 24972098330851277157823

theorem tailTrace_492409 : CollatzResearch.WordTrace tailWord_492409 prefixEnd_492409 24972098330851277157823 := by
  unfold tailWord_492409
  simp only [CollatzResearch.WordTrace]
  refine ⟨17959631673093764607024281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11973087782062509738016187 17959631673093764607024281)
  ·
    refine ⟨13469723754820323455268211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17959631673093764607024281 13469723754820323455268211)
    ·
      refine ⟨20204585632230485182902317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13469723754820323455268211 20204585632230485182902317)
      ·
        refine ⟨7576719612086431943588369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20204585632230485182902317 7576719612086431943588369)
        ·
          refine ⟨5682539709064823957691277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7576719612086431943588369 5682539709064823957691277)
          ·
            refine ⟨2130952390899308984134229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5682539709064823957691277 2130952390899308984134229)
            ·
              refine ⟨24972098330851277157823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2130952390899308984134229 24972098330851277157823)
              ·
                rfl

theorem cell20_492409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 8].length) (baseStart_492409 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_492409 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_492409 prefixEnd_492409 := by exact prefixLift 492409
  have htrace : WordTrace (prefixWord ++ tailWord_492409) baseStart_492409 baseEnd_492409 := by
    simpa [prefixWord, tailWord_492409, baseEnd_492409] using wordTrace_append hprefix tailTrace_492409
  have hstable : (prefixWord ++ tailWord_492409).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492409).length < 2 ^ (prefixWord ++ tailWord_492409).sum := by decide
  have hdescent : baseEnd_492409 < baseStart_492409 := by decide
  rcases family_descends (prefixWord ++ tailWord_492409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492426 : List Nat := [3, 1, 2, 4, 1, 1, 1, 7]
def baseStart_492426 : Nat := 118140960795 + 492426 * 2 ^ 59
def prefixEnd_492426 : Nat := 4983230072969 + 3 ^ 40 * 492426 * 2
def baseEnd_492426 : Nat := 74918881413628330284557

theorem tailTrace_492426 : CollatzResearch.WordTrace tailWord_492426 prefixEnd_492426 74918881413628330284557 := by
  unfold tailWord_492426
  simp only [CollatzResearch.WordTrace]
  refine ⟨4490062928508044127598283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11973501142688117673595421 4490062928508044127598283)
  ·
    refine ⟨6735094392762066191397425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4490062928508044127598283 6735094392762066191397425)
    ·
      refine ⟨5051320794571549643548069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6735094392762066191397425 5051320794571549643548069)
      ·
        refine ⟨947122648982165558165263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5051320794571549643548069 947122648982165558165263)
        ·
          refine ⟨1420683973473248337247895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 947122648982165558165263 1420683973473248337247895)
          ·
            refine ⟨2131025960209872505871843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1420683973473248337247895 2131025960209872505871843)
            ·
              refine ⟨3196538940314808758807765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2131025960209872505871843 3196538940314808758807765)
              ·
                refine ⟨74918881413628330284557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3196538940314808758807765 74918881413628330284557)
                ·
                  rfl

theorem cell20_492426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 7].length) (baseStart_492426 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_492426 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_492426 prefixEnd_492426 := by exact prefixLift 492426
  have htrace : WordTrace (prefixWord ++ tailWord_492426) baseStart_492426 baseEnd_492426 := by
    simpa [prefixWord, tailWord_492426, baseEnd_492426] using wordTrace_append hprefix tailTrace_492426
  have hstable : (prefixWord ++ tailWord_492426).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492426).length < 2 ^ (prefixWord ++ tailWord_492426).sum := by decide
  have hdescent : baseEnd_492426 < baseStart_492426 := by decide
  rcases family_descends (prefixWord ++ tailWord_492426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492457 : List Nat := [1, 2, 1, 1, 1, 1, 6, 5, 2]
def baseStart_492457 : Nat := 118140960795 + 492457 * 2 ^ 59
def prefixEnd_492457 : Nat := 4983230072969 + 3 ^ 40 * 492457 * 2
def baseEnd_492457 : Nat := 224770793485586660820211

theorem tailTrace_492457 : CollatzResearch.WordTrace tailWord_492457 prefixEnd_492457 224770793485586660820211 := by
  unfold tailWord_492457
  simp only [CollatzResearch.WordTrace]
  refine ⟨17961382376919868804771625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11974254917946579203181083 17961382376919868804771625)
  ·
    refine ⟨13471036782689901603578719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17961382376919868804771625 13471036782689901603578719)
    ·
      refine ⟨20206555174034852405368079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13471036782689901603578719 20206555174034852405368079)
      ·
        refine ⟨30309832761052278608052119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20206555174034852405368079 30309832761052278608052119)
        ·
          refine ⟨45464749141578417912078179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30309832761052278608052119 45464749141578417912078179)
          ·
            refine ⟨68197123712367626868117269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45464749141578417912078179 68197123712367626868117269)
            ·
              refine ⟨3196740174017232509442997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 68197123712367626868117269 3196740174017232509442997)
              ·
                refine ⟨299694391314115547760281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3196740174017232509442997 299694391314115547760281)
                ·
                  refine ⟨224770793485586660820211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 299694391314115547760281 224770793485586660820211)
                  ·
                    rfl

theorem cell20_492457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 5, 2].length) (baseStart_492457 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_492457 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_492457 prefixEnd_492457 := by exact prefixLift 492457
  have htrace : WordTrace (prefixWord ++ tailWord_492457) baseStart_492457 baseEnd_492457 := by
    simpa [prefixWord, tailWord_492457, baseEnd_492457] using wordTrace_append hprefix tailTrace_492457
  have hstable : (prefixWord ++ tailWord_492457).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492457).length < 2 ^ (prefixWord ++ tailWord_492457).sum := by decide
  have hdescent : baseEnd_492457 < baseStart_492457 := by decide
  rcases family_descends (prefixWord ++ tailWord_492457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492471 : List Nat := [1, 1, 3, 1, 3, 1, 3, 4, 3]
def baseStart_492471 : Nat := 118140960795 + 492471 * 2 ^ 59
def prefixEnd_492471 : Nat := 4983230072969 + 3 ^ 40 * 492471 * 2
def baseEnd_492471 : Nat := 224777183467064834353487

theorem tailTrace_492471 : CollatzResearch.WordTrace tailWord_492471 prefixEnd_492471 224777183467064834353487 := by
  unfold tailWord_492471
  simp only [CollatzResearch.WordTrace]
  refine ⟨17961892998869149195781267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11974595332579432797187511 17961892998869149195781267)
  ·
    refine ⟨26942839498303723793671901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17961892998869149195781267 26942839498303723793671901)
    ·
      refine ⟨10103564811863896422626963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26942839498303723793671901 10103564811863896422626963)
      ·
        refine ⟨15155347217795844633940445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10103564811863896422626963 15155347217795844633940445)
        ·
          refine ⟨5683255206673441737727667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15155347217795844633940445 5683255206673441737727667)
          ·
            refine ⟨8524882810010162606591501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5683255206673441737727667 8524882810010162606591501)
            ·
              refine ⟨3196831053753810977471813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8524882810010162606591501 3196831053753810977471813)
              ·
                refine ⟨599405822578839558275965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3196831053753810977471813 599405822578839558275965)
                ·
                  refine ⟨224777183467064834353487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 599405822578839558275965 224777183467064834353487)
                  ·
                    rfl

theorem cell20_492471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 4, 3].length) (baseStart_492471 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_492471 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_492471 prefixEnd_492471 := by exact prefixLift 492471
  have htrace : WordTrace (prefixWord ++ tailWord_492471) baseStart_492471 baseEnd_492471 := by
    simpa [prefixWord, tailWord_492471, baseEnd_492471] using wordTrace_append hprefix tailTrace_492471
  have hstable : (prefixWord ++ tailWord_492471).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492471).length < 2 ^ (prefixWord ++ tailWord_492471).sum := by decide
  have hdescent : baseEnd_492471 < baseStart_492471 := by decide
  rcases family_descends (prefixWord ++ tailWord_492471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492526 : List Nat := [4, 1, 2, 1, 4, 1, 1, 1, 5]
def baseStart_492526 : Nat := 118140960795 + 492526 * 2 ^ 59
def prefixEnd_492526 : Nat := 4983230072969 + 3 ^ 40 * 492526 * 2
def baseEnd_492526 : Nat := 224802286965729087519929

theorem tailTrace_492526 : CollatzResearch.WordTrace tailWord_492526 prefixEnd_492526 224802286965729087519929 := by
  unfold tailWord_492526
  simp only [CollatzResearch.WordTrace]
  refine ⟨2245487376708736698629179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11975932675779929059355621 2245487376708736698629179)
  ·
    refine ⟨3368231065063105047943769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2245487376708736698629179 3368231065063105047943769)
    ·
      refine ⟨2526173298797328785957827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3368231065063105047943769 2526173298797328785957827)
      ·
        refine ⟨3789259948195993178936741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2526173298797328785957827 3789259948195993178936741)
        ·
          refine ⟨710486240286748721050639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3789259948195993178936741 710486240286748721050639)
          ·
            refine ⟨1065729360430123081575959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 710486240286748721050639 1065729360430123081575959)
            ·
              refine ⟨1598594040645184622363939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1065729360430123081575959 1598594040645184622363939)
              ·
                refine ⟨2397891060967776933545909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1598594040645184622363939 2397891060967776933545909)
                ·
                  refine ⟨224802286965729087519929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2397891060967776933545909 224802286965729087519929)
                  ·
                    rfl

theorem cell20_492526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 1, 5].length) (baseStart_492526 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_492526 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_492526 prefixEnd_492526 := by exact prefixLift 492526
  have htrace : WordTrace (prefixWord ++ tailWord_492526) baseStart_492526 baseEnd_492526 := by
    simpa [prefixWord, tailWord_492526, baseEnd_492526] using wordTrace_append hprefix tailTrace_492526
  have hstable : (prefixWord ++ tailWord_492526).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492526).length < 2 ^ (prefixWord ++ tailWord_492526).sum := by decide
  have hdescent : baseEnd_492526 < baseStart_492526 := by decide
  rcases family_descends (prefixWord ++ tailWord_492526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492567 : List Nat := [1, 1, 3, 5, 1, 3, 1, 3, 2]
def baseStart_492567 : Nat := 118140960795 + 492567 * 2 ^ 59
def prefixEnd_492567 : Nat := 4983230072969 + 3 ^ 40 * 492567 * 2
def baseEnd_492567 : Nat := 224821000482915167153095

theorem tailTrace_492567 : CollatzResearch.WordTrace tailWord_492567 prefixEnd_492567 224821000482915167153095 := by
  unfold tailWord_492567
  simp only [CollatzResearch.WordTrace]
  refine ⟨17965394406521357591275955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11976929604347571727517303 17965394406521357591275955)
  ·
    refine ⟨26948091609782036386913933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17965394406521357591275955 26948091609782036386913933)
    ·
      refine ⟨10105534353668263645092725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26948091609782036386913933 10105534353668263645092725)
      ·
        refine ⟨947393845656399716727443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10105534353668263645092725 947393845656399716727443)
        ·
          refine ⟨1421090768484599575091165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 947393845656399716727443 1421090768484599575091165)
          ·
            refine ⟨532909038181724840659187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1421090768484599575091165 532909038181724840659187)
            ·
              refine ⟨799363557272587260988781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 532909038181724840659187 799363557272587260988781)
              ·
                refine ⟨299761333977220222870793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 799363557272587260988781 299761333977220222870793)
                ·
                  refine ⟨224821000482915167153095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 299761333977220222870793 224821000482915167153095)
                  ·
                    rfl

theorem cell20_492567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 1, 3, 2].length) (baseStart_492567 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_492567 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_492567 prefixEnd_492567 := by exact prefixLift 492567
  have htrace : WordTrace (prefixWord ++ tailWord_492567) baseStart_492567 baseEnd_492567 := by
    simpa [prefixWord, tailWord_492567, baseEnd_492567] using wordTrace_append hprefix tailTrace_492567
  have hstable : (prefixWord ++ tailWord_492567).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492567).length < 2 ^ (prefixWord ++ tailWord_492567).sum := by decide
  have hdescent : baseEnd_492567 < baseStart_492567 := by decide
  rcases family_descends (prefixWord ++ tailWord_492567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492578 : List Nat := [3, 3, 1, 1, 1, 5, 6]
def baseStart_492578 : Nat := 118140960795 + 492578 * 2 ^ 59
def prefixEnd_492578 : Nat := 4983230072969 + 3 ^ 40 * 492578 * 2
def baseEnd_492578 : Nat := 24980669020294224198487

theorem tailTrace_492578 : CollatzResearch.WordTrace tailWord_492578 prefixEnd_492578 24980669020294224198487 := by
  unfold tailWord_492578
  simp only [CollatzResearch.WordTrace]
  refine ⟨4491448902370376617481597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11977197072987670979950925 4491448902370376617481597)
  ·
    refine ⟨1684293338388891231555599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4491448902370376617481597 1684293338388891231555599)
    ·
      refine ⟨2526440007583336847333399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1684293338388891231555599 2526440007583336847333399)
      ·
        refine ⟨3789660011375005271000099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2526440007583336847333399 3789660011375005271000099)
        ·
          refine ⟨5684490017062507906500149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3789660011375005271000099 5684490017062507906500149)
          ·
            refine ⟨532920939099610116234389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5684490017062507906500149 532920939099610116234389)
            ·
              refine ⟨24980669020294224198487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 532920939099610116234389 24980669020294224198487)
              ·
                rfl

theorem cell20_492578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 6].length) (baseStart_492578 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_492578 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_492578 prefixEnd_492578 := by exact prefixLift 492578
  have htrace : WordTrace (prefixWord ++ tailWord_492578) baseStart_492578 baseEnd_492578 := by
    simpa [prefixWord, tailWord_492578, baseEnd_492578] using wordTrace_append hprefix tailTrace_492578
  have hstable : (prefixWord ++ tailWord_492578).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492578).length < 2 ^ (prefixWord ++ tailWord_492578).sum := by decide
  have hdescent : baseEnd_492578 < baseStart_492578 := by decide
  rcases family_descends (prefixWord ++ tailWord_492578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492588 : List Nat := [2, 2, 1, 1, 1, 2, 7, 2, 2]
def baseStart_492588 : Nat := 118140960795 + 492588 * 2 ^ 59
def prefixEnd_492588 : Nat := 4983230072969 + 3 ^ 40 * 492588 * 2
def baseEnd_492588 : Nat := 224830585455132427453009

theorem tailTrace_492588 : CollatzResearch.WordTrace tailWord_492588 prefixEnd_492588 224830585455132427453009 := by
  unfold tailWord_492588
  simp only [CollatzResearch.WordTrace]
  refine ⟨8983080169722639088895209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11977440226296852118526945 8983080169722639088895209)
  ·
    refine ⟨6737310127291979316671407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8983080169722639088895209 6737310127291979316671407)
    ·
      refine ⟨10105965190937968975007111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6737310127291979316671407 10105965190937968975007111)
      ·
        refine ⟨15158947786406953462510667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10105965190937968975007111 15158947786406953462510667)
        ·
          refine ⟨22738421679610430193766001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15158947786406953462510667 22738421679610430193766001)
          ·
            refine ⟨17053816259707822645324501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22738421679610430193766001 17053816259707822645324501)
            ·
              refine ⟨399698818586902093249793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 17053816259707822645324501 399698818586902093249793)
              ·
                refine ⟨299774113940176569937345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 399698818586902093249793 299774113940176569937345)
                ·
                  refine ⟨224830585455132427453009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 299774113940176569937345 224830585455132427453009)
                  ·
                    rfl

theorem cell20_492588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 7, 2, 2].length) (baseStart_492588 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_492588 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_492588 prefixEnd_492588 := by exact prefixLift 492588
  have htrace : WordTrace (prefixWord ++ tailWord_492588) baseStart_492588 baseEnd_492588 := by
    simpa [prefixWord, tailWord_492588, baseEnd_492588] using wordTrace_append hprefix tailTrace_492588
  have hstable : (prefixWord ++ tailWord_492588).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492588).length < 2 ^ (prefixWord ++ tailWord_492588).sum := by decide
  have hdescent : baseEnd_492588 < baseStart_492588 := by decide
  rcases family_descends (prefixWord ++ tailWord_492588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492598 : List Nat := [5, 1, 2, 1, 1, 4, 2, 1, 3]
def baseStart_492598 : Nat := 118140960795 + 492598 * 2 ^ 59
def prefixEnd_492598 : Nat := 4983230072969 + 3 ^ 40 * 492598 * 2
def baseEnd_492598 : Nat := 224835149727616837119635

theorem tailTrace_492598 : CollatzResearch.WordTrace tailWord_492598 prefixEnd_492598 224835149727616837119635 := by
  unfold tailWord_492598
  simp only [CollatzResearch.WordTrace]
  refine ⟨1122907816838065617853403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11977683379606033257102965 1122907816838065617853403)
  ·
    refine ⟨1684361725257098426780105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1122907816838065617853403 1684361725257098426780105)
    ·
      refine ⟨1263271293942823820085079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1684361725257098426780105 1263271293942823820085079)
      ·
        refine ⟨1894906940914235730127619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1263271293942823820085079 1894906940914235730127619)
        ·
          refine ⟨2842360411371353595191429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1894906940914235730127619 2842360411371353595191429)
          ·
            refine ⟨532942577132128799098393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2842360411371353595191429 532942577132128799098393)
            ·
              refine ⟨399706932849096599323795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 532942577132128799098393 399706932849096599323795)
              ·
                refine ⟨599560399273644898985693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 399706932849096599323795 599560399273644898985693)
                ·
                  refine ⟨224835149727616837119635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 599560399273644898985693 224835149727616837119635)
                  ·
                    rfl

theorem cell20_492598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 2, 1, 3].length) (baseStart_492598 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_492598 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_492598 prefixEnd_492598 := by exact prefixLift 492598
  have htrace : WordTrace (prefixWord ++ tailWord_492598) baseStart_492598 baseEnd_492598 := by
    simpa [prefixWord, tailWord_492598, baseEnd_492598] using wordTrace_append hprefix tailTrace_492598
  have hstable : (prefixWord ++ tailWord_492598).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492598).length < 2 ^ (prefixWord ++ tailWord_492598).sum := by decide
  have hdescent : baseEnd_492598 < baseStart_492598 := by decide
  rcases family_descends (prefixWord ++ tailWord_492598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492602 : List Nat := [3, 1, 1, 1, 3, 1, 6, 1, 3]
def baseStart_492602 : Nat := 118140960795 + 492602 * 2 ^ 59
def prefixEnd_492602 : Nat := 4983230072969 + 3 ^ 40 * 492602 * 2
def baseEnd_492602 : Nat := 224836975436610600986285

theorem tailTrace_492602 : CollatzResearch.WordTrace tailWord_492602 prefixEnd_492602 224836975436610600986285 := by
  unfold tailWord_492602
  simp only [CollatzResearch.WordTrace]
  refine ⟨4491667740348639642200015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11977780640929705712533373 4491667740348639642200015)
  ·
    refine ⟨6737501610522959463300023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4491667740348639642200015 6737501610522959463300023)
    ·
      refine ⟨10106252415784439194950035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6737501610522959463300023 10106252415784439194950035)
      ·
        refine ⟨15159378623676658792425053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10106252415784439194950035 15159378623676658792425053)
        ·
          refine ⟨5684766983878747047159395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15159378623676658792425053 5684766983878747047159395)
          ·
            refine ⟨8527150475818120570739093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5684766983878747047159395 8527150475818120570739093)
            ·
              refine ⟨399710178553974401753395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 8527150475818120570739093 399710178553974401753395)
              ·
                refine ⟨599565267830961602630093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 399710178553974401753395 599565267830961602630093)
                ·
                  refine ⟨224836975436610600986285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 599565267830961602630093 224836975436610600986285)
                  ·
                    rfl

theorem cell20_492602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 6, 1, 3].length) (baseStart_492602 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_492602 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_492602 prefixEnd_492602 := by exact prefixLift 492602
  have htrace : WordTrace (prefixWord ++ tailWord_492602) baseStart_492602 baseEnd_492602 := by
    simpa [prefixWord, tailWord_492602, baseEnd_492602] using wordTrace_append hprefix tailTrace_492602
  have hstable : (prefixWord ++ tailWord_492602).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492602).length < 2 ^ (prefixWord ++ tailWord_492602).sum := by decide
  have hdescent : baseEnd_492602 < baseStart_492602 := by decide
  rcases family_descends (prefixWord ++ tailWord_492602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492651 : List Nat := [1, 1, 1, 1, 2, 2, 1, 1, 10]
def baseStart_492651 : Nat := 118140960795 + 492651 * 2 ^ 59
def prefixEnd_492651 : Nat := 4983230072969 + 3 ^ 40 * 492651 * 2
def baseEnd_492651 : Nat := 224859340371784208352751

theorem tailTrace_492651 : CollatzResearch.WordTrace tailWord_492651 prefixEnd_492651 224859340371784208352751 := by
  unfold tailWord_492651
  simp only [CollatzResearch.WordTrace]
  refine ⟨17968458138217039937333807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11978972092144693291555871 17968458138217039937333807)
  ·
    refine ⟨26952687207325559906000711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17968458138217039937333807 26952687207325559906000711)
    ·
      refine ⟨40429030810988339859001067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26952687207325559906000711 40429030810988339859001067)
      ·
        refine ⟨60643546216482509788501601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40429030810988339859001067 60643546216482509788501601)
        ·
          refine ⟨45482659662361882341376201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60643546216482509788501601 45482659662361882341376201)
          ·
            refine ⟨34111994746771411756032151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45482659662361882341376201 34111994746771411756032151)
            ·
              refine ⟨51167992120157117634048227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34111994746771411756032151 51167992120157117634048227)
              ·
                refine ⟨76751988180235676451072341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51167992120157117634048227 76751988180235676451072341)
                ·
                  refine ⟨224859340371784208352751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 76751988180235676451072341 224859340371784208352751)
                  ·
                    rfl

theorem cell20_492651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 10].length) (baseStart_492651 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_492651 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_492651 prefixEnd_492651 := by exact prefixLift 492651
  have htrace : WordTrace (prefixWord ++ tailWord_492651) baseStart_492651 baseEnd_492651 := by
    simpa [prefixWord, tailWord_492651, baseEnd_492651] using wordTrace_append hprefix tailTrace_492651
  have hstable : (prefixWord ++ tailWord_492651).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492651).length < 2 ^ (prefixWord ++ tailWord_492651).sum := by decide
  have hdescent : baseEnd_492651 < baseStart_492651 := by decide
  rcases family_descends (prefixWord ++ tailWord_492651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492654 : List Nat := [4, 1, 2, 2, 1, 2, 3, 5]
def baseStart_492654 : Nat := 118140960795 + 492654 * 2 ^ 59
def prefixEnd_492654 : Nat := 4983230072969 + 3 ^ 40 * 492654 * 2
def baseEnd_492654 : Nat := 74953569884509843750913

theorem tailTrace_492654 : CollatzResearch.WordTrace tailWord_492654 prefixEnd_492654 74953569884509843750913 := by
  unfold tailWord_492654
  simp only [CollatzResearch.WordTrace]
  refine ⟨2246070944650771431211627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11979045038137447633128677 2246070944650771431211627)
  ·
    refine ⟨3369106416976157146817441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2246070944650771431211627 3369106416976157146817441)
    ·
      refine ⟨2526829812732117860113081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3369106416976157146817441 2526829812732117860113081)
      ·
        refine ⟨1895122359549088395084811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2526829812732117860113081 1895122359549088395084811)
        ·
          refine ⟨2842683539323632592627217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1895122359549088395084811 2842683539323632592627217)
          ·
            refine ⟨2132012654492724444470413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2842683539323632592627217 2132012654492724444470413)
            ·
              refine ⟨799504745434771666676405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2132012654492724444470413 799504745434771666676405)
              ·
                refine ⟨74953569884509843750913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 799504745434771666676405 74953569884509843750913)
                ·
                  rfl

theorem cell20_492654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 3, 5].length) (baseStart_492654 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_492654 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_492654 prefixEnd_492654 := by exact prefixLift 492654
  have htrace : WordTrace (prefixWord ++ tailWord_492654) baseStart_492654 baseEnd_492654 := by
    simpa [prefixWord, tailWord_492654, baseEnd_492654] using wordTrace_append hprefix tailTrace_492654
  have hstable : (prefixWord ++ tailWord_492654).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492654).length < 2 ^ (prefixWord ++ tailWord_492654).sum := by decide
  have hdescent : baseEnd_492654 < baseStart_492654 := by decide
  rcases family_descends (prefixWord ++ tailWord_492654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492668 : List Nat := [2, 2, 2, 1, 1, 3, 3, 2, 4]
def baseStart_492668 : Nat := 118140960795 + 492668 * 2 ^ 59
def prefixEnd_492668 : Nat := 4983230072969 + 3 ^ 40 * 492668 * 2
def baseEnd_492668 : Nat := 224867099635007704786015

theorem tailTrace_492668 : CollatzResearch.WordTrace tailWord_492668 prefixEnd_492668 224867099635007704786015 := by
  unfold tailWord_492668
  simp only [CollatzResearch.WordTrace]
  refine ⟨8984539089577725920351329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11979385452770301227135105 8984539089577725920351329)
  ·
    refine ⟨6738404317183294440263497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8984539089577725920351329 6738404317183294440263497)
    ·
      refine ⟨5053803237887470830197623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6738404317183294440263497 5053803237887470830197623)
      ·
        refine ⟨7580704856831206245296435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5053803237887470830197623 7580704856831206245296435)
        ·
          refine ⟨11371057285246809367944653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7580704856831206245296435 11371057285246809367944653)
          ·
            refine ⟨4264146481967553512979245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11371057285246809367944653 4264146481967553512979245)
            ·
              refine ⟨1599054930737832567367217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4264146481967553512979245 1599054930737832567367217)
              ·
                refine ⟨1199291198053374425525413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1599054930737832567367217 1199291198053374425525413)
                ·
                  refine ⟨224867099635007704786015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1199291198053374425525413 224867099635007704786015)
                  ·
                    rfl

theorem cell20_492668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 2, 4].length) (baseStart_492668 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_492668 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_492668 prefixEnd_492668 := by exact prefixLift 492668
  have htrace : WordTrace (prefixWord ++ tailWord_492668) baseStart_492668 baseEnd_492668 := by
    simpa [prefixWord, tailWord_492668, baseEnd_492668] using wordTrace_append hprefix tailTrace_492668
  have hstable : (prefixWord ++ tailWord_492668).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492668).length < 2 ^ (prefixWord ++ tailWord_492668).sum := by decide
  have hdescent : baseEnd_492668 < baseStart_492668 := by decide
  rcases family_descends (prefixWord ++ tailWord_492668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492702 : List Nat := [4, 3, 1, 1, 2, 2, 2, 1, 4]
def baseStart_492702 : Nat := 118140960795 + 492702 * 2 ^ 59
def prefixEnd_492702 : Nat := 4983230072969 + 3 ^ 40 * 492702 * 2
def baseEnd_492702 : Nat := 224882618161454697652543

theorem tailTrace_492702 : CollatzResearch.WordTrace tailWord_492702 prefixEnd_492702 224882618161454697652543 := by
  unfold tailWord_492702
  simp only [CollatzResearch.WordTrace]
  refine ⟨2246289782629034455930045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11980212174021517098293573 2246289782629034455930045)
  ·
    refine ⟨842358668485887920973767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2246289782629034455930045 842358668485887920973767)
    ·
      refine ⟨1263538002728831881460651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 842358668485887920973767 1263538002728831881460651)
      ·
        refine ⟨1895307004093247822190977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1263538002728831881460651 1895307004093247822190977)
        ·
          refine ⟨1421480253069935866643233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1895307004093247822190977 1421480253069935866643233)
          ·
            refine ⟨1066110189802451899982425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1421480253069935866643233 1066110189802451899982425)
            ·
              refine ⟨799582642351838924986819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1066110189802451899982425 799582642351838924986819)
              ·
                refine ⟨1199373963527758387480229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 799582642351838924986819 1199373963527758387480229)
                ·
                  refine ⟨224882618161454697652543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1199373963527758387480229 224882618161454697652543)
                  ·
                    rfl

theorem cell20_492702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_492702 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_492702 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_492702 prefixEnd_492702 := by exact prefixLift 492702
  have htrace : WordTrace (prefixWord ++ tailWord_492702) baseStart_492702 baseEnd_492702 := by
    simpa [prefixWord, tailWord_492702, baseEnd_492702] using wordTrace_append hprefix tailTrace_492702
  have hstable : (prefixWord ++ tailWord_492702).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492702).length < 2 ^ (prefixWord ++ tailWord_492702).sum := by decide
  have hdescent : baseEnd_492702 < baseStart_492702 := by decide
  rcases family_descends (prefixWord ++ tailWord_492702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492726 : List Nat := [5, 1, 3, 2, 1, 1, 1, 6]
def baseStart_492726 : Nat := 118140960795 + 492726 * 2 ^ 59
def prefixEnd_492726 : Nat := 4983230072969 + 3 ^ 40 * 492726 * 2
def baseEnd_492726 : Nat := 74964524138472426950815

theorem tailTrace_492726 : CollatzResearch.WordTrace tailWord_492726 prefixEnd_492726 74964524138472426950815 := by
  unfold tailWord_492726
  simp only [CollatzResearch.WordTrace]
  refine ⟨1123199600809082984144627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11980795741963551830876021 1123199600809082984144627)
  ·
    refine ⟨1684799401213624476216941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1123199600809082984144627 1684799401213624476216941)
    ·
      refine ⟨631799775455109178581353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1684799401213624476216941 631799775455109178581353)
      ·
        refine ⟨473849831591331883936015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 631799775455109178581353 473849831591331883936015)
        ·
          refine ⟨710774747386997825904023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 473849831591331883936015 710774747386997825904023)
          ·
            refine ⟨1066162121080496738856035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 710774747386997825904023 1066162121080496738856035)
            ·
              refine ⟨1599243181620745108284053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1066162121080496738856035 1599243181620745108284053)
              ·
                refine ⟨74964524138472426950815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1599243181620745108284053 74964524138472426950815)
                ·
                  rfl

theorem cell20_492726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 6].length) (baseStart_492726 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_492726 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_492726 prefixEnd_492726 := by exact prefixLift 492726
  have htrace : WordTrace (prefixWord ++ tailWord_492726) baseStart_492726 baseEnd_492726 := by
    simpa [prefixWord, tailWord_492726, baseEnd_492726] using wordTrace_append hprefix tailTrace_492726
  have hstable : (prefixWord ++ tailWord_492726).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492726).length < 2 ^ (prefixWord ++ tailWord_492726).sum := by decide
  have hdescent : baseEnd_492726 < baseStart_492726 := by decide
  rcases family_descends (prefixWord ++ tailWord_492726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492757 : List Nat := [1, 3, 2, 4, 1, 2, 3, 2, 2]
def baseStart_492757 : Nat := 118140960795 + 492757 * 2 ^ 59
def prefixEnd_492757 : Nat := 4983230072969 + 3 ^ 40 * 492757 * 2
def baseEnd_492757 : Nat := 224907721660118950818985

theorem tailTrace_492757 : CollatzResearch.WordTrace tailWord_492757 prefixEnd_492757 224907721660118950818985 := by
  unfold tailWord_492757
  simp only [CollatzResearch.WordTrace]
  refine ⟨17972324275833020040692525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11981549517222013360461683 17972324275833020040692525)
  ·
    refine ⟨6739621603437382515259697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17972324275833020040692525 6739621603437382515259697)
    ·
      refine ⟨5054716202578036886444773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6739621603437382515259697 5054716202578036886444773)
      ·
        refine ⟨947759287983381916208395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5054716202578036886444773 947759287983381916208395)
        ·
          refine ⟨1421638931975072874312593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 947759287983381916208395 1421638931975072874312593)
          ·
            refine ⟨1066229198981304655734445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1421638931975072874312593 1066229198981304655734445)
            ·
              refine ⟨399835949617989245900417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1066229198981304655734445 399835949617989245900417)
              ·
                refine ⟨299876962213491934425313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 399835949617989245900417 299876962213491934425313)
                ·
                  refine ⟨224907721660118950818985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 299876962213491934425313 224907721660118950818985)
                  ·
                    rfl

theorem cell20_492757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 3, 2, 2].length) (baseStart_492757 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_492757 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_492757 prefixEnd_492757 := by exact prefixLift 492757
  have htrace : WordTrace (prefixWord ++ tailWord_492757) baseStart_492757 baseEnd_492757 := by
    simpa [prefixWord, tailWord_492757, baseEnd_492757] using wordTrace_append hprefix tailTrace_492757
  have hstable : (prefixWord ++ tailWord_492757).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492757).length < 2 ^ (prefixWord ++ tailWord_492757).sum := by decide
  have hdescent : baseEnd_492757 < baseStart_492757 := by decide
  rcases family_descends (prefixWord ++ tailWord_492757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492782 : List Nat := [4, 1, 2, 1, 1, 1, 2, 4, 4]
def baseStart_492782 : Nat := 118140960795 + 492782 * 2 ^ 59
def prefixEnd_492782 : Nat := 4983230072969 + 3 ^ 40 * 492782 * 2
def baseEnd_492782 : Nat := 224919132341329974985549

theorem tailTrace_492782 : CollatzResearch.WordTrace tailWord_492782 prefixEnd_492782 224919132341329974985549 := by
  unfold tailWord_492782
  simp only [CollatzResearch.WordTrace]
  refine ⟨2246654512592806163794075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11982157400494966206901733 2246654512592806163794075)
  ·
    refine ⟨3369981768889209245691113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2246654512592806163794075 3369981768889209245691113)
    ·
      refine ⟨2527486326666906934268335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3369981768889209245691113 2527486326666906934268335)
      ·
        refine ⟨3791229490000360401402503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2527486326666906934268335 3791229490000360401402503)
        ·
          refine ⟨5686844235000540602103755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3791229490000360401402503 5686844235000540602103755)
          ·
            refine ⟨8530266352500810903155633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5686844235000540602103755 8530266352500810903155633)
            ·
              refine ⟨6397699764375608177366725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8530266352500810903155633 6397699764375608177366725)
              ·
                refine ⟨1199568705820426533256261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6397699764375608177366725 1199568705820426533256261)
                ·
                  refine ⟨224919132341329974985549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1199568705820426533256261 224919132341329974985549)
                  ·
                    rfl

theorem cell20_492782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 4, 4].length) (baseStart_492782 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_492782 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_492782 prefixEnd_492782 := by exact prefixLift 492782
  have htrace : WordTrace (prefixWord ++ tailWord_492782) baseStart_492782 baseEnd_492782 := by
    simpa [prefixWord, tailWord_492782, baseEnd_492782] using wordTrace_append hprefix tailTrace_492782
  have hstable : (prefixWord ++ tailWord_492782).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492782).length < 2 ^ (prefixWord ++ tailWord_492782).sum := by decide
  have hdescent : baseEnd_492782 < baseStart_492782 := by decide
  rcases family_descends (prefixWord ++ tailWord_492782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492806 : List Nat := [6, 2, 12]
def baseStart_492806 : Nat := 118140960795 + 492806 * 2 ^ 59
def prefixEnd_492806 : Nat := 4983230072969 + 3 ^ 40 * 492806 * 2
def baseEnd_492806 : Nat := 308546072147177720419

theorem tailTrace_492806 : CollatzResearch.WordTrace tailWord_492806 prefixEnd_492806 308546072147177720419 := by
  unfold tailWord_492806
  simp only [CollatzResearch.WordTrace]
  refine ⟨561690982895484419038321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 11982740968437000939484181 561690982895484419038321)
  ·
    refine ⟨421268237171613314278741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 561690982895484419038321 421268237171613314278741)
    ·
      refine ⟨308546072147177720419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 12 421268237171613314278741 308546072147177720419)
      ·
        rfl

theorem cell20_492806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 12].length) (baseStart_492806 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_492806 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_492806 prefixEnd_492806 := by exact prefixLift 492806
  have htrace : WordTrace (prefixWord ++ tailWord_492806) baseStart_492806 baseEnd_492806 := by
    simpa [prefixWord, tailWord_492806, baseEnd_492806] using wordTrace_append hprefix tailTrace_492806
  have hstable : (prefixWord ++ tailWord_492806).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492806).length < 2 ^ (prefixWord ++ tailWord_492806).sum := by decide
  have hdescent : baseEnd_492806 < baseStart_492806 := by decide
  rcases family_descends (prefixWord ++ tailWord_492806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492868 : List Nat := [2, 3, 4, 1, 1, 2, 1, 1, 5]
def baseStart_492868 : Nat := 118140960795 + 492868 * 2 ^ 59
def prefixEnd_492868 : Nat := 4983230072969 + 3 ^ 40 * 492868 * 2
def baseEnd_492868 : Nat := 224958385084695898118531

theorem tailTrace_492868 : CollatzResearch.WordTrace tailWord_492868 prefixEnd_492868 224958385084695898118531 := by
  unfold tailWord_492868
  simp only [CollatzResearch.WordTrace]
  refine ⟨8988186389215442998991629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11984248518953923998655505 8988186389215442998991629)
  ·
    refine ⟨3370569895955791124621861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8988186389215442998991629 3370569895955791124621861)
    ·
      refine ⟨631981855491710835866599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3370569895955791124621861 631981855491710835866599)
      ·
        refine ⟨947972783237566253799899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 631981855491710835866599 947972783237566253799899)
        ·
          refine ⟨1421959174856349380699849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 947972783237566253799899 1421959174856349380699849)
          ·
            refine ⟨1066469381142262035524887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1421959174856349380699849 1066469381142262035524887)
            ·
              refine ⟨1599704071713393053287331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1066469381142262035524887 1599704071713393053287331)
              ·
                refine ⟨2399556107570089579930997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1599704071713393053287331 2399556107570089579930997)
                ·
                  refine ⟨224958385084695898118531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2399556107570089579930997 224958385084695898118531)
                  ·
                    rfl

theorem cell20_492868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 1, 5].length) (baseStart_492868 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_492868 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_492868 prefixEnd_492868 := by exact prefixLift 492868
  have htrace : WordTrace (prefixWord ++ tailWord_492868) baseStart_492868 baseEnd_492868 := by
    simpa [prefixWord, tailWord_492868, baseEnd_492868] using wordTrace_append hprefix tailTrace_492868
  have hstable : (prefixWord ++ tailWord_492868).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492868).length < 2 ^ (prefixWord ++ tailWord_492868).sum := by decide
  have hdescent : baseEnd_492868 < baseStart_492868 := by decide
  rcases family_descends (prefixWord ++ tailWord_492868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492896 : List Nat := [2, 1, 1, 3, 4, 1, 2, 2, 4]
def baseStart_492896 : Nat := 118140960795 + 492896 * 2 ^ 59
def prefixEnd_492896 : Nat := 4983230072969 + 3 ^ 40 * 492896 * 2
def baseEnd_492896 : Nat := 224971165047652245185083

theorem tailTrace_492896 : CollatzResearch.WordTrace tailWord_492896 prefixEnd_492896 224971165047652245185083 := by
  unfold tailWord_492896
  simp only [CollatzResearch.WordTrace]
  refine ⟨8988697011164723390001271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11984929348219631186668361 8988697011164723390001271)
  ·
    refine ⟨13483045516747085085001907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8988697011164723390001271 13483045516747085085001907)
    ·
      refine ⟨20224568275120627627502861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13483045516747085085001907 20224568275120627627502861)
      ·
        refine ⟨7584213103170235360313573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20224568275120627627502861 7584213103170235360313573)
        ·
          refine ⟨1422039956844419130058795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7584213103170235360313573 1422039956844419130058795)
          ·
            refine ⟨2133059935266628695088193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1422039956844419130058795 2133059935266628695088193)
            ·
              refine ⟨1599794951449971521316145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2133059935266628695088193 1599794951449971521316145)
              ·
                refine ⟨1199846213587478640987109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1599794951449971521316145 1199846213587478640987109)
                ·
                  refine ⟨224971165047652245185083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1199846213587478640987109 224971165047652245185083)
                  ·
                    rfl

theorem cell20_492896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 2, 4].length) (baseStart_492896 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_492896 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_492896 prefixEnd_492896 := by exact prefixLift 492896
  have htrace : WordTrace (prefixWord ++ tailWord_492896) baseStart_492896 baseEnd_492896 := by
    simpa [prefixWord, tailWord_492896, baseEnd_492896] using wordTrace_append hprefix tailTrace_492896
  have hstable : (prefixWord ++ tailWord_492896).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492896).length < 2 ^ (prefixWord ++ tailWord_492896).sum := by decide
  have hdescent : baseEnd_492896 < baseStart_492896 := by decide
  rcases family_descends (prefixWord ++ tailWord_492896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492913 : List Nat := [1, 2, 2, 2, 1, 2, 5, 3, 2]
def baseStart_492913 : Nat := 118140960795 + 492913 * 2 ^ 59
def prefixEnd_492913 : Nat := 4983230072969 + 3 ^ 40 * 492913 * 2
def baseEnd_492913 : Nat := 224978924310875741618347

theorem tailTrace_492913 : CollatzResearch.WordTrace tailWord_492913 prefixEnd_492913 224978924310875741618347 := by
  unfold tailWord_492913
  simp only [CollatzResearch.WordTrace]
  refine ⟨17978014063267858683371393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11985342708845239122247595 17978014063267858683371393)
  ·
    refine ⟨13483510547450894012528545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17978014063267858683371393 13483510547450894012528545)
    ·
      refine ⟨10112632910588170509396409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13483510547450894012528545 10112632910588170509396409)
      ·
        refine ⟨7584474682941127882047307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10112632910588170509396409 7584474682941127882047307)
        ·
          refine ⟨11376712024411691823070961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7584474682941127882047307 11376712024411691823070961)
          ·
            refine ⟨8532534018308768867303221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11376712024411691823070961 8532534018308768867303221)
            ·
              refine ⟨799925064216447081309677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8532534018308768867303221 799925064216447081309677)
              ·
                refine ⟨299971899081167655491129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 799925064216447081309677 299971899081167655491129)
                ·
                  refine ⟨224978924310875741618347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 299971899081167655491129 224978924310875741618347)
                  ·
                    rfl

theorem cell20_492913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 5, 3, 2].length) (baseStart_492913 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_492913 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_492913 prefixEnd_492913 := by exact prefixLift 492913
  have htrace : WordTrace (prefixWord ++ tailWord_492913) baseStart_492913 baseEnd_492913 := by
    simpa [prefixWord, tailWord_492913, baseEnd_492913] using wordTrace_append hprefix tailTrace_492913
  have hstable : (prefixWord ++ tailWord_492913).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492913).length < 2 ^ (prefixWord ++ tailWord_492913).sum := by decide
  have hdescent : baseEnd_492913 < baseStart_492913 := by decide
  rcases family_descends (prefixWord ++ tailWord_492913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492926 : List Nat := [4, 2, 3, 2, 2, 1, 1, 1, 4]
def baseStart_492926 : Nat := 118140960795 + 492926 * 2 ^ 59
def prefixEnd_492926 : Nat := 4983230072969 + 3 ^ 40 * 492926 * 2
def baseEnd_492926 : Nat := 224984857865105474184961

theorem tailTrace_492926 : CollatzResearch.WordTrace tailWord_492926 prefixEnd_492926 224984857865105474184961 := by
  unfold tailWord_492926
  simp only [CollatzResearch.WordTrace]
  refine ⟨2247311026527595237949329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11985658808147174602396421 2247311026527595237949329)
  ·
    refine ⟨1685483269895696428461997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2247311026527595237949329 1685483269895696428461997)
    ·
      refine ⟨632056226210886160673249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1685483269895696428461997 632056226210886160673249)
      ·
        refine ⟨474042169658164620504937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 632056226210886160673249 474042169658164620504937)
        ·
          refine ⟨355531627243623465378703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 474042169658164620504937 355531627243623465378703)
          ·
            refine ⟨533297440865435198068055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 355531627243623465378703 533297440865435198068055)
            ·
              refine ⟨799946161298152797102083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 533297440865435198068055 799946161298152797102083)
              ·
                refine ⟨1199919241947229195653125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 799946161298152797102083 1199919241947229195653125)
                ·
                  refine ⟨224984857865105474184961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1199919241947229195653125 224984857865105474184961)
                  ·
                    rfl

theorem cell20_492926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 1, 1, 4].length) (baseStart_492926 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_492926 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_492926 prefixEnd_492926 := by exact prefixLift 492926
  have htrace : WordTrace (prefixWord ++ tailWord_492926) baseStart_492926 baseEnd_492926 := by
    simpa [prefixWord, tailWord_492926, baseEnd_492926] using wordTrace_append hprefix tailTrace_492926
  have hstable : (prefixWord ++ tailWord_492926).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492926).length < 2 ^ (prefixWord ++ tailWord_492926).sum := by decide
  have hdescent : baseEnd_492926 < baseStart_492926 := by decide
  rcases family_descends (prefixWord ++ tailWord_492926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492930 : List Nat := [3, 4, 2, 1, 1, 1, 3, 1, 4]
def baseStart_492930 : Nat := 118140960795 + 492930 * 2 ^ 59
def prefixEnd_492930 : Nat := 4983230072969 + 3 ^ 40 * 492930 * 2
def baseEnd_492930 : Nat := 224986683574099238051611

theorem tailTrace_492930 : CollatzResearch.WordTrace tailWord_492930 prefixEnd_492930 224986683574099238051611 := by
  unfold tailWord_492930
  simp only [CollatzResearch.WordTrace]
  refine ⟨4494658526051567646685061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11985756069470847057826829 4494658526051567646685061)
  ·
    refine ⟨842748473634668933753449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4494658526051567646685061 842748473634668933753449)
    ·
      refine ⟨632061355226001700315087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 842748473634668933753449 632061355226001700315087)
      ·
        refine ⟨948092032839002550472631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 632061355226001700315087 948092032839002550472631)
        ·
          refine ⟨1422138049258503825708947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 948092032839002550472631 1422138049258503825708947)
          ·
            refine ⟨2133207073887755738563421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1422138049258503825708947 2133207073887755738563421)
            ·
              refine ⟨799952652707908401961283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2133207073887755738563421 799952652707908401961283)
              ·
                refine ⟨1199928979061862602941925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 799952652707908401961283 1199928979061862602941925)
                ·
                  refine ⟨224986683574099238051611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1199928979061862602941925 224986683574099238051611)
                  ·
                    rfl

theorem cell20_492930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 3, 1, 4].length) (baseStart_492930 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_492930 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_492930 prefixEnd_492930 := by exact prefixLift 492930
  have htrace : WordTrace (prefixWord ++ tailWord_492930) baseStart_492930 baseEnd_492930 := by
    simpa [prefixWord, tailWord_492930, baseEnd_492930] using wordTrace_append hprefix tailTrace_492930
  have hstable : (prefixWord ++ tailWord_492930).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492930).length < 2 ^ (prefixWord ++ tailWord_492930).sum := by decide
  have hdescent : baseEnd_492930 < baseStart_492930 := by decide
  rcases family_descends (prefixWord ++ tailWord_492930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492985 : List Nat := [1, 2, 1, 4, 4, 2, 2, 2, 2]
def baseStart_492985 : Nat := 118140960795 + 492985 * 2 ^ 59
def prefixEnd_492985 : Nat := 4983230072969 + 3 ^ 40 * 492985 * 2
def baseEnd_492985 : Nat := 225011787072763491218053

theorem tailTrace_492985 : CollatzResearch.WordTrace tailWord_492985 prefixEnd_492985 225011787072763491218053 := by
  unfold tailWord_492985
  simp only [CollatzResearch.WordTrace]
  refine ⟨17980640119007014979992409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11987093412671343319994939 17980640119007014979992409)
  ·
    refine ⟨13485480089255261234994307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17980640119007014979992409 13485480089255261234994307)
    ·
      refine ⟨20228220133882891852491461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13485480089255261234994307 20228220133882891852491461)
      ·
        refine ⟨3792791275103042222342149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20228220133882891852491461 3792791275103042222342149)
        ·
          refine ⟨711148364081820416689153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3792791275103042222342149 711148364081820416689153)
          ·
            refine ⟨533361273061365312516865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 711148364081820416689153 533361273061365312516865)
            ·
              refine ⟨400020954796023984387649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 533361273061365312516865 400020954796023984387649)
              ·
                refine ⟨300015716097017988290737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 400020954796023984387649 300015716097017988290737)
                ·
                  refine ⟨225011787072763491218053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 300015716097017988290737 225011787072763491218053)
                  ·
                    rfl

theorem cell20_492985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 2, 2, 2].length) (baseStart_492985 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_492985 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_492985 prefixEnd_492985 := by exact prefixLift 492985
  have htrace : WordTrace (prefixWord ++ tailWord_492985) baseStart_492985 baseEnd_492985 := by
    simpa [prefixWord, tailWord_492985, baseEnd_492985] using wordTrace_append hprefix tailTrace_492985
  have hstable : (prefixWord ++ tailWord_492985).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492985).length < 2 ^ (prefixWord ++ tailWord_492985).sum := by decide
  have hdescent : baseEnd_492985 < baseStart_492985 := by decide
  rcases family_descends (prefixWord ++ tailWord_492985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492989 : List Nat := [1, 4, 1, 2, 2, 1, 3, 4, 2]
def baseStart_492989 : Nat := 118140960795 + 492989 * 2 ^ 59
def prefixEnd_492989 : Nat := 4983230072969 + 3 ^ 40 * 492989 * 2
def baseEnd_492989 : Nat := 225013612781757255084703

theorem tailTrace_492989 : CollatzResearch.WordTrace tailWord_492989 prefixEnd_492989 225013612781757255084703 := by
  unfold tailWord_492989
  simp only [CollatzResearch.WordTrace]
  refine ⟨17980786010992523663138021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11987190673995015775425347 17980786010992523663138021)
  ·
    refine ⟨3371397377061098186838379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17980786010992523663138021 3371397377061098186838379)
    ·
      refine ⟨5057096065591647280257569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3371397377061098186838379 5057096065591647280257569)
      ·
        refine ⟨3792822049193735460193177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5057096065591647280257569 3792822049193735460193177)
        ·
          refine ⟨2844616536895301595144883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3792822049193735460193177 2844616536895301595144883)
          ·
            refine ⟨4266924805342952392717325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2844616536895301595144883 4266924805342952392717325)
            ·
              refine ⟨1600096802003607147268997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4266924805342952392717325 1600096802003607147268997)
              ·
                refine ⟨300018150375676340112937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1600096802003607147268997 300018150375676340112937)
                ·
                  refine ⟨225013612781757255084703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 300018150375676340112937 225013612781757255084703)
                  ·
                    rfl

theorem cell20_492989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 4, 2].length) (baseStart_492989 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_492989 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_492989 prefixEnd_492989 := by exact prefixLift 492989
  have htrace : WordTrace (prefixWord ++ tailWord_492989) baseStart_492989 baseEnd_492989 := by
    simpa [prefixWord, tailWord_492989, baseEnd_492989] using wordTrace_append hprefix tailTrace_492989
  have hstable : (prefixWord ++ tailWord_492989).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492989).length < 2 ^ (prefixWord ++ tailWord_492989).sum := by decide
  have hdescent : baseEnd_492989 < baseStart_492989 := by decide
  rcases family_descends (prefixWord ++ tailWord_492989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492996 : List Nat := [2, 3, 3, 2, 1, 1, 3, 5]
def baseStart_492996 : Nat := 118140960795 + 492996 * 2 ^ 59
def prefixEnd_492996 : Nat := 4983230072969 + 3 ^ 40 * 492996 * 2
def baseEnd_492996 : Nat := 75005602590832113950447

theorem tailTrace_492996 : CollatzResearch.WordTrace tailWord_492996 prefixEnd_492996 75005602590832113950447 := by
  unfold tailWord_492996
  simp only [CollatzResearch.WordTrace]
  refine ⟨8990520660983581929321421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11987360881311442572428561 8990520660983581929321421)
  ·
    refine ⟨3371445247868843223495533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8990520660983581929321421 3371445247868843223495533)
    ·
      refine ⟨1264291967950816208810825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3371445247868843223495533 1264291967950816208810825)
      ·
        refine ⟨948218975963112156608119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1264291967950816208810825 948218975963112156608119)
        ·
          refine ⟨1422328463944668234912179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 948218975963112156608119 1422328463944668234912179)
          ·
            refine ⟨2133492695917002352368269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1422328463944668234912179 2133492695917002352368269)
            ·
              refine ⟨800059760968875882138101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2133492695917002352368269 800059760968875882138101)
              ·
                refine ⟨75005602590832113950447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 800059760968875882138101 75005602590832113950447)
                ·
                  rfl

theorem cell20_492996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 3, 5].length) (baseStart_492996 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_492996 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_492996 prefixEnd_492996 := by exact prefixLift 492996
  have htrace : WordTrace (prefixWord ++ tailWord_492996) baseStart_492996 baseEnd_492996 := by
    simpa [prefixWord, tailWord_492996, baseEnd_492996] using wordTrace_append hprefix tailTrace_492996
  have hstable : (prefixWord ++ tailWord_492996).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492996).length < 2 ^ (prefixWord ++ tailWord_492996).sum := by decide
  have hdescent : baseEnd_492996 < baseStart_492996 := by decide
  rcases family_descends (prefixWord ++ tailWord_492996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
