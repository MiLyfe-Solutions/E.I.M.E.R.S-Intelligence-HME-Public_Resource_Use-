import V185TrunkScan21Chunk043

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_532515 : List Nat := [1, 1, 1, 4, 3, 1, 1, 1, 8]
def baseStart_532515 : Nat := 118140960795 + 532515 * 2 ^ 59
def prefixEnd_532515 : Nat := 4983230072969 + 3 ^ 40 * 532515 * 2
def baseEnd_532515 : Nat := 121527178101817451694895

theorem tailTrace_532515 : CollatzResearch.WordTrace tailWord_532515 prefixEnd_532515 121527178101817451694895 := by
  unfold tailWord_532515
  simp only [CollatzResearch.WordTrace]
  refine ⟨19422417665796576166502999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12948278443864384111001999 19422417665796576166502999)
  ·
    refine ⟨29133626498694864249754499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19422417665796576166502999 29133626498694864249754499)
    ·
      refine ⟨43700439748042296374631749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29133626498694864249754499 43700439748042296374631749)
      ·
        refine ⟨8193832452757930570243453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43700439748042296374631749 8193832452757930570243453)
        ·
          refine ⟨3072687169784223963841295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8193832452757930570243453 3072687169784223963841295)
          ·
            refine ⟨4609030754676335945761943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3072687169784223963841295 4609030754676335945761943)
            ·
              refine ⟨6913546132014503918642915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4609030754676335945761943 6913546132014503918642915)
              ·
                refine ⟨10370319198021755877964373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6913546132014503918642915 10370319198021755877964373)
                ·
                  refine ⟨121527178101817451694895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10370319198021755877964373 121527178101817451694895)
                  ·
                    rfl

theorem cell21_532515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 1, 8].length) (baseStart_532515 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_532515 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_532515 prefixEnd_532515 := by exact prefixLift 532515
  have htrace : WordTrace (prefixWord ++ tailWord_532515) baseStart_532515 baseEnd_532515 := by
    simpa [prefixWord, tailWord_532515, baseEnd_532515] using wordTrace_append hprefix tailTrace_532515
  have hstable : (prefixWord ++ tailWord_532515).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532515).length < 2 ^ (prefixWord ++ tailWord_532515).sum := by decide
  have hdescent : baseEnd_532515 < baseStart_532515 := by decide
  rcases family_descends (prefixWord ++ tailWord_532515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532642 : List Nat := [3, 3, 1, 3, 1, 3, 1, 2, 4]
def baseStart_532642 : Nat := 118140960795 + 532642 * 2 ^ 59
def prefixEnd_532642 : Nat := 4983230072969 + 3 ^ 40 * 532642 * 2
def baseEnd_532642 : Nat := 121556161232093453077969

theorem tailTrace_532642 : CollatzResearch.WordTrace tailWord_532642 prefixEnd_532642 121556161232093453077969 := by
  unfold tailWord_532642
  simp only [CollatzResearch.WordTrace]
  refine ⟨4856762434084119214094045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12951366490890984570917453 4856762434084119214094045)
  ·
    refine ⟨1821285912781544705285267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4856762434084119214094045 1821285912781544705285267)
    ·
      refine ⟨2731928869172317057927901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1821285912781544705285267 2731928869172317057927901)
      ·
        refine ⟨1024473325939618896722963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2731928869172317057927901 1024473325939618896722963)
        ·
          refine ⟨1536709988909428345084445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1024473325939618896722963 1536709988909428345084445)
          ·
            refine ⟨576266245841035629406667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1536709988909428345084445 576266245841035629406667)
            ·
              refine ⟨864399368761553444110001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 576266245841035629406667 864399368761553444110001)
              ·
                refine ⟨648299526571165083082501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 864399368761553444110001 648299526571165083082501)
                ·
                  refine ⟨121556161232093453077969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 648299526571165083082501 121556161232093453077969)
                  ·
                    rfl

theorem cell21_532642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 1, 2, 4].length) (baseStart_532642 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_532642 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_532642 prefixEnd_532642 := by exact prefixLift 532642
  have htrace : WordTrace (prefixWord ++ tailWord_532642) baseStart_532642 baseEnd_532642 := by
    simpa [prefixWord, tailWord_532642, baseEnd_532642] using wordTrace_append hprefix tailTrace_532642
  have hstable : (prefixWord ++ tailWord_532642).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532642).length < 2 ^ (prefixWord ++ tailWord_532642).sum := by decide
  have hdescent : baseEnd_532642 < baseStart_532642 := by decide
  rcases family_descends (prefixWord ++ tailWord_532642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532673 : List Nat := [1, 2, 6, 1, 2, 2, 2, 5]
def baseStart_532673 : Nat := 118140960795 + 532673 * 2 ^ 59
def prefixEnd_532673 : Nat := 4983230072969 + 3 ^ 40 * 532673 * 2
def baseEnd_532673 : Nat := 40521078618148096020413

theorem tailTrace_532673 : CollatzResearch.WordTrace tailWord_532673 prefixEnd_532673 40521078618148096020413 := by
  unfold tailWord_532673
  simp only [CollatzResearch.WordTrace]
  refine ⟨19428180399224169150754673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12952120266149446100503115 19428180399224169150754673)
  ·
    refine ⟨14571135299418126863066005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19428180399224169150754673 14571135299418126863066005)
    ·
      refine ⟨683021967160224696706219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 14571135299418126863066005 683021967160224696706219)
      ·
        refine ⟨1024532950740337045059329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 683021967160224696706219 1024532950740337045059329)
        ·
          refine ⟨768399713055252783794497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1024532950740337045059329 768399713055252783794497)
          ·
            refine ⟨576299784791439587845873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 768399713055252783794497 576299784791439587845873)
            ·
              refine ⟨432224838593579690884405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 576299784791439587845873 432224838593579690884405)
              ·
                refine ⟨40521078618148096020413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 432224838593579690884405 40521078618148096020413)
                ·
                  rfl

theorem cell21_532673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 2, 5].length) (baseStart_532673 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_532673 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_532673 prefixEnd_532673 := by exact prefixLift 532673
  have htrace : WordTrace (prefixWord ++ tailWord_532673) baseStart_532673 baseEnd_532673 := by
    simpa [prefixWord, tailWord_532673, baseEnd_532673] using wordTrace_append hprefix tailTrace_532673
  have hstable : (prefixWord ++ tailWord_532673).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532673).length < 2 ^ (prefixWord ++ tailWord_532673).sum := by decide
  have hdescent : baseEnd_532673 < baseStart_532673 := by decide
  rcases family_descends (prefixWord ++ tailWord_532673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532760 : List Nat := [2, 1, 2, 3, 1, 2, 4, 2, 4]
def baseStart_532760 : Nat := 118140960795 + 532760 * 2 ^ 59
def prefixEnd_532760 : Nat := 4983230072969 + 3 ^ 40 * 532760 * 2
def baseEnd_532760 : Nat := 121583090439751470111061

theorem tailTrace_532760 : CollatzResearch.WordTrace tailWord_532760 prefixEnd_532760 121583090439751470111061 := by
  unfold tailWord_532760
  simp only [CollatzResearch.WordTrace]
  refine ⟨9715676774954491504585867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12954235699939322006114489 9715676774954491504585867)
  ·
    refine ⟨14573515162431737256878801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9715676774954491504585867 14573515162431737256878801)
    ·
      refine ⟨10930136371823802942659101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14573515162431737256878801 10930136371823802942659101)
      ·
        refine ⟨4098801139433926103497163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10930136371823802942659101 4098801139433926103497163)
        ·
          refine ⟨6148201709150889155245745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4098801139433926103497163 6148201709150889155245745)
          ·
            refine ⟨4611151281863166866434309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6148201709150889155245745 4611151281863166866434309)
            ·
              refine ⟨864590865349343787456433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4611151281863166866434309 864590865349343787456433)
              ·
                refine ⟨648443149012007840592325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 864590865349343787456433 648443149012007840592325)
                ·
                  refine ⟨121583090439751470111061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 648443149012007840592325 121583090439751470111061)
                  ·
                    rfl

theorem cell21_532760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 4, 2, 4].length) (baseStart_532760 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_532760 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_532760 prefixEnd_532760 := by exact prefixLift 532760
  have htrace : WordTrace (prefixWord ++ tailWord_532760) baseStart_532760 baseEnd_532760 := by
    simpa [prefixWord, tailWord_532760, baseEnd_532760] using wordTrace_append hprefix tailTrace_532760
  have hstable : (prefixWord ++ tailWord_532760).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532760).length < 2 ^ (prefixWord ++ tailWord_532760).sum := by decide
  have hdescent : baseEnd_532760 < baseStart_532760 := by decide
  rcases family_descends (prefixWord ++ tailWord_532760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532819 : List Nat := [1, 1, 1, 2, 1, 1, 4, 6, 4]
def baseStart_532819 : Nat := 118140960795 + 532819 * 2 ^ 59
def prefixEnd_532819 : Nat := 4983230072969 + 3 ^ 40 * 532819 * 2
def baseEnd_532819 : Nat := 121596555043580478627607

theorem tailTrace_532819 : CollatzResearch.WordTrace tailWord_532819 prefixEnd_532819 121596555043580478627607 := by
  unfold tailWord_532819
  simp only [CollatzResearch.WordTrace]
  refine ⟨19433505456695236085569511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12955670304463490723713007 19433505456695236085569511)
  ·
    refine ⟨29150258185042854128354267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19433505456695236085569511 29150258185042854128354267)
    ·
      refine ⟨43725387277564281192531401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29150258185042854128354267 43725387277564281192531401)
      ·
        refine ⟨32794040458173210894398551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43725387277564281192531401 32794040458173210894398551)
        ·
          refine ⟨49191060687259816341597827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32794040458173210894398551 49191060687259816341597827)
          ·
            refine ⟨73786591030889724512396741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49191060687259816341597827 73786591030889724512396741)
            ·
              refine ⟨13834985818291823346074389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 73786591030889724512396741 13834985818291823346074389)
              ·
                refine ⟨648514960232429219347237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 13834985818291823346074389 648514960232429219347237)
                ·
                  refine ⟨121596555043580478627607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 648514960232429219347237 121596555043580478627607)
                  ·
                    rfl

theorem cell21_532819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 6, 4].length) (baseStart_532819 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_532819 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_532819 prefixEnd_532819 := by exact prefixLift 532819
  have htrace : WordTrace (prefixWord ++ tailWord_532819) baseStart_532819 baseEnd_532819 := by
    simpa [prefixWord, tailWord_532819, baseEnd_532819] using wordTrace_append hprefix tailTrace_532819
  have hstable : (prefixWord ++ tailWord_532819).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532819).length < 2 ^ (prefixWord ++ tailWord_532819).sum := by decide
  have hdescent : baseEnd_532819 < baseStart_532819 := by decide
  rcases family_descends (prefixWord ++ tailWord_532819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532850 : List Nat := [3, 2, 1, 2, 1, 4, 1, 7]
def baseStart_532850 : Nat := 118140960795 + 532850 * 2 ^ 59
def prefixEnd_532850 : Nat := 4983230072969 + 3 ^ 40 * 532850 * 2
def baseEnd_532850 : Nat := 40534543221977104536959

theorem tailTrace_532850 : CollatzResearch.WordTrace tailWord_532850 prefixEnd_532850 40534543221977104536959 := by
  unfold tailWord_532850
  simp only [CollatzResearch.WordTrace]
  refine ⟨4858659029895732094987001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12956424079721952253298669 4858659029895732094987001)
  ·
    refine ⟨3643994272421799071240251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4858659029895732094987001 3643994272421799071240251)
    ·
      refine ⟨5465991408632698606860377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3643994272421799071240251 5465991408632698606860377)
      ·
        refine ⟨4099493556474523955145283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5465991408632698606860377 4099493556474523955145283)
        ·
          refine ⟨6149240334711785932717925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4099493556474523955145283 6149240334711785932717925)
          ·
            refine ⟨1152982562758459862384611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6149240334711785932717925 1152982562758459862384611)
            ·
              refine ⟨1729473844137689793576917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1152982562758459862384611 1729473844137689793576917)
              ·
                refine ⟨40534543221977104536959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1729473844137689793576917 40534543221977104536959)
                ·
                  rfl

theorem cell21_532850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 7].length) (baseStart_532850 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_532850 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_532850 prefixEnd_532850 := by exact prefixLift 532850
  have htrace : WordTrace (prefixWord ++ tailWord_532850) baseStart_532850 baseEnd_532850 := by
    simpa [prefixWord, tailWord_532850, baseEnd_532850] using wordTrace_append hprefix tailTrace_532850
  have hstable : (prefixWord ++ tailWord_532850).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532850).length < 2 ^ (prefixWord ++ tailWord_532850).sum := by decide
  have hdescent : baseEnd_532850 < baseStart_532850 := by decide
  rcases family_descends (prefixWord ++ tailWord_532850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532867 : List Nat := [1, 1, 1, 3, 7, 1, 7]
def baseStart_532867 : Nat := 118140960795 + 532867 * 2 ^ 59
def prefixEnd_532867 : Nat := 4983230072969 + 3 ^ 40 * 532867 * 2
def baseEnd_532867 : Nat := 13511945477504784647501

theorem tailTrace_532867 : CollatzResearch.WordTrace tailWord_532867 prefixEnd_532867 13511945477504784647501 := by
  unfold tailWord_532867
  simp only [CollatzResearch.WordTrace]
  refine ⟨19435256160521340283316855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12956837440347560188877903 19435256160521340283316855)
  ·
    refine ⟨29152884240782010424975283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19435256160521340283316855 29152884240782010424975283)
    ·
      refine ⟨43729326361173015637462925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29152884240782010424975283 43729326361173015637462925)
      ·
        refine ⟨16398497385439880864048597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43729326361173015637462925 16398497385439880864048597)
        ·
          refine ⟨384339782471247207751139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 16398497385439880864048597 384339782471247207751139)
          ·
            refine ⟨576509673706870811626709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 384339782471247207751139 576509673706870811626709)
            ·
              refine ⟨13511945477504784647501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 576509673706870811626709 13511945477504784647501)
              ·
                rfl

theorem cell21_532867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 7].length) (baseStart_532867 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_532867 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_532867 prefixEnd_532867 := by exact prefixLift 532867
  have htrace : WordTrace (prefixWord ++ tailWord_532867) baseStart_532867 baseEnd_532867 := by
    simpa [prefixWord, tailWord_532867, baseEnd_532867] using wordTrace_append hprefix tailTrace_532867
  have hstable : (prefixWord ++ tailWord_532867).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532867).length < 2 ^ (prefixWord ++ tailWord_532867).sum := by decide
  have hdescent : baseEnd_532867 < baseStart_532867 := by decide
  rcases family_descends (prefixWord ++ tailWord_532867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532957 : List Nat := [1, 4, 3, 1, 1, 1, 3, 2, 5]
def baseStart_532957 : Nat := 118140960795 + 532957 * 2 ^ 59
def prefixEnd_532957 : Nat := 4983230072969 + 3 ^ 40 * 532957 * 2
def baseEnd_532957 : Nat := 121628048523722905327325

theorem tailTrace_532957 : CollatzResearch.WordTrace tailWord_532957 prefixEnd_532957 121628048523722905327325 := by
  unfold tailWord_532957
  simp only [CollatzResearch.WordTrace]
  refine ⟨19438538730195285654093125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12959025820130190436062083 19438538730195285654093125)
  ·
    refine ⟨3644726011911616060142461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19438538730195285654093125 3644726011911616060142461)
    ·
      refine ⟨1366772254466856022553423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3644726011911616060142461 1366772254466856022553423)
      ·
        refine ⟨2050158381700284033830135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1366772254466856022553423 2050158381700284033830135)
        ·
          refine ⟨3075237572550426050745203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2050158381700284033830135 3075237572550426050745203)
          ·
            refine ⟨4612856358825639076117805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3075237572550426050745203 4612856358825639076117805)
            ·
              refine ⟨1729821134559614653544177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4612856358825639076117805 1729821134559614653544177)
              ·
                refine ⟨1297365850919710990158133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1729821134559614653544177 1297365850919710990158133)
                ·
                  refine ⟨121628048523722905327325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1297365850919710990158133 121628048523722905327325)
                  ·
                    rfl

theorem cell21_532957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 2, 5].length) (baseStart_532957 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_532957 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_532957 prefixEnd_532957 := by exact prefixLift 532957
  have htrace : WordTrace (prefixWord ++ tailWord_532957) baseStart_532957 baseEnd_532957 := by
    simpa [prefixWord, tailWord_532957, baseEnd_532957] using wordTrace_append hprefix tailTrace_532957
  have hstable : (prefixWord ++ tailWord_532957).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532957).length < 2 ^ (prefixWord ++ tailWord_532957).sum := by decide
  have hdescent : baseEnd_532957 < baseStart_532957 := by decide
  rcases family_descends (prefixWord ++ tailWord_532957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532974 : List Nat := [4, 1, 2, 1, 2, 2, 1, 5, 3]
def baseStart_532974 : Nat := 118140960795 + 532974 * 2 ^ 59
def prefixEnd_532974 : Nat := 4983230072969 + 3 ^ 40 * 532974 * 2
def baseEnd_532974 : Nat := 121631928155334653543957

theorem tailTrace_532974 : CollatzResearch.WordTrace tailWord_532974 prefixEnd_532974 121631928155334653543957 := by
  unfold tailWord_532974
  simp only [CollatzResearch.WordTrace]
  refine ⟨2429894846391712194682747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12959439180755798371641317 2429894846391712194682747)
  ·
    refine ⟨3644842269587568292024121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2429894846391712194682747 3644842269587568292024121)
    ·
      refine ⟨2733631702190676219018091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3644842269587568292024121 2733631702190676219018091)
      ·
        refine ⟨4100447553286014328527137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2733631702190676219018091 4100447553286014328527137)
        ·
          refine ⟨3075335664964510746395353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4100447553286014328527137 3075335664964510746395353)
          ·
            refine ⟨2306501748723383059796515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3075335664964510746395353 2306501748723383059796515)
            ·
              refine ⟨3459752623085074589694773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2306501748723383059796515 3459752623085074589694773)
              ·
                refine ⟨324351808414225742783885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3459752623085074589694773 324351808414225742783885)
                ·
                  refine ⟨121631928155334653543957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 324351808414225742783885 121631928155334653543957)
                  ·
                    rfl

theorem cell21_532974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 5, 3].length) (baseStart_532974 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_532974 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_532974 prefixEnd_532974 := by exact prefixLift 532974
  have htrace : WordTrace (prefixWord ++ tailWord_532974) baseStart_532974 baseEnd_532974 := by
    simpa [prefixWord, tailWord_532974, baseEnd_532974] using wordTrace_append hprefix tailTrace_532974
  have hstable : (prefixWord ++ tailWord_532974).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532974).length < 2 ^ (prefixWord ++ tailWord_532974).sum := by decide
  have hdescent : baseEnd_532974 < baseStart_532974 := by decide
  rcases family_descends (prefixWord ++ tailWord_532974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533047 : List Nat := [1, 1, 3, 1, 2, 3, 2, 4, 4]
def baseStart_533047 : Nat := 118140960795 + 533047 * 2 ^ 59
def prefixEnd_533047 : Nat := 4983230072969 + 3 ^ 40 * 533047 * 2
def baseEnd_533047 : Nat := 121648587749902748827141

theorem tailTrace_533047 : CollatzResearch.WordTrace tailWord_533047 prefixEnd_533047 121648587749902748827141 := by
  unfold tailWord_533047
  simp only [CollatzResearch.WordTrace]
  refine ⟨19441821299869231024869395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12961214199912820683246263 19441821299869231024869395)
  ·
    refine ⟨29162731949803846537304093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19441821299869231024869395 29162731949803846537304093)
    ·
      refine ⟨10936024481176442451489035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29162731949803846537304093 10936024481176442451489035)
      ·
        refine ⟨16404036721764663677233553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10936024481176442451489035 16404036721764663677233553)
        ·
          refine ⟨12303027541323497757925165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16404036721764663677233553 12303027541323497757925165)
          ·
            refine ⟨4613635327996311659221937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12303027541323497757925165 4613635327996311659221937)
            ·
              refine ⟨3460226495997233744416453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4613635327996311659221937 3460226495997233744416453)
              ·
                refine ⟨648792467999481327078085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3460226495997233744416453 648792467999481327078085)
                ·
                  refine ⟨121648587749902748827141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 648792467999481327078085 121648587749902748827141)
                  ·
                    rfl

theorem cell21_533047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 4, 4].length) (baseStart_533047 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_533047 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_533047 prefixEnd_533047 := by exact prefixLift 533047
  have htrace : WordTrace (prefixWord ++ tailWord_533047) baseStart_533047 baseEnd_533047 := by
    simpa [prefixWord, tailWord_533047, baseEnd_533047] using wordTrace_append hprefix tailTrace_533047
  have hstable : (prefixWord ++ tailWord_533047).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533047).length < 2 ^ (prefixWord ++ tailWord_533047).sum := by decide
  have hdescent : baseEnd_533047 < baseStart_533047 := by decide
  rcases family_descends (prefixWord ++ tailWord_533047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533061 : List Nat := [1, 3, 1, 1, 1, 5, 1, 8]
def baseStart_533061 : Nat := 118140960795 + 533061 * 2 ^ 59
def prefixEnd_533061 : Nat := 4983230072969 + 3 ^ 40 * 533061 * 2
def baseEnd_533061 : Nat := 40550594246880611864593

theorem tailTrace_533061 : CollatzResearch.WordTrace tailWord_533061 prefixEnd_533061 40550594246880611864593 := by
  unfold tailWord_533061
  simp only [CollatzResearch.WordTrace]
  refine ⟨19442331921818511415879037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12961554614545674277252691 19442331921818511415879037)
  ·
    refine ⟨7290874470681941780954639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19442331921818511415879037 7290874470681941780954639)
    ·
      refine ⟨10936311706022912671431959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7290874470681941780954639 10936311706022912671431959)
      ·
        refine ⟨16404467559034369007147939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10936311706022912671431959 16404467559034369007147939)
        ·
          refine ⟨24606701338551553510721909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16404467559034369007147939 24606701338551553510721909)
          ·
            refine ⟨2306878250489208141630179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 24606701338551553510721909 2306878250489208141630179)
            ·
              refine ⟨3460317375733812212445269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2306878250489208141630179 3460317375733812212445269)
              ·
                refine ⟨40550594246880611864593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3460317375733812212445269 40550594246880611864593)
                ·
                  rfl

theorem cell21_533061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 8].length) (baseStart_533061 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_533061 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_533061 prefixEnd_533061 := by exact prefixLift 533061
  have htrace : WordTrace (prefixWord ++ tailWord_533061) baseStart_533061 baseEnd_533061 := by
    simpa [prefixWord, tailWord_533061, baseEnd_533061] using wordTrace_append hprefix tailTrace_533061
  have hstable : (prefixWord ++ tailWord_533061).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533061).length < 2 ^ (prefixWord ++ tailWord_533061).sum := by decide
  have hdescent : baseEnd_533061 < baseStart_533061 := by decide
  rcases family_descends (prefixWord ++ tailWord_533061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533123 : List Nat := [1, 1, 1, 3, 3, 1, 4, 3, 4]
def baseStart_533123 : Nat := 118140960795 + 533123 * 2 ^ 59
def prefixEnd_533123 : Nat := 4983230072969 + 3 ^ 40 * 533123 * 2
def baseEnd_533123 : Nat := 121665931985343505560319

theorem tailTrace_533123 : CollatzResearch.WordTrace tailWord_533123 prefixEnd_533123 121665931985343505560319 := by
  unfold tailWord_533123
  simp only [CollatzResearch.WordTrace]
  refine ⟨19444593247593896004636023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12963062165062597336424015 19444593247593896004636023)
  ·
    refine ⟨29166889871390844006954035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19444593247593896004636023 29166889871390844006954035)
    ·
      refine ⟨43750334807086266010431053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29166889871390844006954035 43750334807086266010431053)
      ·
        refine ⟨16406375552657349753911645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43750334807086266010431053 16406375552657349753911645)
        ·
          refine ⟨6152390832246506157716867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16406375552657349753911645 6152390832246506157716867)
          ·
            refine ⟨9228586248369759236575301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6152390832246506157716867 9228586248369759236575301)
            ·
              refine ⟨1730359921569329856857869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9228586248369759236575301 1730359921569329856857869)
              ·
                refine ⟨648884970588498696321701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1730359921569329856857869 648884970588498696321701)
                ·
                  refine ⟨121665931985343505560319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 648884970588498696321701 121665931985343505560319)
                  ·
                    rfl

theorem cell21_533123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 3, 4].length) (baseStart_533123 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_533123 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_533123 prefixEnd_533123 := by exact prefixLift 533123
  have htrace : WordTrace (prefixWord ++ tailWord_533123) baseStart_533123 baseEnd_533123 := by
    simpa [prefixWord, tailWord_533123, baseEnd_533123] using wordTrace_append hprefix tailTrace_533123
  have hstable : (prefixWord ++ tailWord_533123).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533123).length < 2 ^ (prefixWord ++ tailWord_533123).sum := by decide
  have hdescent : baseEnd_533123 < baseStart_533123 := by decide
  rcases family_descends (prefixWord ++ tailWord_533123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533219 : List Nat := [1, 1, 1, 7, 1, 2, 3, 2, 3]
def baseStart_533219 : Nat := 118140960795 + 533219 * 2 ^ 59
def prefixEnd_533219 : Nat := 4983230072969 + 3 ^ 40 * 533219 * 2
def baseEnd_533219 : Nat := 121687840493268671960123

theorem tailTrace_533219 : CollatzResearch.WordTrace tailWord_533219 prefixEnd_533219 121687840493268671960123 := by
  unfold tailWord_533219
  simp only [CollatzResearch.WordTrace]
  refine ⟨19448094655246104400130711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12965396436830736266753807 19448094655246104400130711)
  ·
    refine ⟨29172141982869156600196067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19448094655246104400130711 29172141982869156600196067)
    ·
      refine ⟨43758212974303734900294101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29172141982869156600196067 43758212974303734900294101)
      ·
        refine ⟨1025583116585243786725643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 43758212974303734900294101 1025583116585243786725643)
        ·
          refine ⟨1538374674877865680088465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1025583116585243786725643 1538374674877865680088465)
          ·
            refine ⟨1153781006158399260066349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1538374674877865680088465 1153781006158399260066349)
            ·
              refine ⟨432667877309399722524881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1153781006158399260066349 432667877309399722524881)
              ·
                refine ⟨324500907982049791893661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 432667877309399722524881 324500907982049791893661)
                ·
                  refine ⟨121687840493268671960123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 324500907982049791893661 121687840493268671960123)
                  ·
                    rfl

theorem cell21_533219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 3, 2, 3].length) (baseStart_533219 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_533219 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_533219 prefixEnd_533219 := by exact prefixLift 533219
  have htrace : WordTrace (prefixWord ++ tailWord_533219) baseStart_533219 baseEnd_533219 := by
    simpa [prefixWord, tailWord_533219, baseEnd_533219] using wordTrace_append hprefix tailTrace_533219
  have hstable : (prefixWord ++ tailWord_533219).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533219).length < 2 ^ (prefixWord ++ tailWord_533219).sum := by decide
  have hdescent : baseEnd_533219 < baseStart_533219 := by decide
  rcases family_descends (prefixWord ++ tailWord_533219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533230 : List Nat := [4, 1, 2, 1, 1, 4, 2, 6]
def baseStart_533230 : Nat := 118140960795 + 533230 * 2 ^ 59
def prefixEnd_533230 : Nat := 4983230072969 + 3 ^ 40 * 533230 * 2
def baseEnd_533230 : Nat := 40563450281045032425589

theorem tailTrace_533230 : CollatzResearch.WordTrace tailWord_533230 prefixEnd_533230 40563450281045032425589 := by
  unfold tailWord_533230
  simp only [CollatzResearch.WordTrace]
  refine ⟨2431061982275781659847643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12965663905470835519187429 2431061982275781659847643)
  ·
    refine ⟨3646592973413672489771465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2431061982275781659847643 3646592973413672489771465)
    ·
      refine ⟨2734944730060254367328599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3646592973413672489771465 2734944730060254367328599)
      ·
        refine ⟨4102417095090381550992899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2734944730060254367328599 4102417095090381550992899)
        ·
          refine ⟨6153625642635572326489349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4102417095090381550992899 6153625642635572326489349)
          ·
            refine ⟨1153804807994169811216753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6153625642635572326489349 1153804807994169811216753)
            ·
              refine ⟨865353605995627358412565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1153804807994169811216753 865353605995627358412565)
              ·
                refine ⟨40563450281045032425589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 865353605995627358412565 40563450281045032425589)
                ·
                  rfl

theorem cell21_533230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 2, 6].length) (baseStart_533230 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_533230 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_533230 prefixEnd_533230 := by exact prefixLift 533230
  have htrace : WordTrace (prefixWord ++ tailWord_533230) baseStart_533230 baseEnd_533230 := by
    simpa [prefixWord, tailWord_533230, baseEnd_533230] using wordTrace_append hprefix tailTrace_533230
  have hstable : (prefixWord ++ tailWord_533230).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533230).length < 2 ^ (prefixWord ++ tailWord_533230).sum := by decide
  have hdescent : baseEnd_533230 < baseStart_533230 := by decide
  rcases family_descends (prefixWord ++ tailWord_533230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533337 : List Nat := [1, 2, 1, 2, 2, 4, 2, 4, 3]
def baseStart_533337 : Nat := 118140960795 + 533337 * 2 ^ 59
def prefixEnd_533337 : Nat := 4983230072969 + 3 ^ 40 * 533337 * 2
def baseEnd_533337 : Nat := 121714769700926688993215

theorem tailTrace_533337 : CollatzResearch.WordTrace tailWord_533337 prefixEnd_533337 121714769700926688993215 := by
  unfold tailWord_533337
  simp only [CollatzResearch.WordTrace]
  refine ⟨19452398468818610552926265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12968265645879073701950843 19452398468818610552926265)
  ·
    refine ⟨14589298851613957914694699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19452398468818610552926265 14589298851613957914694699)
    ·
      refine ⟨21883948277420936872042049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14589298851613957914694699 21883948277420936872042049)
      ·
        refine ⟨16412961208065702654031537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21883948277420936872042049 16412961208065702654031537)
        ·
          refine ⟨12309720906049276990523653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16412961208065702654031537 12309720906049276990523653)
          ·
            refine ⟨2308072669884239435723185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12309720906049276990523653 2308072669884239435723185)
            ·
              refine ⟨1731054502413179576792389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2308072669884239435723185 1731054502413179576792389)
              ·
                refine ⟨324572719202471170648573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1731054502413179576792389 324572719202471170648573)
                ·
                  refine ⟨121714769700926688993215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 324572719202471170648573 121714769700926688993215)
                  ·
                    rfl

theorem cell21_533337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 4, 3].length) (baseStart_533337 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_533337 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_533337 prefixEnd_533337 := by exact prefixLift 533337
  have htrace : WordTrace (prefixWord ++ tailWord_533337) baseStart_533337 baseEnd_533337 := by
    simpa [prefixWord, tailWord_533337, baseEnd_533337] using wordTrace_append hprefix tailTrace_533337
  have hstable : (prefixWord ++ tailWord_533337).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533337).length < 2 ^ (prefixWord ++ tailWord_533337).sum := by decide
  have hdescent : baseEnd_533337 < baseStart_533337 := by decide
  rcases family_descends (prefixWord ++ tailWord_533337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533402 : List Nat := [3, 1, 1, 4, 4, 1, 2, 1, 4]
def baseStart_533402 : Nat := 118140960795 + 533402 * 2 ^ 59
def prefixEnd_533402 : Nat := 4983230072969 + 3 ^ 40 * 533402 * 2
def baseEnd_533402 : Nat := 121729603586501020409749

theorem tailTrace_533402 : CollatzResearch.WordTrace tailWord_533402 prefixEnd_533402 121729603586501020409749 := by
  unfold tailWord_533402
  simp only [CollatzResearch.WordTrace]
  refine ⟨4863692303395781663510615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12969846142388751102694973 4863692303395781663510615)
  ·
    refine ⟨7295538455093672495265923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4863692303395781663510615 7295538455093672495265923)
    ·
      refine ⟨10943307682640508742898885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7295538455093672495265923 10943307682640508742898885)
      ·
        refine ⟨2051870190495095389293541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10943307682640508742898885 2051870190495095389293541)
        ·
          refine ⟨384725660717830385492539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2051870190495095389293541 384725660717830385492539)
          ·
            refine ⟨577088491076745578238809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 384725660717830385492539 577088491076745578238809)
            ·
              refine ⟨432816368307559183679107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 577088491076745578238809 432816368307559183679107)
              ·
                refine ⟨649224552461338775518661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 432816368307559183679107 649224552461338775518661)
                ·
                  refine ⟨121729603586501020409749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 649224552461338775518661 121729603586501020409749)
                  ·
                    rfl

theorem cell21_533402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 2, 1, 4].length) (baseStart_533402 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_533402 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_533402 prefixEnd_533402 := by exact prefixLift 533402
  have htrace : WordTrace (prefixWord ++ tailWord_533402) baseStart_533402 baseEnd_533402 := by
    simpa [prefixWord, tailWord_533402, baseEnd_533402] using wordTrace_append hprefix tailTrace_533402
  have hstable : (prefixWord ++ tailWord_533402).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533402).length < 2 ^ (prefixWord ++ tailWord_533402).sum := by decide
  have hdescent : baseEnd_533402 < baseStart_533402 := by decide
  rcases family_descends (prefixWord ++ tailWord_533402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533458 : List Nat := [3, 2, 2, 3, 1, 1, 3, 6]
def baseStart_533458 : Nat := 118140960795 + 533458 * 2 ^ 59
def prefixEnd_533458 : Nat := 4983230072969 + 3 ^ 40 * 533458 * 2
def baseEnd_533458 : Nat := 40580794516485789158767

theorem tailTrace_533458 : CollatzResearch.WordTrace tailWord_533458 prefixEnd_533458 40580794516485789158767 := by
  unfold tailWord_533458
  simp only [CollatzResearch.WordTrace]
  refine ⟨4864202925345062054520257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12971207800920165478720685 4864202925345062054520257)
  ·
    refine ⟨3648152194008796540890193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4864202925345062054520257 3648152194008796540890193)
    ·
      refine ⟨2736114145506597405667645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3648152194008796540890193 2736114145506597405667645)
      ·
        refine ⟨1026042804564974027125367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2736114145506597405667645 1026042804564974027125367)
        ·
          refine ⟨1539064206847461040688051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1026042804564974027125367 1539064206847461040688051)
          ·
            refine ⟨2308596310271191561032077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1539064206847461040688051 2308596310271191561032077)
            ·
              refine ⟨865723616351696835387029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2308596310271191561032077 865723616351696835387029)
              ·
                refine ⟨40580794516485789158767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 865723616351696835387029 40580794516485789158767)
                ·
                  rfl

theorem cell21_533458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 3, 6].length) (baseStart_533458 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_533458 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_533458 prefixEnd_533458 := by exact prefixLift 533458
  have htrace : WordTrace (prefixWord ++ tailWord_533458) baseStart_533458 baseEnd_533458 := by
    simpa [prefixWord, tailWord_533458, baseEnd_533458] using wordTrace_append hprefix tailTrace_533458
  have hstable : (prefixWord ++ tailWord_533458).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533458).length < 2 ^ (prefixWord ++ tailWord_533458).sum := by decide
  have hdescent : baseEnd_533458 < baseStart_533458 := by decide
  rcases family_descends (prefixWord ++ tailWord_533458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533489 : List Nat := [1, 2, 2, 2, 4, 1, 1, 5, 3]
def baseStart_533489 : Nat := 118140960795 + 533489 * 2 ^ 59
def prefixEnd_533489 : Nat := 4983230072969 + 3 ^ 40 * 533489 * 2
def baseEnd_533489 : Nat := 121749458171808202459571

theorem tailTrace_533489 : CollatzResearch.WordTrace tailWord_533489 prefixEnd_533489 121749458171808202459571 := by
  unfold tailWord_533489
  simp only [CollatzResearch.WordTrace]
  refine ⟨19457942364267940512459521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12971961576178627008306347 19457942364267940512459521)
  ·
    refine ⟨14593456773200955384344641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19457942364267940512459521 14593456773200955384344641)
    ·
      refine ⟨10945092579900716538258481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14593456773200955384344641 10945092579900716538258481)
      ·
        refine ⟨8208819434925537403693861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10945092579900716538258481 8208819434925537403693861)
        ·
          refine ⟨1539153644048538263192599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8208819434925537403693861 1539153644048538263192599)
          ·
            refine ⟨2308730466072807394788899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1539153644048538263192599 2308730466072807394788899)
            ·
              refine ⟨3463095699109211092183349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2308730466072807394788899 3463095699109211092183349)
              ·
                refine ⟨324665221791488539892189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3463095699109211092183349 324665221791488539892189)
                ·
                  refine ⟨121749458171808202459571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 324665221791488539892189 121749458171808202459571)
                  ·
                    rfl

theorem cell21_533489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 5, 3].length) (baseStart_533489 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_533489 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_533489 prefixEnd_533489 := by exact prefixLift 533489
  have htrace : WordTrace (prefixWord ++ tailWord_533489) baseStart_533489 baseEnd_533489 := by
    simpa [prefixWord, tailWord_533489, baseEnd_533489] using wordTrace_append hprefix tailTrace_533489
  have hstable : (prefixWord ++ tailWord_533489).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533489).length < 2 ^ (prefixWord ++ tailWord_533489).sum := by decide
  have hdescent : baseEnd_533489 < baseStart_533489 := by decide
  rcases family_descends (prefixWord ++ tailWord_533489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533562 : List Nat := [3, 1, 1, 1, 3, 1, 4, 1, 6]
def baseStart_533562 : Nat := 118140960795 + 533562 * 2 ^ 59
def prefixEnd_533562 : Nat := 4983230072969 + 3 ^ 40 * 533562 * 2
def baseEnd_533562 : Nat := 121766117766376297742755

theorem tailTrace_533562 : CollatzResearch.WordTrace tailWord_533562 prefixEnd_533562 121766117766376297742755 := by
  unfold tailWord_533562
  simp only [CollatzResearch.WordTrace]
  refine ⟨4865151223250868494966735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12973736595335649319911293 4865151223250868494966735)
  ·
    refine ⟨7297726834876302742450103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4865151223250868494966735 7297726834876302742450103)
    ·
      refine ⟨10946590252314454113675155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7297726834876302742450103 10946590252314454113675155)
      ·
        refine ⟨16419885378471681170512733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10946590252314454113675155 16419885378471681170512733)
        ·
          refine ⟨6157457016926880438942275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16419885378471681170512733 6157457016926880438942275)
          ·
            refine ⟨9236185525390320658413413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6157457016926880438942275 9236185525390320658413413)
            ·
              refine ⟨1731784786010685123452515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9236185525390320658413413 1731784786010685123452515)
              ·
                refine ⟨2597677179016027685178773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1731784786010685123452515 2597677179016027685178773)
                ·
                  refine ⟨121766117766376297742755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2597677179016027685178773 121766117766376297742755)
                  ·
                    rfl

theorem cell21_533562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 1, 6].length) (baseStart_533562 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_533562 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_533562 prefixEnd_533562 := by exact prefixLift 533562
  have htrace : WordTrace (prefixWord ++ tailWord_533562) baseStart_533562 baseEnd_533562 := by
    simpa [prefixWord, tailWord_533562, baseEnd_533562] using wordTrace_append hprefix tailTrace_533562
  have hstable : (prefixWord ++ tailWord_533562).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533562).length < 2 ^ (prefixWord ++ tailWord_533562).sum := by decide
  have hdescent : baseEnd_533562 < baseStart_533562 := by decide
  rcases family_descends (prefixWord ++ tailWord_533562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533565 : List Nat := [1, 4, 1, 3, 1, 4, 1, 1, 5]
def baseStart_533565 : Nat := 118140960795 + 533565 * 2 ^ 59
def prefixEnd_533565 : Nat := 4983230072969 + 3 ^ 40 * 533565 * 2
def baseEnd_533565 : Nat := 121766802407248959192749

theorem tailTrace_533565 : CollatzResearch.WordTrace tailWord_533565 prefixEnd_533565 121766802407248959192749 := by
  unfold tailWord_533565
  simp only [CollatzResearch.WordTrace]
  refine ⟨19460714311992605492226149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12973809541328403661484099 19460714311992605492226149)
  ·
    refine ⟨3648883933498613529792403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19460714311992605492226149 3648883933498613529792403)
    ·
      refine ⟨5473325900247920294688605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3648883933498613529792403 5473325900247920294688605)
      ·
        refine ⟨2052497212592970110508227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5473325900247920294688605 2052497212592970110508227)
        ·
          refine ⟨3078745818889455165762341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2052497212592970110508227 3078745818889455165762341)
          ·
            refine ⟨577264841041772843580439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3078745818889455165762341 577264841041772843580439)
            ·
              refine ⟨865897261562659265370659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 577264841041772843580439 865897261562659265370659)
              ·
                refine ⟨1298845892343988898055989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 865897261562659265370659 1298845892343988898055989)
                ·
                  refine ⟨121766802407248959192749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1298845892343988898055989 121766802407248959192749)
                  ·
                    rfl

theorem cell21_533565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 1, 1, 5].length) (baseStart_533565 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_533565 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_533565 prefixEnd_533565 := by exact prefixLift 533565
  have htrace : WordTrace (prefixWord ++ tailWord_533565) baseStart_533565 baseEnd_533565 := by
    simpa [prefixWord, tailWord_533565, baseEnd_533565] using wordTrace_append hprefix tailTrace_533565
  have hstable : (prefixWord ++ tailWord_533565).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533565).length < 2 ^ (prefixWord ++ tailWord_533565).sum := by decide
  have hdescent : baseEnd_533565 < baseStart_533565 := by decide
  rcases family_descends (prefixWord ++ tailWord_533565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533658 : List Nat := [3, 1, 1, 5, 1, 2, 2, 3, 3]
def baseStart_533658 : Nat := 118140960795 + 533658 * 2 ^ 59
def prefixEnd_533658 : Nat := 4983230072969 + 3 ^ 40 * 533658 * 2
def baseEnd_533658 : Nat := 121788026274301464142559

theorem tailTrace_533658 : CollatzResearch.WordTrace tailWord_533658 prefixEnd_533658 121788026274301464142559 := by
  unfold tailWord_533658
  simp only [CollatzResearch.WordTrace]
  refine ⟨4866026575163920593840407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12976070867103788250241085 4866026575163920593840407)
  ·
    refine ⟨7299039862745880890760611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4866026575163920593840407 7299039862745880890760611)
    ·
      refine ⟨10948559794118821336140917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7299039862745880890760611 10948559794118821336140917)
      ·
        refine ⟨1026427480698639500263211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10948559794118821336140917 1026427480698639500263211)
        ·
          refine ⟨1539641221047959250394817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1026427480698639500263211 1539641221047959250394817)
          ·
            refine ⟨1154730915785969437796113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1539641221047959250394817 1154730915785969437796113)
            ·
              refine ⟨866048186839477078347085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1154730915785969437796113 866048186839477078347085)
              ·
                refine ⟨324768070064803904380157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 866048186839477078347085 324768070064803904380157)
                ·
                  refine ⟨121788026274301464142559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 324768070064803904380157 121788026274301464142559)
                  ·
                    rfl

theorem cell21_533658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 2, 3, 3].length) (baseStart_533658 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_533658 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_533658 prefixEnd_533658 := by exact prefixLift 533658
  have htrace : WordTrace (prefixWord ++ tailWord_533658) baseStart_533658 baseEnd_533658 := by
    simpa [prefixWord, tailWord_533658, baseEnd_533658] using wordTrace_append hprefix tailTrace_533658
  have hstable : (prefixWord ++ tailWord_533658).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533658).length < 2 ^ (prefixWord ++ tailWord_533658).sum := by decide
  have hdescent : baseEnd_533658 < baseStart_533658 := by decide
  rcases family_descends (prefixWord ++ tailWord_533658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533683 : List Nat := [1, 1, 1, 2, 3, 2, 3, 3, 5]
def baseStart_533683 : Nat := 118140960795 + 533683 * 2 ^ 59
def prefixEnd_533683 : Nat := 4983230072969 + 3 ^ 40 * 533683 * 2
def baseEnd_533683 : Nat := 121793731614906976225841

theorem tailTrace_533683 : CollatzResearch.WordTrace tailWord_533683 prefixEnd_533683 121793731614906976225841 := by
  unfold tailWord_533683
  simp only [CollatzResearch.WordTrace]
  refine ⟨19465018125565111645021703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12976678750376741096681135 19465018125565111645021703)
  ·
    refine ⟨29197527188347667467532555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19465018125565111645021703 29197527188347667467532555)
    ·
      refine ⟨43796290782521501201298833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29197527188347667467532555 43796290782521501201298833)
      ·
        refine ⟨32847218086891125900974125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43796290782521501201298833 32847218086891125900974125)
        ·
          refine ⟨12317706782584172212865297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32847218086891125900974125 12317706782584172212865297)
          ·
            refine ⟨9238280086938129159648973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12317706782584172212865297 9238280086938129159648973)
            ·
              refine ⟨3464355032601798434868365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9238280086938129159648973 3464355032601798434868365)
              ·
                refine ⟨1299133137225674413075637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3464355032601798434868365 1299133137225674413075637)
                ·
                  refine ⟨121793731614906976225841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1299133137225674413075637 121793731614906976225841)
                  ·
                    rfl

theorem cell21_533683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 3, 5].length) (baseStart_533683 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_533683 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_533683 prefixEnd_533683 := by exact prefixLift 533683
  have htrace : WordTrace (prefixWord ++ tailWord_533683) baseStart_533683 baseEnd_533683 := by
    simpa [prefixWord, tailWord_533683, baseEnd_533683] using wordTrace_append hprefix tailTrace_533683
  have hstable : (prefixWord ++ tailWord_533683).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533683).length < 2 ^ (prefixWord ++ tailWord_533683).sum := by decide
  have hdescent : baseEnd_533683 < baseStart_533683 := by decide
  rcases family_descends (prefixWord ++ tailWord_533683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533709 : List Nat := [1, 6, 2, 2, 2, 1, 1, 3, 3]
def baseStart_533709 : Nat := 118140960795 + 533709 * 2 ^ 59
def prefixEnd_533709 : Nat := 4983230072969 + 3 ^ 40 * 533709 * 2
def baseEnd_533709 : Nat := 121799665169136708792455

theorem tailTrace_533709 : CollatzResearch.WordTrace tailWord_533709 prefixEnd_533709 121799665169136708792455 := by
  unfold tailWord_533709
  simp only [CollatzResearch.WordTrace]
  refine ⟨19465966423470918085468181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12977310948980612056978787 19465966423470918085468181)
  ·
    refine ⟨912467176100199285256321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 19465966423470918085468181 912467176100199285256321)
    ·
      refine ⟨684350382075149463942241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 912467176100199285256321 684350382075149463942241)
      ·
        refine ⟨513262786556362097956681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 684350382075149463942241 513262786556362097956681)
        ·
          refine ⟨384947089917271573467511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 513262786556362097956681 384947089917271573467511)
          ·
            refine ⟨577420634875907360201267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 384947089917271573467511 577420634875907360201267)
            ·
              refine ⟨866130952313861040301901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 577420634875907360201267 866130952313861040301901)
              ·
                refine ⟨324799107117697890113213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 866130952313861040301901 324799107117697890113213)
                ·
                  refine ⟨121799665169136708792455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 324799107117697890113213 121799665169136708792455)
                  ·
                    rfl

theorem cell21_533709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 1, 3, 3].length) (baseStart_533709 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_533709 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_533709 prefixEnd_533709 := by exact prefixLift 533709
  have htrace : WordTrace (prefixWord ++ tailWord_533709) baseStart_533709 baseEnd_533709 := by
    simpa [prefixWord, tailWord_533709, baseEnd_533709] using wordTrace_append hprefix tailTrace_533709
  have hstable : (prefixWord ++ tailWord_533709).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533709).length < 2 ^ (prefixWord ++ tailWord_533709).sum := by decide
  have hdescent : baseEnd_533709 < baseStart_533709 := by decide
  rcases family_descends (prefixWord ++ tailWord_533709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533714 : List Nat := [3, 2, 2, 2, 1, 1, 1, 1, 8]
def baseStart_533714 : Nat := 118140960795 + 533714 * 2 ^ 59
def prefixEnd_533714 : Nat := 4983230072969 + 3 ^ 40 * 533714 * 2
def baseEnd_533714 : Nat := 121800806237257811209111

theorem tailTrace_533714 : CollatzResearch.WordTrace tailWord_533714 prefixEnd_533714 121800806237257811209111 := by
  unfold tailWord_533714
  simp only [CollatzResearch.WordTrace]
  refine ⟨4866537197113200984850049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12977432525635202626266797 4866537197113200984850049)
  ·
    refine ⟨3649902897834900738637537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4866537197113200984850049 3649902897834900738637537)
    ·
      refine ⟨2737427173376175553978153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3649902897834900738637537 2737427173376175553978153)
      ·
        refine ⟨2053070380032131665483615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2737427173376175553978153 2053070380032131665483615)
        ·
          refine ⟨3079605570048197498225423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2053070380032131665483615 3079605570048197498225423)
          ·
            refine ⟨4619408355072296247338135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3079605570048197498225423 4619408355072296247338135)
            ·
              refine ⟨6929112532608444371007203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4619408355072296247338135 6929112532608444371007203)
              ·
                refine ⟨10393668798912666556510805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6929112532608444371007203 10393668798912666556510805)
                ·
                  refine ⟨121800806237257811209111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10393668798912666556510805 121800806237257811209111)
                  ·
                    rfl

theorem cell21_533714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 1, 8].length) (baseStart_533714 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_533714 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_533714 prefixEnd_533714 := by exact prefixLift 533714
  have htrace : WordTrace (prefixWord ++ tailWord_533714) baseStart_533714 baseEnd_533714 := by
    simpa [prefixWord, tailWord_533714, baseEnd_533714] using wordTrace_append hprefix tailTrace_533714
  have hstable : (prefixWord ++ tailWord_533714).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533714).length < 2 ^ (prefixWord ++ tailWord_533714).sum := by decide
  have hdescent : baseEnd_533714 < baseStart_533714 := by decide
  rcases family_descends (prefixWord ++ tailWord_533714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533728 : List Nat := [2, 1, 1, 3, 1, 4, 9]
def baseStart_533728 : Nat := 118140960795 + 533728 * 2 ^ 59
def prefixEnd_533728 : Nat := 4983230072969 + 3 ^ 40 * 533728 * 2
def baseEnd_533728 : Nat := 13533777914221877552861

theorem tailTrace_533728 : CollatzResearch.WordTrace tailWord_533728 prefixEnd_533728 13533777914221877552861 := by
  unfold tailWord_533728
  simp only [CollatzResearch.WordTrace]
  refine ⟨9733329705201042165204919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12977772940268056220273225 9733329705201042165204919)
  ·
    refine ⟨14599994557801563247807379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9733329705201042165204919 14599994557801563247807379)
    ·
      refine ⟨21899991836702344871711069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14599994557801563247807379 21899991836702344871711069)
      ·
        refine ⟨8212496938763379326891651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21899991836702344871711069 8212496938763379326891651)
        ·
          refine ⟨12318745408145068990337477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8212496938763379326891651 12318745408145068990337477)
          ·
            refine ⟨2309764764027200435688277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12318745408145068990337477 2309764764027200435688277)
            ·
              refine ⟨13533777914221877552861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2309764764027200435688277 13533777914221877552861)
              ·
                rfl

theorem cell21_533728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 9].length) (baseStart_533728 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_533728 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_533728 prefixEnd_533728 := by exact prefixLift 533728
  have htrace : WordTrace (prefixWord ++ tailWord_533728) baseStart_533728 baseEnd_533728 := by
    simpa [prefixWord, tailWord_533728, baseEnd_533728] using wordTrace_append hprefix tailTrace_533728
  have hstable : (prefixWord ++ tailWord_533728).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533728).length < 2 ^ (prefixWord ++ tailWord_533728).sum := by decide
  have hdescent : baseEnd_533728 < baseStart_533728 := by decide
  rcases family_descends (prefixWord ++ tailWord_533728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533897 : List Nat := [1, 2, 1, 1, 7, 2, 7]
def baseStart_533897 : Nat := 118140960795 + 533897 * 2 ^ 59
def prefixEnd_533897 : Nat := 4983230072969 + 3 ^ 40 * 533897 * 2
def baseEnd_533897 : Nat := 13538063258943351073193

theorem tailTrace_533897 : CollatzResearch.WordTrace tailWord_533897 prefixEnd_533897 13538063258943351073193 := by
  unfold tailWord_533897
  simp only [CollatzResearch.WordTrace]
  refine ⟨19472823346789826193311945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12981882231193217462207963 19472823346789826193311945)
  ·
    refine ⟨14604617510092369644983959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19472823346789826193311945 14604617510092369644983959)
    ·
      refine ⟨21906926265138554467475939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14604617510092369644983959 21906926265138554467475939)
      ·
        refine ⟨32860389397707831701213909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21906926265138554467475939 32860389397707831701213909)
        ·
          refine ⟨770165376508777305497201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 32860389397707831701213909 770165376508777305497201)
          ·
            refine ⟨577624032381582979122901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 770165376508777305497201 577624032381582979122901)
            ·
              refine ⟨13538063258943351073193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 577624032381582979122901 13538063258943351073193)
              ·
                rfl

theorem cell21_533897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 7].length) (baseStart_533897 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_533897 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_533897 prefixEnd_533897 := by exact prefixLift 533897
  have htrace : WordTrace (prefixWord ++ tailWord_533897) baseStart_533897 baseEnd_533897 := by
    simpa [prefixWord, tailWord_533897, baseEnd_533897] using wordTrace_append hprefix tailTrace_533897
  have hstable : (prefixWord ++ tailWord_533897).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533897).length < 2 ^ (prefixWord ++ tailWord_533897).sum := by decide
  have hdescent : baseEnd_533897 < baseStart_533897 := by decide
  rcases family_descends (prefixWord ++ tailWord_533897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533925 : List Nat := [1, 3, 1, 2, 1, 1, 2, 2, 8]
def baseStart_533925 : Nat := 118140960795 + 533925 * 2 ^ 59
def prefixEnd_533925 : Nat := 4983230072969 + 3 ^ 40 * 533925 * 2
def baseEnd_533925 : Nat := 121848959311968333192013

theorem tailTrace_533925 : CollatzResearch.WordTrace tailWord_533925 prefixEnd_533925 121848959311968333192013 := by
  unfold tailWord_533925
  simp only [CollatzResearch.WordTrace]
  refine ⟨19473844590688386975331229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12982563060458924650220819 19473844590688386975331229)
  ·
    refine ⟨7302691721508145115749211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19473844590688386975331229 7302691721508145115749211)
    ·
      refine ⟨10954037582262217673623817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7302691721508145115749211 10954037582262217673623817)
      ·
        refine ⟨8215528186696663255217863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10954037582262217673623817 8215528186696663255217863)
        ·
          refine ⟨12323292280044994882826795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8215528186696663255217863 12323292280044994882826795)
          ·
            refine ⟨18484938420067492324240193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12323292280044994882826795 18484938420067492324240193)
            ·
              refine ⟨13863703815050619243180145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18484938420067492324240193 13863703815050619243180145)
              ·
                refine ⟨10397777861287964432385109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13863703815050619243180145 10397777861287964432385109)
                ·
                  refine ⟨121848959311968333192013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10397777861287964432385109 121848959311968333192013)
                  ·
                    rfl

theorem cell21_533925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 2, 8].length) (baseStart_533925 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_533925 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_533925 prefixEnd_533925 := by exact prefixLift 533925
  have htrace : WordTrace (prefixWord ++ tailWord_533925) baseStart_533925 baseEnd_533925 := by
    simpa [prefixWord, tailWord_533925, baseEnd_533925] using wordTrace_append hprefix tailTrace_533925
  have hstable : (prefixWord ++ tailWord_533925).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533925).length < 2 ^ (prefixWord ++ tailWord_533925).sum := by decide
  have hdescent : baseEnd_533925 < baseStart_533925 := by decide
  rcases family_descends (prefixWord ++ tailWord_533925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533954 : List Nat := [3, 5, 2, 1, 1, 2, 2, 2, 3]
def baseStart_533954 : Nat := 118140960795 + 533954 * 2 ^ 59
def prefixEnd_533954 : Nat := 4983230072969 + 3 ^ 40 * 533954 * 2
def baseEnd_533954 : Nat := 121855577507070727208621

theorem tailTrace_533954 : CollatzResearch.WordTrace tailWord_533954 prefixEnd_533954 121855577507070727208621 := by
  unfold tailWord_533954
  simp only [CollatzResearch.WordTrace]
  refine ⟨4868725576895831232034229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12983268205055549952091277 4868725576895831232034229)
  ·
    refine ⟨456443022833984178003209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4868725576895831232034229 456443022833984178003209)
    ·
      refine ⟨342332267125488133502407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 456443022833984178003209 342332267125488133502407)
      ·
        refine ⟨513498400688232200253611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 342332267125488133502407 513498400688232200253611)
        ·
          refine ⟨770247601032348300380417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 513498400688232200253611 770247601032348300380417)
          ·
            refine ⟨577685700774261225285313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 770247601032348300380417 577685700774261225285313)
            ·
              refine ⟨433264275580695918963985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 577685700774261225285313 433264275580695918963985)
              ·
                refine ⟨324948206685521939222989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 433264275580695918963985 324948206685521939222989)
                ·
                  refine ⟨121855577507070727208621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 324948206685521939222989 121855577507070727208621)
                  ·
                    rfl

theorem cell21_533954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 2, 2, 3].length) (baseStart_533954 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_533954 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_533954 prefixEnd_533954 := by exact prefixLift 533954
  have htrace : WordTrace (prefixWord ++ tailWord_533954) baseStart_533954 baseEnd_533954 := by
    simpa [prefixWord, tailWord_533954, baseEnd_533954] using wordTrace_append hprefix tailTrace_533954
  have hstable : (prefixWord ++ tailWord_533954).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533954).length < 2 ^ (prefixWord ++ tailWord_533954).sum := by decide
  have hdescent : baseEnd_533954 < baseStart_533954 := by decide
  rcases family_descends (prefixWord ++ tailWord_533954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533962 : List Nat := [3, 1, 2, 1, 2, 5, 2, 2, 3]
def baseStart_533962 : Nat := 118140960795 + 533962 * 2 ^ 59
def prefixEnd_533962 : Nat := 4983230072969 + 3 ^ 40 * 533962 * 2
def baseEnd_533962 : Nat := 121857403216064491075271

theorem tailTrace_533962 : CollatzResearch.WordTrace tailWord_533962 prefixEnd_533962 121857403216064491075271 := by
  unfold tailWord_533962
  simp only [CollatzResearch.WordTrace]
  refine ⟨4868798522888585573607035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12983462727702894862952093 4868798522888585573607035)
  ·
    refine ⟨7303197784332878360410553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4868798522888585573607035 7303197784332878360410553)
    ·
      refine ⟨5477398338249658770307915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7303197784332878360410553 5477398338249658770307915)
      ·
        refine ⟨8216097507374488155461873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5477398338249658770307915 8216097507374488155461873)
        ·
          refine ⟨6162073130530866116596405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8216097507374488155461873 6162073130530866116596405)
          ·
            refine ⟨577694355987268698430913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6162073130530866116596405 577694355987268698430913)
            ·
              refine ⟨433270766990451523823185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 577694355987268698430913 433270766990451523823185)
              ·
                refine ⟨324953075242838642867389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 433270766990451523823185 324953075242838642867389)
                ·
                  refine ⟨121857403216064491075271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 324953075242838642867389 121857403216064491075271)
                  ·
                    rfl

theorem cell21_533962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 2, 2, 3].length) (baseStart_533962 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_533962 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_533962 prefixEnd_533962 := by exact prefixLift 533962
  have htrace : WordTrace (prefixWord ++ tailWord_533962) baseStart_533962 baseEnd_533962 := by
    simpa [prefixWord, tailWord_533962, baseEnd_533962] using wordTrace_append hprefix tailTrace_533962
  have hstable : (prefixWord ++ tailWord_533962).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533962).length < 2 ^ (prefixWord ++ tailWord_533962).sum := by decide
  have hdescent : baseEnd_533962 < baseStart_533962 := by decide
  rcases family_descends (prefixWord ++ tailWord_533962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533987 : List Nat := [1, 1, 1, 6, 2, 1, 1, 1, 7]
def baseStart_533987 : Nat := 118140960795 + 533987 * 2 ^ 59
def prefixEnd_533987 : Nat := 4983230072969 + 3 ^ 40 * 533987 * 2
def baseEnd_533987 : Nat := 121863108556670003158553

theorem tailTrace_533987 : CollatzResearch.WordTrace tailWord_533987 prefixEnd_533987 121863108556670003158553 := by
  unfold tailWord_533987
  simp only [CollatzResearch.WordTrace]
  refine ⟨19476105916463771564088215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12984070610975847709392143 19476105916463771564088215)
  ·
    refine ⟨29214158874695657346132323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19476105916463771564088215 29214158874695657346132323)
    ·
      refine ⟨43821238312043486019198485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29214158874695657346132323 43821238312043486019198485)
      ·
        refine ⟨2054120545877038407149929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 43821238312043486019198485 2054120545877038407149929)
        ·
          refine ⟨1540590409407778805362447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2054120545877038407149929 1540590409407778805362447)
          ·
            refine ⟨2310885614111668208043671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1540590409407778805362447 2310885614111668208043671)
            ·
              refine ⟨3466328421167502312065507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2310885614111668208043671 3466328421167502312065507)
              ·
                refine ⟨5199492631751253468098261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3466328421167502312065507 5199492631751253468098261)
                ·
                  refine ⟨121863108556670003158553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5199492631751253468098261 121863108556670003158553)
                  ·
                    rfl

theorem cell21_533987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 1, 7].length) (baseStart_533987 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_533987 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_533987 prefixEnd_533987 := by exact prefixLift 533987
  have htrace : WordTrace (prefixWord ++ tailWord_533987) baseStart_533987 baseEnd_533987 := by
    simpa [prefixWord, tailWord_533987, baseEnd_533987] using wordTrace_append hprefix tailTrace_533987
  have hstable : (prefixWord ++ tailWord_533987).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533987).length < 2 ^ (prefixWord ++ tailWord_533987).sum := by decide
  have hdescent : baseEnd_533987 < baseStart_533987 := by decide
  rcases family_descends (prefixWord ++ tailWord_533987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534035 : List Nat := [1, 1, 1, 2, 1, 7, 3, 1, 4]
def baseStart_534035 : Nat := 118140960795 + 534035 * 2 ^ 59
def prefixEnd_534035 : Nat := 4983230072969 + 3 ^ 40 * 534035 * 2
def baseEnd_534035 : Nat := 121874062810632586358455

theorem tailTrace_534035 : CollatzResearch.WordTrace tailWord_534035 prefixEnd_534035 121874062810632586358455 := by
  unfold tailWord_534035
  simp only [CollatzResearch.WordTrace]
  refine ⟨19477856620289875761835559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12985237746859917174557039 19477856620289875761835559)
  ·
    refine ⟨29216784930434813642753339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19477856620289875761835559 29216784930434813642753339)
    ·
      refine ⟨43825177395652220464130009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29216784930434813642753339 43825177395652220464130009)
      ·
        refine ⟨32868883046739165348097507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43825177395652220464130009 32868883046739165348097507)
        ·
          refine ⟨49303324570108748022146261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32868883046739165348097507 49303324570108748022146261)
          ·
            refine ⟨1155546669611923781769053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 49303324570108748022146261 1155546669611923781769053)
            ·
              refine ⟨433330001104471418163395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1155546669611923781769053 433330001104471418163395)
              ·
                refine ⟨649995001656707127245093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 433330001104471418163395 649995001656707127245093)
                ·
                  refine ⟨121874062810632586358455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 649995001656707127245093 121874062810632586358455)
                  ·
                    rfl

theorem cell21_534035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 3, 1, 4].length) (baseStart_534035 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_534035 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_534035 prefixEnd_534035 := by exact prefixLift 534035
  have htrace : WordTrace (prefixWord ++ tailWord_534035) baseStart_534035 baseEnd_534035 := by
    simpa [prefixWord, tailWord_534035, baseEnd_534035] using wordTrace_append hprefix tailTrace_534035
  have hstable : (prefixWord ++ tailWord_534035).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534035).length < 2 ^ (prefixWord ++ tailWord_534035).sum := by decide
  have hdescent : baseEnd_534035 < baseStart_534035 := by decide
  rcases family_descends (prefixWord ++ tailWord_534035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534049 : List Nat := [1, 2, 3, 2, 2, 2, 4, 5]
def baseStart_534049 : Nat := 118140960795 + 534049 * 2 ^ 59
def prefixEnd_534049 : Nat := 4983230072969 + 3 ^ 40 * 534049 * 2
def baseEnd_534049 : Nat := 40625752600457224375031

theorem tailTrace_534049 : CollatzResearch.WordTrace tailWord_534049 prefixEnd_534049 40625752600457224375031 := by
  unfold tailWord_534049
  simp only [CollatzResearch.WordTrace]
  refine ⟨19478367242239156152845201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12985578161492770768563467 19478367242239156152845201)
  ·
    refine ⟨14608775431679367114633901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19478367242239156152845201 14608775431679367114633901)
    ·
      refine ⟨5478290786879762667987713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14608775431679367114633901 5478290786879762667987713)
      ·
        refine ⟨4108718090159822000990785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5478290786879762667987713 4108718090159822000990785)
        ·
          refine ⟨3081538567619866500743089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4108718090159822000990785 3081538567619866500743089)
          ·
            refine ⟨2311153925714899875557317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3081538567619866500743089 2311153925714899875557317)
            ·
              refine ⟨433341361071543726666997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2311153925714899875557317 433341361071543726666997)
              ·
                refine ⟨40625752600457224375031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 433341361071543726666997 40625752600457224375031)
                ·
                  rfl

theorem cell21_534049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 4, 5].length) (baseStart_534049 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_534049 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_534049 prefixEnd_534049 := by exact prefixLift 534049
  have htrace : WordTrace (prefixWord ++ tailWord_534049) baseStart_534049 baseEnd_534049 := by
    simpa [prefixWord, tailWord_534049, baseEnd_534049] using wordTrace_append hprefix tailTrace_534049
  have hstable : (prefixWord ++ tailWord_534049).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534049).length < 2 ^ (prefixWord ++ tailWord_534049).sum := by decide
  have hdescent : baseEnd_534049 < baseStart_534049 := by decide
  rcases family_descends (prefixWord ++ tailWord_534049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534086 : List Nat := [6, 1, 1, 1, 3, 2, 2, 1, 4]
def baseStart_534086 : Nat := 118140960795 + 534086 * 2 ^ 59
def prefixEnd_534086 : Nat := 4983230072969 + 3 ^ 40 * 534086 * 2
def baseEnd_534086 : Nat := 121885701705467831008351

theorem tailTrace_534086 : CollatzResearch.WordTrace tailWord_534086 prefixEnd_534086 121885701705467831008351 := by
  unfold tailWord_534086
  simp only [CollatzResearch.WordTrace]
  refine ⟨608741148222034733498191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 12986477828736740981294741 608741148222034733498191)
  ·
    refine ⟨913111722333052100247287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 608741148222034733498191 913111722333052100247287)
    ·
      refine ⟨1369667583499578150370931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 913111722333052100247287 1369667583499578150370931)
      ·
        refine ⟨2054501375249367225556397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1369667583499578150370931 2054501375249367225556397)
        ·
          refine ⟨770438015718512709583649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2054501375249367225556397 770438015718512709583649)
          ·
            refine ⟨577828511788884532187737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 770438015718512709583649 577828511788884532187737)
            ·
              refine ⟨433371383841663399140803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 577828511788884532187737 433371383841663399140803)
              ·
                refine ⟨650057075762495098711205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 433371383841663399140803 650057075762495098711205)
                ·
                  refine ⟨121885701705467831008351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 650057075762495098711205 121885701705467831008351)
                  ·
                    rfl

theorem cell21_534086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 2, 1, 4].length) (baseStart_534086 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_534086 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_534086 prefixEnd_534086 := by exact prefixLift 534086
  have htrace : WordTrace (prefixWord ++ tailWord_534086) baseStart_534086 baseEnd_534086 := by
    simpa [prefixWord, tailWord_534086, baseEnd_534086] using wordTrace_append hprefix tailTrace_534086
  have hstable : (prefixWord ++ tailWord_534086).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534086).length < 2 ^ (prefixWord ++ tailWord_534086).sum := by decide
  have hdescent : baseEnd_534086 < baseStart_534086 := by decide
  rcases family_descends (prefixWord ++ tailWord_534086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534125 : List Nat := [1, 5, 1, 1, 5, 8]
def baseStart_534125 : Nat := 118140960795 + 534125 * 2 ^ 59
def prefixEnd_534125 : Nat := 4983230072969 + 3 ^ 40 * 534125 * 2
def baseEnd_534125 : Nat := 4514614890252312216973

theorem tailTrace_534125 : CollatzResearch.WordTrace tailWord_534125 prefixEnd_534125 4514614890252312216973 := by
  unfold tailWord_534125
  simp only [CollatzResearch.WordTrace]
  refine ⟨19481139189963821132611829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12987426126642547421741219 19481139189963821132611829)
  ·
    refine ⟨1826356799059108231182359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19481139189963821132611829 1826356799059108231182359)
    ·
      refine ⟨2739535198588662346773539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1826356799059108231182359 2739535198588662346773539)
      ·
        refine ⟨4109302797882993520160309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2739535198588662346773539 4109302797882993520160309)
        ·
          refine ⟨385247137301530642515029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4109302797882993520160309 385247137301530642515029)
          ·
            refine ⟨4514614890252312216973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 385247137301530642515029 4514614890252312216973)
            ·
              rfl

theorem cell21_534125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 8].length) (baseStart_534125 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_534125 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_534125 prefixEnd_534125 := by exact prefixLift 534125
  have htrace : WordTrace (prefixWord ++ tailWord_534125) baseStart_534125 baseEnd_534125 := by
    simpa [prefixWord, tailWord_534125, baseEnd_534125] using wordTrace_append hprefix tailTrace_534125
  have hstable : (prefixWord ++ tailWord_534125).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534125).length < 2 ^ (prefixWord ++ tailWord_534125).sum := by decide
  have hdescent : baseEnd_534125 < baseStart_534125 := by decide
  rcases family_descends (prefixWord ++ tailWord_534125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534218 : List Nat := [3, 1, 2, 1, 5, 2, 2, 5]
def baseStart_534218 : Nat := 118140960795 + 534218 * 2 ^ 59
def prefixEnd_534218 : Nat := 4983230072969 + 3 ^ 40 * 534218 * 2
def baseEnd_534218 : Nat := 40638608634621644936027

theorem tailTrace_534218 : CollatzResearch.WordTrace tailWord_534218 prefixEnd_534218 40638608634621644936027 := by
  unfold tailWord_534218
  simp only [CollatzResearch.WordTrace]
  refine ⟨4871132794656724503936827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12989687452417932010498205 4871132794656724503936827)
  ·
    refine ⟨7306699191985086755905241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4871132794656724503936827 7306699191985086755905241)
    ·
      refine ⟨5480024393988815066928931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7306699191985086755905241 5480024393988815066928931)
      ·
        refine ⟨8220036590983222600393397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5480024393988815066928931 8220036590983222600393397)
        ·
          refine ⟨770628430404677118786881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8220036590983222600393397 770628430404677118786881)
          ·
            refine ⟨577971322803507839090161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 770628430404677118786881 577971322803507839090161)
            ·
              refine ⟨433478492102630879317621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 577971322803507839090161 433478492102630879317621)
              ·
                refine ⟨40638608634621644936027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 433478492102630879317621 40638608634621644936027)
                ·
                  rfl

theorem cell21_534218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 2, 5].length) (baseStart_534218 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_534218 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_534218 prefixEnd_534218 := by exact prefixLift 534218
  have htrace : WordTrace (prefixWord ++ tailWord_534218) baseStart_534218 baseEnd_534218 := by
    simpa [prefixWord, tailWord_534218, baseEnd_534218] using wordTrace_append hprefix tailTrace_534218
  have hstable : (prefixWord ++ tailWord_534218).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534218).length < 2 ^ (prefixWord ++ tailWord_534218).sum := by decide
  have hdescent : baseEnd_534218 < baseStart_534218 := by decide
  rcases family_descends (prefixWord ++ tailWord_534218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534322 : List Nat := [3, 2, 1, 1, 3, 2, 2, 3, 4]
def baseStart_534322 : Nat := 118140960795 + 534322 * 2 ^ 59
def prefixEnd_534322 : Nat := 4983230072969 + 3 ^ 40 * 534322 * 2
def baseEnd_534322 : Nat := 121939560120783865074535

theorem tailTrace_534322 : CollatzResearch.WordTrace tailWord_534322 prefixEnd_534322 121939560120783865074535 := by
  unfold tailWord_534322
  simp only [CollatzResearch.WordTrace]
  refine ⟨4872081092562530944383305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12992216246833415851688813 4872081092562530944383305)
  ·
    refine ⟨3654060819421898208287479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4872081092562530944383305 3654060819421898208287479)
    ·
      refine ⟨5481091229132847312431219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3654060819421898208287479 5481091229132847312431219)
      ·
        refine ⟨8221636843699270968646829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5481091229132847312431219 8221636843699270968646829)
        ·
          refine ⟨3083113816387226613242561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8221636843699270968646829 3083113816387226613242561)
          ·
            refine ⟨2312335362290419959931921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3083113816387226613242561 2312335362290419959931921)
            ·
              refine ⟨1734251521717814969948941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2312335362290419959931921 1734251521717814969948941)
              ·
                refine ⟨650344320644180613730853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1734251521717814969948941 650344320644180613730853)
                ·
                  refine ⟨121939560120783865074535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 650344320644180613730853 121939560120783865074535)
                  ·
                    rfl

theorem cell21_534322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 3, 4].length) (baseStart_534322 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_534322 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_534322 prefixEnd_534322 := by exact prefixLift 534322
  have htrace : WordTrace (prefixWord ++ tailWord_534322) baseStart_534322 baseEnd_534322 := by
    simpa [prefixWord, tailWord_534322, baseEnd_534322] using wordTrace_append hprefix tailTrace_534322
  have hstable : (prefixWord ++ tailWord_534322).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534322).length < 2 ^ (prefixWord ++ tailWord_534322).sum := by decide
  have hdescent : baseEnd_534322 < baseStart_534322 := by decide
  rcases family_descends (prefixWord ++ tailWord_534322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534342 : List Nat := [6, 1, 1, 2, 1, 1, 1, 5, 3]
def baseStart_534342 : Nat := 118140960795 + 534342 * 2 ^ 59
def prefixEnd_534342 : Nat := 4983230072969 + 3 ^ 40 * 534342 * 2
def baseEnd_534342 : Nat := 121944124393268274741161

theorem tailTrace_534342 : CollatzResearch.WordTrace tailWord_534342 prefixEnd_534342 121944124393268274741161 := by
  unfold tailWord_534342
  simp only [CollatzResearch.WordTrace]
  refine ⟨609032932193052099789415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 12992702553451778128840853 609032932193052099789415)
  ·
    refine ⟨913549398289578149684123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 609032932193052099789415 913549398289578149684123)
    ·
      refine ⟨1370324097434367224526185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 913549398289578149684123 1370324097434367224526185)
      ·
        refine ⟨1027743073075775418394639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1370324097434367224526185 1027743073075775418394639)
        ·
          refine ⟨1541614609613663127591959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1027743073075775418394639 1541614609613663127591959)
          ·
            refine ⟨2312421914420494691387939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1541614609613663127591959 2312421914420494691387939)
            ·
              refine ⟨3468632871630742037081909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2312421914420494691387939 3468632871630742037081909)
              ·
                refine ⟨325184331715382065976429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3468632871630742037081909 325184331715382065976429)
                ·
                  refine ⟨121944124393268274741161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 325184331715382065976429 121944124393268274741161)
                  ·
                    rfl

theorem cell21_534342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 5, 3].length) (baseStart_534342 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_534342 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_534342 prefixEnd_534342 := by exact prefixLift 534342
  have htrace : WordTrace (prefixWord ++ tailWord_534342) baseStart_534342 baseEnd_534342 := by
    simpa [prefixWord, tailWord_534342, baseEnd_534342] using wordTrace_append hprefix tailTrace_534342
  have hstable : (prefixWord ++ tailWord_534342).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534342).length < 2 ^ (prefixWord ++ tailWord_534342).sum := by decide
  have hdescent : baseEnd_534342 < baseStart_534342 := by decide
  rcases family_descends (prefixWord ++ tailWord_534342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534367 : List Nat := [1, 1, 2, 3, 1, 5, 2, 1, 5]
def baseStart_534367 : Nat := 118140960795 + 534367 * 2 ^ 59
def prefixEnd_534367 : Nat := 4983230072969 + 3 ^ 40 * 534367 * 2
def baseEnd_534367 : Nat := 121949829733873786824443

theorem tailTrace_534367 : CollatzResearch.WordTrace tailWord_534367 prefixEnd_534367 121949829733873786824443 := by
  unfold tailWord_534367
  simp only [CollatzResearch.WordTrace]
  refine ⟨19489965655087096462921355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12993310436724730975280903 19489965655087096462921355)
  ·
    refine ⟨29234948482630644694382033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19489965655087096462921355 29234948482630644694382033)
    ·
      refine ⟨21926211361972983520786525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29234948482630644694382033 21926211361972983520786525)
      ·
        refine ⟨8222329260739868820294947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21926211361972983520786525 8222329260739868820294947)
        ·
          refine ⟨12333493891109803230442421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8222329260739868820294947 12333493891109803230442421)
          ·
            refine ⟨1156265052291544052853977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12333493891109803230442421 1156265052291544052853977)
            ·
              refine ⟨867198789218658039640483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1156265052291544052853977 867198789218658039640483)
              ·
                refine ⟨1300798183827987059460725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 867198789218658039640483 1300798183827987059460725)
                ·
                  refine ⟨121949829733873786824443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1300798183827987059460725 121949829733873786824443)
                  ·
                    rfl

theorem cell21_534367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 2, 1, 5].length) (baseStart_534367 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_534367 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_534367 prefixEnd_534367 := by exact prefixLift 534367
  have htrace : WordTrace (prefixWord ++ tailWord_534367) baseStart_534367 baseEnd_534367 := by
    simpa [prefixWord, tailWord_534367, baseEnd_534367] using wordTrace_append hprefix tailTrace_534367
  have hstable : (prefixWord ++ tailWord_534367).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534367).length < 2 ^ (prefixWord ++ tailWord_534367).sum := by decide
  have hdescent : baseEnd_534367 < baseStart_534367 := by decide
  rcases family_descends (prefixWord ++ tailWord_534367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534418 : List Nat := [3, 2, 3, 2, 1, 2, 3, 2, 3]
def baseStart_534418 : Nat := 118140960795 + 534418 * 2 ^ 59
def prefixEnd_534418 : Nat := 4983230072969 + 3 ^ 40 * 534418 * 2
def baseEnd_534418 : Nat := 121961468628709031474339

theorem tailTrace_534418 : CollatzResearch.WordTrace tailWord_534418 prefixEnd_534418 121961468628709031474339 := by
  unfold tailWord_534418
  simp only [CollatzResearch.WordTrace]
  refine ⟨4872956444475583043256977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12994550518601554782018605 4872956444475583043256977)
  ·
    refine ⟨3654717333356687282442733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4872956444475583043256977 3654717333356687282442733)
    ·
      refine ⟨1370519000008757730916025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3654717333356687282442733 1370519000008757730916025)
      ·
        refine ⟨1027889250006568298187019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1370519000008757730916025 1027889250006568298187019)
        ·
          refine ⟨1541833875009852447280529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1027889250006568298187019 1541833875009852447280529)
          ·
            refine ⟨1156375406257389335460397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1541833875009852447280529 1156375406257389335460397)
            ·
              refine ⟨433640777346521000797649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1156375406257389335460397 433640777346521000797649)
              ·
                refine ⟨325230583009890750598237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 433640777346521000797649 325230583009890750598237)
                ·
                  refine ⟨121961468628709031474339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 325230583009890750598237 121961468628709031474339)
                  ·
                    rfl

theorem cell21_534418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 3, 2, 3].length) (baseStart_534418 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_534418 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_534418 prefixEnd_534418 := by exact prefixLift 534418
  have htrace : WordTrace (prefixWord ++ tailWord_534418) baseStart_534418 baseEnd_534418 := by
    simpa [prefixWord, tailWord_534418, baseEnd_534418] using wordTrace_append hprefix tailTrace_534418
  have hstable : (prefixWord ++ tailWord_534418).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534418).length < 2 ^ (prefixWord ++ tailWord_534418).sum := by decide
  have hdescent : baseEnd_534418 < baseStart_534418 := by decide
  rcases family_descends (prefixWord ++ tailWord_534418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534533 : List Nat := [1, 3, 1, 1, 2, 5, 1, 1, 6]
def baseStart_534533 : Nat := 118140960795 + 534533 * 2 ^ 59
def prefixEnd_534533 : Nat := 4983230072969 + 3 ^ 40 * 534533 * 2
def baseEnd_534533 : Nat := 121987713195494387057437

theorem tailTrace_534533 : CollatzResearch.WordTrace tailWord_534533 prefixEnd_534533 121987713195494387057437 := by
  unfold tailWord_534533
  simp only [CollatzResearch.WordTrace]
  refine ⟨19496020172485706813464253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12997346781657137875642835 19496020172485706813464253)
  ·
    refine ⟨7311007564682140055049095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19496020172485706813464253 7311007564682140055049095)
    ·
      refine ⟨10966511347023210082573643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7311007564682140055049095 10966511347023210082573643)
      ·
        refine ⟨16449767020534815123860465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10966511347023210082573643 16449767020534815123860465)
        ·
          refine ⟨12337325265401111342895349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16449767020534815123860465 12337325265401111342895349)
          ·
            refine ⟨1156624243631354188396439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12337325265401111342895349 1156624243631354188396439)
            ·
              refine ⟨1734936365447031282594659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1156624243631354188396439 1734936365447031282594659)
              ·
                refine ⟨2602404548170546923891989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1734936365447031282594659 2602404548170546923891989)
                ·
                  refine ⟨121987713195494387057437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2602404548170546923891989 121987713195494387057437)
                  ·
                    rfl

theorem cell21_534533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 1, 6].length) (baseStart_534533 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_534533 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_534533 prefixEnd_534533 := by exact prefixLift 534533
  have htrace : WordTrace (prefixWord ++ tailWord_534533) baseStart_534533 baseEnd_534533 := by
    simpa [prefixWord, tailWord_534533, baseEnd_534533] using wordTrace_append hprefix tailTrace_534533
  have hstable : (prefixWord ++ tailWord_534533).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534533).length < 2 ^ (prefixWord ++ tailWord_534533).sum := by decide
  have hdescent : baseEnd_534533 < baseStart_534533 := by decide
  rcases family_descends (prefixWord ++ tailWord_534533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534646 : List Nat := [5, 1, 1, 2, 1, 4, 2, 2, 3]
def baseStart_534646 : Nat := 118140960795 + 534646 * 2 ^ 59
def prefixEnd_534646 : Nat := 4983230072969 + 3 ^ 40 * 534646 * 2
def baseEnd_534646 : Nat := 122013501335031301673873

theorem tailTrace_534646 : CollatzResearch.WordTrace tailWord_534646 prefixEnd_534646 122013501335031301673873 := by
  unfold tailWord_534646
  simp only [CollatzResearch.WordTrace]
  refine ⟨1218758851317270444520487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13000094414050884741551861 1218758851317270444520487)
  ·
    refine ⟨1828138276975905666780731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1218758851317270444520487 1828138276975905666780731)
    ·
      refine ⟨2742207415463858500171097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1828138276975905666780731 2742207415463858500171097)
      ·
        refine ⟨2056655561597893875128323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2742207415463858500171097 2056655561597893875128323)
        ·
          refine ⟨3084983342396840812692485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2056655561597893875128323 3084983342396840812692485)
          ·
            refine ⟨578434376699407652379841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3084983342396840812692485 578434376699407652379841)
            ·
              refine ⟨433825782524555739284881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 578434376699407652379841 433825782524555739284881)
              ·
                refine ⟨325369336893416804463661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 433825782524555739284881 325369336893416804463661)
                ·
                  refine ⟨122013501335031301673873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 325369336893416804463661 122013501335031301673873)
                  ·
                    rfl

theorem cell21_534646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 2, 2, 3].length) (baseStart_534646 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_534646 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_534646 prefixEnd_534646 := by exact prefixLift 534646
  have htrace : WordTrace (prefixWord ++ tailWord_534646) baseStart_534646 baseEnd_534646 := by
    simpa [prefixWord, tailWord_534646, baseEnd_534646] using wordTrace_append hprefix tailTrace_534646
  have hstable : (prefixWord ++ tailWord_534646).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534646).length < 2 ^ (prefixWord ++ tailWord_534646).sum := by decide
  have hdescent : baseEnd_534646 < baseStart_534646 := by decide
  rcases family_descends (prefixWord ++ tailWord_534646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534657 : List Nat := [1, 2, 4, 2, 3, 2, 1, 6]
def baseStart_534657 : Nat := 118140960795 + 534657 * 2 ^ 59
def prefixEnd_534657 : Nat := 4983230072969 + 3 ^ 40 * 534657 * 2
def baseEnd_534657 : Nat := 40672003894965908996839

theorem tailTrace_534657 : CollatzResearch.WordTrace tailWord_534657 prefixEnd_534657 40672003894965908996839 := by
  unfold tailWord_534657
  simp only [CollatzResearch.WordTrace]
  refine ⟨19500542824036475990978225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13000361882690983993985483 19500542824036475990978225)
  ·
    refine ⟨14625407118027356993233669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19500542824036475990978225 14625407118027356993233669)
    ·
      refine ⟨2742263834630129436231313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14625407118027356993233669 2742263834630129436231313)
      ·
        refine ⟨2056697875972597077173485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2742263834630129436231313 2056697875972597077173485)
        ·
          refine ⟨771261703489723903940057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2056697875972597077173485 771261703489723903940057)
          ·
            refine ⟨578446277617292927955043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 771261703489723903940057 578446277617292927955043)
            ·
              refine ⟨867669416425939391932565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 578446277617292927955043 867669416425939391932565)
              ·
                refine ⟨40672003894965908996839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 867669416425939391932565 40672003894965908996839)
                ·
                  rfl

theorem cell21_534657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 1, 6].length) (baseStart_534657 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_534657 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_534657 prefixEnd_534657 := by exact prefixLift 534657
  have htrace : WordTrace (prefixWord ++ tailWord_534657) baseStart_534657 baseEnd_534657 := by
    simpa [prefixWord, tailWord_534657, baseEnd_534657] using wordTrace_append hprefix tailTrace_534657
  have hstable : (prefixWord ++ tailWord_534657).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534657).length < 2 ^ (prefixWord ++ tailWord_534657).sum := by decide
  have hdescent : baseEnd_534657 < baseStart_534657 := by decide
  rcases family_descends (prefixWord ++ tailWord_534657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534668 : List Nat := [2, 2, 1, 2, 1, 1, 1, 1, 10]
def baseStart_534668 : Nat := 118140960795 + 534668 * 2 ^ 59
def prefixEnd_534668 : Nat := 4983230072969 + 3 ^ 40 * 534668 * 2
def baseEnd_534668 : Nat := 122018522034764152307161

theorem tailTrace_534668 : CollatzResearch.WordTrace tailWord_534668 prefixEnd_534668 122018522034764152307161 := by
  unfold tailWord_534668
  simp only [CollatzResearch.WordTrace]
  refine ⟨9750472013498312434814329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13000629351331083246419105 9750472013498312434814329)
  ·
    refine ⟨7312854010123734326110747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9750472013498312434814329 7312854010123734326110747)
    ·
      refine ⟨10969281015185601489166121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7312854010123734326110747 10969281015185601489166121)
      ·
        refine ⟨8226960761389201116874591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10969281015185601489166121 8226960761389201116874591)
        ·
          refine ⟨12340441142083801675311887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8226960761389201116874591 12340441142083801675311887)
          ·
            refine ⟨18510661713125702512967831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12340441142083801675311887 18510661713125702512967831)
            ·
              refine ⟨27765992569688553769451747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18510661713125702512967831 27765992569688553769451747)
              ·
                refine ⟨41648988854532830654177621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27765992569688553769451747 41648988854532830654177621)
                ·
                  refine ⟨122018522034764152307161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 41648988854532830654177621 122018522034764152307161)
                  ·
                    rfl

theorem cell21_534668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 10].length) (baseStart_534668 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_534668 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_534668 prefixEnd_534668 := by exact prefixLift 534668
  have htrace : WordTrace (prefixWord ++ tailWord_534668) baseStart_534668 baseEnd_534668 := by
    simpa [prefixWord, tailWord_534668, baseEnd_534668] using wordTrace_append hprefix tailTrace_534668
  have hstable : (prefixWord ++ tailWord_534668).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534668).length < 2 ^ (prefixWord ++ tailWord_534668).sum := by decide
  have hdescent : baseEnd_534668 < baseStart_534668 := by decide
  rcases family_descends (prefixWord ++ tailWord_534668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534688 : List Nat := [2, 1, 1, 4, 2, 3, 2, 3, 3]
def baseStart_534688 : Nat := 118140960795 + 534688 * 2 ^ 59
def prefixEnd_534688 : Nat := 4983230072969 + 3 ^ 40 * 534688 * 2
def baseEnd_534688 : Nat := 122023086307248561973787

theorem tailTrace_534688 : CollatzResearch.WordTrace tailWord_534688 prefixEnd_534688 122023086307248561973787 := by
  unfold tailWord_534688
  simp only [CollatzResearch.WordTrace]
  refine ⟨9750836743462084142678359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13001115657949445523571145 9750836743462084142678359)
  ·
    refine ⟨14626255115193126214017539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9750836743462084142678359 14626255115193126214017539)
    ·
      refine ⟨21939382672789689321026309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14626255115193126214017539 21939382672789689321026309)
      ·
        refine ⟨4113634251148066747692433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21939382672789689321026309 4113634251148066747692433)
        ·
          refine ⟨3085225688361050060769325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4113634251148066747692433 3085225688361050060769325)
          ·
            refine ⟨1156959633135393772788497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3085225688361050060769325 1156959633135393772788497)
            ·
              refine ⟨867719724851545329591373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1156959633135393772788497 867719724851545329591373)
              ·
                refine ⟨325394896819329498596765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 867719724851545329591373 325394896819329498596765)
                ·
                  refine ⟨122023086307248561973787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 325394896819329498596765 122023086307248561973787)
                  ·
                    rfl

theorem cell21_534688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 2, 3, 3].length) (baseStart_534688 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_534688 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_534688 prefixEnd_534688 := by exact prefixLift 534688
  have htrace : WordTrace (prefixWord ++ tailWord_534688) baseStart_534688 baseEnd_534688 := by
    simpa [prefixWord, tailWord_534688, baseEnd_534688] using wordTrace_append hprefix tailTrace_534688
  have hstable : (prefixWord ++ tailWord_534688).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534688).length < 2 ^ (prefixWord ++ tailWord_534688).sum := by decide
  have hdescent : baseEnd_534688 < baseStart_534688 := by decide
  rcases family_descends (prefixWord ++ tailWord_534688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534730 : List Nat := [3, 1, 2, 1, 3, 1, 1, 4, 5]
def baseStart_534730 : Nat := 118140960795 + 534730 * 2 ^ 59
def prefixEnd_534730 : Nat := 4983230072969 + 3 ^ 40 * 534730 * 2
def baseEnd_534730 : Nat := 122032671279465822273701

theorem tailTrace_534730 : CollatzResearch.WordTrace tailWord_534730 prefixEnd_534730 122032671279465822273701 := by
  unfold tailWord_534730
  simp only [CollatzResearch.WordTrace]
  refine ⟨4875801338193002364596411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13002136901848006305590429 4875801338193002364596411)
  ·
    refine ⟨7313702007289503546894617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4875801338193002364596411 7313702007289503546894617)
    ·
      refine ⟨5485276505467127660170963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7313702007289503546894617 5485276505467127660170963)
      ·
        refine ⟨8227914758200691490256445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5485276505467127660170963 8227914758200691490256445)
        ·
          refine ⟨3085468034325259308846167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8227914758200691490256445 3085468034325259308846167)
          ·
            refine ⟨4628202051487888963269251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3085468034325259308846167 4628202051487888963269251)
            ·
              refine ⟨6942303077231833444903877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4628202051487888963269251 6942303077231833444903877)
              ·
                refine ⟨1301681826980968770919477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6942303077231833444903877 1301681826980968770919477)
                ·
                  refine ⟨122032671279465822273701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1301681826980968770919477 122032671279465822273701)
                  ·
                    rfl

theorem cell21_534730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 4, 5].length) (baseStart_534730 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_534730 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_534730 prefixEnd_534730 := by exact prefixLift 534730
  have htrace : WordTrace (prefixWord ++ tailWord_534730) baseStart_534730 baseEnd_534730 := by
    simpa [prefixWord, tailWord_534730, baseEnd_534730] using wordTrace_append hprefix tailTrace_534730
  have hstable : (prefixWord ++ tailWord_534730).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534730).length < 2 ^ (prefixWord ++ tailWord_534730).sum := by decide
  have hdescent : baseEnd_534730 < baseStart_534730 := by decide
  rcases family_descends (prefixWord ++ tailWord_534730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534764 : List Nat := [2, 2, 1, 1, 2, 3, 5, 2, 3]
def baseStart_534764 : Nat := 118140960795 + 534764 * 2 ^ 59
def prefixEnd_534764 : Nat := 4983230072969 + 3 ^ 40 * 534764 * 2
def baseEnd_534764 : Nat := 122040430542689318706965

theorem tailTrace_534764 : CollatzResearch.WordTrace tailWord_534764 prefixEnd_534764 122040430542689318706965 := by
  unfold tailWord_534764
  simp only [CollatzResearch.WordTrace]
  refine ⟨9752222717324416632561673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13002963623099222176748897 9752222717324416632561673)
  ·
    refine ⟨7314167037993312474421255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9752222717324416632561673 7314167037993312474421255)
    ·
      refine ⟨10971250556989968711631883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7314167037993312474421255 10971250556989968711631883)
      ·
        refine ⟨16456875835484953067447825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10971250556989968711631883 16456875835484953067447825)
        ·
          refine ⟨12342656876613714800585869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16456875835484953067447825 12342656876613714800585869)
          ·
            refine ⟨4628496328730143050219701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12342656876613714800585869 4628496328730143050219701)
            ·
              refine ⟨433921530818450910958097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4628496328730143050219701 433921530818450910958097)
              ·
                refine ⟨325441148113838183218573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 433921530818450910958097 325441148113838183218573)
                ·
                  refine ⟨122040430542689318706965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 325441148113838183218573 122040430542689318706965)
                  ·
                    rfl

theorem cell21_534764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 5, 2, 3].length) (baseStart_534764 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_534764 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_534764 prefixEnd_534764 := by exact prefixLift 534764
  have htrace : WordTrace (prefixWord ++ tailWord_534764) baseStart_534764 baseEnd_534764 := by
    simpa [prefixWord, tailWord_534764, baseEnd_534764] using wordTrace_append hprefix tailTrace_534764
  have hstable : (prefixWord ++ tailWord_534764).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534764).length < 2 ^ (prefixWord ++ tailWord_534764).sum := by decide
  have hdescent : baseEnd_534764 < baseStart_534764 := by decide
  rcases family_descends (prefixWord ++ tailWord_534764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534778 : List Nat := [3, 1, 1, 1, 1, 5, 4, 1, 4]
def baseStart_534778 : Nat := 118140960795 + 534778 * 2 ^ 59
def prefixEnd_534778 : Nat := 4983230072969 + 3 ^ 40 * 534778 * 2
def baseEnd_534778 : Nat := 122043625533428405473603

theorem tailTrace_534778 : CollatzResearch.WordTrace tailWord_534778 prefixEnd_534778 122043625533428405473603 := by
  unfold tailWord_534778
  simp only [CollatzResearch.WordTrace]
  refine ⟨4876239014149528414033247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13003304037732075770755325 4876239014149528414033247)
  ·
    refine ⟨7314358521224292621049871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4876239014149528414033247 7314358521224292621049871)
    ·
      refine ⟨10971537781836438931574807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7314358521224292621049871 10971537781836438931574807)
      ·
        refine ⟨16457306672754658397362211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10971537781836438931574807 16457306672754658397362211)
        ·
          refine ⟨24685960009131987596043317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16457306672754658397362211 24685960009131987596043317)
          ·
            refine ⟨2314308750856123837129061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 24685960009131987596043317 2314308750856123837129061)
            ·
              refine ⟨433932890785523219461699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2314308750856123837129061 433932890785523219461699)
              ·
                refine ⟨650899336178284829192549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 433932890785523219461699 650899336178284829192549)
                ·
                  refine ⟨122043625533428405473603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 650899336178284829192549 122043625533428405473603)
                  ·
                    rfl

theorem cell21_534778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 4, 1, 4].length) (baseStart_534778 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_534778 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_534778 prefixEnd_534778 := by exact prefixLift 534778
  have htrace : WordTrace (prefixWord ++ tailWord_534778) baseStart_534778 baseEnd_534778 := by
    simpa [prefixWord, tailWord_534778, baseEnd_534778] using wordTrace_append hprefix tailTrace_534778
  have hstable : (prefixWord ++ tailWord_534778).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534778).length < 2 ^ (prefixWord ++ tailWord_534778).sum := by decide
  have hdescent : baseEnd_534778 < baseStart_534778 := by decide
  rcases family_descends (prefixWord ++ tailWord_534778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534826 : List Nat := [3, 1, 4, 2, 3, 1, 1, 6]
def baseStart_534826 : Nat := 118140960795 + 534826 * 2 ^ 59
def prefixEnd_534826 : Nat := 4983230072969 + 3 ^ 40 * 534826 * 2
def baseEnd_534826 : Nat := 40684859929130329557835

theorem tailTrace_534826 : CollatzResearch.WordTrace tailWord_534826 prefixEnd_534826 40684859929130329557835 := by
  unfold tailWord_534826
  simp only [CollatzResearch.WordTrace]
  refine ⟨4876676690106054463470083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13004471173616145235920221 4876676690106054463470083)
  ·
    refine ⟨7315015035159081695205125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4876676690106054463470083 7315015035159081695205125)
    ·
      refine ⟨1371565319092327817850961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7315015035159081695205125 1371565319092327817850961)
      ·
        refine ⟨1028673989319245863388221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1371565319092327817850961 1028673989319245863388221)
        ·
          refine ⟨385752745994717198770583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1028673989319245863388221 385752745994717198770583)
          ·
            refine ⟨578629118992075798155875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 385752745994717198770583 578629118992075798155875)
            ·
              refine ⟨867943678488113697233813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 578629118992075798155875 867943678488113697233813)
              ·
                refine ⟨40684859929130329557835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 867943678488113697233813 40684859929130329557835)
                ·
                  rfl

theorem cell21_534826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 1, 6].length) (baseStart_534826 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_534826 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_534826 prefixEnd_534826 := by exact prefixLift 534826
  have htrace : WordTrace (prefixWord ++ tailWord_534826) baseStart_534826 baseEnd_534826 := by
    simpa [prefixWord, tailWord_534826, baseEnd_534826] using wordTrace_append hprefix tailTrace_534826
  have hstable : (prefixWord ++ tailWord_534826).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534826).length < 2 ^ (prefixWord ++ tailWord_534826).sum := by decide
  have hdescent : baseEnd_534826 < baseStart_534826 := by decide
  rcases family_descends (prefixWord ++ tailWord_534826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534837 : List Nat := [1, 3, 3, 1, 2, 1, 1, 5, 4]
def baseStart_534837 : Nat := 118140960795 + 534837 * 2 ^ 59
def prefixEnd_534837 : Nat := 4983230072969 + 3 ^ 40 * 534837 * 2
def baseEnd_534837 : Nat := 122057090137257413990149

theorem tailTrace_534837 : CollatzResearch.WordTrace tailWord_534837 prefixEnd_534837 122057090137257413990149 := by
  unfold tailWord_534837
  simp only [CollatzResearch.WordTrace]
  refine ⟨19507107963384366732530765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13004738642256244488353843 19507107963384366732530765)
  ·
    refine ⟨7315165486269137524699037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19507107963384366732530765 7315165486269137524699037)
    ·
      refine ⟨2743187057350926571762139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7315165486269137524699037 2743187057350926571762139)
      ·
        refine ⟨4114780586026389857643209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2743187057350926571762139 4114780586026389857643209)
        ·
          refine ⟨3086085439519792393232407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4114780586026389857643209 3086085439519792393232407)
          ·
            refine ⟨4629128159279688589848611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3086085439519792393232407 4629128159279688589848611)
            ·
              refine ⟨6943692238919532884772917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4629128159279688589848611 6943692238919532884772917)
              ·
                refine ⟨650971147398706207947461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6943692238919532884772917 650971147398706207947461)
                ·
                  refine ⟨122057090137257413990149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 650971147398706207947461 122057090137257413990149)
                  ·
                    rfl

theorem cell21_534837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 5, 4].length) (baseStart_534837 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_534837 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_534837 prefixEnd_534837 := by exact prefixLift 534837
  have htrace : WordTrace (prefixWord ++ tailWord_534837) baseStart_534837 baseEnd_534837 := by
    simpa [prefixWord, tailWord_534837, baseEnd_534837] using wordTrace_append hprefix tailTrace_534837
  have hstable : (prefixWord ++ tailWord_534837).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534837).length < 2 ^ (prefixWord ++ tailWord_534837).sum := by decide
  have hdescent : baseEnd_534837 < baseStart_534837 := by decide
  rcases family_descends (prefixWord ++ tailWord_534837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534913 : List Nat := [1, 2, 4, 3, 1, 1, 1, 2, 6]
def baseStart_534913 : Nat := 118140960795 + 534913 * 2 ^ 59
def prefixEnd_534913 : Nat := 4983230072969 + 3 ^ 40 * 534913 * 2
def baseEnd_534913 : Nat := 122074434372698170723327

theorem tailTrace_534913 : CollatzResearch.WordTrace tailWord_534913 prefixEnd_534913 122074434372698170723327 := by
  unfold tailWord_534913
  simp only [CollatzResearch.WordTrace]
  refine ⟨19509879911109031712297393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13006586607406021141531595 19509879911109031712297393)
  ·
    refine ⟨14632409933331773784223045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19509879911109031712297393 14632409933331773784223045)
    ·
      refine ⟨2743576862499707584541821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14632409933331773784223045 2743576862499707584541821)
      ·
        refine ⟨1028841323437390344203183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2743576862499707584541821 1028841323437390344203183)
        ·
          refine ⟨1543261985156085516304775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1028841323437390344203183 1543261985156085516304775)
          ·
            refine ⟨2314892977734128274457163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1543261985156085516304775 2314892977734128274457163)
            ·
              refine ⟨3472339466601192411685745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2314892977734128274457163 3472339466601192411685745)
              ·
                refine ⟨2604254599950894308764309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3472339466601192411685745 2604254599950894308764309)
                ·
                  refine ⟨122074434372698170723327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2604254599950894308764309 122074434372698170723327)
                  ·
                    rfl

theorem cell21_534913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 2, 6].length) (baseStart_534913 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_534913 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_534913 prefixEnd_534913 := by exact prefixLift 534913
  have htrace : WordTrace (prefixWord ++ tailWord_534913) baseStart_534913 baseEnd_534913 := by
    simpa [prefixWord, tailWord_534913, baseEnd_534913] using wordTrace_append hprefix tailTrace_534913
  have hstable : (prefixWord ++ tailWord_534913).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534913).length < 2 ^ (prefixWord ++ tailWord_534913).sum := by decide
  have hdescent : baseEnd_534913 < baseStart_534913 := by decide
  rcases family_descends (prefixWord ++ tailWord_534913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535051 : List Nat := [1, 1, 1, 1, 7, 1, 2, 4, 3]
def baseStart_535051 : Nat := 118140960795 + 535051 * 2 ^ 59
def prefixEnd_535051 : Nat := 4983230072969 + 3 ^ 40 * 535051 * 2
def baseEnd_535051 : Nat := 122105927852840597423045

theorem tailTrace_535051 : CollatzResearch.WordTrace tailWord_535051 prefixEnd_535051 122105927852840597423045 := by
  unfold tailWord_535051
  simp only [CollatzResearch.WordTrace]
  refine ⟨19514913184609081280821007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13009942123072720853880671 19514913184609081280821007)
  ·
    refine ⟨29272369776913621921231511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19514913184609081280821007 29272369776913621921231511)
    ·
      refine ⟨43908554665370432881847267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29272369776913621921231511 43908554665370432881847267)
      ·
        refine ⟨65862831998055649322770901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43908554665370432881847267 65862831998055649322770901)
        ·
          refine ⟨1543660124954429281002443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 65862831998055649322770901 1543660124954429281002443)
          ·
            refine ⟨2315490187431643921503665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1543660124954429281002443 2315490187431643921503665)
            ·
              refine ⟨1736617640573732941127749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2315490187431643921503665 1736617640573732941127749)
              ·
                refine ⟨325615807607574926461453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1736617640573732941127749 325615807607574926461453)
                ·
                  refine ⟨122105927852840597423045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 325615807607574926461453 122105927852840597423045)
                  ·
                    rfl

theorem cell21_535051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 4, 3].length) (baseStart_535051 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_535051 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_535051 prefixEnd_535051 := by exact prefixLift 535051
  have htrace : WordTrace (prefixWord ++ tailWord_535051) baseStart_535051 baseEnd_535051 := by
    simpa [prefixWord, tailWord_535051, baseEnd_535051] using wordTrace_append hprefix tailTrace_535051
  have hstable : (prefixWord ++ tailWord_535051).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535051).length < 2 ^ (prefixWord ++ tailWord_535051).sum := by decide
  have hdescent : baseEnd_535051 < baseStart_535051 := by decide
  rcases family_descends (prefixWord ++ tailWord_535051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535102 : List Nat := [4, 2, 1, 4, 1, 1, 3, 2, 3]
def baseStart_535102 : Nat := 118140960795 + 535102 * 2 ^ 59
def prefixEnd_535102 : Nat := 4983230072969 + 3 ^ 40 * 535102 * 2
def baseEnd_535102 : Nat := 122117566747675842072941

theorem tailTrace_535102 : CollatzResearch.WordTrace tailWord_535102 prefixEnd_535102 122117566747675842072941 := by
  unfold tailWord_535102
  simp only [CollatzResearch.WordTrace]
  refine ⟨2439596663428039623865945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13011182204949544660618373 2439596663428039623865945)
  ·
    refine ⟨1829697497571029717899459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2439596663428039623865945 1829697497571029717899459)
    ·
      refine ⟨2744546246356544576849189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1829697497571029717899459 2744546246356544576849189)
      ·
        refine ⟨514602421191852108159223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2744546246356544576849189 514602421191852108159223)
        ·
          refine ⟨771903631787778162238835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 514602421191852108159223 771903631787778162238835)
          ·
            refine ⟨1157855447681667243358253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 771903631787778162238835 1157855447681667243358253)
            ·
              refine ⟨434195792880625216259345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1157855447681667243358253 434195792880625216259345)
              ·
                refine ⟨325646844660468912194509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 434195792880625216259345 325646844660468912194509)
                ·
                  refine ⟨122117566747675842072941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 325646844660468912194509 122117566747675842072941)
                  ·
                    rfl

theorem cell21_535102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 3, 2, 3].length) (baseStart_535102 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_535102 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_535102 prefixEnd_535102 := by exact prefixLift 535102
  have htrace : WordTrace (prefixWord ++ tailWord_535102) baseStart_535102 baseEnd_535102 := by
    simpa [prefixWord, tailWord_535102, baseEnd_535102] using wordTrace_append hprefix tailTrace_535102
  have hstable : (prefixWord ++ tailWord_535102).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535102).length < 2 ^ (prefixWord ++ tailWord_535102).sum := by decide
  have hdescent : baseEnd_535102 < baseStart_535102 := by decide
  rcases family_descends (prefixWord ++ tailWord_535102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535172 : List Nat := [2, 3, 2, 1, 3, 3, 1, 6]
def baseStart_535172 : Nat := 118140960795 + 535172 * 2 ^ 59
def prefixEnd_535172 : Nat := 4983230072969 + 3 ^ 40 * 535172 * 2
def baseEnd_535172 : Nat := 40711180567123758635377

theorem tailTrace_535172 : CollatzResearch.WordTrace tailWord_535172 prefixEnd_535172 40711180567123758635377 := by
  unfold tailWord_535172
  simp only [CollatzResearch.WordTrace]
  refine ⟨9759663208585359472987885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13012884278113812630650513 9759663208585359472987885)
  ·
    refine ⟨3659873703219509802370457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9759663208585359472987885 3659873703219509802370457)
    ·
      refine ⟨2744905277414632351777843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3659873703219509802370457 2744905277414632351777843)
      ·
        refine ⟨4117357916121948527666765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2744905277414632351777843 4117357916121948527666765)
        ·
          refine ⟨1544009218545730697875037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4117357916121948527666765 1544009218545730697875037)
          ·
            refine ⟨579003456954649011703139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1544009218545730697875037 579003456954649011703139)
            ·
              refine ⟨868505185431973517554709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 579003456954649011703139 868505185431973517554709)
              ·
                refine ⟨40711180567123758635377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 868505185431973517554709 40711180567123758635377)
                ·
                  rfl

theorem cell21_535172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 1, 6].length) (baseStart_535172 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_535172 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_535172 prefixEnd_535172 := by exact prefixLift 535172
  have htrace : WordTrace (prefixWord ++ tailWord_535172) baseStart_535172 baseEnd_535172 := by
    simpa [prefixWord, tailWord_535172, baseEnd_535172] using wordTrace_append hprefix tailTrace_535172
  have hstable : (prefixWord ++ tailWord_535172).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535172).length < 2 ^ (prefixWord ++ tailWord_535172).sum := by decide
  have hdescent : baseEnd_535172 < baseStart_535172 := by decide
  rcases family_descends (prefixWord ++ tailWord_535172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535186 : List Nat := [3, 2, 3, 1, 2, 1, 1, 1, 7]
def baseStart_535186 : Nat := 118140960795 + 535186 * 2 ^ 59
def prefixEnd_535186 : Nat := 4983230072969 + 3 ^ 40 * 535186 * 2
def baseEnd_535186 : Nat := 122136736692110362672769

theorem tailTrace_535186 : CollatzResearch.WordTrace tailWord_535186 prefixEnd_535186 122136736692110362672769 := by
  unfold tailWord_535186
  simp only [CollatzResearch.WordTrace]
  refine ⟨4879959259779999834246353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13013224692746666224656941 4879959259779999834246353)
  ·
    refine ⟨3659969444834999875684765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4879959259779999834246353 3659969444834999875684765)
    ·
      refine ⟨1372488541813124953381787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3659969444834999875684765 1372488541813124953381787)
      ·
        refine ⟨2058732812719687430072681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1372488541813124953381787 2058732812719687430072681)
        ·
          refine ⟨1544049609539765572554511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2058732812719687430072681 1544049609539765572554511)
          ·
            refine ⟨2316074414309648358831767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1544049609539765572554511 2316074414309648358831767)
            ·
              refine ⟨3474111621464472538247651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2316074414309648358831767 3474111621464472538247651)
              ·
                refine ⟨5211167432196708807371477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3474111621464472538247651 5211167432196708807371477)
                ·
                  refine ⟨122136736692110362672769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5211167432196708807371477 122136736692110362672769)
                  ·
                    rfl

theorem cell21_535186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 1, 7].length) (baseStart_535186 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_535186 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_535186 prefixEnd_535186 := by exact prefixLift 535186
  have htrace : WordTrace (prefixWord ++ tailWord_535186) baseStart_535186 baseEnd_535186 := by
    simpa [prefixWord, tailWord_535186, baseEnd_535186] using wordTrace_append hprefix tailTrace_535186
  have hstable : (prefixWord ++ tailWord_535186).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535186).length < 2 ^ (prefixWord ++ tailWord_535186).sum := by decide
  have hdescent : baseEnd_535186 < baseStart_535186 := by decide
  rcases family_descends (prefixWord ++ tailWord_535186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535276 : List Nat := [2, 2, 1, 1, 2, 2, 1, 6, 4]
def baseStart_535276 : Nat := 118140960795 + 535276 * 2 ^ 59
def prefixEnd_535276 : Nat := 4983230072969 + 3 ^ 40 * 535276 * 2
def baseEnd_535276 : Nat := 122157275918290206172585

theorem tailTrace_535276 : CollatzResearch.WordTrace tailWord_535276 prefixEnd_535276 122157275918290206172585 := by
  unfold tailWord_535276
  simp only [CollatzResearch.WordTrace]
  refine ⟨9761559804396972353880841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13015413072529296471841121 9761559804396972353880841)
  ·
    refine ⟨7321169853297729265410631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9761559804396972353880841 7321169853297729265410631)
    ·
      refine ⟨10981754779946593898115947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7321169853297729265410631 10981754779946593898115947)
      ·
        refine ⟨16472632169919890847173921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10981754779946593898115947 16472632169919890847173921)
        ·
          refine ⟨12354474127439918135380441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16472632169919890847173921 12354474127439918135380441)
          ·
            refine ⟨9265855595579938601535331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12354474127439918135380441 9265855595579938601535331)
            ·
              refine ⟨13898783393369907902302997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9265855595579938601535331 13898783393369907902302997)
              ·
                refine ⟨651505471564214432920453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 13898783393369907902302997 651505471564214432920453)
                ·
                  refine ⟨122157275918290206172585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 651505471564214432920453 122157275918290206172585)
                  ·
                    rfl

theorem cell21_535276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 4].length) (baseStart_535276 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_535276 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_535276 prefixEnd_535276 := by exact prefixLift 535276
  have htrace : WordTrace (prefixWord ++ tailWord_535276) baseStart_535276 baseEnd_535276 := by
    simpa [prefixWord, tailWord_535276, baseEnd_535276] using wordTrace_append hprefix tailTrace_535276
  have hstable : (prefixWord ++ tailWord_535276).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535276).length < 2 ^ (prefixWord ++ tailWord_535276).sum := by decide
  have hdescent : baseEnd_535276 < baseStart_535276 := by decide
  rcases family_descends (prefixWord ++ tailWord_535276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535285 : List Nat := [1, 3, 6, 1, 1, 2, 2, 1, 4]
def baseStart_535285 : Nat := 118140960795 + 535285 * 2 ^ 59
def prefixEnd_535285 : Nat := 4983230072969 + 3 ^ 40 * 535285 * 2
def baseEnd_535285 : Nat := 122159329840908190522567

theorem tailTrace_535285 : CollatzResearch.WordTrace tailWord_535285 prefixEnd_535285 122159329840908190522567 := by
  unfold tailWord_535285
  simp only [CollatzResearch.WordTrace]
  refine ⟨19523447865761339244839309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13015631910507559496559539 19523447865761339244839309)
  ·
    refine ⟨7321292949660502216814741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19523447865761339244839309 7321292949660502216814741)
    ·
      refine ⟨343185607015336041413191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 7321292949660502216814741 343185607015336041413191)
      ·
        refine ⟨514778410523004062119787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 343185607015336041413191 514778410523004062119787)
        ·
          refine ⟨772167615784506093179681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 514778410523004062119787 772167615784506093179681)
          ·
            refine ⟨579125711838379569884761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 772167615784506093179681 579125711838379569884761)
            ·
              refine ⟨434344283878784677413571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 579125711838379569884761 434344283878784677413571)
              ·
                refine ⟨651516425818177016120357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 434344283878784677413571 651516425818177016120357)
                ·
                  refine ⟨122159329840908190522567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 651516425818177016120357 122159329840908190522567)
                  ·
                    rfl

theorem cell21_535285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 2, 1, 4].length) (baseStart_535285 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_535285 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_535285 prefixEnd_535285 := by exact prefixLift 535285
  have htrace : WordTrace (prefixWord ++ tailWord_535285) baseStart_535285 baseEnd_535285 := by
    simpa [prefixWord, tailWord_535285, baseEnd_535285] using wordTrace_append hprefix tailTrace_535285
  have hstable : (prefixWord ++ tailWord_535285).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535285).length < 2 ^ (prefixWord ++ tailWord_535285).sum := by decide
  have hdescent : baseEnd_535285 < baseStart_535285 := by decide
  rcases family_descends (prefixWord ++ tailWord_535285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535290 : List Nat := [3, 1, 1, 1, 1, 3, 3, 8]
def baseStart_535290 : Nat := 118140960795 + 535290 * 2 ^ 59
def prefixEnd_535290 : Nat := 4983230072969 + 3 ^ 40 * 535290 * 2
def baseEnd_535290 : Nat := 40720156969676430979741

theorem tailTrace_535290 : CollatzResearch.WordTrace tailWord_535290 prefixEnd_535290 40720156969676430979741 := by
  unfold tailWord_535290
  simp only [CollatzResearch.WordTrace]
  refine ⟨4880907557685806274692831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13015753487162150065847549 4880907557685806274692831)
  ·
    refine ⟨7321361336528709412039247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4880907557685806274692831 7321361336528709412039247)
    ·
      refine ⟨10982042004793064118058871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7321361336528709412039247 10982042004793064118058871)
      ·
        refine ⟨16473063007189596177088307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10982042004793064118058871 16473063007189596177088307)
        ·
          refine ⟨24709594510784394265632461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16473063007189596177088307 24709594510784394265632461)
          ·
            refine ⟨9266097941544147849612173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24709594510784394265632461 9266097941544147849612173)
            ·
              refine ⟨3474786728079055443604565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9266097941544147849612173 3474786728079055443604565)
              ·
                refine ⟨40720156969676430979741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3474786728079055443604565 40720156969676430979741)
                ·
                  rfl

theorem cell21_535290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 8].length) (baseStart_535290 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_535290 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_535290 prefixEnd_535290 := by exact prefixLift 535290
  have htrace : WordTrace (prefixWord ++ tailWord_535290) baseStart_535290 baseEnd_535290 := by
    simpa [prefixWord, tailWord_535290, baseEnd_535290] using wordTrace_append hprefix tailTrace_535290
  have hstable : (prefixWord ++ tailWord_535290).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535290).length < 2 ^ (prefixWord ++ tailWord_535290).sum := by decide
  have hdescent : baseEnd_535290 < baseStart_535290 := by decide
  rcases family_descends (prefixWord ++ tailWord_535290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535352 : List Nat := [2, 1, 2, 1, 3, 2, 1, 5, 4]
def baseStart_535352 : Nat := 118140960795 + 535352 * 2 ^ 59
def prefixEnd_535352 : Nat := 4983230072969 + 3 ^ 40 * 535352 * 2
def baseEnd_535352 : Nat := 122174620153730962905763

theorem tailTrace_535352 : CollatzResearch.WordTrace tailWord_535352 prefixEnd_535352 122174620153730962905763 := by
  unfold tailWord_535352
  simp only [CollatzResearch.WordTrace]
  refine ⟨9762945778259304843764155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13017261037679073125018873 9762945778259304843764155)
  ·
    refine ⟨14644418667388957265646233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9762945778259304843764155 14644418667388957265646233)
    ·
      refine ⟨10983314000541717949234675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14644418667388957265646233 10983314000541717949234675)
      ·
        refine ⟨16474971000812576923852013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10983314000541717949234675 16474971000812576923852013)
        ·
          refine ⟨6178114125304716346444505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16474971000812576923852013 6178114125304716346444505)
          ·
            refine ⟨4633585593978537259833379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6178114125304716346444505 4633585593978537259833379)
            ·
              refine ⟨6950378390967805889750069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4633585593978537259833379 6950378390967805889750069)
              ·
                refine ⟨651597974153231802164069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6950378390967805889750069 651597974153231802164069)
                ·
                  refine ⟨122174620153730962905763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 651597974153231802164069 122174620153730962905763)
                  ·
                    rfl

theorem cell21_535352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 5, 4].length) (baseStart_535352 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_535352 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_535352 prefixEnd_535352 := by exact prefixLift 535352
  have htrace : WordTrace (prefixWord ++ tailWord_535352) baseStart_535352 baseEnd_535352 := by
    simpa [prefixWord, tailWord_535352, baseEnd_535352] using wordTrace_append hprefix tailTrace_535352
  have hstable : (prefixWord ++ tailWord_535352).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535352).length < 2 ^ (prefixWord ++ tailWord_535352).sum := by decide
  have hdescent : baseEnd_535352 < baseStart_535352 := by decide
  rcases family_descends (prefixWord ++ tailWord_535352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535397 : List Nat := [1, 3, 1, 3, 1, 1, 3, 3, 5]
def baseStart_535397 : Nat := 118140960795 + 535397 * 2 ^ 59
def prefixEnd_535397 : Nat := 4983230072969 + 3 ^ 40 * 535397 * 2
def baseEnd_535397 : Nat := 122184889766820884655671

theorem tailTrace_535397 : CollatzResearch.WordTrace tailWord_535397 prefixEnd_535397 122184889766820884655671 := by
  unfold tailWord_535397
  simp only [CollatzResearch.WordTrace]
  refine ⟨19527532841355582372916445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13018355227570388248610963 19527532841355582372916445)
  ·
    refine ⟨7322824815508343389843667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19527532841355582372916445 7322824815508343389843667)
    ·
      refine ⟨10984237223262515084765501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7322824815508343389843667 10984237223262515084765501)
      ·
        refine ⟨4119088958723443156787063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10984237223262515084765501 4119088958723443156787063)
        ·
          refine ⟨6178633438085164735180595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4119088958723443156787063 6178633438085164735180595)
          ·
            refine ⟨9267950157127747102770893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6178633438085164735180595 9267950157127747102770893)
            ·
              refine ⟨3475481308922905163539085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9267950157127747102770893 3475481308922905163539085)
              ·
                refine ⟨1303305490846089436327157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3475481308922905163539085 1303305490846089436327157)
                ·
                  refine ⟨122184889766820884655671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1303305490846089436327157 122184889766820884655671)
                  ·
                    rfl

theorem cell21_535397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 3, 5].length) (baseStart_535397 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_535397 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_535397 prefixEnd_535397 := by exact prefixLift 535397
  have htrace : WordTrace (prefixWord ++ tailWord_535397) baseStart_535397 baseEnd_535397 := by
    simpa [prefixWord, tailWord_535397, baseEnd_535397] using wordTrace_append hprefix tailTrace_535397
  have hstable : (prefixWord ++ tailWord_535397).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535397).length < 2 ^ (prefixWord ++ tailWord_535397).sum := by decide
  have hdescent : baseEnd_535397 < baseStart_535397 := by decide
  rcases family_descends (prefixWord ++ tailWord_535397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535431 : List Nat := [1, 1, 4, 2, 3, 1, 3, 3, 3]
def baseStart_535431 : Nat := 118140960795 + 535431 * 2 ^ 59
def prefixEnd_535431 : Nat := 4983230072969 + 3 ^ 40 * 535431 * 2
def baseEnd_535431 : Nat := 122192649030044381088935

theorem tailTrace_535431 : CollatzResearch.WordTrace tailWord_535431 prefixEnd_535431 122192649030044381088935 := by
  unfold tailWord_535431
  simp only [CollatzResearch.WordTrace]
  refine ⟨19528772923232406179654147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13019181948821604119769431 19528772923232406179654147)
  ·
    refine ⟨29293159384848609269481221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19528772923232406179654147 29293159384848609269481221)
    ·
      refine ⟨5492467384659114238027729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29293159384848609269481221 5492467384659114238027729)
      ·
        refine ⟨4119350538494335678520797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5492467384659114238027729 4119350538494335678520797)
        ·
          refine ⟨1544756451935375879445299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4119350538494335678520797 1544756451935375879445299)
          ·
            refine ⟨2317134677903063819167949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1544756451935375879445299 2317134677903063819167949)
            ·
              refine ⟨868925504213648932187981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2317134677903063819167949 868925504213648932187981)
              ·
                refine ⟨325847064080118349570493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 868925504213648932187981 325847064080118349570493)
                ·
                  refine ⟨122192649030044381088935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 325847064080118349570493 122192649030044381088935)
                  ·
                    rfl

theorem cell21_535431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 3, 3, 3].length) (baseStart_535431 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_535431 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_535431 prefixEnd_535431 := by exact prefixLift 535431
  have htrace : WordTrace (prefixWord ++ tailWord_535431) baseStart_535431 baseEnd_535431 := by
    simpa [prefixWord, tailWord_535431, baseEnd_535431] using wordTrace_append hprefix tailTrace_535431
  have hstable : (prefixWord ++ tailWord_535431).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535431).length < 2 ^ (prefixWord ++ tailWord_535431).sum := by decide
  have hdescent : baseEnd_535431 < baseStart_535431 := by decide
  rcases family_descends (prefixWord ++ tailWord_535431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535476 : List Nat := [2, 5, 2, 1, 1, 1, 2, 7]
def baseStart_535476 : Nat := 118140960795 + 535476 * 2 ^ 59
def prefixEnd_535476 : Nat := 4983230072969 + 3 ^ 40 * 535476 * 2
def baseEnd_535476 : Nat := 40734306214378100946281

theorem tailTrace_535476 : CollatzResearch.WordTrace tailWord_535476 prefixEnd_535476 40734306214378100946281 := by
  unfold tailWord_535476
  simp only [CollatzResearch.WordTrace]
  refine ⟨9765207104034689432521141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13020276138712919243361521 9765207104034689432521141)
  ·
    refine ⟨915488166003252134298857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9765207104034689432521141 915488166003252134298857)
    ·
      refine ⟨686616124502439100724143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 915488166003252134298857 686616124502439100724143)
      ·
        refine ⟨1029924186753658651086215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 686616124502439100724143 1029924186753658651086215)
        ·
          refine ⟨1544886280130487976629323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1029924186753658651086215 1544886280130487976629323)
          ·
            refine ⟨2317329420195731964943985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1544886280130487976629323 2317329420195731964943985)
            ·
              refine ⟨1737997065146798973707989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2317329420195731964943985 1737997065146798973707989)
              ·
                refine ⟨40734306214378100946281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1737997065146798973707989 40734306214378100946281)
                ·
                  rfl

theorem cell21_535476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 7].length) (baseStart_535476 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_535476 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_535476 prefixEnd_535476 := by exact prefixLift 535476
  have htrace : WordTrace (prefixWord ++ tailWord_535476) baseStart_535476 baseEnd_535476 := by
    simpa [prefixWord, tailWord_535476, baseEnd_535476] using wordTrace_append hprefix tailTrace_535476
  have hstable : (prefixWord ++ tailWord_535476).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535476).length < 2 ^ (prefixWord ++ tailWord_535476).sum := by decide
  have hdescent : baseEnd_535476 < baseStart_535476 := by decide
  rcases family_descends (prefixWord ++ tailWord_535476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535487 : List Nat := [1, 1, 2, 2, 2, 1, 2, 4, 6]
def baseStart_535487 : Nat := 118140960795 + 535487 * 2 ^ 59
def prefixEnd_535487 : Nat := 4983230072969 + 3 ^ 40 * 535487 * 2
def baseEnd_535487 : Nat := 122205428993000728155487

theorem tailTrace_535487 : CollatzResearch.WordTrace tailWord_535487 prefixEnd_535487 122205428993000728155487 := by
  unfold tailWord_535487
  simp only [CollatzResearch.WordTrace]
  refine ⟨19530815411029527743692715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13020543607353018495795143 19530815411029527743692715)
  ·
    refine ⟨29296223116544291615539073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19530815411029527743692715 29296223116544291615539073)
    ·
      refine ⟨21972167337408218711654305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29296223116544291615539073 21972167337408218711654305)
      ·
        refine ⟨16479125503056164033740729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21972167337408218711654305 16479125503056164033740729)
        ·
          refine ⟨12359344127292123025305547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16479125503056164033740729 12359344127292123025305547)
          ·
            refine ⟨18539016190938184537958321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12359344127292123025305547 18539016190938184537958321)
            ·
              refine ⟨13904262143203638403468741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18539016190938184537958321 13904262143203638403468741)
              ·
                refine ⟨2607049151850682200650389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13904262143203638403468741 2607049151850682200650389)
                ·
                  refine ⟨122205428993000728155487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2607049151850682200650389 122205428993000728155487)
                  ·
                    rfl

theorem cell21_535487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 4, 6].length) (baseStart_535487 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_535487 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_535487 prefixEnd_535487 := by exact prefixLift 535487
  have htrace : WordTrace (prefixWord ++ tailWord_535487) baseStart_535487 baseEnd_535487 := by
    simpa [prefixWord, tailWord_535487, baseEnd_535487] using wordTrace_append hprefix tailTrace_535487
  have hstable : (prefixWord ++ tailWord_535487).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535487).length < 2 ^ (prefixWord ++ tailWord_535487).sum := by decide
  have hdescent : baseEnd_535487 < baseStart_535487 := by decide
  rcases family_descends (prefixWord ++ tailWord_535487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535535 : List Nat := [1, 1, 2, 1, 4, 4, 3, 5]
def baseStart_535535 : Nat := 118140960795 + 535535 * 2 ^ 59
def prefixEnd_535535 : Nat := 4983230072969 + 3 ^ 40 * 535535 * 2
def baseEnd_535535 : Nat := 40738794415654437118463

theorem tailTrace_535535 : CollatzResearch.WordTrace tailWord_535535 prefixEnd_535535 40738794415654437118463 := by
  unfold tailWord_535535
  simp only [CollatzResearch.WordTrace]
  refine ⟨19532566114855631941440059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13021710743237087960960039 19532566114855631941440059)
  ·
    refine ⟨29298849172283447912160089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19532566114855631941440059 29298849172283447912160089)
    ·
      refine ⟨21974136879212585934120067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29298849172283447912160089 21974136879212585934120067)
      ·
        refine ⟨32961205318818878901180101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21974136879212585934120067 32961205318818878901180101)
        ·
          refine ⟨6180225997278539793971269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32961205318818878901180101 6180225997278539793971269)
          ·
            refine ⟨1158792374489726211369613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6180225997278539793971269 1158792374489726211369613)
            ·
              refine ⟨434547140433647329263605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1158792374489726211369613 434547140433647329263605)
              ·
                refine ⟨40738794415654437118463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 434547140433647329263605 40738794415654437118463)
                ·
                  rfl

theorem cell21_535535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 3, 5].length) (baseStart_535535 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_535535 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_535535 prefixEnd_535535 := by exact prefixLift 535535
  have htrace : WordTrace (prefixWord ++ tailWord_535535) baseStart_535535 baseEnd_535535 := by
    simpa [prefixWord, tailWord_535535, baseEnd_535535] using wordTrace_append hprefix tailTrace_535535
  have hstable : (prefixWord ++ tailWord_535535).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535535).length < 2 ^ (prefixWord ++ tailWord_535535).sum := by decide
  have hdescent : baseEnd_535535 < baseStart_535535 := by decide
  rcases family_descends (prefixWord ++ tailWord_535535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535541 : List Nat := [1, 3, 5, 2, 1, 1, 2, 3, 3]
def baseStart_535541 : Nat := 118140960795 + 535541 * 2 ^ 59
def prefixEnd_535541 : Nat := 4983230072969 + 3 ^ 40 * 535541 * 2
def baseEnd_535541 : Nat := 122217752528708634255377

theorem tailTrace_535541 : CollatzResearch.WordTrace tailWord_535541 prefixEnd_535541 122217752528708634255377 := by
  unfold tailWord_535541
  simp only [CollatzResearch.WordTrace]
  refine ⟨19532784952833894966158477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13021856635222596644105651 19532784952833894966158477)
  ·
    refine ⟨7324794357312710612309429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19532784952833894966158477 7324794357312710612309429)
    ·
      refine ⟨686699470998066619904009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7324794357312710612309429 686699470998066619904009)
      ·
        refine ⟨515024603248549964928007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 686699470998066619904009 515024603248549964928007)
        ·
          refine ⟨772536904872824947392011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 515024603248549964928007 772536904872824947392011)
          ·
            refine ⟨1158805357309237421088017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 772536904872824947392011 1158805357309237421088017)
            ·
              refine ⟨869104017981928065816013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1158805357309237421088017 869104017981928065816013)
              ·
                refine ⟨325914006743223024681005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 869104017981928065816013 325914006743223024681005)
                ·
                  refine ⟨122217752528708634255377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 325914006743223024681005 122217752528708634255377)
                  ·
                    rfl

theorem cell21_535541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 2, 3, 3].length) (baseStart_535541 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_535541 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_535541 prefixEnd_535541 := by exact prefixLift 535541
  have htrace : WordTrace (prefixWord ++ tailWord_535541) baseStart_535541 baseEnd_535541 := by
    simpa [prefixWord, tailWord_535541, baseEnd_535541] using wordTrace_append hprefix tailTrace_535541
  have hstable : (prefixWord ++ tailWord_535541).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535541).length < 2 ^ (prefixWord ++ tailWord_535541).sum := by decide
  have hdescent : baseEnd_535541 < baseStart_535541 := by decide
  rcases family_descends (prefixWord ++ tailWord_535541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535566 : List Nat := [4, 1, 1, 2, 2, 3, 2, 1, 5]
def baseStart_535566 : Nat := 118140960795 + 535566 * 2 ^ 59
def prefixEnd_535566 : Nat := 4983230072969 + 3 ^ 40 * 535566 * 2
def baseEnd_535566 : Nat := 122223457869314146338659

theorem tailTrace_535566 : CollatzResearch.WordTrace tailWord_535566 prefixEnd_535566 122223457869314146338659 := by
  unfold tailWord_535566
  simp only [CollatzResearch.WordTrace]
  refine ⟨2441712097217915529477319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13022464518495549490545701 2441712097217915529477319)
  ·
    refine ⟨3662568145826873294215979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2441712097217915529477319 3662568145826873294215979)
    ·
      refine ⟨5493852218740309941323969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3662568145826873294215979 5493852218740309941323969)
      ·
        refine ⟨4120389164055232455992977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5493852218740309941323969 4120389164055232455992977)
        ·
          refine ⟨3090291873041424341994733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4120389164055232455992977 3090291873041424341994733)
          ·
            refine ⟨1158859452390534128248025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3090291873041424341994733 1158859452390534128248025)
            ·
              refine ⟨869144589292900596186019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1158859452390534128248025 869144589292900596186019)
              ·
                refine ⟨1303716883939350894279029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 869144589292900596186019 1303716883939350894279029)
                ·
                  refine ⟨122223457869314146338659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1303716883939350894279029 122223457869314146338659)
                  ·
                    rfl

theorem cell21_535566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 2, 1, 5].length) (baseStart_535566 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_535566 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_535566 prefixEnd_535566 := by exact prefixLift 535566
  have htrace : WordTrace (prefixWord ++ tailWord_535566) baseStart_535566 baseEnd_535566 := by
    simpa [prefixWord, tailWord_535566, baseEnd_535566] using wordTrace_append hprefix tailTrace_535566
  have hstable : (prefixWord ++ tailWord_535566).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535566).length < 2 ^ (prefixWord ++ tailWord_535566).sum := by decide
  have hdescent : baseEnd_535566 < baseStart_535566 := by decide
  rcases family_descends (prefixWord ++ tailWord_535566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535673 : List Nat := [1, 2, 1, 3, 5, 1, 2, 2, 4]
def baseStart_535673 : Nat := 118140960795 + 535673 * 2 ^ 59
def prefixEnd_535673 : Nat := 4983230072969 + 3 ^ 40 * 535673 * 2
def baseEnd_535673 : Nat := 122247876727105738055107

theorem tailTrace_535673 : CollatzResearch.WordTrace tailWord_535673 prefixEnd_535673 122247876727105738055107 := by
  unfold tailWord_535673
  simp only [CollatzResearch.WordTrace]
  refine ⟨19537599388355681509963673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13025066258903787673309115 19537599388355681509963673)
  ·
    refine ⟨14653199541266761132472755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19537599388355681509963673 14653199541266761132472755)
    ·
      refine ⟨21979799311900141698709133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14653199541266761132472755 21979799311900141698709133)
      ·
        refine ⟨8242424741962553137015925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21979799311900141698709133 8242424741962553137015925)
        ·
          refine ⟨772727319558989356595243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8242424741962553137015925 772727319558989356595243)
          ·
            refine ⟨1159090979338484034892865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 772727319558989356595243 1159090979338484034892865)
            ·
              refine ⟨869318234503863026169649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1159090979338484034892865 869318234503863026169649)
              ·
                refine ⟨651988675877897269627237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 869318234503863026169649 651988675877897269627237)
                ·
                  refine ⟨122247876727105738055107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 651988675877897269627237 122247876727105738055107)
                  ·
                    rfl

theorem cell21_535673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 2, 2, 4].length) (baseStart_535673 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_535673 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_535673 prefixEnd_535673 := by exact prefixLift 535673
  have htrace : WordTrace (prefixWord ++ tailWord_535673) baseStart_535673 baseEnd_535673 := by
    simpa [prefixWord, tailWord_535673, baseEnd_535673] using wordTrace_append hprefix tailTrace_535673
  have hstable : (prefixWord ++ tailWord_535673).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535673).length < 2 ^ (prefixWord ++ tailWord_535673).sum := by decide
  have hdescent : baseEnd_535673 < baseStart_535673 := by decide
  rcases family_descends (prefixWord ++ tailWord_535673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535822 : List Nat := [4, 1, 1, 2, 1, 3, 2, 7]
def baseStart_535822 : Nat := 118140960795 + 535822 * 2 ^ 59
def prefixEnd_535822 : Nat := 4983230072969 + 3 ^ 40 * 535822 * 2
def baseEnd_535822 : Nat := 40760626852371530023823

theorem tailTrace_535822 : CollatzResearch.WordTrace tailWord_535822 prefixEnd_535822 40760626852371530023823 := by
  unfold tailWord_535822
  simp only [CollatzResearch.WordTrace]
  refine ⟨2442879233101984994642215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13028689243210586638091813 2442879233101984994642215)
  ·
    refine ⟨3664318849652977491963323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2442879233101984994642215 3664318849652977491963323)
    ·
      refine ⟨5496478274479466237944985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3664318849652977491963323 5496478274479466237944985)
      ·
        refine ⟨4122358705859599678458739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5496478274479466237944985 4122358705859599678458739)
        ·
          refine ⟨6183538058789399517688109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4122358705859599678458739 6183538058789399517688109)
          ·
            refine ⟨2318826772046024819133041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6183538058789399517688109 2318826772046024819133041)
            ·
              refine ⟨1739120079034518614349781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2318826772046024819133041 1739120079034518614349781)
              ·
                refine ⟨40760626852371530023823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1739120079034518614349781 40760626852371530023823)
                ·
                  rfl

theorem cell21_535822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 7].length) (baseStart_535822 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_535822 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_535822 prefixEnd_535822 := by exact prefixLift 535822
  have htrace : WordTrace (prefixWord ++ tailWord_535822) baseStart_535822 baseEnd_535822 := by
    simpa [prefixWord, tailWord_535822, baseEnd_535822] using wordTrace_append hprefix tailTrace_535822
  have hstable : (prefixWord ++ tailWord_535822).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535822).length < 2 ^ (prefixWord ++ tailWord_535822).sum := by decide
  have hdescent : baseEnd_535822 < baseStart_535822 := by decide
  rcases family_descends (prefixWord ++ tailWord_535822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535881 : List Nat := [1, 2, 1, 1, 2, 3, 2, 9]
def baseStart_535881 : Nat := 118140960795 + 535881 * 2 ^ 59
def prefixEnd_535881 : Nat := 4983230072969 + 3 ^ 40 * 535881 * 2
def baseEnd_535881 : Nat := 40765115053647866196005

theorem tailTrace_535881 : CollatzResearch.WordTrace tailWord_535881 prefixEnd_535881 40765115053647866196005 := by
  unfold tailWord_535881
  simp only [CollatzResearch.WordTrace]
  refine ⟨19545185771602133033535497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13030123847734755355690331 19545185771602133033535497)
  ·
    refine ⟨14658889328701599775151623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19545185771602133033535497 14658889328701599775151623)
    ·
      refine ⟨21988333993052399662727435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14658889328701599775151623 21988333993052399662727435)
      ·
        refine ⟨32982500989578599494091153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21988333993052399662727435 32982500989578599494091153)
        ·
          refine ⟨24736875742183949620568365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32982500989578599494091153 24736875742183949620568365)
          ·
            refine ⟨9276328403318981107713137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24736875742183949620568365 9276328403318981107713137)
            ·
              refine ⟨6957246302489235830784853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9276328403318981107713137 6957246302489235830784853)
              ·
                refine ⟨40765115053647866196005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 6957246302489235830784853 40765115053647866196005)
                ·
                  rfl

theorem cell21_535881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 9].length) (baseStart_535881 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_535881 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_535881 prefixEnd_535881 := by exact prefixLift 535881
  have htrace : WordTrace (prefixWord ++ tailWord_535881) baseStart_535881 baseEnd_535881 := by
    simpa [prefixWord, tailWord_535881, baseEnd_535881] using wordTrace_append hprefix tailTrace_535881
  have hstable : (prefixWord ++ tailWord_535881).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535881).length < 2 ^ (prefixWord ++ tailWord_535881).sum := by decide
  have hdescent : baseEnd_535881 < baseStart_535881 := by decide
  rcases family_descends (prefixWord ++ tailWord_535881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535943 : List Nat := [1, 1, 4, 2, 2, 2, 1, 2, 6]
def baseStart_535943 : Nat := 118140960795 + 535943 * 2 ^ 59
def prefixEnd_535943 : Nat := 4983230072969 + 3 ^ 40 * 535943 * 2
def baseEnd_535943 : Nat := 122309494405645268554555

theorem tailTrace_535943 : CollatzResearch.WordTrace tailWord_535943 prefixEnd_535943 122309494405645268554555 := by
  unfold tailWord_535943
  simp only [CollatzResearch.WordTrace]
  refine ⟨19547447097377517622292483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13031631398251678414861655 19547447097377517622292483)
  ·
    refine ⟨29321170646066276433438725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19547447097377517622292483 29321170646066276433438725)
    ·
      refine ⟨5497719496137426831269761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29321170646066276433438725 5497719496137426831269761)
      ·
        refine ⟨4123289622103070123452321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5497719496137426831269761 4123289622103070123452321)
        ·
          refine ⟨3092467216577302592589241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4123289622103070123452321 3092467216577302592589241)
          ·
            refine ⟨2319350412432976944441931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3092467216577302592589241 2319350412432976944441931)
            ·
              refine ⟨3479025618649465416662897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2319350412432976944441931 3479025618649465416662897)
              ·
                refine ⟨2609269213987099062497173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3479025618649465416662897 2609269213987099062497173)
                ·
                  refine ⟨122309494405645268554555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2609269213987099062497173 122309494405645268554555)
                  ·
                    rfl

theorem cell21_535943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 2, 6].length) (baseStart_535943 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_535943 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_535943 prefixEnd_535943 := by exact prefixLift 535943
  have htrace : WordTrace (prefixWord ++ tailWord_535943) baseStart_535943 baseEnd_535943 := by
    simpa [prefixWord, tailWord_535943, baseEnd_535943] using wordTrace_append hprefix tailTrace_535943
  have hstable : (prefixWord ++ tailWord_535943).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535943).length < 2 ^ (prefixWord ++ tailWord_535943).sum := by decide
  have hdescent : baseEnd_535943 < baseStart_535943 := by decide
  rcases family_descends (prefixWord ++ tailWord_535943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535957 : List Nat := [1, 3, 2, 1, 1, 2, 11]
def baseStart_535957 : Nat := 118140960795 + 535957 * 2 ^ 59
def prefixEnd_535957 : Nat := 4983230072969 + 3 ^ 40 * 535957 * 2
def baseEnd_535957 : Nat := 13590298821820483924577

theorem tailTrace_535957 : CollatzResearch.WordTrace tailWord_535957 prefixEnd_535957 13590298821820483924577 := by
  unfold tailWord_535957
  simp only [CollatzResearch.WordTrace]
  refine ⟨19547957719326798013302125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13031971812884532008868083 19547957719326798013302125)
  ·
    refine ⟨7330484144747549254988297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19547957719326798013302125 7330484144747549254988297)
    ·
      refine ⟨5497863108560661941241223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7330484144747549254988297 5497863108560661941241223)
      ·
        refine ⟨8246794662840992911861835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5497863108560661941241223 8246794662840992911861835)
        ·
          refine ⟨12370191994261489367792753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8246794662840992911861835 12370191994261489367792753)
          ·
            refine ⟨9277643995696117025844565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12370191994261489367792753 9277643995696117025844565)
            ·
              refine ⟨13590298821820483924577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 9277643995696117025844565 13590298821820483924577)
              ·
                rfl

theorem cell21_535957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 11].length) (baseStart_535957 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_535957 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_535957 prefixEnd_535957 := by exact prefixLift 535957
  have htrace : WordTrace (prefixWord ++ tailWord_535957) baseStart_535957 baseEnd_535957 := by
    simpa [prefixWord, tailWord_535957, baseEnd_535957] using wordTrace_append hprefix tailTrace_535957
  have hstable : (prefixWord ++ tailWord_535957).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535957).length < 2 ^ (prefixWord ++ tailWord_535957).sum := by decide
  have hdescent : baseEnd_535957 < baseStart_535957 := by decide
  rcases family_descends (prefixWord ++ tailWord_535957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536081 : List Nat := [1, 2, 2, 1, 1, 2, 3, 6, 3]
def baseStart_536081 : Nat := 118140960795 + 536081 * 2 ^ 59
def prefixEnd_536081 : Nat := 4983230072969 + 3 ^ 40 * 536081 * 2
def baseEnd_536081 : Nat := 122340987885787695254273

theorem tailTrace_536081 : CollatzResearch.WordTrace tailWord_536081 prefixEnd_536081 122340987885787695254273 := by
  unfold tailWord_536081
  simp only [CollatzResearch.WordTrace]
  refine ⟨19552480370877567190816097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13034986913918378127210731 19552480370877567190816097)
  ·
    refine ⟨14664360278158175393112073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19552480370877567190816097 14664360278158175393112073)
    ·
      refine ⟨10998270208618631544834055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14664360278158175393112073 10998270208618631544834055)
      ·
        refine ⟨16497405312927947317251083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10998270208618631544834055 16497405312927947317251083)
        ·
          refine ⟨24746107969391920975876625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16497405312927947317251083 24746107969391920975876625)
          ·
            refine ⟨18559580977043940731907469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24746107969391920975876625 18559580977043940731907469)
            ·
              refine ⟨6959842866391477774465301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18559580977043940731907469 6959842866391477774465301)
              ·
                refine ⟨326242634362100520678061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 6959842866391477774465301 326242634362100520678061)
                ·
                  refine ⟨122340987885787695254273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 326242634362100520678061 122340987885787695254273)
                  ·
                    rfl

theorem cell21_536081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 6, 3].length) (baseStart_536081 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_536081 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_536081 prefixEnd_536081 := by exact prefixLift 536081
  have htrace : WordTrace (prefixWord ++ tailWord_536081) baseStart_536081 baseEnd_536081 := by
    simpa [prefixWord, tailWord_536081, baseEnd_536081] using wordTrace_append hprefix tailTrace_536081
  have hstable : (prefixWord ++ tailWord_536081).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536081).length < 2 ^ (prefixWord ++ tailWord_536081).sum := by decide
  have hdescent : baseEnd_536081 < baseStart_536081 := by decide
  rcases family_descends (prefixWord ++ tailWord_536081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536095 : List Nat := [1, 1, 2, 4, 1, 1, 2, 5, 4]
def baseStart_536095 : Nat := 118140960795 + 536095 * 2 ^ 59
def prefixEnd_536095 : Nat := 4983230072969 + 3 ^ 40 * 536095 * 2
def baseEnd_536095 : Nat := 122344182876526782020911

theorem tailTrace_536095 : CollatzResearch.WordTrace tailWord_536095 prefixEnd_536095 122344182876526782020911 := by
  unfold tailWord_536095
  simp only [CollatzResearch.WordTrace]
  refine ⟨19552990992826847581825739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13035327328551231721217159 19552990992826847581825739)
  ·
    refine ⟨29329486489240271372738609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19552990992826847581825739 29329486489240271372738609)
    ·
      refine ⟨21997114866930203529553957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29329486489240271372738609 21997114866930203529553957)
      ·
        refine ⟨4124459037549413161791367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21997114866930203529553957 4124459037549413161791367)
        ·
          refine ⟨6186688556324119742687051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4124459037549413161791367 6186688556324119742687051)
          ·
            refine ⟨9280032834486179614030577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6186688556324119742687051 9280032834486179614030577)
            ·
              refine ⟨6960024625864634710522933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9280032834486179614030577 6960024625864634710522933)
              ·
                refine ⟨652502308674809504111525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6960024625864634710522933 652502308674809504111525)
                ·
                  refine ⟨122344182876526782020911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 652502308674809504111525 122344182876526782020911)
                  ·
                    rfl

theorem cell21_536095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 5, 4].length) (baseStart_536095 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_536095 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_536095 prefixEnd_536095 := by exact prefixLift 536095
  have htrace : WordTrace (prefixWord ++ tailWord_536095) baseStart_536095 baseEnd_536095 := by
    simpa [prefixWord, tailWord_536095, baseEnd_536095] using wordTrace_append hprefix tailTrace_536095
  have hstable : (prefixWord ++ tailWord_536095).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536095).length < 2 ^ (prefixWord ++ tailWord_536095).sum := by decide
  have hdescent : baseEnd_536095 < baseStart_536095 := by decide
  rcases family_descends (prefixWord ++ tailWord_536095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536202 : List Nat := [3, 1, 2, 3, 2, 1, 3, 6]
def baseStart_536202 : Nat := 118140960795 + 536202 * 2 ^ 59
def prefixEnd_536202 : Nat := 4983230072969 + 3 ^ 40 * 536202 * 2
def baseEnd_536202 : Nat := 40789533911439457912453

theorem tailTrace_536202 : CollatzResearch.WordTrace tailWord_536202 prefixEnd_536202 40789533911439457912453 := by
  unfold tailWord_536202
  simp only [CollatzResearch.WordTrace]
  refine ⟨4889223400859801213992715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13037929068959469903980573 4889223400859801213992715)
  ·
    refine ⟨7333835101289701820989073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4889223400859801213992715 7333835101289701820989073)
    ·
      refine ⟨5500376325967276365741805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7333835101289701820989073 5500376325967276365741805)
      ·
        refine ⟨2062641122237728637153177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5500376325967276365741805 2062641122237728637153177)
        ·
          refine ⟨1546980841678296477864883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2062641122237728637153177 1546980841678296477864883)
          ·
            refine ⟨2320471262517444716797325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1546980841678296477864883 2320471262517444716797325)
            ·
              refine ⟨870176723444041768798997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2320471262517444716797325 870176723444041768798997)
              ·
                refine ⟨40789533911439457912453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 870176723444041768798997 40789533911439457912453)
                ·
                  rfl

theorem cell21_536202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 3, 6].length) (baseStart_536202 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_536202 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_536202 prefixEnd_536202 := by exact prefixLift 536202
  have htrace : WordTrace (prefixWord ++ tailWord_536202) baseStart_536202 baseEnd_536202 := by
    simpa [prefixWord, tailWord_536202, baseEnd_536202] using wordTrace_append hprefix tailTrace_536202
  have hstable : (prefixWord ++ tailWord_536202).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536202).length < 2 ^ (prefixWord ++ tailWord_536202).sum := by decide
  have hdescent : baseEnd_536202 < baseStart_536202 := by decide
  rcases family_descends (prefixWord ++ tailWord_536202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536216 : List Nat := [2, 1, 2, 4, 1, 2, 1, 1, 7]
def baseStart_536216 : Nat := 118140960795 + 536216 * 2 ^ 59
def prefixEnd_536216 : Nat := 4983230072969 + 3 ^ 40 * 536216 * 2
def baseEnd_536216 : Nat := 122371796725057460503997

theorem tailTrace_536216 : CollatzResearch.WordTrace tailWord_536216 prefixEnd_536216 122371796725057460503997 := by
  unfold tailWord_536216
  simp only [CollatzResearch.WordTrace]
  refine ⟨9778702112694242623490251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13038269483592323497987001 9778702112694242623490251)
  ·
    refine ⟨14668053169041363935235377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9778702112694242623490251 14668053169041363935235377)
    ·
      refine ⟨11001039876781022951426533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14668053169041363935235377 11001039876781022951426533)
      ·
        refine ⟨2062694976896441803392475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11001039876781022951426533 2062694976896441803392475)
        ·
          refine ⟨3094042465344662705088713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2062694976896441803392475 3094042465344662705088713)
          ·
            refine ⟨2320531849008497028816535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3094042465344662705088713 2320531849008497028816535)
            ·
              refine ⟨3480797773512745543224803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2320531849008497028816535 3480797773512745543224803)
              ·
                refine ⟨5221196660269118314837205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3480797773512745543224803 5221196660269118314837205)
                ·
                  refine ⟨122371796725057460503997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5221196660269118314837205 122371796725057460503997)
                  ·
                    rfl

theorem cell21_536216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 1, 7].length) (baseStart_536216 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_536216 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_536216 prefixEnd_536216 := by exact prefixLift 536216
  have htrace : WordTrace (prefixWord ++ tailWord_536216) baseStart_536216 baseEnd_536216 := by
    simpa [prefixWord, tailWord_536216, baseEnd_536216] using wordTrace_append hprefix tailTrace_536216
  have hstable : (prefixWord ++ tailWord_536216).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536216).length < 2 ^ (prefixWord ++ tailWord_536216).sum := by decide
  have hdescent : baseEnd_536216 < baseStart_536216 := by decide
  rcases family_descends (prefixWord ++ tailWord_536216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536247 : List Nat := [1, 1, 3, 1, 5, 2, 1, 1, 6]
def baseStart_536247 : Nat := 118140960795 + 536247 * 2 ^ 59
def prefixEnd_536247 : Nat := 4983230072969 + 3 ^ 40 * 536247 * 2
def baseEnd_536247 : Nat := 122378871347408295487267

theorem tailTrace_536247 : CollatzResearch.WordTrace tailWord_536247 prefixEnd_536247 122378871347408295487267 := by
  unfold tailWord_536247
  simp only [CollatzResearch.WordTrace]
  refine ⟨19558534888276177541358995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13039023258850785027572663 19558534888276177541358995)
  ·
    refine ⟨29337802332414266312038493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19558534888276177541358995 29337802332414266312038493)
    ·
      refine ⟨11001675874655349867014435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29337802332414266312038493 11001675874655349867014435)
      ·
        refine ⟨16502513811983024800521653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11001675874655349867014435 16502513811983024800521653)
        ·
          refine ⟨1547110669873408575048905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16502513811983024800521653 1547110669873408575048905)
          ·
            refine ⟨1160333002405056431286679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1547110669873408575048905 1160333002405056431286679)
            ·
              refine ⟨1740499503607584646930019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1160333002405056431286679 1740499503607584646930019)
              ·
                refine ⟨2610749255411376970395029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1740499503607584646930019 2610749255411376970395029)
                ·
                  refine ⟨122378871347408295487267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2610749255411376970395029 122378871347408295487267)
                  ·
                    rfl

theorem cell21_536247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 1, 6].length) (baseStart_536247 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_536247 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_536247 prefixEnd_536247 := by exact prefixLift 536247
  have htrace : WordTrace (prefixWord ++ tailWord_536247) baseStart_536247 baseEnd_536247 := by
    simpa [prefixWord, tailWord_536247, baseEnd_536247] using wordTrace_append hprefix tailTrace_536247
  have hstable : (prefixWord ++ tailWord_536247).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536247).length < 2 ^ (prefixWord ++ tailWord_536247).sum := by decide
  have hdescent : baseEnd_536247 < baseStart_536247 := by decide
  rcases family_descends (prefixWord ++ tailWord_536247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536264 : List Nat := [2, 1, 3, 1, 2, 2, 5, 1, 4]
def baseStart_536264 : Nat := 118140960795 + 536264 * 2 ^ 59
def prefixEnd_536264 : Nat := 4983230072969 + 3 ^ 40 * 536264 * 2
def baseEnd_536264 : Nat := 122382750979020043703899

theorem tailTrace_536264 : CollatzResearch.WordTrace tailWord_536264 prefixEnd_536264 122382750979020043703899 := by
  unfold tailWord_536264
  simp only [CollatzResearch.WordTrace]
  refine ⟨9779577464607294722363923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13039436619476392963151897 9779577464607294722363923)
  ·
    refine ⟨14669366196910942083545885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9779577464607294722363923 14669366196910942083545885)
    ·
      refine ⟨5501012323841603281329707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14669366196910942083545885 5501012323841603281329707)
      ·
        refine ⟨8251518485762404921994561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5501012323841603281329707 8251518485762404921994561)
        ·
          refine ⟨6188638864321803691495921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8251518485762404921994561 6188638864321803691495921)
          ·
            refine ⟨4641479148241352768621941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6188638864321803691495921 4641479148241352768621941)
            ·
              refine ⟨435138670147626822058307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4641479148241352768621941 435138670147626822058307)
              ·
                refine ⟨652708005221440233087461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 435138670147626822058307 652708005221440233087461)
                ·
                  refine ⟨122382750979020043703899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 652708005221440233087461 122382750979020043703899)
                  ·
                    rfl

theorem cell21_536264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 5, 1, 4].length) (baseStart_536264 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_536264 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_536264 prefixEnd_536264 := by exact prefixLift 536264
  have htrace : WordTrace (prefixWord ++ tailWord_536264) baseStart_536264 baseEnd_536264 := by
    simpa [prefixWord, tailWord_536264, baseEnd_536264] using wordTrace_append hprefix tailTrace_536264
  have hstable : (prefixWord ++ tailWord_536264).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536264).length < 2 ^ (prefixWord ++ tailWord_536264).sum := by decide
  have hdescent : baseEnd_536264 < baseStart_536264 := by decide
  rcases family_descends (prefixWord ++ tailWord_536264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536275 : List Nat := [1, 1, 1, 2, 1, 1, 1, 2, 11]
def baseStart_536275 : Nat := 118140960795 + 536275 * 2 ^ 59
def prefixEnd_536275 : Nat := 4983230072969 + 3 ^ 40 * 536275 * 2
def baseEnd_536275 : Nat := 122385261328886469020543

theorem tailTrace_536275 : CollatzResearch.WordTrace tailWord_536275 prefixEnd_536275 122385261328886469020543 := by
  unfold tailWord_536275
  simp only [CollatzResearch.WordTrace]
  refine ⟨19559556132174738323378279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13039704088116492215585519 19559556132174738323378279)
  ·
    refine ⟨29339334198262107485067419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19559556132174738323378279 29339334198262107485067419)
    ·
      refine ⟨44009001297393161227601129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29339334198262107485067419 44009001297393161227601129)
      ·
        refine ⟨33006750973044870920700847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44009001297393161227601129 33006750973044870920700847)
        ·
          refine ⟨49510126459567306381051271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33006750973044870920700847 49510126459567306381051271)
          ·
            refine ⟨74265189689350959571576907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49510126459567306381051271 74265189689350959571576907)
            ·
              refine ⟨111397784534026439357365361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74265189689350959571576907 111397784534026439357365361)
              ·
                refine ⟨83548338400519829518024021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 111397784534026439357365361 83548338400519829518024021)
                ·
                  refine ⟨122385261328886469020543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 83548338400519829518024021 122385261328886469020543)
                  ·
                    rfl

theorem cell21_536275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 11].length) (baseStart_536275 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_536275 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_536275 prefixEnd_536275 := by exact prefixLift 536275
  have htrace : WordTrace (prefixWord ++ tailWord_536275) baseStart_536275 baseEnd_536275 := by
    simpa [prefixWord, tailWord_536275, baseEnd_536275] using wordTrace_append hprefix tailTrace_536275
  have hstable : (prefixWord ++ tailWord_536275).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536275).length < 2 ^ (prefixWord ++ tailWord_536275).sum := by decide
  have hdescent : baseEnd_536275 < baseStart_536275 := by decide
  rcases family_descends (prefixWord ++ tailWord_536275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536284 : List Nat := [2, 2, 5, 1, 2, 2, 1, 3, 3]
def baseStart_536284 : Nat := 118140960795 + 536284 * 2 ^ 59
def prefixEnd_536284 : Nat := 4983230072969 + 3 ^ 40 * 536284 * 2
def baseEnd_536284 : Nat := 122387315251504453370525

theorem tailTrace_536284 : CollatzResearch.WordTrace tailWord_536284 prefixEnd_536284 122387315251504453370525 := by
  unfold tailWord_536284
  simp only [CollatzResearch.WordTrace]
  refine ⟨9779942194571066430227953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13039922926094755240303937 9779942194571066430227953)
  ·
    refine ⟨7334956645928299822670965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9779942194571066430227953 7334956645928299822670965)
    ·
      refine ⟨687652185555778108375403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7334956645928299822670965 687652185555778108375403)
      ·
        refine ⟨1031478278333667162563105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 687652185555778108375403 1031478278333667162563105)
        ·
          refine ⟨773608708750250371922329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1031478278333667162563105 773608708750250371922329)
          ·
            refine ⟨580206531562687778941747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 773608708750250371922329 580206531562687778941747)
            ·
              refine ⟨870309797344031668412621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 580206531562687778941747 870309797344031668412621)
              ·
                refine ⟨326366174004011875654733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 870309797344031668412621 326366174004011875654733)
                ·
                  refine ⟨122387315251504453370525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 326366174004011875654733 122387315251504453370525)
                  ·
                    rfl

theorem cell21_536284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 1, 3, 3].length) (baseStart_536284 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_536284 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_536284 prefixEnd_536284 := by exact prefixLift 536284
  have htrace : WordTrace (prefixWord ++ tailWord_536284) baseStart_536284 baseEnd_536284 := by
    simpa [prefixWord, tailWord_536284, baseEnd_536284] using wordTrace_append hprefix tailTrace_536284
  have hstable : (prefixWord ++ tailWord_536284).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536284).length < 2 ^ (prefixWord ++ tailWord_536284).sum := by decide
  have hdescent : baseEnd_536284 < baseStart_536284 := by decide
  rcases family_descends (prefixWord ++ tailWord_536284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536295 : List Nat := [1, 1, 5, 4, 1, 2, 7]
def baseStart_536295 : Nat := 118140960795 + 536295 * 2 ^ 59
def prefixEnd_536295 : Nat := 4983230072969 + 3 ^ 40 * 536295 * 2
def baseEnd_536295 : Nat := 13598869511263430965241

theorem tailTrace_536295 : CollatzResearch.WordTrace tailWord_536295 prefixEnd_536295 13598869511263430965241 := by
  unfold tailWord_536295
  simp only [CollatzResearch.WordTrace]
  refine ⟨19560285592102281739106339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13040190394734854492737559 19560285592102281739106339)
  ·
    refine ⟨29340428388153422608659509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19560285592102281739106339 29340428388153422608659509)
    ·
      refine ⟨2750665161389383369561829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 29340428388153422608659509 2750665161389383369561829)
      ·
        refine ⟨515749717760509381792843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2750665161389383369561829 515749717760509381792843)
        ·
          refine ⟨773624576640764072689265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 515749717760509381792843 773624576640764072689265)
          ·
            refine ⟨580218432480573054516949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 773624576640764072689265 580218432480573054516949)
            ·
              refine ⟨13598869511263430965241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 580218432480573054516949 13598869511263430965241)
              ·
                rfl

theorem cell21_536295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 7].length) (baseStart_536295 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_536295 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_536295 prefixEnd_536295 := by exact prefixLift 536295
  have htrace : WordTrace (prefixWord ++ tailWord_536295) baseStart_536295 baseEnd_536295 := by
    simpa [prefixWord, tailWord_536295, baseEnd_536295] using wordTrace_append hprefix tailTrace_536295
  have hstable : (prefixWord ++ tailWord_536295).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536295).length < 2 ^ (prefixWord ++ tailWord_536295).sum := by decide
  have hdescent : baseEnd_536295 < baseStart_536295 := by decide
  rcases family_descends (prefixWord ++ tailWord_536295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536371 : List Nat := [1, 1, 1, 2, 8, 1, 1, 6]
def baseStart_536371 : Nat := 118140960795 + 536371 * 2 ^ 59
def prefixEnd_536371 : Nat := 4983230072969 + 3 ^ 40 * 536371 * 2
def baseEnd_536371 : Nat := 40802389945603878473449

theorem tailTrace_536371 : CollatzResearch.WordTrace tailWord_536371 prefixEnd_536371 40802389945603878473449 := by
  unfold tailWord_536371
  simp only [CollatzResearch.WordTrace]
  refine ⟨19563057539826946718872967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13042038359884631145915311 19563057539826946718872967)
  ·
    refine ⟨29344586309740420078309451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19563057539826946718872967 29344586309740420078309451)
    ·
      refine ⟨44016879464610630117464177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29344586309740420078309451 44016879464610630117464177)
      ·
        refine ⟨33012659598457972588098133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44016879464610630117464177 33012659598457972588098133)
        ·
          refine ⟨386867104669429366266775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 33012659598457972588098133 386867104669429366266775)
          ·
            refine ⟨580300657004144049400163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 386867104669429366266775 580300657004144049400163)
            ·
              refine ⟨870450985506216074100245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 580300657004144049400163 870450985506216074100245)
              ·
                refine ⟨40802389945603878473449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 870450985506216074100245 40802389945603878473449)
                ·
                  rfl

theorem cell21_536371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 1, 6].length) (baseStart_536371 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_536371 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_536371 prefixEnd_536371 := by exact prefixLift 536371
  have htrace : WordTrace (prefixWord ++ tailWord_536371) baseStart_536371 baseEnd_536371 := by
    simpa [prefixWord, tailWord_536371, baseEnd_536371] using wordTrace_append hprefix tailTrace_536371
  have hstable : (prefixWord ++ tailWord_536371).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536371).length < 2 ^ (prefixWord ++ tailWord_536371).sum := by decide
  have hdescent : baseEnd_536371 < baseStart_536371 := by decide
  rcases family_descends (prefixWord ++ tailWord_536371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536402 : List Nat := [3, 2, 2, 1, 1, 4, 2, 3, 3]
def baseStart_536402 : Nat := 118140960795 + 536402 * 2 ^ 59
def prefixEnd_536402 : Nat := 4983230072969 + 3 ^ 40 * 536402 * 2
def baseEnd_536402 : Nat := 122414244459162470403617

theorem tailTrace_536402 : CollatzResearch.WordTrace tailWord_536402 prefixEnd_536402 122414244459162470403617 := by
  unfold tailWord_536402
  simp only [CollatzResearch.WordTrace]
  refine ⟨4891047050678659753312865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13042792135143092675500973 4891047050678659753312865)
  ·
    refine ⟨3668285288008994814984649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4891047050678659753312865 3668285288008994814984649)
    ·
      refine ⟨2751213966006746111238487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3668285288008994814984649 2751213966006746111238487)
      ·
        refine ⟨4126820949010119166857731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2751213966006746111238487 4126820949010119166857731)
        ·
          refine ⟨6190231423515178750286597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4126820949010119166857731 6190231423515178750286597)
          ·
            refine ⟨1160668391909096015678737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6190231423515178750286597 1160668391909096015678737)
            ·
              refine ⟨870501293931822011759053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1160668391909096015678737 870501293931822011759053)
              ·
                refine ⟨326437985224433254409645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 870501293931822011759053 326437985224433254409645)
                ·
                  refine ⟨122414244459162470403617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 326437985224433254409645 122414244459162470403617)
                  ·
                    rfl

theorem cell21_536402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 2, 3, 3].length) (baseStart_536402 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_536402 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_536402 prefixEnd_536402 := by exact prefixLift 536402
  have htrace : WordTrace (prefixWord ++ tailWord_536402) baseStart_536402 baseEnd_536402 := by
    simpa [prefixWord, tailWord_536402, baseEnd_536402] using wordTrace_append hprefix tailTrace_536402
  have hstable : (prefixWord ++ tailWord_536402).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536402).length < 2 ^ (prefixWord ++ tailWord_536402).sum := by decide
  have hdescent : baseEnd_536402 < baseStart_536402 := by decide
  rcases family_descends (prefixWord ++ tailWord_536402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536416 : List Nat := [2, 1, 1, 3, 3, 4, 1, 2, 4]
def baseStart_536416 : Nat := 118140960795 + 536416 * 2 ^ 59
def prefixEnd_536416 : Nat := 4983230072969 + 3 ^ 40 * 536416 * 2
def baseEnd_536416 : Nat := 122417439449901557170255

theorem tailTrace_536416 : CollatzResearch.WordTrace tailWord_536416 prefixEnd_536416 122417439449901557170255 := by
  unfold tailWord_536416
  simp only [CollatzResearch.WordTrace]
  refine ⟨9782349412331959702130551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13043132549775946269507401 9782349412331959702130551)
  ·
    refine ⟨14673524118497939553195827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9782349412331959702130551 14673524118497939553195827)
    ·
      refine ⟨22010286177746909329793741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14673524118497939553195827 22010286177746909329793741)
      ·
        refine ⟨8253857316655090998672653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22010286177746909329793741 8253857316655090998672653)
        ·
          refine ⟨3095196493745659124502245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8253857316655090998672653 3095196493745659124502245)
          ·
            refine ⟨580349342577311085844171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3095196493745659124502245 580349342577311085844171)
            ·
              refine ⟨870524013865966628766257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 580349342577311085844171 870524013865966628766257)
              ·
                refine ⟨652893010399474971574693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 870524013865966628766257 652893010399474971574693)
                ·
                  refine ⟨122417439449901557170255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 652893010399474971574693 122417439449901557170255)
                  ·
                    rfl

theorem cell21_536416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 1, 2, 4].length) (baseStart_536416 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_536416 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_536416 prefixEnd_536416 := by exact prefixLift 536416
  have htrace : WordTrace (prefixWord ++ tailWord_536416) baseStart_536416 baseEnd_536416 := by
    simpa [prefixWord, tailWord_536416, baseEnd_536416] using wordTrace_append hprefix tailTrace_536416
  have hstable : (prefixWord ++ tailWord_536416).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536416).length < 2 ^ (prefixWord ++ tailWord_536416).sum := by decide
  have hdescent : baseEnd_536416 < baseStart_536416 := by decide
  rcases family_descends (prefixWord ++ tailWord_536416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536503 : List Nat := [1, 1, 3, 1, 3, 1, 1, 3, 7]
def baseStart_536503 : Nat := 118140960795 + 536503 * 2 ^ 59
def prefixEnd_536503 : Nat := 4983230072969 + 3 ^ 40 * 536503 * 2
def baseEnd_536503 : Nat := 122437294035208739220077

theorem tailTrace_536503 : CollatzResearch.WordTrace tailWord_536503 prefixEnd_536503 122437294035208739220077 := by
  unfold tailWord_536503
  simp only [CollatzResearch.WordTrace]
  refine ⟨19567871975348733262678163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13045247983565822175118775 19567871975348733262678163)
  ·
    refine ⟨29351807963023099894017245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19567871975348733262678163 29351807963023099894017245)
    ·
      refine ⟨11006927986133662460256467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29351807963023099894017245 11006927986133662460256467)
      ·
        refine ⟨16510391979200493690384701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11006927986133662460256467 16510391979200493690384701)
        ·
          refine ⟨6191396992200185133894263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16510391979200493690384701 6191396992200185133894263)
          ·
            refine ⟨9287095488300277700841395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6191396992200185133894263 9287095488300277700841395)
            ·
              refine ⟨13930643232450416551262093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9287095488300277700841395 13930643232450416551262093)
              ·
                refine ⟨5223991212168906206723285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13930643232450416551262093 5223991212168906206723285)
                ·
                  refine ⟨122437294035208739220077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5223991212168906206723285 122437294035208739220077)
                  ·
                    rfl

theorem cell21_536503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 3, 7].length) (baseStart_536503 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_536503 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_536503 prefixEnd_536503 := by exact prefixLift 536503
  have htrace : WordTrace (prefixWord ++ tailWord_536503) baseStart_536503 baseEnd_536503 := by
    simpa [prefixWord, tailWord_536503, baseEnd_536503] using wordTrace_append hprefix tailTrace_536503
  have hstable : (prefixWord ++ tailWord_536503).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536503).length < 2 ^ (prefixWord ++ tailWord_536503).sum := by decide
  have hdescent : baseEnd_536503 < baseStart_536503 := by decide
  rcases family_descends (prefixWord ++ tailWord_536503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536616 : List Nat := [2, 1, 5, 3, 1, 2, 2, 5]
def baseStart_536616 : Nat := 118140960795 + 536616 * 2 ^ 59
def prefixEnd_536616 : Nat := 4983230072969 + 3 ^ 40 * 536616 * 2
def baseEnd_536616 : Nat := 40821027391581884612171

theorem tailTrace_536616 : CollatzResearch.WordTrace tailWord_536616 prefixEnd_536616 40821027391581884612171 := by
  unfold tailWord_536616
  simp only [CollatzResearch.WordTrace]
  refine ⟨9785996711969676780770851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13047995615959569041027801 9785996711969676780770851)
  ·
    refine ⟨14678995067954515171156277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9785996711969676780770851 14678995067954515171156277)
    ·
      refine ⟨1376155787620735797295901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14678995067954515171156277 1376155787620735797295901)
      ·
        refine ⟨516058420357775923985963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1376155787620735797295901 516058420357775923985963)
        ·
          refine ⟨774087630536663885978945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 516058420357775923985963 774087630536663885978945)
          ·
            refine ⟨580565722902497914484209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 774087630536663885978945 580565722902497914484209)
            ·
              refine ⟨435424292176873435863157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 580565722902497914484209 435424292176873435863157)
              ·
                refine ⟨40821027391581884612171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 435424292176873435863157 40821027391581884612171)
                ·
                  rfl

theorem cell21_536616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 2, 5].length) (baseStart_536616 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_536616 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_536616 prefixEnd_536616 := by exact prefixLift 536616
  have htrace : WordTrace (prefixWord ++ tailWord_536616) baseStart_536616 baseEnd_536616 := by
    simpa [prefixWord, tailWord_536616, baseEnd_536616] using wordTrace_append hprefix tailTrace_536616
  have hstable : (prefixWord ++ tailWord_536616).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536616).length < 2 ^ (prefixWord ++ tailWord_536616).sum := by decide
  have hdescent : baseEnd_536616 < baseStart_536616 := by decide
  rcases family_descends (prefixWord ++ tailWord_536616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536641 : List Nat := [1, 2, 5, 1, 2, 1, 9]
def baseStart_536641 : Nat := 118140960795 + 536641 * 2 ^ 59
def prefixEnd_536641 : Nat := 4983230072969 + 3 ^ 40 * 536641 * 2
def baseEnd_536641 : Nat := 13607643057261240657755

theorem tailTrace_536641 : CollatzResearch.WordTrace tailWord_536641 prefixEnd_536641 13607643057261240657755 := by
  unfold tailWord_536641
  simp only [CollatzResearch.WordTrace]
  refine ⟨19572905248848782831201777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13048603499232521887467851 19572905248848782831201777)
  ·
    refine ⟨14679678936636587123401333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19572905248848782831201777 14679678936636587123401333)
    ·
      refine ⟨1376219900309680042818875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14679678936636587123401333 1376219900309680042818875)
      ·
        refine ⟨2064329850464520064228313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1376219900309680042818875 2064329850464520064228313)
        ·
          refine ⟨1548247387848390048171235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2064329850464520064228313 1548247387848390048171235)
          ·
            refine ⟨2322371081772585072256853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1548247387848390048171235 2322371081772585072256853)
            ·
              refine ⟨13607643057261240657755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2322371081772585072256853 13607643057261240657755)
              ·
                rfl

theorem cell21_536641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 9].length) (baseStart_536641 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_536641 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_536641 prefixEnd_536641 := by exact prefixLift 536641
  have htrace : WordTrace (prefixWord ++ tailWord_536641) baseStart_536641 baseEnd_536641 := by
    simpa [prefixWord, tailWord_536641, baseEnd_536641] using wordTrace_append hprefix tailTrace_536641
  have hstable : (prefixWord ++ tailWord_536641).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536641).length < 2 ^ (prefixWord ++ tailWord_536641).sum := by decide
  have hdescent : baseEnd_536641 < baseStart_536641 := by decide
  rcases family_descends (prefixWord ++ tailWord_536641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536658 : List Nat := [3, 2, 2, 1, 4, 1, 2, 6]
def baseStart_536658 : Nat := 118140960795 + 536658 * 2 ^ 59
def prefixEnd_536658 : Nat := 4983230072969 + 3 ^ 40 * 536658 * 2
def baseEnd_536658 : Nat := 40824222382320971378809

theorem tailTrace_536658 : CollatzResearch.WordTrace tailWord_536658 prefixEnd_536658 40824222382320971378809 := by
  unfold tailWord_536658
  simp only [CollatzResearch.WordTrace]
  refine ⟨4893381322446798683642657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13049016859858129823047085 4893381322446798683642657)
  ·
    refine ⟨3670035991835099012731993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4893381322446798683642657 3670035991835099012731993)
    ·
      refine ⟨2752526993876324259548995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3670035991835099012731993 2752526993876324259548995)
      ·
        refine ⟨4128790490814486389323493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2752526993876324259548995 4128790490814486389323493)
        ·
          refine ⟨774148217027716197998155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4128790490814486389323493 774148217027716197998155)
          ·
            refine ⟨1161222325541574296997233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 774148217027716197998155 1161222325541574296997233)
            ·
              refine ⟨870916744156180722747925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1161222325541574296997233 870916744156180722747925)
              ·
                refine ⟨40824222382320971378809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 870916744156180722747925 40824222382320971378809)
                ·
                  rfl

theorem cell21_536658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 2, 6].length) (baseStart_536658 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_536658 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_536658 prefixEnd_536658 := by exact prefixLift 536658
  have htrace : WordTrace (prefixWord ++ tailWord_536658) baseStart_536658 baseEnd_536658 := by
    simpa [prefixWord, tailWord_536658, baseEnd_536658] using wordTrace_append hprefix tailTrace_536658
  have hstable : (prefixWord ++ tailWord_536658).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536658).length < 2 ^ (prefixWord ++ tailWord_536658).sum := by decide
  have hdescent : baseEnd_536658 < baseStart_536658 := by decide
  rcases family_descends (prefixWord ++ tailWord_536658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536700 : List Nat := [2, 2, 2, 1, 1, 13]
def baseStart_536700 : Nat := 118140960795 + 536700 * 2 ^ 59
def prefixEnd_536700 : Nat := 4983230072969 + 3 ^ 40 * 536700 * 2
def baseEnd_536700 : Nat := 4536379708117784238383

theorem tailTrace_536700 : CollatzResearch.WordTrace tailWord_536700 prefixEnd_536700 4536379708117784238383 := by
  unfold tailWord_536700
  simp only [CollatzResearch.WordTrace]
  refine ⟨9787528577817517953799777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13050038103756690605066369 9787528577817517953799777)
  ·
    refine ⟨7340646433363138465349833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9787528577817517953799777 7340646433363138465349833)
    ·
      refine ⟨5505484825022353849012375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7340646433363138465349833 5505484825022353849012375)
      ·
        refine ⟨8258227237533530773518563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5505484825022353849012375 8258227237533530773518563)
        ·
          refine ⟨12387340856300296160277845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8258227237533530773518563 12387340856300296160277845)
          ·
            refine ⟨4536379708117784238383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 12387340856300296160277845 4536379708117784238383)
            ·
              rfl

theorem cell21_536700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 13].length) (baseStart_536700 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_536700 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_536700 prefixEnd_536700 := by exact prefixLift 536700
  have htrace : WordTrace (prefixWord ++ tailWord_536700) baseStart_536700 baseEnd_536700 := by
    simpa [prefixWord, tailWord_536700, baseEnd_536700] using wordTrace_append hprefix tailTrace_536700
  have hstable : (prefixWord ++ tailWord_536700).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536700).length < 2 ^ (prefixWord ++ tailWord_536700).sum := by decide
  have hdescent : baseEnd_536700 < baseStart_536700 := by decide
  rcases family_descends (prefixWord ++ tailWord_536700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536726 : List Nat := [5, 3, 2, 1, 1, 1, 3, 5]
def baseStart_536726 : Nat := 118140960795 + 536726 * 2 ^ 59
def prefixEnd_536726 : Nat := 4983230072969 + 3 ^ 40 * 536726 * 2
def baseEnd_536726 : Nat := 40829395224469969000985

theorem tailTrace_536726 : CollatzResearch.WordTrace tailWord_536726 prefixEnd_536726 40829395224469969000985 := by
  unfold tailWord_536726
  simp only [CollatzResearch.WordTrace]
  refine ⟨1223500340846302646752877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13050670302360561565364021 1223500340846302646752877)
  ·
    refine ⟨458812627817363492532329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1223500340846302646752877 458812627817363492532329)
    ·
      refine ⟨344109470863022619399247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 458812627817363492532329 344109470863022619399247)
      ·
        refine ⟨516164206294533929098871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 344109470863022619399247 516164206294533929098871)
        ·
          refine ⟨774246309441800893648307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 516164206294533929098871 774246309441800893648307)
          ·
            refine ⟨1161369464162701340472461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 774246309441800893648307 1161369464162701340472461)
            ·
              refine ⟨435513549061013002677173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1161369464162701340472461 435513549061013002677173)
              ·
                refine ⟨40829395224469969000985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 435513549061013002677173 40829395224469969000985)
                ·
                  rfl

theorem cell21_536726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 3, 5].length) (baseStart_536726 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_536726 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_536726 prefixEnd_536726 := by exact prefixLift 536726
  have htrace : WordTrace (prefixWord ++ tailWord_536726) baseStart_536726 baseEnd_536726 := by
    simpa [prefixWord, tailWord_536726, baseEnd_536726] using wordTrace_append hprefix tailTrace_536726
  have hstable : (prefixWord ++ tailWord_536726).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536726).length < 2 ^ (prefixWord ++ tailWord_536726).sum := by decide
  have hdescent : baseEnd_536726 < baseStart_536726 := by decide
  rcases family_descends (prefixWord ++ tailWord_536726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536776 : List Nat := [2, 1, 3, 1, 2, 1, 1, 10]
def baseStart_536776 : Nat := 118140960795 + 536776 * 2 ^ 59
def prefixEnd_536776 : Nat := 4983230072969 + 3 ^ 40 * 536776 * 2
def baseEnd_536776 : Nat := 40833198784873643723173

theorem tailTrace_536776 : CollatzResearch.WordTrace tailWord_536776 prefixEnd_536776 40833198784873643723173 := by
  unfold tailWord_536776
  simp only [CollatzResearch.WordTrace]
  refine ⟨9788914551679850443683091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13051886068906467258244121 9788914551679850443683091)
  ·
    refine ⟨14683371827519775665524637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9788914551679850443683091 14683371827519775665524637)
    ·
      refine ⟨5506264435319915874571739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14683371827519775665524637 5506264435319915874571739)
      ·
        refine ⟨8259396652979873811857609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5506264435319915874571739 8259396652979873811857609)
        ·
          refine ⟨6194547489734905358893207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8259396652979873811857609 6194547489734905358893207)
          ·
            refine ⟨9291821234602358038339811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6194547489734905358893207 9291821234602358038339811)
            ·
              refine ⟨13937731851903537057509717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9291821234602358038339811 13937731851903537057509717)
              ·
                refine ⟨40833198784873643723173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 13937731851903537057509717 40833198784873643723173)
                ·
                  rfl

theorem cell21_536776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 10].length) (baseStart_536776 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_536776 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_536776 prefixEnd_536776 := by exact prefixLift 536776
  have htrace : WordTrace (prefixWord ++ tailWord_536776) baseStart_536776 baseEnd_536776 := by
    simpa [prefixWord, tailWord_536776, baseEnd_536776] using wordTrace_append hprefix tailTrace_536776
  have hstable : (prefixWord ++ tailWord_536776).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536776).length < 2 ^ (prefixWord ++ tailWord_536776).sum := by decide
  have hdescent : baseEnd_536776 < baseStart_536776 := by decide
  rcases family_descends (prefixWord ++ tailWord_536776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536779 : List Nat := [1, 1, 1, 1, 3, 2, 7, 1, 4]
def baseStart_536779 : Nat := 118140960795 + 536779 * 2 ^ 59
def prefixEnd_536779 : Nat := 4983230072969 + 3 ^ 40 * 536779 * 2
def baseEnd_536779 : Nat := 122500280995493592619513

theorem tailTrace_536779 : CollatzResearch.WordTrace tailWord_536779 prefixEnd_536779 122500280995493592619513 := by
  unfold tailWord_536779
  simp only [CollatzResearch.WordTrace]
  refine ⟨19577938522348832399725391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13051959014899221599816927 19577938522348832399725391)
  ·
    refine ⟨29366907783523248599588087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19577938522348832399725391 29366907783523248599588087)
    ·
      refine ⟨44050361675284872899382131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29366907783523248599588087 44050361675284872899382131)
      ·
        refine ⟨66075542512927309349073197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44050361675284872899382131 66075542512927309349073197)
        ·
          refine ⟨24778328442347741005902449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66075542512927309349073197 24778328442347741005902449)
          ·
            refine ⟨18583746331760805754426837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24778328442347741005902449 18583746331760805754426837)
            ·
              refine ⟨435556554650643884869379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 18583746331760805754426837 435556554650643884869379)
              ·
                refine ⟨653334831975965827304069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 435556554650643884869379 653334831975965827304069)
                ·
                  refine ⟨122500280995493592619513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 653334831975965827304069 122500280995493592619513)
                  ·
                    rfl

theorem cell21_536779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 7, 1, 4].length) (baseStart_536779 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_536779 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_536779 prefixEnd_536779 := by exact prefixLift 536779
  have htrace : WordTrace (prefixWord ++ tailWord_536779) baseStart_536779 baseEnd_536779 := by
    simpa [prefixWord, tailWord_536779, baseEnd_536779] using wordTrace_append hprefix tailTrace_536779
  have hstable : (prefixWord ++ tailWord_536779).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536779).length < 2 ^ (prefixWord ++ tailWord_536779).sum := by decide
  have hdescent : baseEnd_536779 < baseStart_536779 := by decide
  rcases family_descends (prefixWord ++ tailWord_536779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536793 : List Nat := [1, 2, 1, 2, 3, 1, 6, 5]
def baseStart_536793 : Nat := 118140960795 + 536793 * 2 ^ 59
def prefixEnd_536793 : Nat := 4983230072969 + 3 ^ 40 * 536793 * 2
def baseEnd_536793 : Nat := 40834491995410893128717

theorem tailTrace_536793 : CollatzResearch.WordTrace tailWord_536793 prefixEnd_536793 40834491995410893128717 := by
  unfold tailWord_536793
  simp only [CollatzResearch.WordTrace]
  refine ⟨19578449144298112790735033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13052299429532075193823355 19578449144298112790735033)
  ·
    refine ⟨14683836858223584593051275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19578449144298112790735033 14683836858223584593051275)
    ·
      refine ⟨22025755287335376889576913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14683836858223584593051275 22025755287335376889576913)
      ·
        refine ⟨16519316465501532667182685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22025755287335376889576913 16519316465501532667182685)
        ·
          refine ⟨6194743674563074750193507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16519316465501532667182685 6194743674563074750193507)
          ·
            refine ⟨9292115511844612125290261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6194743674563074750193507 9292115511844612125290261)
            ·
              refine ⟨435567914617716193372981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 9292115511844612125290261 435567914617716193372981)
              ·
                refine ⟨40834491995410893128717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 435567914617716193372981 40834491995410893128717)
                ·
                  rfl

theorem cell21_536793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 6, 5].length) (baseStart_536793 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_536793 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_536793 prefixEnd_536793 := by exact prefixLift 536793
  have htrace : WordTrace (prefixWord ++ tailWord_536793) baseStart_536793 baseEnd_536793 := by
    simpa [prefixWord, tailWord_536793, baseEnd_536793] using wordTrace_append hprefix tailTrace_536793
  have hstable : (prefixWord ++ tailWord_536793).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536793).length < 2 ^ (prefixWord ++ tailWord_536793).sum := by decide
  have hdescent : baseEnd_536793 < baseStart_536793 := by decide
  rcases family_descends (prefixWord ++ tailWord_536793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536824 : List Nat := [2, 1, 2, 1, 1, 2, 1, 8, 3]
def baseStart_536824 : Nat := 118140960795 + 536824 * 2 ^ 59
def prefixEnd_536824 : Nat := 4983230072969 + 3 ^ 40 * 536824 * 2
def baseEnd_536824 : Nat := 122510550608583514369421

theorem tailTrace_536824 : CollatzResearch.WordTrace tailWord_536824 prefixEnd_536824 122510550608583514369421 := by
  unfold tailWord_536824
  simp only [CollatzResearch.WordTrace]
  refine ⟨9789789903592902542556763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13053053204790536723409017 9789789903592902542556763)
  ·
    refine ⟨14684684855389353813835145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9789789903592902542556763 14684684855389353813835145)
    ·
      refine ⟨11013513641542015360376359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14684684855389353813835145 11013513641542015360376359)
      ·
        refine ⟨16520270462313023040564539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11013513641542015360376359 16520270462313023040564539)
        ·
          refine ⟨24780405693469534560846809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16520270462313023040564539 24780405693469534560846809)
          ·
            refine ⟨18585304270102150920635107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24780405693469534560846809 18585304270102150920635107)
            ·
              refine ⟨27877956405153226380952661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18585304270102150920635107 27877956405153226380952661)
              ·
                refine ⟨326694801622889371651789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 27877956405153226380952661 326694801622889371651789)
                ·
                  refine ⟨122510550608583514369421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 326694801622889371651789 122510550608583514369421)
                  ·
                    rfl

theorem cell21_536824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 8, 3].length) (baseStart_536824 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_536824 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_536824 prefixEnd_536824 := by exact prefixLift 536824
  have htrace : WordTrace (prefixWord ++ tailWord_536824) baseStart_536824 baseEnd_536824 := by
    simpa [prefixWord, tailWord_536824, baseEnd_536824] using wordTrace_append hprefix tailTrace_536824
  have hstable : (prefixWord ++ tailWord_536824).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536824).length < 2 ^ (prefixWord ++ tailWord_536824).sum := by decide
  have hdescent : baseEnd_536824 < baseStart_536824 := by decide
  rcases family_descends (prefixWord ++ tailWord_536824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536869 : List Nat := [1, 3, 1, 2, 6, 8]
def baseStart_536869 : Nat := 118140960795 + 536869 * 2 ^ 59
def prefixEnd_536869 : Nat := 4983230072969 + 3 ^ 40 * 536869 * 2
def baseEnd_536869 : Nat := 4537808156358275411827

theorem tailTrace_536869 : CollatzResearch.WordTrace tailWord_536869 prefixEnd_536869 4537808156358275411827 := by
  unfold tailWord_536869
  simp only [CollatzResearch.WordTrace]
  refine ⟨19581221092022777770501661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13054147394681851847001107 19581221092022777770501661)
  ·
    refine ⟨7342957909508541663938123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19581221092022777770501661 7342957909508541663938123)
    ·
      refine ⟨11014436864262812495907185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7342957909508541663938123 11014436864262812495907185)
      ·
        refine ⟨8260827648197109371930389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11014436864262812495907185 8260827648197109371930389)
        ·
          refine ⟨387226296009239501809237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 8260827648197109371930389 387226296009239501809237)
          ·
            refine ⟨4537808156358275411827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 387226296009239501809237 4537808156358275411827)
            ·
              rfl

theorem cell21_536869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 8].length) (baseStart_536869 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_536869 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_536869 prefixEnd_536869 := by exact prefixLift 536869
  have htrace : WordTrace (prefixWord ++ tailWord_536869) baseStart_536869 baseEnd_536869 := by
    simpa [prefixWord, tailWord_536869, baseEnd_536869] using wordTrace_append hprefix tailTrace_536869
  have hstable : (prefixWord ++ tailWord_536869).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536869).length < 2 ^ (prefixWord ++ tailWord_536869).sum := by decide
  have hdescent : baseEnd_536869 < baseStart_536869 := by decide
  rcases family_descends (prefixWord ++ tailWord_536869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536872 : List Nat := [2, 1, 5, 1, 3, 1, 2, 2, 4]
def baseStart_536872 : Nat := 118140960795 + 536872 * 2 ^ 59
def prefixEnd_536872 : Nat := 4983230072969 + 3 ^ 40 * 536872 * 2
def baseEnd_536872 : Nat := 122521504862546097569323

theorem tailTrace_536872 : CollatzResearch.WordTrace tailWord_536872 prefixEnd_536872 122521504862546097569323 := by
  unfold tailWord_536872
  simp only [CollatzResearch.WordTrace]
  refine ⟨9790665255505954641430435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13054220340674606188573913 9790665255505954641430435)
  ·
    refine ⟨14685997883258931962145653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9790665255505954641430435 14685997883258931962145653)
    ·
      refine ⟨1376812301555524871451155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14685997883258931962145653 1376812301555524871451155)
      ·
        refine ⟨2065218452333287307176733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1376812301555524871451155 2065218452333287307176733)
        ·
          refine ⟨774456919624982740191275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2065218452333287307176733 774456919624982740191275)
          ·
            refine ⟨1161685379437474110286913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 774456919624982740191275 1161685379437474110286913)
            ·
              refine ⟨871264034578105582715185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1161685379437474110286913 871264034578105582715185)
              ·
                refine ⟨653448025933579187036389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 871264034578105582715185 653448025933579187036389)
                ·
                  refine ⟨122521504862546097569323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 653448025933579187036389 122521504862546097569323)
                  ·
                    rfl

theorem cell21_536872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 2, 2, 4].length) (baseStart_536872 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_536872 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_536872 prefixEnd_536872 := by exact prefixLift 536872
  have htrace : WordTrace (prefixWord ++ tailWord_536872) baseStart_536872 baseEnd_536872 := by
    simpa [prefixWord, tailWord_536872, baseEnd_536872] using wordTrace_append hprefix tailTrace_536872
  have hstable : (prefixWord ++ tailWord_536872).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536872).length < 2 ^ (prefixWord ++ tailWord_536872).sum := by decide
  have hdescent : baseEnd_536872 < baseStart_536872 := by decide
  rcases family_descends (prefixWord ++ tailWord_536872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536883 : List Nat := [1, 1, 1, 2, 5, 1, 2, 3, 5]
def baseStart_536883 : Nat := 118140960795 + 536883 * 2 ^ 59
def prefixEnd_536883 : Nat := 4983230072969 + 3 ^ 40 * 536883 * 2
def baseEnd_536883 : Nat := 122524015212412522885967

theorem tailTrace_536883 : CollatzResearch.WordTrace tailWord_536883 prefixEnd_536883 122524015212412522885967 := by
  unfold tailWord_536883
  simp only [CollatzResearch.WordTrace]
  refine ⟨19581731713972058161511303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13054487809314705441007535 19581731713972058161511303)
  ·
    refine ⟨29372597570958087242266955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19581731713972058161511303 29372597570958087242266955)
    ·
      refine ⟨44058896356437130863400433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29372597570958087242266955 44058896356437130863400433)
      ·
        refine ⟨33044172267327848147550325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44058896356437130863400433 33044172267327848147550325)
        ·
          refine ⟨3097891150061985763832843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 33044172267327848147550325 3097891150061985763832843)
          ·
            refine ⟨4646836725092978645749265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3097891150061985763832843 4646836725092978645749265)
            ·
              refine ⟨3485127543819733984311949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4646836725092978645749265 3485127543819733984311949)
              ·
                refine ⟨1306922828932400244116981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3485127543819733984311949 1306922828932400244116981)
                ·
                  refine ⟨122524015212412522885967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1306922828932400244116981 122524015212412522885967)
                  ·
                    rfl

theorem cell21_536883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 3, 5].length) (baseStart_536883 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_536883 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_536883 prefixEnd_536883 := by exact prefixLift 536883
  have htrace : WordTrace (prefixWord ++ tailWord_536883) baseStart_536883 baseEnd_536883 := by
    simpa [prefixWord, tailWord_536883, baseEnd_536883] using wordTrace_append hprefix tailTrace_536883
  have hstable : (prefixWord ++ tailWord_536883).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536883).length < 2 ^ (prefixWord ++ tailWord_536883).sum := by decide
  have hdescent : baseEnd_536883 < baseStart_536883 := by decide
  rcases family_descends (prefixWord ++ tailWord_536883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_537128 : List Nat := [2, 1, 5, 2, 1, 1, 2, 2, 5]
def baseStart_537128 : Nat := 118140960795 + 537128 * 2 ^ 59
def prefixEnd_537128 : Nat := 4983230072969 + 3 ^ 40 * 537128 * 2
def baseEnd_537128 : Nat := 122579927550346541302133

theorem tailTrace_537128 : CollatzResearch.WordTrace tailWord_537128 prefixEnd_537128 122579927550346541302133 := by
  unfold tailWord_537128
  simp only [CollatzResearch.WordTrace]
  refine ⟨9795333799042232502090019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13060445065389643336120025 9795333799042232502090019)
  ·
    refine ⟨14693000698563348753135029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9795333799042232502090019 14693000698563348753135029)
    ·
      refine ⟨1377468815490313945606409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14693000698563348753135029 1377468815490313945606409)
      ·
        refine ⟨1033101611617735459204807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1377468815490313945606409 1033101611617735459204807)
        ·
          refine ⟨1549652417426603188807211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1033101611617735459204807 1549652417426603188807211)
          ·
            refine ⟨2324478626139904783210817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1549652417426603188807211 2324478626139904783210817)
            ·
              refine ⟨1743358969604928587408113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2324478626139904783210817 1743358969604928587408113)
              ·
                refine ⟨1307519227203696440556085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1743358969604928587408113 1307519227203696440556085)
                ·
                  refine ⟨122579927550346541302133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1307519227203696440556085 122579927550346541302133)
                  ·
                    rfl

theorem cell21_537128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 2, 5].length) (baseStart_537128 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_537128 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_537128 prefixEnd_537128 := by exact prefixLift 537128
  have htrace : WordTrace (prefixWord ++ tailWord_537128) baseStart_537128 baseEnd_537128 := by
    simpa [prefixWord, tailWord_537128, baseEnd_537128] using wordTrace_append hprefix tailTrace_537128
  have hstable : (prefixWord ++ tailWord_537128).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_537128).length < 2 ^ (prefixWord ++ tailWord_537128).sum := by decide
  have hdescent : baseEnd_537128 < baseStart_537128 := by decide
  rcases family_descends (prefixWord ++ tailWord_537128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_537221 : List Nat := [1, 3, 1, 1, 4, 2, 4, 2, 3]
def baseStart_537221 : Nat := 118140960795 + 537221 * 2 ^ 59
def prefixEnd_537221 : Nat := 4983230072969 + 3 ^ 40 * 537221 * 2
def baseEnd_537221 : Nat := 122601151417399046251943

theorem tailTrace_537221 : CollatzResearch.WordTrace tailWord_537221 prefixEnd_537221 122601151417399046251943 := by
  unfold tailWord_537221
  simp only [CollatzResearch.WordTrace]
  refine ⟨19594059586747541887315517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13062706391165027924877011 19594059586747541887315517)
  ·
    refine ⟨7347772345030328207743319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19594059586747541887315517 7347772345030328207743319)
    ·
      refine ⟨11021658517545492311614979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7347772345030328207743319 11021658517545492311614979)
      ·
        refine ⟨16532487776318238467422469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11021658517545492311614979 16532487776318238467422469)
        ·
          refine ⟨3099841458059669712641713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16532487776318238467422469 3099841458059669712641713)
          ·
            refine ⟨2324881093544752284481285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3099841458059669712641713 2324881093544752284481285)
            ·
              refine ⟨435915205039641053340241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2324881093544752284481285 435915205039641053340241)
              ·
                refine ⟨326936403779730790005181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 435915205039641053340241 326936403779730790005181)
                ·
                  refine ⟨122601151417399046251943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 326936403779730790005181 122601151417399046251943)
                  ·
                    rfl

theorem cell21_537221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 4, 2, 3].length) (baseStart_537221 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_537221 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_537221 prefixEnd_537221 := by exact prefixLift 537221
  have htrace : WordTrace (prefixWord ++ tailWord_537221) baseStart_537221 baseEnd_537221 := by
    simpa [prefixWord, tailWord_537221, baseEnd_537221] using wordTrace_append hprefix tailTrace_537221
  have hstable : (prefixWord ++ tailWord_537221).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_537221).length < 2 ^ (prefixWord ++ tailWord_537221).sum := by decide
  have hdescent : baseEnd_537221 < baseStart_537221 := by decide
  rcases family_descends (prefixWord ++ tailWord_537221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_537280 : List Nat := [2, 1, 1, 2, 4, 2, 2, 4, 3]
def baseStart_537280 : Nat := 118140960795 + 537280 * 2 ^ 59
def prefixEnd_537280 : Nat := 4983230072969 + 3 ^ 40 * 537280 * 2
def baseEnd_537280 : Nat := 122614616021228054768489

theorem tailTrace_537280 : CollatzResearch.WordTrace tailWord_537280 prefixEnd_537280 122614616021228054768489 := by
  unfold tailWord_537280
  simp only [CollatzResearch.WordTrace]
  refine ⟨9798105746766897481856647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13064140995689196642475529 9798105746766897481856647)
  ·
    refine ⟨14697158620150346222784971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9798105746766897481856647 14697158620150346222784971)
    ·
      refine ⟨22045737930225519334177457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14697158620150346222784971 22045737930225519334177457)
      ·
        refine ⟨16534303447669139500633093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22045737930225519334177457 16534303447669139500633093)
        ·
          refine ⟨3100181896437963656368705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16534303447669139500633093 3100181896437963656368705)
          ·
            refine ⟨2325136422328472742276529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3100181896437963656368705 2325136422328472742276529)
            ·
              refine ⟨1743852316746354556707397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2325136422328472742276529 1743852316746354556707397)
              ·
                refine ⟨326972309389941479382637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1743852316746354556707397 326972309389941479382637)
                ·
                  refine ⟨122614616021228054768489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 326972309389941479382637 122614616021228054768489)
                  ·
                    rfl

theorem cell21_537280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 4, 3].length) (baseStart_537280 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_537280 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_537280 prefixEnd_537280 := by exact prefixLift 537280
  have htrace : WordTrace (prefixWord ++ tailWord_537280) baseStart_537280 baseEnd_537280 := by
    simpa [prefixWord, tailWord_537280, baseEnd_537280] using wordTrace_append hprefix tailTrace_537280
  have hstable : (prefixWord ++ tailWord_537280).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_537280).length < 2 ^ (prefixWord ++ tailWord_537280).sum := by decide
  have hdescent : baseEnd_537280 < baseStart_537280 := by decide
  rcases family_descends (prefixWord ++ tailWord_537280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_537286 : List Nat := [6, 1, 2, 1, 2, 1, 3, 1, 4]
def baseStart_537286 : Nat := 118140960795 + 537286 * 2 ^ 59
def prefixEnd_537286 : Nat := 4983230072969 + 3 ^ 40 * 537286 * 2
def baseEnd_537286 : Nat := 122615985302973377668477

theorem tailTrace_537286 : CollatzResearch.WordTrace tailWord_537286 prefixEnd_537286 122615985302973377668477 := by
  unfold tailWord_537286
  simp only [CollatzResearch.WordTrace]
  refine ⟨612388447859751812138491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 13064286887674705325621141 612388447859751812138491)
  ·
    refine ⟨918582671789627718207737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 612388447859751812138491 918582671789627718207737)
    ·
      refine ⟨688937003842220788655803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 918582671789627718207737 688937003842220788655803)
      ·
        refine ⟨1033405505763331182983705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 688937003842220788655803 1033405505763331182983705)
        ·
          refine ⟨775054129322498387237779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1033405505763331182983705 775054129322498387237779)
          ·
            refine ⟨1162581193983747580856669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 775054129322498387237779 1162581193983747580856669)
            ·
              refine ⟨435967947743905342821251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1162581193983747580856669 435967947743905342821251)
              ·
                refine ⟨653951921615858014231877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 435967947743905342821251 653951921615858014231877)
                ·
                  refine ⟨122615985302973377668477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 653951921615858014231877 122615985302973377668477)
                  ·
                    rfl

theorem cell21_537286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 3, 1, 4].length) (baseStart_537286 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_537286 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_537286 prefixEnd_537286 := by exact prefixLift 537286
  have htrace : WordTrace (prefixWord ++ tailWord_537286) baseStart_537286 baseEnd_537286 := by
    simpa [prefixWord, tailWord_537286, baseEnd_537286] using wordTrace_append hprefix tailTrace_537286
  have hstable : (prefixWord ++ tailWord_537286).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_537286).length < 2 ^ (prefixWord ++ tailWord_537286).sum := by decide
  have hdescent : baseEnd_537286 < baseStart_537286 := by decide
  rcases family_descends (prefixWord ++ tailWord_537286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_537390 : List Nat := [4, 1, 3, 2, 1, 1, 4, 2, 3]
def baseStart_537390 : Nat := 118140960795 + 537390 * 2 ^ 59
def prefixEnd_537390 : Nat := 4983230072969 + 3 ^ 40 * 537390 * 2
def baseEnd_537390 : Nat := 122639719519892307934931

theorem tailTrace_537390 : CollatzResearch.WordTrace tailWord_537390 prefixEnd_537390 122639719519892307934931 := by
  unfold tailWord_537390
  simp only [CollatzResearch.WordTrace]
  refine ⟨2450027940391910468777203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13066815682090189166811749 2450027940391910468777203)
  ·
    refine ⟨3675041910587865703165805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2450027940391910468777203 3675041910587865703165805)
    ·
      refine ⟨1378140716470449638687177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3675041910587865703165805 1378140716470449638687177)
      ·
        refine ⟨1033605537352837229015383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1378140716470449638687177 1033605537352837229015383)
        ·
          refine ⟨1550408306029255843523075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1033605537352837229015383 1550408306029255843523075)
          ·
            refine ⟨2325612459043883765284613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1550408306029255843523075 2325612459043883765284613)
            ·
              refine ⟨436052336070728205990865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2325612459043883765284613 436052336070728205990865)
              ·
                refine ⟨327039252053046154493149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 436052336070728205990865 327039252053046154493149)
                ·
                  refine ⟨122639719519892307934931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 327039252053046154493149 122639719519892307934931)
                  ·
                    rfl

theorem cell21_537390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 4, 2, 3].length) (baseStart_537390 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_537390 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_537390 prefixEnd_537390 := by exact prefixLift 537390
  have htrace : WordTrace (prefixWord ++ tailWord_537390) baseStart_537390 baseEnd_537390 := by
    simpa [prefixWord, tailWord_537390, baseEnd_537390] using wordTrace_append hprefix tailTrace_537390
  have hstable : (prefixWord ++ tailWord_537390).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_537390).length < 2 ^ (prefixWord ++ tailWord_537390).sum := by decide
  have hdescent : baseEnd_537390 < baseStart_537390 := by decide
  rcases family_descends (prefixWord ++ tailWord_537390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_537429 : List Nat := [1, 3, 2, 2, 2, 1, 2, 2, 6]
def baseStart_537429 : Nat := 118140960795 + 537429 * 2 ^ 59
def prefixEnd_537429 : Nat := 4983230072969 + 3 ^ 40 * 537429 * 2
def baseEnd_537429 : Nat := 122648619851236906784851

theorem tailTrace_537429 : CollatzResearch.WordTrace tailWord_537429 prefixEnd_537429 122648619851236906784851 := by
  unfold tailWord_537429
  simp only [CollatzResearch.WordTrace]
  refine ⟨19601645969993993410887341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13067763979995995607258227 19601645969993993410887341)
  ·
    refine ⟨7350617238747747529082753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19601645969993993410887341 7350617238747747529082753)
    ·
      refine ⟨5512962929060810646812065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7350617238747747529082753 5512962929060810646812065)
      ·
        refine ⟨4134722196795607985109049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5512962929060810646812065 4134722196795607985109049)
        ·
          refine ⟨3101041647596705988831787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4134722196795607985109049 3101041647596705988831787)
          ·
            refine ⟨4651562471395058983247681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3101041647596705988831787 4651562471395058983247681)
            ·
              refine ⟨3488671853546294237435761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4651562471395058983247681 3488671853546294237435761)
              ·
                refine ⟨2616503890159720678076821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3488671853546294237435761 2616503890159720678076821)
                ·
                  refine ⟨122648619851236906784851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2616503890159720678076821 122648619851236906784851)
                  ·
                    rfl

theorem cell21_537429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 2, 6].length) (baseStart_537429 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_537429 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_537429 prefixEnd_537429 := by exact prefixLift 537429
  have htrace : WordTrace (prefixWord ++ tailWord_537429) baseStart_537429 baseEnd_537429 := by
    simpa [prefixWord, tailWord_537429, baseEnd_537429] using wordTrace_append hprefix tailTrace_537429
  have hstable : (prefixWord ++ tailWord_537429).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_537429).length < 2 ^ (prefixWord ++ tailWord_537429).sum := by decide
  have hdescent : baseEnd_537429 < baseStart_537429 := by decide
  rcases family_descends (prefixWord ++ tailWord_537429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_537477 : List Nat := [1, 3, 1, 1, 3, 5, 2, 5]
def baseStart_537477 : Nat := 118140960795 + 537477 * 2 ^ 59
def prefixEnd_537477 : Nat := 4983230072969 + 3 ^ 40 * 537477 * 2
def baseEnd_537477 : Nat := 40886524701733163328251

theorem tailTrace_537477 : CollatzResearch.WordTrace tailWord_537477 prefixEnd_537477 40886524701733163328251 := by
  unfold tailWord_537477
  simp only [CollatzResearch.WordTrace]
  refine ⟨19603396673820097608634685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13068931115880065072423123 19603396673820097608634685)
  ·
    refine ⟨7351273752682536603238007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19603396673820097608634685 7351273752682536603238007)
    ·
      refine ⟨11026910629023804904857011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7351273752682536603238007 11026910629023804904857011)
      ·
        refine ⟨16540365943535707357285517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11026910629023804904857011 16540365943535707357285517)
        ·
          refine ⟨6202637228825890258982069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16540365943535707357285517 6202637228825890258982069)
          ·
            refine ⟨581497240202427211779569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6202637228825890258982069 581497240202427211779569)
            ·
              refine ⟨436122930151820408834677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 581497240202427211779569 436122930151820408834677)
              ·
                refine ⟨40886524701733163328251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 436122930151820408834677 40886524701733163328251)
                ·
                  rfl

theorem cell21_537477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 2, 5].length) (baseStart_537477 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_537477 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_537477 prefixEnd_537477 := by exact prefixLift 537477
  have htrace : WordTrace (prefixWord ++ tailWord_537477) baseStart_537477 baseEnd_537477 := by
    simpa [prefixWord, tailWord_537477, baseEnd_537477] using wordTrace_append hprefix tailTrace_537477
  have hstable : (prefixWord ++ tailWord_537477).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_537477).length < 2 ^ (prefixWord ++ tailWord_537477).sum := by decide
  have hdescent : baseEnd_537477 < baseStart_537477 := by decide
  rcases family_descends (prefixWord ++ tailWord_537477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_537491 : List Nat := [1, 1, 1, 2, 1, 2, 1, 9, 3]
def baseStart_537491 : Nat := 118140960795 + 537491 * 2 ^ 59
def prefixEnd_537491 : Nat := 4983230072969 + 3 ^ 40 * 537491 * 2
def baseEnd_537491 : Nat := 122662769095938576751391

theorem tailTrace_537491 : CollatzResearch.WordTrace tailWord_537491 prefixEnd_537491 122662769095938576751391 := by
  unfold tailWord_537491
  simp only [CollatzResearch.WordTrace]
  refine ⟨19603907295769377999644327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13069271530512918666429551 19603907295769377999644327)
  ·
    refine ⟨29405860943654066999466491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19603907295769377999644327 29405860943654066999466491)
    ·
      refine ⟨44108791415481100499199737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29405860943654066999466491 44108791415481100499199737)
      ·
        refine ⟨33081593561610825374399803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44108791415481100499199737 33081593561610825374399803)
        ·
          refine ⟨49622390342416238061599705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33081593561610825374399803 49622390342416238061599705)
          ·
            refine ⟨37216792756812178546199779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49622390342416238061599705 37216792756812178546199779)
            ·
              refine ⟨55825189135218267819299669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37216792756812178546199779 55825189135218267819299669)
              ·
                refine ⟨327100717589169538003709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 55825189135218267819299669 327100717589169538003709)
                ·
                  refine ⟨122662769095938576751391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 327100717589169538003709 122662769095938576751391)
                  ·
                    rfl

theorem cell21_537491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 9, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 9, 3].length) (baseStart_537491 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_537491 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_537491 prefixEnd_537491 := by exact prefixLift 537491
  have htrace : WordTrace (prefixWord ++ tailWord_537491) baseStart_537491 baseEnd_537491 := by
    simpa [prefixWord, tailWord_537491, baseEnd_537491] using wordTrace_append hprefix tailTrace_537491
  have hstable : (prefixWord ++ tailWord_537491).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_537491).length < 2 ^ (prefixWord ++ tailWord_537491).sum := by decide
  have hdescent : baseEnd_537491 < baseStart_537491 := by decide
  rcases family_descends (prefixWord ++ tailWord_537491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_537494 : List Nat := [5, 3, 1, 1, 1, 1, 9]
def baseStart_537494 : Nat := 118140960795 + 537494 * 2 ^ 59
def prefixEnd_537494 : Nat := 4983230072969 + 3 ^ 40 * 537494 * 2
def baseEnd_537494 : Nat := 13629272637423470911265

theorem tailTrace_537494 : CollatzResearch.WordTrace tailWord_537494 prefixEnd_537494 13629272637423470911265 := by
  unfold tailWord_537494
  simp only [CollatzResearch.WordTrace]
  refine ⟨1225251044672406844500221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13069344476505673008002357 1225251044672406844500221)
  ·
    refine ⟨459469141752152566687583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1225251044672406844500221 459469141752152566687583)
    ·
      refine ⟨689203712628228850031375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 459469141752152566687583 689203712628228850031375)
      ·
        refine ⟨1033805568942343275047063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 689203712628228850031375 1033805568942343275047063)
        ·
          refine ⟨1550708353413514912570595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1033805568942343275047063 1550708353413514912570595)
          ·
            refine ⟨2326062530120272368855893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1550708353413514912570595 2326062530120272368855893)
            ·
              refine ⟨13629272637423470911265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2326062530120272368855893 13629272637423470911265)
              ·
                rfl

theorem cell21_537494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 9].length) (baseStart_537494 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_537494 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_537494 prefixEnd_537494 := by exact prefixLift 537494
  have htrace : WordTrace (prefixWord ++ tailWord_537494) baseStart_537494 baseEnd_537494 := by
    simpa [prefixWord, tailWord_537494, baseEnd_537494] using wordTrace_append hprefix tailTrace_537494
  have hstable : (prefixWord ++ tailWord_537494).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_537494).length < 2 ^ (prefixWord ++ tailWord_537494).sum := by decide
  have hdescent : baseEnd_537494 < baseStart_537494 := by decide
  rcases family_descends (prefixWord ++ tailWord_537494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_537570 : List Nat := [3, 3, 3, 1, 1, 3, 1, 6]
def baseStart_537570 : Nat := 118140960795 + 537570 * 2 ^ 59
def prefixEnd_537570 : Nat := 4983230072969 + 3 ^ 40 * 537570 * 2
def baseEnd_537570 : Nat := 40893599324083998311521

theorem tailTrace_537570 : CollatzResearch.WordTrace tailWord_537570 prefixEnd_537570 40893599324083998311521 := by
  unfold tailWord_537570
  simp only [CollatzResearch.WordTrace]
  refine ⟨4901697165620793622942541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13071192441655449661180109 4901697165620793622942541)
  ·
    refine ⟨1838136437107797608603453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4901697165620793622942541 1838136437107797608603453)
    ·
      refine ⟨689301163915424103226295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1838136437107797608603453 689301163915424103226295)
      ·
        refine ⟨1033951745873136154839443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 689301163915424103226295 1033951745873136154839443)
        ·
          refine ⟨1550927618809704232259165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1033951745873136154839443 1550927618809704232259165)
          ·
            refine ⟨581597857053639087097187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1550927618809704232259165 581597857053639087097187)
            ·
              refine ⟨872396785580458630645781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 581597857053639087097187 872396785580458630645781)
              ·
                refine ⟨40893599324083998311521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 872396785580458630645781 40893599324083998311521)
                ·
                  rfl

theorem cell21_537570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 1, 6].length) (baseStart_537570 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_537570 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_537570 prefixEnd_537570 := by exact prefixLift 537570
  have htrace : WordTrace (prefixWord ++ tailWord_537570) baseStart_537570 baseEnd_537570 := by
    simpa [prefixWord, tailWord_537570, baseEnd_537570] using wordTrace_append hprefix tailTrace_537570
  have hstable : (prefixWord ++ tailWord_537570).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_537570).length < 2 ^ (prefixWord ++ tailWord_537570).sum := by decide
  have hdescent : baseEnd_537570 < baseStart_537570 := by decide
  rcases family_descends (prefixWord ++ tailWord_537570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_537618 : List Nat := [3, 2, 5, 1, 1, 1, 2, 1, 5]
def baseStart_537618 : Nat := 118140960795 + 537618 * 2 ^ 59
def prefixEnd_537618 : Nat := 4983230072969 + 3 ^ 40 * 537618 * 2
def baseEnd_537618 : Nat := 122691752226214578134465

theorem tailTrace_537618 : CollatzResearch.WordTrace tailWord_537618 prefixEnd_537618 122691752226214578134465 := by
  unfold tailWord_537618
  simp only [CollatzResearch.WordTrace]
  refine ⟨4902134841577319672379377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13072359577539519126345005 4902134841577319672379377)
  ·
    refine ⟨3676601131182989754284533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4902134841577319672379377 3676601131182989754284533)
    ·
      refine ⟨344681356048405289464175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3676601131182989754284533 344681356048405289464175)
      ·
        refine ⟨517022034072607934196263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 344681356048405289464175 517022034072607934196263)
        ·
          refine ⟨775533051108911901294395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 517022034072607934196263 775533051108911901294395)
          ·
            refine ⟨1163299576663367851941593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 775533051108911901294395 1163299576663367851941593)
            ·
              refine ⟨872474682497525888956195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1163299576663367851941593 872474682497525888956195)
              ·
                refine ⟨1308712023746288833434293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 872474682497525888956195 1308712023746288833434293)
                ·
                  refine ⟨122691752226214578134465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1308712023746288833434293 122691752226214578134465)
                  ·
                    rfl

theorem cell21_537618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 2, 1, 5].length) (baseStart_537618 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_537618 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_537618 prefixEnd_537618 := by exact prefixLift 537618
  have htrace : WordTrace (prefixWord ++ tailWord_537618) baseStart_537618 baseEnd_537618 := by
    simpa [prefixWord, tailWord_537618, baseEnd_537618] using wordTrace_append hprefix tailTrace_537618
  have hstable : (prefixWord ++ tailWord_537618).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_537618).length < 2 ^ (prefixWord ++ tailWord_537618).sum := by decide
  have hdescent : baseEnd_537618 < baseStart_537618 := by decide
  rcases family_descends (prefixWord ++ tailWord_537618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_537632 : List Nat := [2, 1, 1, 7, 1, 1, 3, 1, 4]
def baseStart_537632 : Nat := 118140960795 + 537632 * 2 ^ 59
def prefixEnd_537632 : Nat := 4983230072969 + 3 ^ 40 * 537632 * 2
def baseEnd_537632 : Nat := 122694947216953664901103

theorem tailTrace_537632 : CollatzResearch.WordTrace tailWord_537632 prefixEnd_537632 122694947216953664901103 := by
  unfold tailWord_537632
  simp only [CollatzResearch.WordTrace]
  refine ⟨9804524994129279540263575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13072699992172372720351433 9804524994129279540263575)
  ·
    refine ⟨14706787491193919310395363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9804524994129279540263575 14706787491193919310395363)
    ·
      refine ⟨22060181236790878965593045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14706787491193919310395363 22060181236790878965593045)
      ·
        refine ⟨517035497737286225756087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 22060181236790878965593045 517035497737286225756087)
        ·
          refine ⟨775553246605929338634131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 517035497737286225756087 775553246605929338634131)
          ·
            refine ⟨1163329869908894007951197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 775553246605929338634131 1163329869908894007951197)
            ·
              refine ⟨436248701215835252981699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1163329869908894007951197 436248701215835252981699)
              ·
                refine ⟨654373051823752879472549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 436248701215835252981699 654373051823752879472549)
                ·
                  refine ⟨122694947216953664901103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 654373051823752879472549 122694947216953664901103)
                  ·
                    rfl

theorem cell21_537632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 3, 1, 4].length) (baseStart_537632 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_537632 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_537632 prefixEnd_537632 := by exact prefixLift 537632
  have htrace : WordTrace (prefixWord ++ tailWord_537632) baseStart_537632 baseEnd_537632 := by
    simpa [prefixWord, tailWord_537632, baseEnd_537632] using wordTrace_append hprefix tailTrace_537632
  have hstable : (prefixWord ++ tailWord_537632).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_537632).length < 2 ^ (prefixWord ++ tailWord_537632).sum := by decide
  have hdescent : baseEnd_537632 < baseStart_537632 := by decide
  rcases family_descends (prefixWord ++ tailWord_537632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_537657 : List Nat := [1, 2, 1, 5, 2, 1, 1, 2, 6]
def baseStart_537657 : Nat := 118140960795 + 537657 * 2 ^ 59
def prefixEnd_537657 : Nat := 4983230072969 + 3 ^ 40 * 537657 * 2
def baseEnd_537657 : Nat := 122700652557559176984385

theorem tailTrace_537657 : CollatzResearch.WordTrace tailWord_537657 prefixEnd_537657 122700652557559176984385 := by
  unfold tailWord_537657
  simp only [CollatzResearch.WordTrace]
  refine ⟨19609961813167988350187225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13073307875445325566791483 19609961813167988350187225)
  ·
    refine ⟨14707471359875991262640419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19609961813167988350187225 14707471359875991262640419)
    ·
      refine ⟨22061207039813986893960629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14707471359875991262640419 22061207039813986893960629)
      ·
        refine ⟨2068238159982561271308809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 22061207039813986893960629 2068238159982561271308809)
        ·
          refine ⟨1551178619986920953481607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2068238159982561271308809 1551178619986920953481607)
          ·
            refine ⟨2326767929980381430222411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1551178619986920953481607 2326767929980381430222411)
            ·
              refine ⟨3490151894970572145333617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2326767929980381430222411 3490151894970572145333617)
              ·
                refine ⟨2617613921227929109000213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3490151894970572145333617 2617613921227929109000213)
                ·
                  refine ⟨122700652557559176984385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2617613921227929109000213 122700652557559176984385)
                  ·
                    rfl

theorem cell21_537657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 2, 6].length) (baseStart_537657 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_537657 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_537657 prefixEnd_537657 := by exact prefixLift 537657
  have htrace : WordTrace (prefixWord ++ tailWord_537657) baseStart_537657 baseEnd_537657 := by
    simpa [prefixWord, tailWord_537657, baseEnd_537657] using wordTrace_append hprefix tailTrace_537657
  have hstable : (prefixWord ++ tailWord_537657).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_537657).length < 2 ^ (prefixWord ++ tailWord_537657).sum := by decide
  have hdescent : baseEnd_537657 < baseStart_537657 := by decide
  rcases family_descends (prefixWord ++ tailWord_537657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_537660 : List Nat := [2, 2, 2, 2, 2, 2, 3, 3, 3]
def baseStart_537660 : Nat := 118140960795 + 537660 * 2 ^ 59
def prefixEnd_537660 : Nat := 4983230072969 + 3 ^ 40 * 537660 * 2
def baseEnd_537660 : Nat := 122701337198431838434379

theorem tailTrace_537660 : CollatzResearch.WordTrace tailWord_537660 prefixEnd_537660 122701337198431838434379 := by
  unfold tailWord_537660
  simp only [CollatzResearch.WordTrace]
  refine ⟨9805035616078559931273217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13073380821438079908364289 9805035616078559931273217)
  ·
    refine ⟨7353776712058919948454913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9805035616078559931273217 7353776712058919948454913)
    ·
      refine ⟨5515332534044189961341185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7353776712058919948454913 5515332534044189961341185)
      ·
        refine ⟨4136499400533142471005889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5515332534044189961341185 4136499400533142471005889)
        ·
          refine ⟨3102374550399856853254417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4136499400533142471005889 3102374550399856853254417)
          ·
            refine ⟨2326780912799892639940813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3102374550399856853254417 2326780912799892639940813)
            ·
              refine ⟨872542842299959739977805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2326780912799892639940813 872542842299959739977805)
              ·
                refine ⟨327203565862484902491677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 872542842299959739977805 327203565862484902491677)
                ·
                  refine ⟨122701337198431838434379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 327203565862484902491677 122701337198431838434379)
                  ·
                    rfl

theorem cell21_537660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 3, 3, 3].length) (baseStart_537660 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_537660 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_537660 prefixEnd_537660 := by exact prefixLift 537660
  have htrace : WordTrace (prefixWord ++ tailWord_537660) baseStart_537660 baseEnd_537660 := by
    simpa [prefixWord, tailWord_537660, baseEnd_537660] using wordTrace_append hprefix tailTrace_537660
  have hstable : (prefixWord ++ tailWord_537660).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_537660).length < 2 ^ (prefixWord ++ tailWord_537660).sum := by decide
  have hdescent : baseEnd_537660 < baseStart_537660 := by decide
  rcases family_descends (prefixWord ++ tailWord_537660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_537671 : List Nat := [1, 1, 4, 1, 3, 2, 9]
def baseStart_537671 : Nat := 118140960795 + 537671 * 2 ^ 59
def prefixEnd_537671 : Nat := 4983230072969 + 3 ^ 40 * 537671 * 2
def baseEnd_537671 : Nat := 13633760838699807083447

theorem tailTrace_537671 : CollatzResearch.WordTrace tailWord_537671 prefixEnd_537671 13633760838699807083447 := by
  unfold tailWord_537671
  simp only [CollatzResearch.WordTrace]
  refine ⟨19610472435117268741196867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13073648290078179160797911 19610472435117268741196867)
  ·
    refine ⟨29415708652675903111795301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19610472435117268741196867 29415708652675903111795301)
    ·
      refine ⟨5515445372376731833461619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29415708652675903111795301 5515445372376731833461619)
      ·
        refine ⟨8273168058565097750192429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5515445372376731833461619 8273168058565097750192429)
        ·
          refine ⟨3102438021961911656322161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8273168058565097750192429 3102438021961911656322161)
          ·
            refine ⟨2326828516471433742241621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3102438021961911656322161 2326828516471433742241621)
            ·
              refine ⟨13633760838699807083447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2326828516471433742241621 13633760838699807083447)
              ·
                rfl

theorem cell21_537671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 9].length) (baseStart_537671 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_537671 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_537671 prefixEnd_537671 := by exact prefixLift 537671
  have htrace : WordTrace (prefixWord ++ tailWord_537671) baseStart_537671 baseEnd_537671 := by
    simpa [prefixWord, tailWord_537671, baseEnd_537671] using wordTrace_append hprefix tailTrace_537671
  have hstable : (prefixWord ++ tailWord_537671).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_537671).length < 2 ^ (prefixWord ++ tailWord_537671).sum := by decide
  have hdescent : baseEnd_537671 < baseStart_537671 := by decide
  rcases family_descends (prefixWord ++ tailWord_537671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_537719 : List Nat := [1, 1, 3, 1, 1, 4, 2, 5, 3]
def baseStart_537719 : Nat := 118140960795 + 537719 * 2 ^ 59
def prefixEnd_537719 : Nat := 4983230072969 + 3 ^ 40 * 537719 * 2
def baseEnd_537719 : Nat := 122714801802260846950925

theorem tailTrace_537719 : CollatzResearch.WordTrace tailWord_537719 prefixEnd_537719 122714801802260846950925 := by
  unfold tailWord_537719
  simp only [CollatzResearch.WordTrace]
  refine ⟨19612223138943372938944211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13074815425962248625962807 19612223138943372938944211)
  ·
    refine ⟨29418334708415059408416317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19612223138943372938944211 29418334708415059408416317)
    ·
      refine ⟨11031875515655647278156119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29418334708415059408416317 11031875515655647278156119)
      ·
        refine ⟨16547813273483470917234179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11031875515655647278156119 16547813273483470917234179)
        ·
          refine ⟨24821719910225206375851269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16547813273483470917234179 24821719910225206375851269)
          ·
            refine ⟨4654072483167226195472113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24821719910225206375851269 4654072483167226195472113)
            ·
              refine ⟨3490554362375419646604085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4654072483167226195472113 3490554362375419646604085)
              ·
                refine ⟨327239471472695591869133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3490554362375419646604085 327239471472695591869133)
                ·
                  refine ⟨122714801802260846950925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 327239471472695591869133 122714801802260846950925)
                  ·
                    rfl

theorem cell21_537719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 5, 3].length) (baseStart_537719 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_537719 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_537719 prefixEnd_537719 := by exact prefixLift 537719
  have htrace : WordTrace (prefixWord ++ tailWord_537719) baseStart_537719 baseEnd_537719 := by
    simpa [prefixWord, tailWord_537719, baseEnd_537719] using wordTrace_append hprefix tailTrace_537719
  have hstable : (prefixWord ++ tailWord_537719).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_537719).length < 2 ^ (prefixWord ++ tailWord_537719).sum := by decide
  have hdescent : baseEnd_537719 < baseStart_537719 := by decide
  rcases family_descends (prefixWord ++ tailWord_537719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_537747 : List Nat := [1, 1, 1, 2, 1, 2, 7, 6]
def baseStart_537747 : Nat := 118140960795 + 537747 * 2 ^ 59
def prefixEnd_537747 : Nat := 4983230072969 + 3 ^ 40 * 537747 * 2
def baseEnd_537747 : Nat := 40907063927913006828067

theorem tailTrace_537747 : CollatzResearch.WordTrace tailWord_537747 prefixEnd_537747 40907063927913006828067 := by
  unfold tailWord_537747
  simp only [CollatzResearch.WordTrace]
  refine ⟨19613244382841933720963495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13075496255227955813975663 19613244382841933720963495)
  ·
    refine ⟨29419866574262900581445243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19613244382841933720963495 29419866574262900581445243)
    ·
      refine ⟨44129799861394350872167865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29419866574262900581445243 44129799861394350872167865)
      ·
        refine ⟨33097349896045763154125899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44129799861394350872167865 33097349896045763154125899)
        ·
          refine ⟨49646024844068644731188849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33097349896045763154125899 49646024844068644731188849)
          ·
            refine ⟨37234518633051483548391637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49646024844068644731188849 37234518633051483548391637)
            ·
              refine ⟨872684030462144145665429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 37234518633051483548391637 872684030462144145665429)
              ·
                refine ⟨40907063927913006828067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 872684030462144145665429 40907063927913006828067)
                ·
                  rfl

theorem cell21_537747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 7, 6].length) (baseStart_537747 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_537747 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_537747 prefixEnd_537747 := by exact prefixLift 537747
  have htrace : WordTrace (prefixWord ++ tailWord_537747) baseStart_537747 baseEnd_537747 := by
    simpa [prefixWord, tailWord_537747, baseEnd_537747] using wordTrace_append hprefix tailTrace_537747
  have hstable : (prefixWord ++ tailWord_537747).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_537747).length < 2 ^ (prefixWord ++ tailWord_537747).sum := by decide
  have hdescent : baseEnd_537747 < baseStart_537747 := by decide
  rcases family_descends (prefixWord ++ tailWord_537747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_537829 : List Nat := [1, 3, 1, 4, 3, 2, 1, 3, 3]
def baseStart_537829 : Nat := 118140960795 + 537829 * 2 ^ 59
def prefixEnd_537829 : Nat := 4983230072969 + 3 ^ 40 * 537829 * 2
def baseEnd_537829 : Nat := 122739905300925100117367

theorem tailTrace_537829 : CollatzResearch.WordTrace tailWord_537829 prefixEnd_537829 122739905300925100117367 := by
  unfold tailWord_537829
  simp only [CollatzResearch.WordTrace]
  refine ⟨19616235168544861725448541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13077490112363241150299027 19616235168544861725448541)
  ·
    refine ⟨7356088188204323147043203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19616235168544861725448541 7356088188204323147043203)
    ·
      refine ⟨11034132282306484720564805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7356088188204323147043203 11034132282306484720564805)
      ·
        refine ⟨2068899802932465885105901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11034132282306484720564805 2068899802932465885105901)
        ·
          refine ⟨775837426099674706914713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2068899802932465885105901 775837426099674706914713)
          ·
            refine ⟨581878069574756030186035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 775837426099674706914713 581878069574756030186035)
            ·
              refine ⟨872817104362134045279053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 581878069574756030186035 872817104362134045279053)
              ·
                refine ⟨327306414135800266979645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 872817104362134045279053 327306414135800266979645)
                ·
                  refine ⟨122739905300925100117367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 327306414135800266979645 122739905300925100117367)
                  ·
                    rfl

theorem cell21_537829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 1, 3, 3].length) (baseStart_537829 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_537829 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_537829 prefixEnd_537829 := by exact prefixLift 537829
  have htrace : WordTrace (prefixWord ++ tailWord_537829) baseStart_537829 baseEnd_537829 := by
    simpa [prefixWord, tailWord_537829, baseEnd_537829] using wordTrace_append hprefix tailTrace_537829
  have hstable : (prefixWord ++ tailWord_537829).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_537829).length < 2 ^ (prefixWord ++ tailWord_537829).sum := by decide
  have hdescent : baseEnd_537829 < baseStart_537829 := by decide
  rcases family_descends (prefixWord ++ tailWord_537829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_537905 : List Nat := [1, 2, 2, 3, 3, 3, 2, 2, 3]
def baseStart_537905 : Nat := 118140960795 + 537905 * 2 ^ 59
def prefixEnd_537905 : Nat := 4983230072969 + 3 ^ 40 * 537905 * 2
def baseEnd_537905 : Nat := 122757249536365856850545

theorem tailTrace_537905 : CollatzResearch.WordTrace tailWord_537905 prefixEnd_537905 122757249536365856850545 := by
  unfold tailWord_537905
  simp only [CollatzResearch.WordTrace]
  refine ⟨19619007116269526705215169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13079338077513017803476779 19619007116269526705215169)
  ·
    refine ⟨14714255337202145028911377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19619007116269526705215169 14714255337202145028911377)
    ·
      refine ⟨11035691502901608771683533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14714255337202145028911377 11035691502901608771683533)
      ·
        refine ⟨4138384313588103289381325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11035691502901608771683533 4138384313588103289381325)
        ·
          refine ⟨1551894117595538733517997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4138384313588103289381325 1551894117595538733517997)
          ·
            refine ⟨581960294098327025069249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1551894117595538733517997 581960294098327025069249)
            ·
              refine ⟨436470220573745268801937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 581960294098327025069249 436470220573745268801937)
              ·
                refine ⟨327352665430308951601453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 436470220573745268801937 327352665430308951601453)
                ·
                  refine ⟨122757249536365856850545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 327352665430308951601453 122757249536365856850545)
                  ·
                    rfl

theorem cell21_537905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 2, 2, 3].length) (baseStart_537905 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_537905 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_537905 prefixEnd_537905 := by exact prefixLift 537905
  have htrace : WordTrace (prefixWord ++ tailWord_537905) baseStart_537905 baseEnd_537905 := by
    simpa [prefixWord, tailWord_537905, baseEnd_537905] using wordTrace_append hprefix tailTrace_537905
  have hstable : (prefixWord ++ tailWord_537905).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_537905).length < 2 ^ (prefixWord ++ tailWord_537905).sum := by decide
  have hdescent : baseEnd_537905 < baseStart_537905 := by decide
  rcases family_descends (prefixWord ++ tailWord_537905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_537916 : List Nat := [2, 2, 2, 2, 1, 5, 1, 6]
def baseStart_537916 : Nat := 118140960795 + 537916 * 2 ^ 59
def prefixEnd_537916 : Nat := 4983230072969 + 3 ^ 40 * 537916 * 2
def baseEnd_537916 : Nat := 40919919962077427389063

theorem tailTrace_537916 : CollatzResearch.WordTrace tailWord_537916 prefixEnd_537916 40919919962077427389063 := by
  unfold tailWord_537916
  simp only [CollatzResearch.WordTrace]
  refine ⟨9809704159614837791932801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13079605546153117055910401 9809704159614837791932801)
  ·
    refine ⟨7357278119711128343949601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9809704159614837791932801 7357278119711128343949601)
    ·
      refine ⟨5517958589783346257962201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7357278119711128343949601 5517958589783346257962201)
      ·
        refine ⟨4138468942337509693471651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5517958589783346257962201 4138468942337509693471651)
        ·
          refine ⟨6207703413506264540207477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4138468942337509693471651 6207703413506264540207477)
          ·
            refine ⟨581972195016212300644451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6207703413506264540207477 581972195016212300644451)
            ·
              refine ⟨872958292524318450966677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 581972195016212300644451 872958292524318450966677)
              ·
                refine ⟨40919919962077427389063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 872958292524318450966677 40919919962077427389063)
                ·
                  rfl

theorem cell21_537916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 1, 6].length) (baseStart_537916 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_537916 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_537916 prefixEnd_537916 := by exact prefixLift 537916
  have htrace : WordTrace (prefixWord ++ tailWord_537916) baseStart_537916 baseEnd_537916 := by
    simpa [prefixWord, tailWord_537916, baseEnd_537916] using wordTrace_append hprefix tailTrace_537916
  have hstable : (prefixWord ++ tailWord_537916).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_537916).length < 2 ^ (prefixWord ++ tailWord_537916).sum := by decide
  have hdescent : baseEnd_537916 < baseStart_537916 := by decide
  rcases family_descends (prefixWord ++ tailWord_537916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_537944 : List Nat := [2, 1, 2, 2, 1, 1, 4, 2, 6]
def baseStart_537944 : Nat := 118140960795 + 537944 * 2 ^ 59
def prefixEnd_537944 : Nat := 4983230072969 + 3 ^ 40 * 537944 * 2
def baseEnd_537944 : Nat := 122766149867710455700465

theorem tailTrace_537944 : CollatzResearch.WordTrace tailWord_537944 prefixEnd_537944 122766149867710455700465 := by
  unfold tailWord_537944
  simp only [CollatzResearch.WordTrace]
  refine ⟨9810214781564118182942443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13080286375418824243923257 9810214781564118182942443)
  ·
    refine ⟨14715322172346177274413665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9810214781564118182942443 14715322172346177274413665)
    ·
      refine ⟨11036491629259632955810249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14715322172346177274413665 11036491629259632955810249)
      ·
        refine ⟨8277368721944724716857687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11036491629259632955810249 8277368721944724716857687)
        ·
          refine ⟨12416053082917087075286531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8277368721944724716857687 12416053082917087075286531)
          ·
            refine ⟨18624079624375630612929797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12416053082917087075286531 18624079624375630612929797)
            ·
              refine ⟨3492014929570430739924337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18624079624375630612929797 3492014929570430739924337)
              ·
                refine ⟨2619011197177823054943253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3492014929570430739924337 2619011197177823054943253)
                ·
                  refine ⟨122766149867710455700465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2619011197177823054943253 122766149867710455700465)
                  ·
                    rfl

theorem cell21_537944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 2, 6].length) (baseStart_537944 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_537944 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_537944 prefixEnd_537944 := by exact prefixLift 537944
  have htrace : WordTrace (prefixWord ++ tailWord_537944) baseStart_537944 baseEnd_537944 := by
    simpa [prefixWord, tailWord_537944, baseEnd_537944] using wordTrace_append hprefix tailTrace_537944
  have hstable : (prefixWord ++ tailWord_537944).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_537944).length < 2 ^ (prefixWord ++ tailWord_537944).sum := by decide
  have hdescent : baseEnd_537944 < baseStart_537944 := by decide
  rcases family_descends (prefixWord ++ tailWord_537944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_537992 : List Nat := [2, 1, 3, 3, 1, 2, 4, 5]
def baseStart_537992 : Nat := 118140960795 + 537992 * 2 ^ 59
def prefixEnd_537992 : Nat := 4983230072969 + 3 ^ 40 * 537992 * 2
def baseEnd_537992 : Nat := 40925701373891012966789

theorem tailTrace_537992 : CollatzResearch.WordTrace tailWord_537992 prefixEnd_537992 40925701373891012966789 := by
  unfold tailWord_537992
  simp only [CollatzResearch.WordTrace]
  refine ⟨9811090133477170281816115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13081453511302893709088153 9811090133477170281816115)
  ·
    refine ⟨14716635200215755422724173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9811090133477170281816115 14716635200215755422724173)
    ·
      refine ⟨5518738200080908283521565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14716635200215755422724173 5518738200080908283521565)
      ·
        refine ⟨2069526825030340606320587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5518738200080908283521565 2069526825030340606320587)
        ·
          refine ⟨3104290237545510909480881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2069526825030340606320587 3104290237545510909480881)
          ·
            refine ⟨2328217678159133182110661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3104290237545510909480881 2328217678159133182110661)
            ·
              refine ⟨436540814654837471645749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2328217678159133182110661 436540814654837471645749)
              ·
                refine ⟨40925701373891012966789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 436540814654837471645749 40925701373891012966789)
                ·
                  rfl

theorem cell21_537992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 4, 5].length) (baseStart_537992 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_537992 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_537992 prefixEnd_537992 := by exact prefixLift 537992
  have htrace : WordTrace (prefixWord ++ tailWord_537992) baseStart_537992 baseEnd_537992 := by
    simpa [prefixWord, tailWord_537992, baseEnd_537992] using wordTrace_append hprefix tailTrace_537992
  have hstable : (prefixWord ++ tailWord_537992).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_537992).length < 2 ^ (prefixWord ++ tailWord_537992).sum := by decide
  have hdescent : baseEnd_537992 < baseStart_537992 := by decide
  rcases family_descends (prefixWord ++ tailWord_537992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_537998 : List Nat := [4, 1, 1, 4, 3, 1, 1, 3, 3]
def baseStart_537998 : Nat := 118140960795 + 537998 * 2 ^ 59
def prefixEnd_537998 : Nat := 4983230072969 + 3 ^ 40 * 537998 * 2
def baseEnd_537998 : Nat := 122778473403418361800355

theorem tailTrace_537998 : CollatzResearch.WordTrace tailWord_537998 prefixEnd_537998 122778473403418361800355 := by
  unfold tailWord_537998
  simp only [CollatzResearch.WordTrace]
  refine ⟨2452799888116575448543831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13081599403288402392233765 2452799888116575448543831)
  ·
    refine ⟨3679199832174863172815747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2452799888116575448543831 3679199832174863172815747)
    ·
      refine ⟨5518799748262294759223621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3679199832174863172815747 5518799748262294759223621)
      ·
        refine ⟨1034774952799180267354429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5518799748262294759223621 1034774952799180267354429)
        ·
          refine ⟨388040607299692600257911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1034774952799180267354429 388040607299692600257911)
          ·
            refine ⟨582060910949538900386867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 388040607299692600257911 582060910949538900386867)
            ·
              refine ⟨873091366424308350580301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 582060910949538900386867 873091366424308350580301)
              ·
                refine ⟨327409262409115631467613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 873091366424308350580301 327409262409115631467613)
                ·
                  refine ⟨122778473403418361800355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 327409262409115631467613 122778473403418361800355)
                  ·
                    rfl

theorem cell21_537998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 1, 3, 3].length) (baseStart_537998 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_537998 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_537998 prefixEnd_537998 := by exact prefixLift 537998
  have htrace : WordTrace (prefixWord ++ tailWord_537998) baseStart_537998 baseEnd_537998 := by
    simpa [prefixWord, tailWord_537998, baseEnd_537998] using wordTrace_append hprefix tailTrace_537998
  have hstable : (prefixWord ++ tailWord_537998).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_537998).length < 2 ^ (prefixWord ++ tailWord_537998).sum := by decide
  have hdescent : baseEnd_537998 < baseStart_537998 := by decide
  rcases family_descends (prefixWord ++ tailWord_537998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538068 : List Nat := [2, 4, 1, 2, 4, 8]
def baseStart_538068 : Nat := 118140960795 + 538068 * 2 ^ 59
def prefixEnd_538068 : Nat := 4983230072969 + 3 ^ 40 * 538068 * 2
def baseEnd_538068 : Nat := 4547942531744955393835

theorem tailTrace_538068 : CollatzResearch.WordTrace tailWord_538068 prefixEnd_538068 4547942531744955393835 := by
  unfold tailWord_538068
  simp only [CollatzResearch.WordTrace]
  refine ⟨9812476107339502771699429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13083301476452670362265905 9812476107339502771699429)
  ·
    refine ⟨1839839270126156769693643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9812476107339502771699429 1839839270126156769693643)
    ·
      refine ⟨2759758905189235154540465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1839839270126156769693643 2759758905189235154540465)
      ·
        refine ⟨2069819178891926365905349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2759758905189235154540465 2069819178891926365905349)
        ·
          refine ⟨388091096042236193607253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2069819178891926365905349 388091096042236193607253)
          ·
            refine ⟨4547942531744955393835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 388091096042236193607253 4547942531744955393835)
            ·
              rfl

theorem cell21_538068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 8].length) (baseStart_538068 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_538068 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_538068 prefixEnd_538068 := by exact prefixLift 538068
  have htrace : WordTrace (prefixWord ++ tailWord_538068) baseStart_538068 baseEnd_538068 := by
    simpa [prefixWord, tailWord_538068, baseEnd_538068] using wordTrace_append hprefix tailTrace_538068
  have hstable : (prefixWord ++ tailWord_538068).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538068).length < 2 ^ (prefixWord ++ tailWord_538068).sum := by decide
  have hdescent : baseEnd_538068 < baseStart_538068 := by decide
  rcases family_descends (prefixWord ++ tailWord_538068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538175 : List Nat := [1, 1, 2, 2, 3, 3, 3, 3, 3]
def baseStart_538175 : Nat := 118140960795 + 538175 * 2 ^ 59
def prefixEnd_538175 : Nat := 4983230072969 + 3 ^ 40 * 538175 * 2
def baseEnd_538175 : Nat := 122818867214905387349993

theorem tailTrace_538175 : CollatzResearch.WordTrace tailWord_538175 prefixEnd_538175 122818867214905387349993 := by
  unfold tailWord_538175
  simp only [CollatzResearch.WordTrace]
  refine ⟨19628854825291362817543979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13085903216860908545029319 19628854825291362817543979)
  ·
    refine ⟨29443282237937044226315969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19628854825291362817543979 29443282237937044226315969)
    ·
      refine ⟨22082461678452783169736977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29443282237937044226315969 22082461678452783169736977)
      ·
        refine ⟨16561846258839587377302733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22082461678452783169736977 16561846258839587377302733)
        ·
          refine ⟨6210692347064845266488525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16561846258839587377302733 6210692347064845266488525)
          ·
            refine ⟨2329009630149316974933197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6210692347064845266488525 2329009630149316974933197)
            ·
              refine ⟨873378611305993865599949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2329009630149316974933197 873378611305993865599949)
              ·
                refine ⟨327516979239747699599981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 873378611305993865599949 327516979239747699599981)
                ·
                  refine ⟨122818867214905387349993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 327516979239747699599981 122818867214905387349993)
                  ·
                    rfl

theorem cell21_538175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 3, 3, 3].length) (baseStart_538175 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_538175 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_538175 prefixEnd_538175 := by exact prefixLift 538175
  have htrace : WordTrace (prefixWord ++ tailWord_538175) baseStart_538175 baseEnd_538175 := by
    simpa [prefixWord, tailWord_538175, baseEnd_538175] using wordTrace_append hprefix tailTrace_538175
  have hstable : (prefixWord ++ tailWord_538175).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538175).length < 2 ^ (prefixWord ++ tailWord_538175).sum := by decide
  have hdescent : baseEnd_538175 < baseStart_538175 := by decide
  rcases family_descends (prefixWord ++ tailWord_538175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538198 : List Nat := [5, 2, 2, 2, 2, 1, 2, 1, 4]
def baseStart_538198 : Nat := 118140960795 + 538198 * 2 ^ 59
def prefixEnd_538198 : Nat := 4983230072969 + 3 ^ 40 * 538198 * 2
def baseEnd_538198 : Nat := 122824116128262458466613

theorem tailTrace_538198 : CollatzResearch.WordTrace tailWord_538198 prefixEnd_538198 122824116128262458466613 := by
  unfold tailWord_538198
  simp only [CollatzResearch.WordTrace]
  refine ⟨1226855856513002359101953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13086462469472025163754165 1226855856513002359101953)
  ·
    refine ⟨920141892384751769326465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1226855856513002359101953 920141892384751769326465)
    ·
      refine ⟨690106419288563826994849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 920141892384751769326465 690106419288563826994849)
      ·
        refine ⟨517579814466422870246137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 690106419288563826994849 517579814466422870246137)
        ·
          refine ⟨388184860849817152684603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 517579814466422870246137 388184860849817152684603)
          ·
            refine ⟨582277291274725729026905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 388184860849817152684603 582277291274725729026905)
            ·
              refine ⟨436707968456044296770179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 582277291274725729026905 436707968456044296770179)
              ·
                refine ⟨655061952684066445155269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 436707968456044296770179 655061952684066445155269)
                ·
                  refine ⟨122824116128262458466613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 655061952684066445155269 122824116128262458466613)
                  ·
                    rfl

theorem cell21_538198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 2, 1, 4].length) (baseStart_538198 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_538198 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_538198 prefixEnd_538198 := by exact prefixLift 538198
  have htrace : WordTrace (prefixWord ++ tailWord_538198) baseStart_538198 baseEnd_538198 := by
    simpa [prefixWord, tailWord_538198, baseEnd_538198] using wordTrace_append hprefix tailTrace_538198
  have hstable : (prefixWord ++ tailWord_538198).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538198).length < 2 ^ (prefixWord ++ tailWord_538198).sum := by decide
  have hdescent : baseEnd_538198 < baseStart_538198 := by decide
  rcases family_descends (prefixWord ++ tailWord_538198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538217 : List Nat := [1, 2, 1, 1, 1, 4, 2, 4, 5]
def baseStart_538217 : Nat := 118140960795 + 538217 * 2 ^ 59
def prefixEnd_538217 : Nat := 4983230072969 + 3 ^ 40 * 538217 * 2
def baseEnd_538217 : Nat := 122828452187122647649907

theorem tailTrace_538217 : CollatzResearch.WordTrace tailWord_538217 prefixEnd_538217 122828452187122647649907 := by
  unfold tailWord_538217
  simp only [CollatzResearch.WordTrace]
  refine ⟨19630386691139203990572905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13086924460759469327048603 19630386691139203990572905)
  ·
    refine ⟨14722790018354402992929679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19630386691139203990572905 14722790018354402992929679)
    ·
      refine ⟨22084185027531604489394519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14722790018354402992929679 22084185027531604489394519)
      ·
        refine ⟨33126277541297406734091779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22084185027531604489394519 33126277541297406734091779)
        ·
          refine ⟨49689416311946110101137669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33126277541297406734091779 49689416311946110101137669)
          ·
            refine ⟨9316765558489895643963313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49689416311946110101137669 9316765558489895643963313)
            ·
              refine ⟨6987574168867421732972485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9316765558489895643963313 6987574168867421732972485)
              ·
                refine ⟨1310170156662641574932341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6987574168867421732972485 1310170156662641574932341)
                ·
                  refine ⟨122828452187122647649907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1310170156662641574932341 122828452187122647649907)
                  ·
                    rfl

theorem cell21_538217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 4, 5].length) (baseStart_538217 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_538217 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_538217 prefixEnd_538217 := by exact prefixLift 538217
  have htrace : WordTrace (prefixWord ++ tailWord_538217) baseStart_538217 baseEnd_538217 := by
    simpa [prefixWord, tailWord_538217, baseEnd_538217] using wordTrace_append hprefix tailTrace_538217
  have hstable : (prefixWord ++ tailWord_538217).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538217).length < 2 ^ (prefixWord ++ tailWord_538217).sum := by decide
  have hdescent : baseEnd_538217 < baseStart_538217 := by decide
  rcases family_descends (prefixWord ++ tailWord_538217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538344 : List Nat := [2, 1, 4, 1, 3, 3, 1, 3, 3]
def baseStart_538344 : Nat := 118140960795 + 538344 * 2 ^ 59
def prefixEnd_538344 : Nat := 4983230072969 + 3 ^ 40 * 538344 * 2
def baseEnd_538344 : Nat := 122857435317398649032981

theorem tailTrace_538344 : CollatzResearch.WordTrace tailWord_538344 prefixEnd_538344 122857435317398649032981 := by
  unfold tailWord_538344
  simp only [CollatzResearch.WordTrace]
  refine ⟨9817509380839552340223043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13090012507786069786964057 9817509380839552340223043)
  ·
    refine ⟨14726264071259328510334565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9817509380839552340223043 14726264071259328510334565)
    ·
      refine ⟨2761174513361124095687731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14726264071259328510334565 2761174513361124095687731)
      ·
        refine ⟨4141761770041686143531597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2761174513361124095687731 4141761770041686143531597)
        ·
          refine ⟨1553160663765632303824349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4141761770041686143531597 1553160663765632303824349)
          ·
            refine ⟨582435248912112113934131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1553160663765632303824349 582435248912112113934131)
            ·
              refine ⟨873652873368168170901197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 582435248912112113934131 873652873368168170901197)
              ·
                refine ⟨327619827513063064087949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 873652873368168170901197 327619827513063064087949)
                ·
                  refine ⟨122857435317398649032981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 327619827513063064087949 122857435317398649032981)
                  ·
                    rfl

theorem cell21_538344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 1, 3, 3].length) (baseStart_538344 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_538344 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_538344 prefixEnd_538344 := by exact prefixLift 538344
  have htrace : WordTrace (prefixWord ++ tailWord_538344) baseStart_538344 baseEnd_538344 := by
    simpa [prefixWord, tailWord_538344, baseEnd_538344] using wordTrace_append hprefix tailTrace_538344
  have hstable : (prefixWord ++ tailWord_538344).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538344).length < 2 ^ (prefixWord ++ tailWord_538344).sum := by decide
  have hdescent : baseEnd_538344 < baseStart_538344 := by decide
  rcases family_descends (prefixWord ++ tailWord_538344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538375 : List Nat := [1, 1, 4, 4, 2, 2, 2, 1, 4]
def baseStart_538375 : Nat := 118140960795 + 538375 * 2 ^ 59
def prefixEnd_538375 : Nat := 4983230072969 + 3 ^ 40 * 538375 * 2
def baseEnd_538375 : Nat := 122864509939749484016251

theorem tailTrace_538375 : CollatzResearch.WordTrace tailWord_538375 prefixEnd_538375 122864509939749484016251 := by
  unfold tailWord_538375
  simp only [CollatzResearch.WordTrace]
  refine ⟨19636149424566796974824579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13090766283044531316549719 19636149424566796974824579)
  ·
    refine ⟨29454224136850195462236869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19636149424566796974824579 29454224136850195462236869)
    ·
      refine ⟨5522667025659411649169413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29454224136850195462236869 5522667025659411649169413)
      ·
        refine ⟨1035500067311139684219265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5522667025659411649169413 1035500067311139684219265)
        ·
          refine ⟨776625050483354763164449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1035500067311139684219265 776625050483354763164449)
          ·
            refine ⟨582468787862516072373337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 776625050483354763164449 582468787862516072373337)
            ·
              refine ⟨436851590896887054280003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 582468787862516072373337 436851590896887054280003)
              ·
                refine ⟨655277386345330581420005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 436851590896887054280003 655277386345330581420005)
                ·
                  refine ⟨122864509939749484016251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 655277386345330581420005 122864509939749484016251)
                  ·
                    rfl

theorem cell21_538375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 2, 1, 4].length) (baseStart_538375 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_538375 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_538375 prefixEnd_538375 := by exact prefixLift 538375
  have htrace : WordTrace (prefixWord ++ tailWord_538375) baseStart_538375 baseEnd_538375 := by
    simpa [prefixWord, tailWord_538375, baseEnd_538375] using wordTrace_append hprefix tailTrace_538375
  have hstable : (prefixWord ++ tailWord_538375).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538375).length < 2 ^ (prefixWord ++ tailWord_538375).sum := by decide
  have hdescent : baseEnd_538375 < baseStart_538375 := by decide
  rcases family_descends (prefixWord ++ tailWord_538375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538383 : List Nat := [1, 1, 2, 1, 1, 1, 4, 2, 8]
def baseStart_538383 : Nat := 118140960795 + 538383 * 2 ^ 59
def prefixEnd_538383 : Nat := 4983230072969 + 3 ^ 40 * 538383 * 2
def baseEnd_538383 : Nat := 122866335648743247882901

theorem tailTrace_538383 : CollatzResearch.WordTrace tailWord_538383 prefixEnd_538383 122866335648743247882901 := by
  unfold tailWord_538383
  simp only [CollatzResearch.WordTrace]
  refine ⟨19636441208537814341115803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13090960805691876227410535 19636441208537814341115803)
  ·
    refine ⟨29454661812806721511673705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19636441208537814341115803 29454661812806721511673705)
    ·
      refine ⟨22090996359605041133755279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29454661812806721511673705 22090996359605041133755279)
      ·
        refine ⟨33136494539407561700632919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22090996359605041133755279 33136494539407561700632919)
        ·
          refine ⟨49704741809111342550949379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33136494539407561700632919 49704741809111342550949379)
          ·
            refine ⟨74557112713667013826424069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49704741809111342550949379 74557112713667013826424069)
            ·
              refine ⟨13979458633812565092454513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 74557112713667013826424069 13979458633812565092454513)
              ·
                refine ⟨10484593975359423819340885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13979458633812565092454513 10484593975359423819340885)
                ·
                  refine ⟨122866335648743247882901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10484593975359423819340885 122866335648743247882901)
                  ·
                    rfl

theorem cell21_538383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 2, 8].length) (baseStart_538383 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_538383 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_538383 prefixEnd_538383 := by exact prefixLift 538383
  have htrace : WordTrace (prefixWord ++ tailWord_538383) baseStart_538383 baseEnd_538383 := by
    simpa [prefixWord, tailWord_538383, baseEnd_538383] using wordTrace_append hprefix tailTrace_538383
  have hstable : (prefixWord ++ tailWord_538383).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538383).length < 2 ^ (prefixWord ++ tailWord_538383).sum := by decide
  have hdescent : baseEnd_538383 < baseStart_538383 := by decide
  rcases family_descends (prefixWord ++ tailWord_538383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538417 : List Nat := [1, 2, 2, 3, 2, 3, 2, 2, 4]
def baseStart_538417 : Nat := 118140960795 + 538417 * 2 ^ 59
def prefixEnd_538417 : Nat := 4983230072969 + 3 ^ 40 * 538417 * 2
def baseEnd_538417 : Nat := 122874094911966744316165

theorem tailTrace_538417 : CollatzResearch.WordTrace tailWord_538417 prefixEnd_538417 122874094911966744316165 := by
  unfold tailWord_538417
  simp only [CollatzResearch.WordTrace]
  refine ⟨19637681290414638147853505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13091787526943092098569003 19637681290414638147853505)
  ·
    refine ⟨14728260967810978610890129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19637681290414638147853505 14728260967810978610890129)
    ·
      refine ⟨11046195725858233958167597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14728260967810978610890129 11046195725858233958167597)
      ·
        refine ⟨4142323397196837734312849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11046195725858233958167597 4142323397196837734312849)
        ·
          refine ⟨3106742547897628300734637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4142323397196837734312849 3106742547897628300734637)
          ·
            refine ⟨1165028455461610612775489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3106742547897628300734637 1165028455461610612775489)
            ·
              refine ⟨873771341596207959581617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1165028455461610612775489 873771341596207959581617)
              ·
                refine ⟨655328506197155969686213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 873771341596207959581617 655328506197155969686213)
                ·
                  refine ⟨122874094911966744316165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 655328506197155969686213 122874094911966744316165)
                  ·
                    rfl

theorem cell21_538417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 2, 2, 4].length) (baseStart_538417 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_538417 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_538417 prefixEnd_538417 := by exact prefixLift 538417
  have htrace : WordTrace (prefixWord ++ tailWord_538417) baseStart_538417 baseEnd_538417 := by
    simpa [prefixWord, tailWord_538417, baseEnd_538417] using wordTrace_append hprefix tailTrace_538417
  have hstable : (prefixWord ++ tailWord_538417).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538417).length < 2 ^ (prefixWord ++ tailWord_538417).sum := by decide
  have hdescent : baseEnd_538417 < baseStart_538417 := by decide
  rcases family_descends (prefixWord ++ tailWord_538417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538420 : List Nat := [2, 5, 1, 1, 2, 2, 1, 4, 3]
def baseStart_538420 : Nat := 118140960795 + 538420 * 2 ^ 59
def prefixEnd_538420 : Nat := 4983230072969 + 3 ^ 40 * 538420 * 2
def baseEnd_538420 : Nat := 122874779552839405766159

theorem tailTrace_538420 : CollatzResearch.WordTrace tailWord_538420 prefixEnd_538420 122874779552839405766159 := by
  unfold tailWord_538420
  simp only [CollatzResearch.WordTrace]
  refine ⟨9818895354701884830106357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13091860472935846440141809 9818895354701884830106357)
  ·
    refine ⟨920521439503301702822471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9818895354701884830106357 920521439503301702822471)
    ·
      refine ⟨1380782159254952554233707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 920521439503301702822471 1380782159254952554233707)
      ·
        refine ⟨2071173238882428831350561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1380782159254952554233707 2071173238882428831350561)
        ·
          refine ⟨1553379929161821623512921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2071173238882428831350561 1553379929161821623512921)
          ·
            refine ⟨1165034946871366217634691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1553379929161821623512921 1165034946871366217634691)
            ·
              refine ⟨1747552420307049326452037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1165034946871366217634691 1747552420307049326452037)
              ·
                refine ⟨327666078807571748709757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1747552420307049326452037 327666078807571748709757)
                ·
                  refine ⟨122874779552839405766159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 327666078807571748709757 122874779552839405766159)
                  ·
                    rfl

theorem cell21_538420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 4, 3].length) (baseStart_538420 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_538420 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_538420 prefixEnd_538420 := by exact prefixLift 538420
  have htrace : WordTrace (prefixWord ++ tailWord_538420) baseStart_538420 baseEnd_538420 := by
    simpa [prefixWord, tailWord_538420, baseEnd_538420] using wordTrace_append hprefix tailTrace_538420
  have hstable : (prefixWord ++ tailWord_538420).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538420).length < 2 ^ (prefixWord ++ tailWord_538420).sum := by decide
  have hdescent : baseEnd_538420 < baseStart_538420 := by decide
  rcases family_descends (prefixWord ++ tailWord_538420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538476 : List Nat := [2, 2, 1, 1, 4, 3, 1, 1, 6]
def baseStart_538476 : Nat := 118140960795 + 538476 * 2 ^ 59
def prefixEnd_538476 : Nat := 4983230072969 + 3 ^ 40 * 538476 * 2
def baseEnd_538476 : Nat := 122887559515795752832711

theorem tailTrace_538476 : CollatzResearch.WordTrace tailWord_538476 prefixEnd_538476 122887559515795752832711 := by
  unfold tailWord_538476
  simp only [CollatzResearch.WordTrace]
  refine ⟨9819916598600445612125641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13093222131467260816167521 9819916598600445612125641)
  ·
    refine ⟨7364937448950334209094231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9819916598600445612125641 7364937448950334209094231)
    ·
      refine ⟨11047406173425501313641347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7364937448950334209094231 11047406173425501313641347)
      ·
        refine ⟨16571109260138251970462021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11047406173425501313641347 16571109260138251970462021)
        ·
          refine ⟨3107082986275922244461629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16571109260138251970462021 3107082986275922244461629)
          ·
            refine ⟨1165156119853470841673111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3107082986275922244461629 1165156119853470841673111)
            ·
              refine ⟨1747734179780206262509667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1165156119853470841673111 1747734179780206262509667)
              ·
                refine ⟨2621601269670309393764501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1747734179780206262509667 2621601269670309393764501)
                ·
                  refine ⟨122887559515795752832711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2621601269670309393764501 122887559515795752832711)
                  ·
                    rfl

theorem cell21_538476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 6].length) (baseStart_538476 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_538476 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_538476 prefixEnd_538476 := by exact prefixLift 538476
  have htrace : WordTrace (prefixWord ++ tailWord_538476) baseStart_538476 baseEnd_538476 := by
    simpa [prefixWord, tailWord_538476, baseEnd_538476] using wordTrace_append hprefix tailTrace_538476
  have hstable : (prefixWord ++ tailWord_538476).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538476).length < 2 ^ (prefixWord ++ tailWord_538476).sum := by decide
  have hdescent : baseEnd_538476 < baseStart_538476 := by decide
  rcases family_descends (prefixWord ++ tailWord_538476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538552 : List Nat := [2, 1, 2, 1, 2, 3, 3, 3, 4]
def baseStart_538552 : Nat := 118140960795 + 538552 * 2 ^ 59
def prefixEnd_538552 : Nat := 4983230072969 + 3 ^ 40 * 538552 * 2
def baseEnd_538552 : Nat := 122904903751236509565889

theorem tailTrace_538552 : CollatzResearch.WordTrace tailWord_538552 prefixEnd_538552 122904903751236509565889 := by
  unfold tailWord_538552
  simp only [CollatzResearch.WordTrace]
  refine ⟨9821302572462778102008955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13095070096617037469345273 9821302572462778102008955)
  ·
    refine ⟨14731953858694167153013433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9821302572462778102008955 14731953858694167153013433)
    ·
      refine ⟨11048965394020625364760075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14731953858694167153013433 11048965394020625364760075)
      ·
        refine ⟨16573448091030938047140113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11048965394020625364760075 16573448091030938047140113)
        ·
          refine ⟨12430086068273203535355085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16573448091030938047140113 12430086068273203535355085)
          ·
            refine ⟨4661282275602451325758157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12430086068273203535355085 4661282275602451325758157)
            ·
              refine ⟨1747980853350919247159309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4661282275602451325758157 1747980853350919247159309)
              ·
                refine ⟨655492820006594717684741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1747980853350919247159309 655492820006594717684741)
                ·
                  refine ⟨122904903751236509565889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 655492820006594717684741 122904903751236509565889)
                  ·
                    rfl

theorem cell21_538552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 3, 4].length) (baseStart_538552 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_538552 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_538552 prefixEnd_538552 := by exact prefixLift 538552
  have htrace : WordTrace (prefixWord ++ tailWord_538552) baseStart_538552 baseEnd_538552 := by
    simpa [prefixWord, tailWord_538552, baseEnd_538552] using wordTrace_append hprefix tailTrace_538552
  have hstable : (prefixWord ++ tailWord_538552).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538552).length < 2 ^ (prefixWord ++ tailWord_538552).sum := by decide
  have hdescent : baseEnd_538552 < baseStart_538552 := by decide
  rcases family_descends (prefixWord ++ tailWord_538552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538589 : List Nat := [1, 4, 3, 1, 3, 2, 2, 2, 3]
def baseStart_538589 : Nat := 118140960795 + 538589 * 2 ^ 59
def prefixEnd_538589 : Nat := 4983230072969 + 3 ^ 40 * 538589 * 2
def baseEnd_538589 : Nat := 122913347655332667449147

theorem tailTrace_538589 : CollatzResearch.WordTrace tailWord_538589 prefixEnd_538589 122913347655332667449147 := by
  unfold tailWord_538589
  simp only [CollatzResearch.WordTrace]
  refine ⟨19643954645791511523114821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13095969763861007682076547 19643954645791511523114821)
  ·
    refine ⟨3683241496085908410584029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19643954645791511523114821 3683241496085908410584029)
    ·
      refine ⟨1381215561032215653969011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3683241496085908410584029 1381215561032215653969011)
      ·
        refine ⟨2071823341548323480953517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1381215561032215653969011 2071823341548323480953517)
        ·
          refine ⟨776933753080621305357569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2071823341548323480953517 776933753080621305357569)
          ·
            refine ⟨582700314810465979018177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 776933753080621305357569 582700314810465979018177)
            ·
              refine ⟨437025236107849484263633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 582700314810465979018177 437025236107849484263633)
              ·
                refine ⟨327768927080887113197725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 437025236107849484263633 327768927080887113197725)
                ·
                  refine ⟨122913347655332667449147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 327768927080887113197725 122913347655332667449147)
                  ·
                    rfl

theorem cell21_538589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 2, 2, 3].length) (baseStart_538589 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_538589 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_538589 prefixEnd_538589 := by exact prefixLift 538589
  have htrace : WordTrace (prefixWord ++ tailWord_538589) baseStart_538589 baseEnd_538589 := by
    simpa [prefixWord, tailWord_538589, baseEnd_538589] using wordTrace_append hprefix tailTrace_538589
  have hstable : (prefixWord ++ tailWord_538589).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538589).length < 2 ^ (prefixWord ++ tailWord_538589).sum := by decide
  have hdescent : baseEnd_538589 < baseStart_538589 := by decide
  rcases family_descends (prefixWord ++ tailWord_538589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538631 : List Nat := [1, 1, 4, 3, 1, 3, 2, 3, 3]
def baseStart_538631 : Nat := 118140960795 + 538631 * 2 ^ 59
def prefixEnd_538631 : Nat := 4983230072969 + 3 ^ 40 * 538631 * 2
def baseEnd_538631 : Nat := 122922932627549927749061

theorem tailTrace_538631 : CollatzResearch.WordTrace tailWord_538631 prefixEnd_538631 122922932627549927749061 := by
  unfold tailWord_538631
  simp only [CollatzResearch.WordTrace]
  refine ⟨19645486511639352696143747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13096991007759568464095831 19645486511639352696143747)
  ·
    refine ⟨29468229767459029044215621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19645486511639352696143747 29468229767459029044215621)
    ·
      refine ⟨5525293081398567945790429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29468229767459029044215621 5525293081398567945790429)
      ·
        refine ⟨2071984905524462979671411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5525293081398567945790429 2071984905524462979671411)
        ·
          refine ⟨3107977358286694469507117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2071984905524462979671411 3107977358286694469507117)
          ·
            refine ⟨1165491509357510426065169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3107977358286694469507117 1165491509357510426065169)
            ·
              refine ⟨874118632018132819548877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1165491509357510426065169 874118632018132819548877)
              ·
                refine ⟨327794487006799807330829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 874118632018132819548877 327794487006799807330829)
                ·
                  refine ⟨122922932627549927749061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 327794487006799807330829 122922932627549927749061)
                  ·
                    rfl

theorem cell21_538631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 2, 3, 3].length) (baseStart_538631 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_538631 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_538631 prefixEnd_538631 := by exact prefixLift 538631
  have htrace : WordTrace (prefixWord ++ tailWord_538631) baseStart_538631 baseEnd_538631 := by
    simpa [prefixWord, tailWord_538631, baseEnd_538631] using wordTrace_append hprefix tailTrace_538631
  have hstable : (prefixWord ++ tailWord_538631).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538631).length < 2 ^ (prefixWord ++ tailWord_538631).sum := by decide
  have hdescent : baseEnd_538631 < baseStart_538631 := by decide
  rcases family_descends (prefixWord ++ tailWord_538631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538637 : List Nat := [1, 7, 1, 2, 2, 1, 1, 2, 4]
def baseStart_538637 : Nat := 118140960795 + 538637 * 2 ^ 59
def prefixEnd_538637 : Nat := 4983230072969 + 3 ^ 40 * 538637 * 2
def baseEnd_538637 : Nat := 122924301909295250649049

theorem tailTrace_538637 : CollatzResearch.WordTrace tailWord_538637 prefixEnd_538637 122924301909295250649049 := by
  unfold tailWord_538637
  simp only [CollatzResearch.WordTrace]
  refine ⟨19645705349617615720862165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13097136899745077147241443 19645705349617615720862165)
  ·
    refine ⟨460446219131662868457707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 19645705349617615720862165 460446219131662868457707)
    ·
      refine ⟨690669328697494302686561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 460446219131662868457707 690669328697494302686561)
      ·
        refine ⟨518001996523120727014921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 690669328697494302686561 518001996523120727014921)
        ·
          refine ⟨388501497392340545261191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 518001996523120727014921 388501497392340545261191)
          ·
            refine ⟨582752246088510817891787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 388501497392340545261191 582752246088510817891787)
            ·
              refine ⟨874128369132766226837681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 582752246088510817891787 874128369132766226837681)
              ·
                refine ⟨655596276849574670128261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 874128369132766226837681 655596276849574670128261)
                ·
                  refine ⟨122924301909295250649049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 655596276849574670128261 122924301909295250649049)
                  ·
                    rfl

theorem cell21_538637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 1, 2, 4].length) (baseStart_538637 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_538637 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_538637 prefixEnd_538637 := by exact prefixLift 538637
  have htrace : WordTrace (prefixWord ++ tailWord_538637) baseStart_538637 baseEnd_538637 := by
    simpa [prefixWord, tailWord_538637, baseEnd_538637] using wordTrace_append hprefix tailTrace_538637
  have hstable : (prefixWord ++ tailWord_538637).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538637).length < 2 ^ (prefixWord ++ tailWord_538637).sum := by decide
  have hdescent : baseEnd_538637 < baseStart_538637 := by decide
  rcases family_descends (prefixWord ++ tailWord_538637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538673 : List Nat := [1, 2, 2, 3, 1, 3, 2, 2, 5]
def baseStart_538673 : Nat := 118140960795 + 538673 * 2 ^ 59
def prefixEnd_538673 : Nat := 4983230072969 + 3 ^ 40 * 538673 * 2
def baseEnd_538673 : Nat := 122932517599767188048975

theorem tailTrace_538673 : CollatzResearch.WordTrace tailWord_538673 prefixEnd_538673 122932517599767188048975 := by
  unfold tailWord_538673
  simp only [CollatzResearch.WordTrace]
  refine ⟨19647018377487193869172673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13098012251658129246115115 19647018377487193869172673)
  ·
    refine ⟨14735263783115395401879505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19647018377487193869172673 14735263783115395401879505)
    ·
      refine ⟨11051447837336546551409629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14735263783115395401879505 11051447837336546551409629)
      ·
        refine ⟨4144292939001204956778611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11051447837336546551409629 4144292939001204956778611)
        ·
          refine ⟨6216439408501807435167917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4144292939001204956778611 6216439408501807435167917)
          ·
            refine ⟨2331164778188177788187969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6216439408501807435167917 2331164778188177788187969)
            ·
              refine ⟨1748373583641133341140977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2331164778188177788187969 1748373583641133341140977)
              ·
                refine ⟨1311280187730850005855733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1748373583641133341140977 1311280187730850005855733)
                ·
                  refine ⟨122932517599767188048975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1311280187730850005855733 122932517599767188048975)
                  ·
                    rfl

theorem cell21_538673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 2, 5].length) (baseStart_538673 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_538673 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_538673 prefixEnd_538673 := by exact prefixLift 538673
  have htrace : WordTrace (prefixWord ++ tailWord_538673) baseStart_538673 baseEnd_538673 := by
    simpa [prefixWord, tailWord_538673, baseEnd_538673] using wordTrace_append hprefix tailTrace_538673
  have hstable : (prefixWord ++ tailWord_538673).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538673).length < 2 ^ (prefixWord ++ tailWord_538673).sum := by decide
  have hdescent : baseEnd_538673 < baseStart_538673 := by decide
  rcases family_descends (prefixWord ++ tailWord_538673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538676 : List Nat := [2, 5, 1, 2, 2, 1, 1, 7]
def baseStart_538676 : Nat := 118140960795 + 538676 * 2 ^ 59
def prefixEnd_538676 : Nat := 4983230072969 + 3 ^ 40 * 538676 * 2
def baseEnd_538676 : Nat := 40977734080213283166323

theorem tailTrace_538676 : CollatzResearch.WordTrace tailWord_538676 prefixEnd_538676 40977734080213283166323 := by
  unfold tailWord_538676
  simp only [CollatzResearch.WordTrace]
  refine ⟨9823563898238162690765941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13098085197650883587687921 9823563898238162690765941)
  ·
    refine ⟨920959115459827752259307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9823563898238162690765941 920959115459827752259307)
    ·
      refine ⟨1381438673189741628388961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 920959115459827752259307 1381438673189741628388961)
      ·
        refine ⟨1036079004892306221291721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1381438673189741628388961 1036079004892306221291721)
        ·
          refine ⟨777059253669229665968791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1036079004892306221291721 777059253669229665968791)
          ·
            refine ⟨1165588880503844498953187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 777059253669229665968791 1165588880503844498953187)
            ·
              refine ⟨1748383320755766748429781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1165588880503844498953187 1748383320755766748429781)
              ·
                refine ⟨40977734080213283166323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1748383320755766748429781 40977734080213283166323)
                ·
                  rfl

theorem cell21_538676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 7].length) (baseStart_538676 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_538676 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_538676 prefixEnd_538676 := by exact prefixLift 538676
  have htrace : WordTrace (prefixWord ++ tailWord_538676) baseStart_538676 baseEnd_538676 := by
    simpa [prefixWord, tailWord_538676, baseEnd_538676] using wordTrace_append hprefix tailTrace_538676
  have hstable : (prefixWord ++ tailWord_538676).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538676).length < 2 ^ (prefixWord ++ tailWord_538676).sum := by decide
  have hdescent : baseEnd_538676 < baseStart_538676 := by decide
  rcases family_descends (prefixWord ++ tailWord_538676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538687 : List Nat := [1, 1, 2, 2, 3, 1, 3, 2, 6]
def baseStart_538687 : Nat := 118140960795 + 538687 * 2 ^ 59
def prefixEnd_538687 : Nat := 4983230072969 + 3 ^ 40 * 538687 * 2
def baseEnd_538687 : Nat := 122935712590506274815613

theorem tailTrace_538687 : CollatzResearch.WordTrace tailWord_538687 prefixEnd_538687 122935712590506274815613 := by
  unfold tailWord_538687
  simp only [CollatzResearch.WordTrace]
  refine ⟨19647528999436474260182315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13098352666290982840121543 19647528999436474260182315)
  ·
    refine ⟨29471293499154711390273473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19647528999436474260182315 29471293499154711390273473)
    ·
      refine ⟨22103470124366033542705105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29471293499154711390273473 22103470124366033542705105)
      ·
        refine ⟨16577602593274525157028829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22103470124366033542705105 16577602593274525157028829)
        ·
          refine ⟨6216600972477946933885811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16577602593274525157028829 6216600972477946933885811)
          ·
            refine ⟨9324901458716920400828717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6216600972477946933885811 9324901458716920400828717)
            ·
              refine ⟨3496838047018845150310769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9324901458716920400828717 3496838047018845150310769)
              ·
                refine ⟨2622628535264133862733077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3496838047018845150310769 2622628535264133862733077)
                ·
                  refine ⟨122935712590506274815613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2622628535264133862733077 122935712590506274815613)
                  ·
                    rfl

theorem cell21_538687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 2, 6].length) (baseStart_538687 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_538687 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_538687 prefixEnd_538687 := by exact prefixLift 538687
  have htrace : WordTrace (prefixWord ++ tailWord_538687) baseStart_538687 baseEnd_538687 := by
    simpa [prefixWord, tailWord_538687, baseEnd_538687] using wordTrace_append hprefix tailTrace_538687
  have hstable : (prefixWord ++ tailWord_538687).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538687).length < 2 ^ (prefixWord ++ tailWord_538687).sum := by decide
  have hdescent : baseEnd_538687 < baseStart_538687 := by decide
  rcases family_descends (prefixWord ++ tailWord_538687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538780 : List Nat := [2, 2, 3, 2, 1, 1, 1, 5, 4]
def baseStart_538780 : Nat := 118140960795 + 538780 * 2 ^ 59
def prefixEnd_538780 : Nat := 4983230072969 + 3 ^ 40 * 538780 * 2
def baseEnd_538780 : Nat := 122956936457558779765423

theorem tailTrace_538780 : CollatzResearch.WordTrace tailWord_538780 prefixEnd_538780 122956936457558779765423 := by
  unfold tailWord_538780
  simp only [CollatzResearch.WordTrace]
  refine ⟨9825460494049775571658897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13100613992066367428878529 9825460494049775571658897)
  ·
    refine ⟨7369095370537331678744173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9825460494049775571658897 7369095370537331678744173)
    ·
      refine ⟨2763410763951499379529065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7369095370537331678744173 2763410763951499379529065)
      ·
        refine ⟨2072558072963624534646799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2763410763951499379529065 2072558072963624534646799)
        ·
          refine ⟨3108837109445436801970199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2072558072963624534646799 3108837109445436801970199)
          ·
            refine ⟨4663255664168155202955299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3108837109445436801970199 4663255664168155202955299)
            ·
              refine ⟨6994883496252232804432949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4663255664168155202955299 6994883496252232804432949)
              ·
                refine ⟨655770327773646825415589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6994883496252232804432949 655770327773646825415589)
                ·
                  refine ⟨122956936457558779765423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 655770327773646825415589 122956936457558779765423)
                  ·
                    rfl

theorem cell21_538780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 5, 4].length) (baseStart_538780 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_538780 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_538780 prefixEnd_538780 := by exact prefixLift 538780
  have htrace : WordTrace (prefixWord ++ tailWord_538780) baseStart_538780 baseEnd_538780 := by
    simpa [prefixWord, tailWord_538780, baseEnd_538780] using wordTrace_append hprefix tailTrace_538780
  have hstable : (prefixWord ++ tailWord_538780).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538780).length < 2 ^ (prefixWord ++ tailWord_538780).sum := by decide
  have hdescent : baseEnd_538780 < baseStart_538780 := by decide
  rcases family_descends (prefixWord ++ tailWord_538780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538808 : List Nat := [2, 1, 2, 1, 2, 1, 3, 2, 7]
def baseStart_538808 : Nat := 118140960795 + 538808 * 2 ^ 59
def prefixEnd_538808 : Nat := 4983230072969 + 3 ^ 40 * 538808 * 2
def baseEnd_538808 : Nat := 122963326439036953298699

theorem tailTrace_538808 : CollatzResearch.WordTrace tailWord_538808 prefixEnd_538808 122963326439036953298699 := by
  unfold tailWord_538808
  simp only [CollatzResearch.WordTrace]
  refine ⟨9825971115999055962668539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13101294821332074616891385 9825971115999055962668539)
  ·
    refine ⟨14738956673998583944002809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9825971115999055962668539 14738956673998583944002809)
    ·
      refine ⟨11054217505498937958002107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14738956673998583944002809 11054217505498937958002107)
      ·
        refine ⟨16581326258248406937003161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11054217505498937958002107 16581326258248406937003161)
        ·
          refine ⟨12435994693686305202752371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16581326258248406937003161 12435994693686305202752371)
          ·
            refine ⟨18653992040529457804128557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12435994693686305202752371 18653992040529457804128557)
            ·
              refine ⟨6995247015198546676548209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18653992040529457804128557 6995247015198546676548209)
              ·
                refine ⟨5246435261398910007411157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6995247015198546676548209 5246435261398910007411157)
                ·
                  refine ⟨122963326439036953298699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5246435261398910007411157 122963326439036953298699)
                  ·
                    rfl

theorem cell21_538808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 2, 7].length) (baseStart_538808 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_538808 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_538808 prefixEnd_538808 := by exact prefixLift 538808
  have htrace : WordTrace (prefixWord ++ tailWord_538808) baseStart_538808 baseEnd_538808 := by
    simpa [prefixWord, tailWord_538808, baseEnd_538808] using wordTrace_append hprefix tailTrace_538808
  have hstable : (prefixWord ++ tailWord_538808).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538808).length < 2 ^ (prefixWord ++ tailWord_538808).sum := by decide
  have hdescent : baseEnd_538808 < baseStart_538808 := by decide
  rcases family_descends (prefixWord ++ tailWord_538808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538814 : List Nat := [4, 2, 1, 1, 4, 2, 1, 2, 4]
def baseStart_538814 : Nat := 118140960795 + 538814 * 2 ^ 59
def prefixEnd_538814 : Nat := 4983230072969 + 3 ^ 40 * 538814 * 2
def baseEnd_538814 : Nat := 122964695720782276198687

theorem tailTrace_538814 : CollatzResearch.WordTrace tailWord_538814 prefixEnd_538814 122964695720782276198687 := by
  unfold tailWord_538814
  simp only [CollatzResearch.WordTrace]
  refine ⟨2456520133747046868756937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13101440713317583300036997 2456520133747046868756937)
  ·
    refine ⟨1842390100310285151567703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2456520133747046868756937 1842390100310285151567703)
    ·
      refine ⟨2763585150465427727351555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1842390100310285151567703 2763585150465427727351555)
      ·
        refine ⟨4145377725698141591027333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2763585150465427727351555 4145377725698141591027333)
        ·
          refine ⟨777258323568401548317625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4145377725698141591027333 777258323568401548317625)
          ·
            refine ⟨582943742676301161238219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 777258323568401548317625 582943742676301161238219)
            ·
              refine ⟨874415614014451741857329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 582943742676301161238219 874415614014451741857329)
              ·
                refine ⟨655811710510838806392997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 874415614014451741857329 655811710510838806392997)
                ·
                  refine ⟨122964695720782276198687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 655811710510838806392997 122964695720782276198687)
                  ·
                    rfl

theorem cell21_538814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 1, 2, 4].length) (baseStart_538814 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_538814 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_538814 prefixEnd_538814 := by exact prefixLift 538814
  have htrace : WordTrace (prefixWord ++ tailWord_538814) baseStart_538814 baseEnd_538814 := by
    simpa [prefixWord, tailWord_538814, baseEnd_538814] using wordTrace_append hprefix tailTrace_538814
  have hstable : (prefixWord ++ tailWord_538814).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538814).length < 2 ^ (prefixWord ++ tailWord_538814).sum := by decide
  have hdescent : baseEnd_538814 < baseStart_538814 := by decide
  rcases family_descends (prefixWord ++ tailWord_538814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538870 : List Nat := [5, 1, 1, 1, 1, 1, 11]
def baseStart_538870 : Nat := 118140960795 + 538870 * 2 ^ 59
def prefixEnd_538870 : Nat := 4983230072969 + 3 ^ 40 * 538870 * 2
def baseEnd_538870 : Nat := 13664163964859847029471

theorem tailTrace_538870 : CollatzResearch.WordTrace tailWord_538870 prefixEnd_538870 13664163964859847029471 := by
  unfold tailWord_538870
  simp only [CollatzResearch.WordTrace]
  refine ⟨1228387722360843532130879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13102802371848997676062709 1228387722360843532130879)
  ·
    refine ⟨1842581583541265298196319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1228387722360843532130879 1842581583541265298196319)
    ·
      refine ⟨2763872375311897947294479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1842581583541265298196319 2763872375311897947294479)
      ·
        refine ⟨4145808562967846920941719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2763872375311897947294479 4145808562967846920941719)
        ·
          refine ⟨6218712844451770381412579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4145808562967846920941719 6218712844451770381412579)
          ·
            refine ⟨9328069266677655572118869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6218712844451770381412579 9328069266677655572118869)
            ·
              refine ⟨13664163964859847029471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 9328069266677655572118869 13664163964859847029471)
              ·
                rfl

theorem cell21_538870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 11].length) (baseStart_538870 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_538870 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_538870 prefixEnd_538870 := by exact prefixLift 538870
  have htrace : WordTrace (prefixWord ++ tailWord_538870) baseStart_538870 baseEnd_538870 := by
    simpa [prefixWord, tailWord_538870, baseEnd_538870] using wordTrace_append hprefix tailTrace_538870
  have hstable : (prefixWord ++ tailWord_538870).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538870).length < 2 ^ (prefixWord ++ tailWord_538870).sum := by decide
  have hdescent : baseEnd_538870 < baseStart_538870 := by decide
  rcases family_descends (prefixWord ++ tailWord_538870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538929 : List Nat := [1, 2, 2, 3, 13]
def baseStart_538929 : Nat := 118140960795 + 538929 * 2 ^ 59
def prefixEnd_538929 : Nat := 4983230072969 + 3 ^ 40 * 538929 * 2
def baseEnd_538929 : Nat := 1518406670216884342985

theorem tailTrace_538929 : CollatzResearch.WordTrace tailWord_538929 prefixEnd_538929 1518406670216884342985 := by
  unfold tailWord_538929
  simp only [CollatzResearch.WordTrace]
  refine ⟨19656355464559749590491841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13104236976373166393661227 19656355464559749590491841)
  ·
    refine ⟨14742266598419812192868881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19656355464559749590491841 14742266598419812192868881)
    ·
      refine ⟨11056699948814859144651661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14742266598419812192868881 11056699948814859144651661)
      ·
        refine ⟨4146262480805572179244373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11056699948814859144651661 4146262480805572179244373)
        ·
          refine ⟨1518406670216884342985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 4146262480805572179244373 1518406670216884342985)
          ·
            rfl

theorem cell21_538929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 13].length) (baseStart_538929 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_538929 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_538929 prefixEnd_538929 := by exact prefixLift 538929
  have htrace : WordTrace (prefixWord ++ tailWord_538929) baseStart_538929 baseEnd_538929 := by
    simpa [prefixWord, tailWord_538929, baseEnd_538929] using wordTrace_append hprefix tailTrace_538929
  have hstable : (prefixWord ++ tailWord_538929).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538929).length < 2 ^ (prefixWord ++ tailWord_538929).sum := by decide
  have hdescent : baseEnd_538929 < baseStart_538929 := by decide
  rcases family_descends (prefixWord ++ tailWord_538929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538960 : List Nat := [2, 1, 1, 1, 1, 6, 1, 1, 7]
def baseStart_538960 : Nat := 118140960795 + 538960 * 2 ^ 59
def prefixEnd_538960 : Nat := 4983230072969 + 3 ^ 40 * 538960 * 2
def baseEnd_538960 : Nat := 122998014909918466765055

theorem tailTrace_538960 : CollatzResearch.WordTrace tailWord_538960 prefixEnd_538960 122998014909918466765055 := by
  unfold tailWord_538960
  simp only [CollatzResearch.WordTrace]
  refine ⟨9828743063723720942435167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13104990751631627923246889 9828743063723720942435167)
  ·
    refine ⟨14743114595585581413652751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9828743063723720942435167 14743114595585581413652751)
    ·
      refine ⟨22114671893378372120479127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14743114595585581413652751 22114671893378372120479127)
      ·
        refine ⟨33172007840067558180718691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22114671893378372120479127 33172007840067558180718691)
        ·
          refine ⟨49758011760101337271078037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33172007840067558180718691 49758011760101337271078037)
          ·
            refine ⟨2332406801254750184581783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 49758011760101337271078037 2332406801254750184581783)
            ·
              refine ⟨3498610201882125276872675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2332406801254750184581783 3498610201882125276872675)
              ·
                refine ⟨5247915302823187915309013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3498610201882125276872675 5247915302823187915309013)
                ·
                  refine ⟨122998014909918466765055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5247915302823187915309013 122998014909918466765055)
                  ·
                    rfl

theorem cell21_538960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 1, 7].length) (baseStart_538960 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_538960 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_538960 prefixEnd_538960 := by exact prefixLift 538960
  have htrace : WordTrace (prefixWord ++ tailWord_538960) baseStart_538960 baseEnd_538960 := by
    simpa [prefixWord, tailWord_538960, baseEnd_538960] using wordTrace_append hprefix tailTrace_538960
  have hstable : (prefixWord ++ tailWord_538960).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538960).length < 2 ^ (prefixWord ++ tailWord_538960).sum := by decide
  have hdescent : baseEnd_538960 < baseStart_538960 := by decide
  rcases family_descends (prefixWord ++ tailWord_538960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538991 : List Nat := [1, 1, 2, 1, 3, 1, 2, 6, 4]
def baseStart_538991 : Nat := 118140960795 + 538991 * 2 ^ 59
def prefixEnd_538991 : Nat := 4983230072969 + 3 ^ 40 * 538991 * 2
def baseEnd_538991 : Nat := 123005089532269301748325

theorem tailTrace_538991 : CollatzResearch.WordTrace tailWord_538991 prefixEnd_538991 123005089532269301748325 := by
  unfold tailWord_538991
  simp only [CollatzResearch.WordTrace]
  refine ⟨19658616790335134179248827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13105744526890089452832551 19658616790335134179248827)
  ·
    refine ⟨29487925185502701268873241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19658616790335134179248827 29487925185502701268873241)
    ·
      refine ⟨22115943889127025951654931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29487925185502701268873241 22115943889127025951654931)
      ·
        refine ⟨33173915833690538927482397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22115943889127025951654931 33173915833690538927482397)
        ·
          refine ⟨12440218437633952097805899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33173915833690538927482397 12440218437633952097805899)
          ·
            refine ⟨18660327656450928146708849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12440218437633952097805899 18660327656450928146708849)
            ·
              refine ⟨13995245742338196110031637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18660327656450928146708849 13995245742338196110031637)
              ·
                refine ⟨656027144172102942657733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 13995245742338196110031637 656027144172102942657733)
                ·
                  refine ⟨123005089532269301748325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 656027144172102942657733 123005089532269301748325)
                  ·
                    rfl

theorem cell21_538991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 6, 4].length) (baseStart_538991 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_538991 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_538991 prefixEnd_538991 := by exact prefixLift 538991
  have htrace : WordTrace (prefixWord ++ tailWord_538991) baseStart_538991 baseEnd_538991 := by
    simpa [prefixWord, tailWord_538991, baseEnd_538991] using wordTrace_append hprefix tailTrace_538991
  have hstable : (prefixWord ++ tailWord_538991).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538991).length < 2 ^ (prefixWord ++ tailWord_538991).sum := by decide
  have hdescent : baseEnd_538991 < baseStart_538991 := by decide
  rcases family_descends (prefixWord ++ tailWord_538991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538994 : List Nat := [3, 2, 1, 2, 1, 3, 2, 4, 3]
def baseStart_538994 : Nat := 118140960795 + 538994 * 2 ^ 59
def prefixEnd_538994 : Nat := 4983230072969 + 3 ^ 40 * 538994 * 2
def baseEnd_538994 : Nat := 123005774173141963198319

theorem tailTrace_538994 : CollatzResearch.WordTrace tailWord_538994 prefixEnd_538994 123005774173141963198319 := by
  unfold tailWord_538994
  simp only [CollatzResearch.WordTrace]
  refine ⟨4914681552331066422902009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13105817472882843794405357 4914681552331066422902009)
  ·
    refine ⟨3686011164248299817176507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4914681552331066422902009 3686011164248299817176507)
    ·
      refine ⟨5529016746372449725764761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3686011164248299817176507 5529016746372449725764761)
      ·
        refine ⟨4146762559779337294323571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5529016746372449725764761 4146762559779337294323571)
        ·
          refine ⟨6220143839669005941485357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4146762559779337294323571 6220143839669005941485357)
          ·
            refine ⟨2332553939875877228057009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6220143839669005941485357 2332553939875877228057009)
            ·
              refine ⟨1749415454906907921042757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2332553939875877228057009 1749415454906907921042757)
              ·
                refine ⟨328015397795045235195517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1749415454906907921042757 328015397795045235195517)
                ·
                  refine ⟨123005774173141963198319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 328015397795045235195517 123005774173141963198319)
                  ·
                    rfl

theorem cell21_538994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 4, 3].length) (baseStart_538994 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_538994 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_538994 prefixEnd_538994 := by exact prefixLift 538994
  have htrace : WordTrace (prefixWord ++ tailWord_538994) baseStart_538994 baseEnd_538994 := by
    simpa [prefixWord, tailWord_538994, baseEnd_538994] using wordTrace_append hprefix tailTrace_538994
  have hstable : (prefixWord ++ tailWord_538994).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538994).length < 2 ^ (prefixWord ++ tailWord_538994).sum := by decide
  have hdescent : baseEnd_538994 < baseStart_538994 := by decide
  rcases family_descends (prefixWord ++ tailWord_538994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_539028 : List Nat := [2, 4, 2, 1, 3, 2, 1, 3, 3]
def baseStart_539028 : Nat := 118140960795 + 539028 * 2 ^ 59
def prefixEnd_539028 : Nat := 4983230072969 + 3 ^ 40 * 539028 * 2
def baseEnd_539028 : Nat := 123013533436365459631583

theorem tailTrace_539028 : CollatzResearch.WordTrace tailWord_539028 prefixEnd_539028 123013533436365459631583 := by
  unfold tailWord_539028
  simp only [CollatzResearch.WordTrace]
  refine ⟨9829983145600544749172869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13106644194134059665563825 9829983145600544749172869)
  ·
    refine ⟨1843121839800102140469913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9829983145600544749172869 1843121839800102140469913)
    ·
      refine ⟨1382341379850076605352435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1843121839800102140469913 1382341379850076605352435)
      ·
        refine ⟨2073512069775114908028653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1382341379850076605352435 2073512069775114908028653)
        ·
          refine ⟨777567026165668090510745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2073512069775114908028653 777567026165668090510745)
          ·
            refine ⟨583175269624251067883059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 777567026165668090510745 583175269624251067883059)
            ·
              refine ⟨874762904436376601824589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 583175269624251067883059 874762904436376601824589)
              ·
                refine ⟨328036089163641225684221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 874762904436376601824589 328036089163641225684221)
                ·
                  refine ⟨123013533436365459631583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 328036089163641225684221 123013533436365459631583)
                  ·
                    rfl

theorem cell21_539028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 1, 3, 3].length) (baseStart_539028 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_539028 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_539028 prefixEnd_539028 := by exact prefixLift 539028
  have htrace : WordTrace (prefixWord ++ tailWord_539028) baseStart_539028 baseEnd_539028 := by
    simpa [prefixWord, tailWord_539028, baseEnd_539028] using wordTrace_append hprefix tailTrace_539028
  have hstable : (prefixWord ++ tailWord_539028).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_539028).length < 2 ^ (prefixWord ++ tailWord_539028).sum := by decide
  have hdescent : baseEnd_539028 < baseStart_539028 := by decide
  rcases family_descends (prefixWord ++ tailWord_539028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_539081 : List Nat := [1, 2, 1, 1, 2, 1, 6, 7]
def baseStart_539081 : Nat := 118140960795 + 539081 * 2 ^ 59
def prefixEnd_539081 : Nat := 4983230072969 + 3 ^ 40 * 539081 * 2
def baseEnd_539081 : Nat := 41008542919483048416047

theorem tailTrace_539081 : CollatzResearch.WordTrace tailWord_539081 prefixEnd_539081 41008542919483048416047 := by
  unfold tailWord_539081
  simp only [CollatzResearch.WordTrace]
  refine ⟨19661899360009079550025097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13107932906672719700016731 19661899360009079550025097)
  ·
    refine ⟨14746424520006809662518823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19661899360009079550025097 14746424520006809662518823)
    ·
      refine ⟨22119636780010214493778235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14746424520006809662518823 22119636780010214493778235)
      ·
        refine ⟨33179455170015321740667353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22119636780010214493778235 33179455170015321740667353)
        ·
          refine ⟨24884591377511491305500515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33179455170015321740667353 24884591377511491305500515)
          ·
            refine ⟨37326887066267236958250773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24884591377511491305500515 37326887066267236958250773)
            ·
              refine ⟨1749697831231276732418005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 37326887066267236958250773 1749697831231276732418005)
              ·
                refine ⟨41008542919483048416047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1749697831231276732418005 41008542919483048416047)
                ·
                  rfl

theorem cell21_539081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 7].length) (baseStart_539081 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_539081 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_539081 prefixEnd_539081 := by exact prefixLift 539081
  have htrace : WordTrace (prefixWord ++ tailWord_539081) baseStart_539081 baseEnd_539081 := by
    simpa [prefixWord, tailWord_539081, baseEnd_539081] using wordTrace_append hprefix tailTrace_539081
  have hstable : (prefixWord ++ tailWord_539081).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_539081).length < 2 ^ (prefixWord ++ tailWord_539081).sum := by decide
  have hdescent : baseEnd_539081 < baseStart_539081 := by decide
  rcases family_descends (prefixWord ++ tailWord_539081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_539146 : List Nat := [3, 1, 2, 2, 2, 1, 4, 3, 3]
def baseStart_539146 : Nat := 118140960795 + 539146 * 2 ^ 59
def prefixEnd_539146 : Nat := 4983230072969 + 3 ^ 40 * 539146 * 2
def baseEnd_539146 : Nat := 123040462644023476664675

theorem tailTrace_539146 : CollatzResearch.WordTrace tailWord_539146 prefixEnd_539146 123040462644023476664675 := by
  unfold tailWord_539146
  simp only [CollatzResearch.WordTrace]
  refine ⟨4916067526193398912785323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13109513403182397100760861 4916067526193398912785323)
  ·
    refine ⟨7374101289290098369177985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4916067526193398912785323 7374101289290098369177985)
    ·
      refine ⟨5530575966967573776883489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7374101289290098369177985 5530575966967573776883489)
      ·
        refine ⟨4147931975225680332662617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5530575966967573776883489 4147931975225680332662617)
        ·
          refine ⟨3110948981419260249496963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4147931975225680332662617 3110948981419260249496963)
          ·
            refine ⟨4666423472128890374245445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3110948981419260249496963 4666423472128890374245445)
            ·
              refine ⟨874954401024166945171021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4666423472128890374245445 874954401024166945171021)
              ·
                refine ⟨328107900384062604439133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 874954401024166945171021 328107900384062604439133)
                ·
                  refine ⟨123040462644023476664675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 328107900384062604439133 123040462644023476664675)
                  ·
                    rfl

theorem cell21_539146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 4, 3, 3].length) (baseStart_539146 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_539146 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_539146 prefixEnd_539146 := by exact prefixLift 539146
  have htrace : WordTrace (prefixWord ++ tailWord_539146) baseStart_539146 baseEnd_539146 := by
    simpa [prefixWord, tailWord_539146, baseEnd_539146] using wordTrace_append hprefix tailTrace_539146
  have hstable : (prefixWord ++ tailWord_539146).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_539146).length < 2 ^ (prefixWord ++ tailWord_539146).sum := by decide
  have hdescent : baseEnd_539146 < baseStart_539146 := by decide
  rcases family_descends (prefixWord ++ tailWord_539146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_539157 : List Nat := [1, 3, 2, 1, 3, 1, 10]
def baseStart_539157 : Nat := 118140960795 + 539157 * 2 ^ 59
def prefixEnd_539157 : Nat := 4983230072969 + 3 ^ 40 * 539157 * 2
def baseEnd_539157 : Nat := 13671441443765544664591

theorem tailTrace_539157 : CollatzResearch.WordTrace tailWord_539157 prefixEnd_539157 13671441443765544664591 := by
  unfold tailWord_539157
  simp only [CollatzResearch.WordTrace]
  refine ⟨19664671307733744529791725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13109780871822496353194483 19664671307733744529791725)
  ·
    refine ⟨7374251740400154198671897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19664671307733744529791725 7374251740400154198671897)
    ·
      refine ⟨5530688805300115649003923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7374251740400154198671897 5530688805300115649003923)
      ·
        refine ⟨8296033207950173473505885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5530688805300115649003923 8296033207950173473505885)
        ·
          refine ⟨3111012452981315052564707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8296033207950173473505885 3111012452981315052564707)
          ·
            refine ⟨4666518679471972578847061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3111012452981315052564707 4666518679471972578847061)
            ·
              refine ⟨13671441443765544664591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 4666518679471972578847061 13671441443765544664591)
              ·
                rfl

theorem cell21_539157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 10].length) (baseStart_539157 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_539157 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_539157 prefixEnd_539157 := by exact prefixLift 539157
  have htrace : WordTrace (prefixWord ++ tailWord_539157) baseStart_539157 baseEnd_539157 := by
    simpa [prefixWord, tailWord_539157, baseEnd_539157] using wordTrace_append hprefix tailTrace_539157
  have hstable : (prefixWord ++ tailWord_539157).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_539157).length < 2 ^ (prefixWord ++ tailWord_539157).sum := by decide
  have hdescent : baseEnd_539157 < baseStart_539157 := by decide
  rcases family_descends (prefixWord ++ tailWord_539157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_539160 : List Nat := [2, 1, 2, 3, 3, 1, 3, 2, 4]
def baseStart_539160 : Nat := 118140960795 + 539160 * 2 ^ 59
def prefixEnd_539160 : Nat := 4983230072969 + 3 ^ 40 * 539160 * 2
def baseEnd_539160 : Nat := 123043657634762563431313

theorem tailTrace_539160 : CollatzResearch.WordTrace tailWord_539160 prefixEnd_539160 123043657634762563431313 := by
  unfold tailWord_539160
  simp only [CollatzResearch.WordTrace]
  refine ⟨9832390363361438021075467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13109853817815250694767289 9832390363361438021075467)
  ·
    refine ⟨14748585545042157031613201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9832390363361438021075467 14748585545042157031613201)
    ·
      refine ⟨11061439158781617773709901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14748585545042157031613201 11061439158781617773709901)
      ·
        refine ⟨4148039684543106665141213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11061439158781617773709901 4148039684543106665141213)
        ·
          refine ⟨1555514881703664999427955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4148039684543106665141213 1555514881703664999427955)
          ·
            refine ⟨2333272322555497499141933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1555514881703664999427955 2333272322555497499141933)
            ·
              refine ⟨874977120958311562178225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2333272322555497499141933 874977120958311562178225)
              ·
                refine ⟨656232840718733671633669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 874977120958311562178225 656232840718733671633669)
                ·
                  refine ⟨123043657634762563431313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 656232840718733671633669 123043657634762563431313)
                  ·
                    rfl

theorem cell21_539160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 3, 2, 4].length) (baseStart_539160 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_539160 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_539160 prefixEnd_539160 := by exact prefixLift 539160
  have htrace : WordTrace (prefixWord ++ tailWord_539160) baseStart_539160 baseEnd_539160 := by
    simpa [prefixWord, tailWord_539160, baseEnd_539160] using wordTrace_append hprefix tailTrace_539160
  have hstable : (prefixWord ++ tailWord_539160).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_539160).length < 2 ^ (prefixWord ++ tailWord_539160).sum := by decide
  have hdescent : baseEnd_539160 < baseStart_539160 := by decide
  rcases family_descends (prefixWord ++ tailWord_539160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_539233 : List Nat := [1, 2, 3, 1, 1, 4, 1, 8]
def baseStart_539233 : Nat := 118140960795 + 539233 * 2 ^ 59
def prefixEnd_539233 : Nat := 4983230072969 + 3 ^ 40 * 539233 * 2
def baseEnd_539233 : Nat := 41020105743110219571499

theorem tailTrace_539233 : CollatzResearch.WordTrace tailWord_539233 prefixEnd_539233 41020105743110219571499 := by
  unfold tailWord_539233
  simp only [CollatzResearch.WordTrace]
  refine ⟨19667443255458409509558353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13111628836972273006372235 19667443255458409509558353)
  ·
    refine ⟨14750582441593807132168765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19667443255458409509558353 14750582441593807132168765)
    ·
      refine ⟨5531468415597677674563287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14750582441593807132168765 5531468415597677674563287)
      ·
        refine ⟨8297202623396516511844931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5531468415597677674563287 8297202623396516511844931)
        ·
          refine ⟨12445803935094774767767397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8297202623396516511844931 12445803935094774767767397)
          ·
            refine ⟨2333588237830270268956387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12445803935094774767767397 2333588237830270268956387)
            ·
              refine ⟨3500382356745405403434581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2333588237830270268956387 3500382356745405403434581)
              ·
                refine ⟨41020105743110219571499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3500382356745405403434581 41020105743110219571499)
                ·
                  rfl

theorem cell21_539233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 8].length) (baseStart_539233 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_539233 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_539233 prefixEnd_539233 := by exact prefixLift 539233
  have htrace : WordTrace (prefixWord ++ tailWord_539233) baseStart_539233 baseEnd_539233 := by
    simpa [prefixWord, tailWord_539233, baseEnd_539233] using wordTrace_append hprefix tailTrace_539233
  have hstable : (prefixWord ++ tailWord_539233).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_539233).length < 2 ^ (prefixWord ++ tailWord_539233).sum := by decide
  have hdescent : baseEnd_539233 < baseStart_539233 := by decide
  rcases family_descends (prefixWord ++ tailWord_539233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_539329 : List Nat := [1, 2, 6, 2, 1, 1, 1, 1, 6]
def baseStart_539329 : Nat := 118140960795 + 539329 * 2 ^ 59
def prefixEnd_539329 : Nat := 4983230072969 + 3 ^ 40 * 539329 * 2
def baseEnd_539329 : Nat := 123082225737255825114301

theorem tailTrace_539329 : CollatzResearch.WordTrace tailWord_539329 prefixEnd_539329 123082225737255825114301 := by
  unfold tailWord_539329
  simp only [CollatzResearch.WordTrace]
  refine ⟨19670944663110617905053041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13113963108740411936702027 19670944663110617905053041)
  ·
    refine ⟨14753208497332963428789781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19670944663110617905053041 14753208497332963428789781)
    ·
      refine ⟨691556648312482660724521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 14753208497332963428789781 691556648312482660724521)
      ·
        refine ⟨518667486234361995543391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 691556648312482660724521 518667486234361995543391)
        ·
          refine ⟨778001229351542993315087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 518667486234361995543391 778001229351542993315087)
          ·
            refine ⟨1167001844027314489972631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 778001229351542993315087 1167001844027314489972631)
            ·
              refine ⟨1750502766040971734958947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1167001844027314489972631 1750502766040971734958947)
              ·
                refine ⟨2625754149061457602438421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1750502766040971734958947 2625754149061457602438421)
                ·
                  refine ⟨123082225737255825114301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2625754149061457602438421 123082225737255825114301)
                  ·
                    rfl

theorem cell21_539329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 1, 6].length) (baseStart_539329 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_539329 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_539329 prefixEnd_539329 := by exact prefixLift 539329
  have htrace : WordTrace (prefixWord ++ tailWord_539329) baseStart_539329 baseEnd_539329 := by
    simpa [prefixWord, tailWord_539329, baseEnd_539329] using wordTrace_append hprefix tailTrace_539329
  have hstable : (prefixWord ++ tailWord_539329).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_539329).length < 2 ^ (prefixWord ++ tailWord_539329).sum := by decide
  have hdescent : baseEnd_539329 < baseStart_539329 := by decide
  rcases family_descends (prefixWord ++ tailWord_539329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_539374 : List Nat := [4, 1, 2, 1, 1, 3, 3, 3, 3]
def baseStart_539374 : Nat := 118140960795 + 539374 * 2 ^ 59
def prefixEnd_539374 : Nat := 4983230072969 + 3 ^ 40 * 539374 * 2
def baseEnd_539374 : Nat := 123092495350345746864209

theorem tailTrace_539374 : CollatzResearch.WordTrace tailWord_539374 prefixEnd_539374 123092495350345746864209 := by
  unfold tailWord_539374
  simp only [CollatzResearch.WordTrace]
  refine ⟨2459073243493448823805147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13115057298631727060294117 2459073243493448823805147)
  ·
    refine ⟨3688609865240173235707721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2459073243493448823805147 3688609865240173235707721)
    ·
      refine ⟨2766457398930129926780791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3688609865240173235707721 2766457398930129926780791)
      ·
        refine ⟨4149686098395194890171187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2766457398930129926780791 4149686098395194890171187)
        ·
          refine ⟨6224529147592792335256781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4149686098395194890171187 6224529147592792335256781)
          ·
            refine ⟨2334198430347297125721293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6224529147592792335256781 2334198430347297125721293)
            ·
              refine ⟨875324411380236422145485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2334198430347297125721293 875324411380236422145485)
              ·
                refine ⟨328246654267588658304557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 875324411380236422145485 328246654267588658304557)
                ·
                  refine ⟨123092495350345746864209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 328246654267588658304557 123092495350345746864209)
                  ·
                    rfl

theorem cell21_539374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 3, 3, 3].length) (baseStart_539374 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_539374 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_539374 prefixEnd_539374 := by exact prefixLift 539374
  have htrace : WordTrace (prefixWord ++ tailWord_539374) baseStart_539374 baseEnd_539374 := by
    simpa [prefixWord, tailWord_539374, baseEnd_539374] using wordTrace_append hprefix tailTrace_539374
  have hstable : (prefixWord ++ tailWord_539374).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_539374).length < 2 ^ (prefixWord ++ tailWord_539374).sum := by decide
  have hdescent : baseEnd_539374 < baseStart_539374 := by decide
  rcases family_descends (prefixWord ++ tailWord_539374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_539447 : List Nat := [1, 1, 3, 1, 2, 1, 6, 2, 4]
def baseStart_539447 : Nat := 118140960795 + 539447 * 2 ^ 59
def prefixEnd_539447 : Nat := 4983230072969 + 3 ^ 40 * 539447 * 2
def baseEnd_539447 : Nat := 123109154944913842147393

theorem tailTrace_539447 : CollatzResearch.WordTrace tailWord_539447 prefixEnd_539447 123109154944913842147393 := by
  unfold tailWord_539447
  simp only [CollatzResearch.WordTrace]
  refine ⟨19675248476683124057848595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13116832317788749371899063 19675248476683124057848595)
  ·
    refine ⟨29512872715024686086772893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19675248476683124057848595 29512872715024686086772893)
    ·
      refine ⟨11067327268134257282539835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29512872715024686086772893 11067327268134257282539835)
      ·
        refine ⟨16600990902201385923809753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11067327268134257282539835 16600990902201385923809753)
        ·
          refine ⟨12450743176651039442857315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16600990902201385923809753 12450743176651039442857315)
          ·
            refine ⟨18676114764976559164285973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12450743176651039442857315 18676114764976559164285973)
            ·
              refine ⟨875442879608276210825905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 18676114764976559164285973 875442879608276210825905)
              ·
                refine ⟨656582159706207158119429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 875442879608276210825905 656582159706207158119429)
                ·
                  refine ⟨123109154944913842147393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 656582159706207158119429 123109154944913842147393)
                  ·
                    rfl

theorem cell21_539447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 6, 2, 4].length) (baseStart_539447 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_539447 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_539447 prefixEnd_539447 := by exact prefixLift 539447
  have htrace : WordTrace (prefixWord ++ tailWord_539447) baseStart_539447 baseEnd_539447 := by
    simpa [prefixWord, tailWord_539447, baseEnd_539447] using wordTrace_append hprefix tailTrace_539447
  have hstable : (prefixWord ++ tailWord_539447).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_539447).length < 2 ^ (prefixWord ++ tailWord_539447).sum := by decide
  have hdescent : baseEnd_539447 < baseStart_539447 := by decide
  rcases family_descends (prefixWord ++ tailWord_539447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_539450 : List Nat := [3, 1, 1, 1, 6, 1, 1, 4, 3]
def baseStart_539450 : Nat := 118140960795 + 539450 * 2 ^ 59
def prefixEnd_539450 : Nat := 4983230072969 + 3 ^ 40 * 539450 * 2
def baseEnd_539450 : Nat := 123109839585786503597387

theorem tailTrace_539450 : CollatzResearch.WordTrace tailWord_539450 prefixEnd_539450 123109839585786503597387 := by
  unfold tailWord_539450
  simp only [CollatzResearch.WordTrace]
  refine ⟨4918839473918063892551951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13116905263781503713471869 4918839473918063892551951)
  ·
    refine ⟨7378259210877095838827927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4918839473918063892551951 7378259210877095838827927)
    ·
      refine ⟨11067388816315643758241891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7378259210877095838827927 11067388816315643758241891)
      ·
        refine ⟨16601083224473465637362837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11067388816315643758241891 16601083224473465637362837)
        ·
          refine ⟨778175776147193701751383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 16601083224473465637362837 778175776147193701751383)
          ·
            refine ⟨1167263664220790552627075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 778175776147193701751383 1167263664220790552627075)
            ·
              refine ⟨1750895496331185828940613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1167263664220790552627075 1750895496331185828940613)
              ·
                refine ⟨328292905562097342926365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1750895496331185828940613 328292905562097342926365)
                ·
                  refine ⟨123109839585786503597387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 328292905562097342926365 123109839585786503597387)
                  ·
                    rfl

theorem cell21_539450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 4, 3].length) (baseStart_539450 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_539450 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_539450 prefixEnd_539450 := by exact prefixLift 539450
  have htrace : WordTrace (prefixWord ++ tailWord_539450) baseStart_539450 baseEnd_539450 := by
    simpa [prefixWord, tailWord_539450, baseEnd_539450] using wordTrace_append hprefix tailTrace_539450
  have hstable : (prefixWord ++ tailWord_539450).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_539450).length < 2 ^ (prefixWord ++ tailWord_539450).sum := by decide
  have hdescent : baseEnd_539450 < baseStart_539450 := by decide
  rcases family_descends (prefixWord ++ tailWord_539450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_539509 : List Nat := [1, 3, 4, 1, 1, 3, 2, 1, 5]
def baseStart_539509 : Nat := 118140960795 + 539509 * 2 ^ 59
def prefixEnd_539509 : Nat := 4983230072969 + 3 ^ 40 * 539509 * 2
def baseEnd_539509 : Nat := 123123304189615512113933

theorem tailTrace_539509 : CollatzResearch.WordTrace tailWord_539509 prefixEnd_539509 123123304189615512113933 := by
  unfold tailWord_539509
  simp only [CollatzResearch.WordTrace]
  refine ⟨19677509802458508646605581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13118339868305672431070387 19677509802458508646605581)
  ·
    refine ⟨7379066175921940742477093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19677509802458508646605581 7379066175921940742477093)
    ·
      refine ⟨1383574907985363889214455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7379066175921940742477093 1383574907985363889214455)
      ·
        refine ⟨2075362361978045833821683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1383574907985363889214455 2075362361978045833821683)
        ·
          refine ⟨3113043542967068750732525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2075362361978045833821683 3113043542967068750732525)
          ·
            refine ⟨1167391328612650781524697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3113043542967068750732525 1167391328612650781524697)
            ·
              refine ⟨875543496459488086143523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1167391328612650781524697 875543496459488086143523)
              ·
                refine ⟨1313315244689232129215285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 875543496459488086143523 1313315244689232129215285)
                ·
                  refine ⟨123123304189615512113933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1313315244689232129215285 123123304189615512113933)
                  ·
                    rfl

theorem cell21_539509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 2, 1, 5].length) (baseStart_539509 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_539509 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_539509 prefixEnd_539509 := by exact prefixLift 539509
  have htrace : WordTrace (prefixWord ++ tailWord_539509) baseStart_539509 baseEnd_539509 := by
    simpa [prefixWord, tailWord_539509, baseEnd_539509] using wordTrace_append hprefix tailTrace_539509
  have hstable : (prefixWord ++ tailWord_539509).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_539509).length < 2 ^ (prefixWord ++ tailWord_539509).sum := by decide
  have hdescent : baseEnd_539509 < baseStart_539509 := by decide
  rcases family_descends (prefixWord ++ tailWord_539509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_539554 : List Nat := [3, 3, 1, 2, 2, 3, 7]
def baseStart_539554 : Nat := 118140960795 + 539554 * 2 ^ 59
def prefixEnd_539554 : Nat := 4983230072969 + 3 ^ 40 * 539554 * 2
def baseEnd_539554 : Nat := 13681508200300603762649

theorem tailTrace_539554 : CollatzResearch.WordTrace tailWord_539554 prefixEnd_539554 13681508200300603762649 := by
  unfold tailWord_539554
  simp only [CollatzResearch.WordTrace]
  refine ⟨4919787771823870332998429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13119434058196987554662477 4919787771823870332998429)
  ·
    refine ⟨1844920414433951374874411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4919787771823870332998429 1844920414433951374874411)
    ·
      refine ⟨2767380621650927062311617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1844920414433951374874411 2767380621650927062311617)
      ·
        refine ⟨2075535466238195296733713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2767380621650927062311617 2075535466238195296733713)
        ·
          refine ⟨1556651599678646472550285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2075535466238195296733713 1556651599678646472550285)
          ·
            refine ⟨583744349879492427206357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1556651599678646472550285 583744349879492427206357)
            ·
              refine ⟨13681508200300603762649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 583744349879492427206357 13681508200300603762649)
              ·
                rfl

theorem cell21_539554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 7].length) (baseStart_539554 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_539554 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_539554 prefixEnd_539554 := by exact prefixLift 539554
  have htrace : WordTrace (prefixWord ++ tailWord_539554) baseStart_539554 baseEnd_539554 := by
    simpa [prefixWord, tailWord_539554, baseEnd_539554] using wordTrace_append hprefix tailTrace_539554
  have hstable : (prefixWord ++ tailWord_539554).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_539554).length < 2 ^ (prefixWord ++ tailWord_539554).sum := by decide
  have hdescent : baseEnd_539554 < baseStart_539554 := by decide
  rcases family_descends (prefixWord ++ tailWord_539554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_539613 : List Nat := [1, 4, 3, 1, 2, 10]
def baseStart_539613 : Nat := 118140960795 + 539613 * 2 ^ 59
def prefixEnd_539613 : Nat := 4983230072969 + 3 ^ 40 * 539613 * 2
def baseEnd_539613 : Nat := 4561001422464238606681

theorem tailTrace_539613 : CollatzResearch.WordTrace tailWord_539613 prefixEnd_539613 4561001422464238606681 := by
  unfold tailWord_539613
  simp only [CollatzResearch.WordTrace]
  refine ⟨19681302994081734408391493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13120868662721156272260995 19681302994081734408391493)
  ·
    refine ⟨3690244311390325201573405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19681302994081734408391493 3690244311390325201573405)
    ·
      refine ⟨1383841616771371950590027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3690244311390325201573405 1383841616771371950590027)
      ·
        refine ⟨2075762425157057925885041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1383841616771371950590027 2075762425157057925885041)
        ·
          refine ⟨1556821818867793444413781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2075762425157057925885041 1556821818867793444413781)
          ·
            refine ⟨4561001422464238606681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1556821818867793444413781 4561001422464238606681)
            ·
              rfl

theorem cell21_539613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 10].length) (baseStart_539613 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_539613 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_539613 prefixEnd_539613 := by exact prefixLift 539613
  have htrace : WordTrace (prefixWord ++ tailWord_539613) baseStart_539613 baseEnd_539613 := by
    simpa [prefixWord, tailWord_539613, baseEnd_539613] using wordTrace_append hprefix tailTrace_539613
  have hstable : (prefixWord ++ tailWord_539613).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_539613).length < 2 ^ (prefixWord ++ tailWord_539613).sum := by decide
  have hdescent : baseEnd_539613 < baseStart_539613 := by decide
  rcases family_descends (prefixWord ++ tailWord_539613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_539636 : List Nat := [2, 6, 2, 1, 1, 1, 1, 2, 5]
def baseStart_539636 : Nat := 118140960795 + 539636 * 2 ^ 59
def prefixEnd_539636 : Nat := 4983230072969 + 3 ^ 40 * 539636 * 2
def baseEnd_539636 : Nat := 123152287319891513497007

theorem tailTrace_539636 : CollatzResearch.WordTrace tailWord_539636 prefixEnd_539636 123152287319891513497007 := by
  unfold tailWord_539636
  simp only [CollatzResearch.WordTrace]
  refine ⟨9841070936499204668239381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13121427915332272890985841 9841070936499204668239381)
  ·
    refine ⟨461300200148400218823721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 9841070936499204668239381 461300200148400218823721)
    ·
      refine ⟨345975150111300164117791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 461300200148400218823721 345975150111300164117791)
      ·
        refine ⟨518962725166950246176687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 345975150111300164117791 518962725166950246176687)
        ·
          refine ⟨778444087750425369265031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 518962725166950246176687 778444087750425369265031)
          ·
            refine ⟨1167666131625638053897547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 778444087750425369265031 1167666131625638053897547)
            ·
              refine ⟨1751499197438457080846321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1167666131625638053897547 1751499197438457080846321)
              ·
                refine ⟨1313624398078842810634741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1751499197438457080846321 1313624398078842810634741)
                ·
                  refine ⟨123152287319891513497007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1313624398078842810634741 123152287319891513497007)
                  ·
                    rfl

theorem cell21_539636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 2, 5].length) (baseStart_539636 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_539636 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_539636 prefixEnd_539636 := by exact prefixLift 539636
  have htrace : WordTrace (prefixWord ++ tailWord_539636) baseStart_539636 baseEnd_539636 := by
    simpa [prefixWord, tailWord_539636, baseEnd_539636] using wordTrace_append hprefix tailTrace_539636
  have hstable : (prefixWord ++ tailWord_539636).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_539636).length < 2 ^ (prefixWord ++ tailWord_539636).sum := by decide
  have hdescent : baseEnd_539636 < baseStart_539636 := by decide
  rcases family_descends (prefixWord ++ tailWord_539636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_539644 : List Nat := [2, 2, 2, 1, 2, 4, 1, 2, 5]
def baseStart_539644 : Nat := 118140960795 + 539644 * 2 ^ 59
def prefixEnd_539644 : Nat := 4983230072969 + 3 ^ 40 * 539644 * 2
def baseEnd_539644 : Nat := 123154113028885277363657

theorem tailTrace_539644 : CollatzResearch.WordTrace tailWord_539644 prefixEnd_539644 123154113028885277363657 := by
  unfold tailWord_539644
  simp only [CollatzResearch.WordTrace]
  refine ⟨9841216828484713351384993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13121622437979617801846657 9841216828484713351384993)
  ·
    refine ⟨7380912621363535013538745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9841216828484713351384993 7380912621363535013538745)
    ·
      refine ⟨5535684466022651260154059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7380912621363535013538745 5535684466022651260154059)
      ·
        refine ⟨8303526699033976890231089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5535684466022651260154059 8303526699033976890231089)
        ·
          refine ⟨6227645024275482667673317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8303526699033976890231089 6227645024275482667673317)
          ·
            refine ⟨1167683442051653000188747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6227645024275482667673317 1167683442051653000188747)
            ·
              refine ⟨1751525163077479500283121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1167683442051653000188747 1751525163077479500283121)
              ·
                refine ⟨1313643872308109625212341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1751525163077479500283121 1313643872308109625212341)
                ·
                  refine ⟨123154113028885277363657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1313643872308109625212341 123154113028885277363657)
                  ·
                    rfl

theorem cell21_539644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 2, 5].length) (baseStart_539644 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_539644 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_539644 prefixEnd_539644 := by exact prefixLift 539644
  have htrace : WordTrace (prefixWord ++ tailWord_539644) baseStart_539644 baseEnd_539644 := by
    simpa [prefixWord, tailWord_539644, baseEnd_539644] using wordTrace_append hprefix tailTrace_539644
  have hstable : (prefixWord ++ tailWord_539644).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_539644).length < 2 ^ (prefixWord ++ tailWord_539644).sum := by decide
  have hdescent : baseEnd_539644 < baseStart_539644 := by decide
  rcases family_descends (prefixWord ++ tailWord_539644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_539751 : List Nat := [1, 1, 5, 1, 1, 4, 1, 3, 4]
def baseStart_539751 : Nat := 118140960795 + 539751 * 2 ^ 59
def prefixEnd_539751 : Nat := 4983230072969 + 3 ^ 40 * 539751 * 2
def baseEnd_539751 : Nat := 123178531886676869080105

theorem tailTrace_539751 : CollatzResearch.WordTrace tailWord_539751 prefixEnd_539751 123178531886676869080105 := by
  unfold tailWord_539751
  simp only [CollatzResearch.WordTrace]
  refine ⟨19686336267581783976915107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13124224178387855984610071 19686336267581783976915107)
  ·
    refine ⟨29529504401372675965372661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19686336267581783976915107 29529504401372675965372661)
    ·
      refine ⟨2768391037628688371753687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 29529504401372675965372661 2768391037628688371753687)
      ·
        refine ⟨4152586556443032557630531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2768391037628688371753687 4152586556443032557630531)
        ·
          refine ⟨6228879834664548836445797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4152586556443032557630531 6228879834664548836445797)
          ·
            refine ⟨1167914968999602906833587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6228879834664548836445797 1167914968999602906833587)
            ·
              refine ⟨1751872453499404360250381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1167914968999602906833587 1751872453499404360250381)
              ·
                refine ⟨656952170062276635093893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1751872453499404360250381 656952170062276635093893)
                ·
                  refine ⟨123178531886676869080105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 656952170062276635093893 123178531886676869080105)
                  ·
                    rfl

theorem cell21_539751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 3, 4].length) (baseStart_539751 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_539751 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_539751 prefixEnd_539751 := by exact prefixLift 539751
  have htrace : WordTrace (prefixWord ++ tailWord_539751) baseStart_539751 baseEnd_539751 := by
    simpa [prefixWord, tailWord_539751, baseEnd_539751] using wordTrace_append hprefix tailTrace_539751
  have hstable : (prefixWord ++ tailWord_539751).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_539751).length < 2 ^ (prefixWord ++ tailWord_539751).sum := by decide
  have hdescent : baseEnd_539751 < baseStart_539751 := by decide
  rcases family_descends (prefixWord ++ tailWord_539751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_539886 : List Nat := [4, 1, 2, 1, 1, 1, 3, 2, 6]
def baseStart_539886 : Nat := 118140960795 + 539886 * 2 ^ 59
def prefixEnd_539886 : Nat := 4983230072969 + 3 ^ 40 * 539886 * 2
def baseEnd_539886 : Nat := 123209340725946634329829

theorem tailTrace_539886 : CollatzResearch.WordTrace tailWord_539886 prefixEnd_539886 123209340725946634329829 := by
  unfold tailWord_539886
  simp only [CollatzResearch.WordTrace]
  refine ⟨2461407515261587754134939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13127506748061801355386341 2461407515261587754134939)
  ·
    refine ⟨3692111272892381631202409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2461407515261587754134939 3692111272892381631202409)
    ·
      refine ⟨2769083454669286223401807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3692111272892381631202409 2769083454669286223401807)
      ·
        refine ⟨4153625182003929335102711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2769083454669286223401807 4153625182003929335102711)
        ·
          refine ⟨6230437773005894002654067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4153625182003929335102711 6230437773005894002654067)
          ·
            refine ⟨9345656659508841003981101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6230437773005894002654067 9345656659508841003981101)
            ·
              refine ⟨3504621247315815376492913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9345656659508841003981101 3504621247315815376492913)
              ·
                refine ⟨2628465935486861532369685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3504621247315815376492913 2628465935486861532369685)
                ·
                  refine ⟨123209340725946634329829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2628465935486861532369685 123209340725946634329829)
                  ·
                    rfl

theorem cell21_539886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 2, 6].length) (baseStart_539886 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_539886 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_539886 prefixEnd_539886 := by exact prefixLift 539886
  have htrace : WordTrace (prefixWord ++ tailWord_539886) baseStart_539886 baseEnd_539886 := by
    simpa [prefixWord, tailWord_539886, baseEnd_539886] using wordTrace_append hprefix tailTrace_539886
  have hstable : (prefixWord ++ tailWord_539886).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_539886).length < 2 ^ (prefixWord ++ tailWord_539886).sum := by decide
  have hdescent : baseEnd_539886 < baseStart_539886 := by decide
  rcases family_descends (prefixWord ++ tailWord_539886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_539892 : List Nat := [2, 6, 1, 2, 1, 2, 7]
def baseStart_539892 : Nat := 118140960795 + 539892 * 2 ^ 59
def prefixEnd_539892 : Nat := 4983230072969 + 3 ^ 40 * 539892 * 2
def baseEnd_539892 : Nat := 13690078889743550803313

theorem tailTrace_539892 : CollatzResearch.WordTrace tailWord_539892 prefixEnd_539892 13690078889743550803313 := by
  unfold tailWord_539892
  simp only [CollatzResearch.WordTrace]
  refine ⟨9845739480035482528898965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13127652640047310038531953 9845739480035482528898965)
  ·
    refine ⟨461519038126663243542139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 9845739480035482528898965 461519038126663243542139)
    ·
      refine ⟨692278557189994865313209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 461519038126663243542139 692278557189994865313209)
      ·
        refine ⟨519208917892496148984907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 692278557189994865313209 519208917892496148984907)
        ·
          refine ⟨778813376838744223477361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 519208917892496148984907 778813376838744223477361)
          ·
            refine ⟨584110032629058167608021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 778813376838744223477361 584110032629058167608021)
            ·
              refine ⟨13690078889743550803313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 584110032629058167608021 13690078889743550803313)
              ·
                rfl

theorem cell21_539892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 7].length) (baseStart_539892 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_539892 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_539892 prefixEnd_539892 := by exact prefixLift 539892
  have htrace : WordTrace (prefixWord ++ tailWord_539892) baseStart_539892 baseEnd_539892 := by
    simpa [prefixWord, tailWord_539892, baseEnd_539892] using wordTrace_append hprefix tailTrace_539892
  have hstable : (prefixWord ++ tailWord_539892).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_539892).length < 2 ^ (prefixWord ++ tailWord_539892).sum := by decide
  have hdescent : baseEnd_539892 < baseStart_539892 := by decide
  rcases family_descends (prefixWord ++ tailWord_539892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_539906 : List Nat := [3, 4, 1, 1, 3, 2, 1, 1, 5]
def baseStart_539906 : Nat := 118140960795 + 539906 * 2 ^ 59
def prefixEnd_539906 : Nat := 4983230072969 + 3 ^ 40 * 539906 * 2
def baseEnd_539906 : Nat := 123213904998431043996455

theorem tailTrace_539906 : CollatzResearch.WordTrace tailWord_539906 prefixEnd_539906 123213904998431043996455 := by
  unfold tailWord_539906
  simp only [CollatzResearch.WordTrace]
  refine ⟨4922997395505061362201893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13127993054680163632538381 4922997395505061362201893)
  ·
    refine ⟨923062011657199005412855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4922997395505061362201893 923062011657199005412855)
    ·
      refine ⟨1384593017485798508119283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 923062011657199005412855 1384593017485798508119283)
      ·
        refine ⟨2076889526228697762178925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1384593017485798508119283 2076889526228697762178925)
        ·
          refine ⟨778833572335761660817097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2076889526228697762178925 778833572335761660817097)
          ·
            refine ⟨584125179251821245612823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 778833572335761660817097 584125179251821245612823)
            ·
              refine ⟨876187768877731868419235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 584125179251821245612823 876187768877731868419235)
              ·
                refine ⟨1314281653316597802628853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 876187768877731868419235 1314281653316597802628853)
                ·
                  refine ⟨123213904998431043996455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1314281653316597802628853 123213904998431043996455)
                  ·
                    rfl

theorem cell21_539906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 1, 1, 5].length) (baseStart_539906 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_539906 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_539906 prefixEnd_539906 := by exact prefixLift 539906
  have htrace : WordTrace (prefixWord ++ tailWord_539906) baseStart_539906 baseEnd_539906 := by
    simpa [prefixWord, tailWord_539906, baseEnd_539906] using wordTrace_append hprefix tailTrace_539906
  have hstable : (prefixWord ++ tailWord_539906).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_539906).length < 2 ^ (prefixWord ++ tailWord_539906).sum := by decide
  have hdescent : baseEnd_539906 < baseStart_539906 := by decide
  rcases family_descends (prefixWord ++ tailWord_539906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_539948 : List Nat := [2, 2, 1, 1, 1, 3, 1, 7, 3]
def baseStart_539948 : Nat := 118140960795 + 539948 * 2 ^ 59
def prefixEnd_539948 : Nat := 4983230072969 + 3 ^ 40 * 539948 * 2
def baseEnd_539948 : Nat := 123223489970648304296369

theorem tailTrace_539948 : CollatzResearch.WordTrace tailWord_539948 prefixEnd_539948 123223489970648304296369 := by
  unfold tailWord_539948
  simp only [CollatzResearch.WordTrace]
  refine ⟨9846760723934043310918249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13129014298578724414557665 9846760723934043310918249)
  ·
    refine ⟨7385070542950532483188687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9846760723934043310918249 7385070542950532483188687)
    ·
      refine ⟨11077605814425798724783031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7385070542950532483188687 11077605814425798724783031)
      ·
        refine ⟨16616408721638698087174547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11077605814425798724783031 16616408721638698087174547)
        ·
          refine ⟨24924613082458047130761821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16616408721638698087174547 24924613082458047130761821)
          ·
            refine ⟨9346729905921767674035683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24924613082458047130761821 9346729905921767674035683)
            ·
              refine ⟨14020094858882651511053525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9346729905921767674035683 14020094858882651511053525)
              ·
                refine ⟨328595973255062144790317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 14020094858882651511053525 328595973255062144790317)
                ·
                  refine ⟨123223489970648304296369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 328595973255062144790317 123223489970648304296369)
                  ·
                    rfl

theorem cell21_539948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 7, 3].length) (baseStart_539948 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_539948 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_539948 prefixEnd_539948 := by exact prefixLift 539948
  have htrace : WordTrace (prefixWord ++ tailWord_539948) baseStart_539948 baseEnd_539948 := by
    simpa [prefixWord, tailWord_539948, baseEnd_539948] using wordTrace_append hprefix tailTrace_539948
  have hstable : (prefixWord ++ tailWord_539948).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_539948).length < 2 ^ (prefixWord ++ tailWord_539948).sum := by decide
  have hdescent : baseEnd_539948 < baseStart_539948 := by decide
  rcases family_descends (prefixWord ++ tailWord_539948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_540030 : List Nat := [4, 2, 3, 2, 1, 1, 3, 1, 4]
def baseStart_540030 : Nat := 118140960795 + 540030 * 2 ^ 59
def prefixEnd_540030 : Nat := 4983230072969 + 3 ^ 40 * 540030 * 2
def baseEnd_540030 : Nat := 123242203487834383929535

theorem tailTrace_540030 : CollatzResearch.WordTrace tailWord_540030 prefixEnd_540030 123242203487834383929535 := by
  unfold tailWord_540030
  simp only [CollatzResearch.WordTrace]
  refine ⟨2462064029196376828290193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13131008155714009750881029 2462064029196376828290193)
  ·
    refine ⟨1846548021897282621217645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2462064029196376828290193 1846548021897282621217645)
    ·
      refine ⟨692455508211480982956617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1846548021897282621217645 692455508211480982956617)
      ·
        refine ⟨519341631158610737217463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 692455508211480982956617 519341631158610737217463)
        ·
          refine ⟨779012446737916105826195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 519341631158610737217463 779012446737916105826195)
          ·
            refine ⟨1168518670106874158739293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 779012446737916105826195 1168518670106874158739293)
            ·
              refine ⟨438194501290077809527235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1168518670106874158739293 438194501290077809527235)
              ·
                refine ⟨657291751935116714290853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 438194501290077809527235 657291751935116714290853)
                ·
                  refine ⟨123242203487834383929535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 657291751935116714290853 123242203487834383929535)
                  ·
                    rfl

theorem cell21_540030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 3, 1, 4].length) (baseStart_540030 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_540030 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_540030 prefixEnd_540030 := by exact prefixLift 540030
  have htrace : WordTrace (prefixWord ++ tailWord_540030) baseStart_540030 baseEnd_540030 := by
    simpa [prefixWord, tailWord_540030, baseEnd_540030] using wordTrace_append hprefix tailTrace_540030
  have hstable : (prefixWord ++ tailWord_540030).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_540030).length < 2 ^ (prefixWord ++ tailWord_540030).sum := by decide
  have hdescent : baseEnd_540030 < baseStart_540030 := by decide
  rcases family_descends (prefixWord ++ tailWord_540030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_540089 : List Nat := [1, 2, 1, 4, 5, 1, 2, 1, 4]
def baseStart_540089 : Nat := 118140960795 + 540089 * 2 ^ 59
def prefixEnd_540089 : Nat := 4983230072969 + 3 ^ 40 * 540089 * 2
def baseEnd_540089 : Nat := 123255668091663392446081

theorem tailTrace_540089 : CollatzResearch.WordTrace tailWord_540089 prefixEnd_540089 123255668091663392446081 := by
  unfold tailWord_540089
  simp only [CollatzResearch.WordTrace]
  refine ⟨19698664140357267702719321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13132442760238178468479547 19698664140357267702719321)
  ·
    refine ⟨14773998105267950777039491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19698664140357267702719321 14773998105267950777039491)
    ·
      refine ⟨22160997157901926165559237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14773998105267950777039491 22160997157901926165559237)
      ·
        refine ⟨4155186967106611156042357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22160997157901926165559237 4155186967106611156042357)
        ·
          refine ⟨389548778166244795878971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4155186967106611156042357 389548778166244795878971)
          ·
            refine ⟨584323167249367193818457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 389548778166244795878971 584323167249367193818457)
            ·
              refine ⟨438242375437025395363843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 584323167249367193818457 438242375437025395363843)
              ·
                refine ⟨657363563155538093045765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 438242375437025395363843 657363563155538093045765)
                ·
                  refine ⟨123255668091663392446081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 657363563155538093045765 123255668091663392446081)
                  ·
                    rfl

theorem cell21_540089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 2, 1, 4].length) (baseStart_540089 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_540089 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_540089 prefixEnd_540089 := by exact prefixLift 540089
  have htrace : WordTrace (prefixWord ++ tailWord_540089) baseStart_540089 baseEnd_540089 := by
    simpa [prefixWord, tailWord_540089, baseEnd_540089] using wordTrace_append hprefix tailTrace_540089
  have hstable : (prefixWord ++ tailWord_540089).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_540089).length < 2 ^ (prefixWord ++ tailWord_540089).sum := by decide
  have hdescent : baseEnd_540089 < baseStart_540089 := by decide
  rcases family_descends (prefixWord ++ tailWord_540089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_540131 : List Nat := [1, 1, 1, 6, 2, 2, 2, 2, 4]
def baseStart_540131 : Nat := 118140960795 + 540131 * 2 ^ 59
def prefixEnd_540131 : Nat := 4983230072969 + 3 ^ 40 * 540131 * 2
def baseEnd_540131 : Nat := 123265253063880652745995

theorem tailTrace_540131 : CollatzResearch.WordTrace tailWord_540131 prefixEnd_540131 123265253063880652745995 := by
  unfold tailWord_540131
  simp only [CollatzResearch.WordTrace]
  refine ⟨19700196006205108875748247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13133464004136739250498831 19700196006205108875748247)
  ·
    refine ⟨29550294009307663313622371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19700196006205108875748247 29550294009307663313622371)
    ·
      refine ⟨44325441013961494970433557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29550294009307663313622371 44325441013961494970433557)
      ·
        refine ⟨2077755047529445076739073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 44325441013961494970433557 2077755047529445076739073)
        ·
          refine ⟨1558316285647083807554305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2077755047529445076739073 1558316285647083807554305)
          ·
            refine ⟨1168737214235312855665729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1558316285647083807554305 1168737214235312855665729)
            ·
              refine ⟨876552910676484641749297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1168737214235312855665729 876552910676484641749297)
              ·
                refine ⟨657414683007363481311973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 876552910676484641749297 657414683007363481311973)
                ·
                  refine ⟨123265253063880652745995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 657414683007363481311973 123265253063880652745995)
                  ·
                    rfl

theorem cell21_540131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 2, 2, 4].length) (baseStart_540131 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_540131 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_540131 prefixEnd_540131 := by exact prefixLift 540131
  have htrace : WordTrace (prefixWord ++ tailWord_540131) baseStart_540131 baseEnd_540131 := by
    simpa [prefixWord, tailWord_540131, baseEnd_540131] using wordTrace_append hprefix tailTrace_540131
  have hstable : (prefixWord ++ tailWord_540131).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_540131).length < 2 ^ (prefixWord ++ tailWord_540131).sum := by decide
  have hdescent : baseEnd_540131 < baseStart_540131 := by decide
  rcases family_descends (prefixWord ++ tailWord_540131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_540145 : List Nat := [1, 2, 2, 2, 3, 4, 1, 6]
def baseStart_540145 : Nat := 118140960795 + 540145 * 2 ^ 59
def prefixEnd_540145 : Nat := 4983230072969 + 3 ^ 40 * 540145 * 2
def baseEnd_540145 : Nat := 41089482684873246504211

theorem tailTrace_540145 : CollatzResearch.WordTrace tailWord_540145 prefixEnd_540145 41089482684873246504211 := by
  unfold tailWord_540145
  simp only [CollatzResearch.WordTrace]
  refine ⟨19700706628154389266757889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13133804418769592844505259 19700706628154389266757889)
  ·
    refine ⟨14775529971115791950068417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19700706628154389266757889 14775529971115791950068417)
    ·
      refine ⟨11081647478336843962551313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14775529971115791950068417 11081647478336843962551313)
      ·
        refine ⟨8311235608752632971913485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11081647478336843962551313 8311235608752632971913485)
        ·
          refine ⟨3116713353282237364467557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8311235608752632971913485 3116713353282237364467557)
          ·
            refine ⟨584383753740419505837667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3116713353282237364467557 584383753740419505837667)
            ·
              refine ⟨876575630610629258756501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 584383753740419505837667 876575630610629258756501)
              ·
                refine ⟨41089482684873246504211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 876575630610629258756501 41089482684873246504211)
                ·
                  rfl

theorem cell21_540145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 1, 6].length) (baseStart_540145 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_540145 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_540145 prefixEnd_540145 := by exact prefixLift 540145
  have htrace : WordTrace (prefixWord ++ tailWord_540145) baseStart_540145 baseEnd_540145 := by
    simpa [prefixWord, tailWord_540145, baseEnd_540145] using wordTrace_append hprefix tailTrace_540145
  have hstable : (prefixWord ++ tailWord_540145).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_540145).length < 2 ^ (prefixWord ++ tailWord_540145).sum := by decide
  have hdescent : baseEnd_540145 < baseStart_540145 := by decide
  rcases family_descends (prefixWord ++ tailWord_540145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_540221 : List Nat := [1, 4, 1, 3, 3, 1, 1, 7]
def baseStart_540221 : Nat := 118140960795 + 540221 * 2 ^ 59
def prefixEnd_540221 : Nat := 4983230072969 + 3 ^ 40 * 540221 * 2
def baseEnd_540221 : Nat := 41095264096686832081937

theorem tailTrace_540221 : CollatzResearch.WordTrace tailWord_540221 prefixEnd_540221 41095264096686832081937 := by
  unfold tailWord_540221
  simp only [CollatzResearch.WordTrace]
  refine ⟨19703478575879054246524517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13135652383919369497683011 19703478575879054246524517)
  ·
    refine ⟨3694402232977322671223347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19703478575879054246524517 3694402232977322671223347)
    ·
      refine ⟨5541603349465984006835021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3694402232977322671223347 5541603349465984006835021)
      ·
        refine ⟨2078101256049744002563133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5541603349465984006835021 2078101256049744002563133)
        ·
          refine ⟨779287971018654000961175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2078101256049744002563133 779287971018654000961175)
          ·
            refine ⟨1168931956527981001441763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 779287971018654000961175 1168931956527981001441763)
            ·
              refine ⟨1753397934791971502162645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1168931956527981001441763 1753397934791971502162645)
              ·
                refine ⟨41095264096686832081937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1753397934791971502162645 41095264096686832081937)
                ·
                  rfl

theorem cell21_540221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 7].length) (baseStart_540221 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_540221 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_540221 prefixEnd_540221 := by exact prefixLift 540221
  have htrace : WordTrace (prefixWord ++ tailWord_540221) baseStart_540221 baseEnd_540221 := by
    simpa [prefixWord, tailWord_540221, baseEnd_540221] using wordTrace_append hprefix tailTrace_540221
  have hstable : (prefixWord ++ tailWord_540221).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_540221).length < 2 ^ (prefixWord ++ tailWord_540221).sum := by decide
  have hdescent : baseEnd_540221 < baseStart_540221 := by decide
  rcases family_descends (prefixWord ++ tailWord_540221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_540252 : List Nat := [2, 2, 4, 1, 2, 1, 3, 1, 5]
def baseStart_540252 : Nat := 118140960795 + 540252 * 2 ^ 59
def prefixEnd_540252 : Nat := 4983230072969 + 3 ^ 40 * 540252 * 2
def baseEnd_540252 : Nat := 123292866912411331229081

theorem tailTrace_540252 : CollatzResearch.WordTrace tailWord_540252 prefixEnd_540252 123292866912411331229081 := by
  unfold tailWord_540252
  simp only [CollatzResearch.WordTrace]
  refine ⟨9852304619383373270451505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13136406159177831027268673 9852304619383373270451505)
  ·
    refine ⟨7389228464537529952838629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9852304619383373270451505 7389228464537529952838629)
    ·
      refine ⟨1385480337100786866157243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7389228464537529952838629 1385480337100786866157243)
      ·
        refine ⟨2078220505651180299235865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1385480337100786866157243 2078220505651180299235865)
        ·
          refine ⟨1558665379238385224426899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2078220505651180299235865 1558665379238385224426899)
          ·
            refine ⟨2337998068857577836640349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1558665379238385224426899 2337998068857577836640349)
            ·
              refine ⟨876749275821591688740131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2337998068857577836640349 876749275821591688740131)
              ·
                refine ⟨1315123913732387533110197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 876749275821591688740131 1315123913732387533110197)
                ·
                  refine ⟨123292866912411331229081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1315123913732387533110197 123292866912411331229081)
                  ·
                    rfl

theorem cell21_540252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 3, 1, 5].length) (baseStart_540252 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_540252 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_540252 prefixEnd_540252 := by exact prefixLift 540252
  have htrace : WordTrace (prefixWord ++ tailWord_540252) baseStart_540252 baseEnd_540252 := by
    simpa [prefixWord, tailWord_540252, baseEnd_540252] using wordTrace_append hprefix tailTrace_540252
  have hstable : (prefixWord ++ tailWord_540252).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_540252).length < 2 ^ (prefixWord ++ tailWord_540252).sum := by decide
  have hdescent : baseEnd_540252 < baseStart_540252 := by decide
  rcases family_descends (prefixWord ++ tailWord_540252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_540356 : List Nat := [2, 3, 3, 1, 1, 1, 10]
def baseStart_540356 : Nat := 118140960795 + 540356 * 2 ^ 59
def prefixEnd_540356 : Nat := 4983230072969 + 3 ^ 40 * 540356 * 2
def baseEnd_540356 : Nat := 13701844569925584610615

theorem tailTrace_540356 : CollatzResearch.WordTrace tailWord_540356 prefixEnd_540356 13701844569925584610615 := by
  unfold tailWord_540356
  simp only [CollatzResearch.WordTrace]
  refine ⟨9854201215194986151344461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13138934953593314868459281 9854201215194986151344461)
  ·
    refine ⟨3695325455698119806754173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9854201215194986151344461 3695325455698119806754173)
    ·
      refine ⟨1385747045886794927532815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3695325455698119806754173 1385747045886794927532815)
      ·
        refine ⟨2078620568830192391299223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1385747045886794927532815 2078620568830192391299223)
        ·
          refine ⟨3117930853245288586948835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2078620568830192391299223 3117930853245288586948835)
          ·
            refine ⟨4676896279867932880423253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3117930853245288586948835 4676896279867932880423253)
            ·
              refine ⟨13701844569925584610615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 4676896279867932880423253 13701844569925584610615)
              ·
                rfl

theorem cell21_540356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 10].length) (baseStart_540356 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_540356 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_540356 prefixEnd_540356 := by exact prefixLift 540356
  have htrace : WordTrace (prefixWord ++ tailWord_540356) baseStart_540356 baseEnd_540356 := by
    simpa [prefixWord, tailWord_540356, baseEnd_540356] using wordTrace_append hprefix tailTrace_540356
  have hstable : (prefixWord ++ tailWord_540356).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_540356).length < 2 ^ (prefixWord ++ tailWord_540356).sum := by decide
  have hdescent : baseEnd_540356 < baseStart_540356 := by decide
  rcases family_descends (prefixWord ++ tailWord_540356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_540401 : List Nat := [1, 2, 2, 2, 2, 3, 1, 2, 6]
def baseStart_540401 : Nat := 118140960795 + 540401 * 2 ^ 59
def prefixEnd_540401 : Nat := 4983230072969 + 3 ^ 40 * 540401 * 2
def baseEnd_540401 : Nat := 123326870742420183245443

theorem tailTrace_540401 : CollatzResearch.WordTrace tailWord_540401 prefixEnd_540401 123326870742420183245443 := by
  unfold tailWord_540401
  simp only [CollatzResearch.WordTrace]
  refine ⟨19710043715226944988077057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13140029143484629992051371 19710043715226944988077057)
  ·
    refine ⟨14782532786420208741057793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19710043715226944988077057 14782532786420208741057793)
    ·
      refine ⟨11086899589815156555793345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14782532786420208741057793 11086899589815156555793345)
      ·
        refine ⟨8315174692361367416845009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11086899589815156555793345 8315174692361367416845009)
        ·
          refine ⟨6236381019271025562633757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8315174692361367416845009 6236381019271025562633757)
          ·
            refine ⟨2338642882226634585987659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6236381019271025562633757 2338642882226634585987659)
            ·
              refine ⟨3507964323339951878981489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2338642882226634585987659 3507964323339951878981489)
              ·
                refine ⟨2630973242504963909236117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3507964323339951878981489 2630973242504963909236117)
                ·
                  refine ⟨123326870742420183245443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2630973242504963909236117 123326870742420183245443)
                  ·
                    rfl

theorem cell21_540401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 2, 6].length) (baseStart_540401 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_540401 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_540401 prefixEnd_540401 := by exact prefixLift 540401
  have htrace : WordTrace (prefixWord ++ tailWord_540401) baseStart_540401 baseEnd_540401 := by
    simpa [prefixWord, tailWord_540401, baseEnd_540401] using wordTrace_append hprefix tailTrace_540401
  have hstable : (prefixWord ++ tailWord_540401).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_540401).length < 2 ^ (prefixWord ++ tailWord_540401).sum := by decide
  have hdescent : baseEnd_540401 < baseStart_540401 := by decide
  rcases family_descends (prefixWord ++ tailWord_540401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_540415 : List Nat := [1, 1, 2, 2, 1, 3, 11]
def baseStart_540415 : Nat := 118140960795 + 540415 * 2 ^ 59
def prefixEnd_540415 : Nat := 4983230072969 + 3 ^ 40 * 540415 * 2
def baseEnd_540415 : Nat := 13703340637017696668009

theorem tailTrace_540415 : CollatzResearch.WordTrace tailWord_540415 prefixEnd_540415 13703340637017696668009 := by
  unfold tailWord_540415
  simp only [CollatzResearch.WordTrace]
  refine ⟨19710554337176225379086699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13140369558117483586057799 19710554337176225379086699)
  ·
    refine ⟨29565831505764338068630049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19710554337176225379086699 29565831505764338068630049)
    ·
      refine ⟨22174373629323253551472537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29565831505764338068630049 22174373629323253551472537)
      ·
        refine ⟨16630780221992440163604403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22174373629323253551472537 16630780221992440163604403)
        ·
          refine ⟨24946170332988660245406605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16630780221992440163604403 24946170332988660245406605)
          ·
            refine ⟨9354813874870747592027477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24946170332988660245406605 9354813874870747592027477)
            ·
              refine ⟨13703340637017696668009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 9354813874870747592027477 13703340637017696668009)
              ·
                rfl

theorem cell21_540415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 11].length) (baseStart_540415 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_540415 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_540415 prefixEnd_540415 := by exact prefixLift 540415
  have htrace : WordTrace (prefixWord ++ tailWord_540415) baseStart_540415 baseEnd_540415 := by
    simpa [prefixWord, tailWord_540415, baseEnd_540415] using wordTrace_append hprefix tailTrace_540415
  have hstable : (prefixWord ++ tailWord_540415).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_540415).length < 2 ^ (prefixWord ++ tailWord_540415).sum := by decide
  have hdescent : baseEnd_540415 < baseStart_540415 := by decide
  rcases family_descends (prefixWord ++ tailWord_540415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_540418 : List Nat := [3, 4, 1, 1, 1, 1, 1, 3, 6]
def baseStart_540418 : Nat := 118140960795 + 540418 * 2 ^ 59
def prefixEnd_540418 : Nat := 4983230072969 + 3 ^ 40 * 540418 * 2
def baseEnd_540418 : Nat := 123330750374031931462075

theorem tailTrace_540418 : CollatzResearch.WordTrace tailWord_540418 prefixEnd_540418 123330750374031931462075 := by
  unfold tailWord_540418
  simp only [CollatzResearch.WordTrace]
  refine ⟨4927665939041339222861477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13140442504110237927630605 4927665939041339222861477)
  ·
    refine ⟨923937363570251104286527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4927665939041339222861477 923937363570251104286527)
    ·
      refine ⟨1385906045355376656429791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 923937363570251104286527 1385906045355376656429791)
      ·
        refine ⟨2078859068033064984644687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1385906045355376656429791 2078859068033064984644687)
        ·
          refine ⟨3118288602049597476967031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2078859068033064984644687 3118288602049597476967031)
          ·
            refine ⟨4677432903074396215450547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3118288602049597476967031 4677432903074396215450547)
            ·
              refine ⟨7016149354611594323175821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4677432903074396215450547 7016149354611594323175821)
              ·
                refine ⟨2631056007979347871190933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7016149354611594323175821 2631056007979347871190933)
                ·
                  refine ⟨123330750374031931462075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2631056007979347871190933 123330750374031931462075)
                  ·
                    rfl

theorem cell21_540418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 3, 6].length) (baseStart_540418 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_540418 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_540418 prefixEnd_540418 := by exact prefixLift 540418
  have htrace : WordTrace (prefixWord ++ tailWord_540418) baseStart_540418 baseEnd_540418 := by
    simpa [prefixWord, tailWord_540418, baseEnd_540418] using wordTrace_append hprefix tailTrace_540418
  have hstable : (prefixWord ++ tailWord_540418).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_540418).length < 2 ^ (prefixWord ++ tailWord_540418).sum := by decide
  have hdescent : baseEnd_540418 < baseStart_540418 := by decide
  rcases family_descends (prefixWord ++ tailWord_540418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_540573 : List Nat := [1, 4, 2, 1, 2, 4, 1, 3, 3]
def baseStart_540573 : Nat := 118140960795 + 540573 * 2 ^ 59
def prefixEnd_540573 : Nat := 4983230072969 + 3 ^ 40 * 540573 * 2
def baseEnd_540573 : Nat := 123366123485786106378425

theorem tailTrace_540573 : CollatzResearch.WordTrace tailWord_540573 prefixEnd_540573 123366123485786106378425 := by
  unfold tailWord_540573
  simp only [CollatzResearch.WordTrace]
  refine ⟨19716317070603818363338373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13144211380402545575558915 19716317070603818363338373)
  ·
    refine ⟨3696809450738215943125945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19716317070603818363338373 3696809450738215943125945)
    ·
      refine ⟨2772607088053661957344459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3696809450738215943125945 2772607088053661957344459)
      ·
        refine ⟨4158910632080492936016689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2772607088053661957344459 4158910632080492936016689)
        ·
          refine ⟨3119182974060369702012517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4158910632080492936016689 3119182974060369702012517)
          ·
            refine ⟨584846807636319319127347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3119182974060369702012517 584846807636319319127347)
            ·
              refine ⟨877270211454478978691021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 584846807636319319127347 877270211454478978691021)
              ·
                refine ⟨328976329295429617009133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 877270211454478978691021 328976329295429617009133)
                ·
                  refine ⟨123366123485786106378425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 328976329295429617009133 123366123485786106378425)
                  ·
                    rfl

theorem cell21_540573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 1, 3, 3].length) (baseStart_540573 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_540573 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_540573 prefixEnd_540573 := by exact prefixLift 540573
  have htrace : WordTrace (prefixWord ++ tailWord_540573) baseStart_540573 baseEnd_540573 := by
    simpa [prefixWord, tailWord_540573, baseEnd_540573] using wordTrace_append hprefix tailTrace_540573
  have hstable : (prefixWord ++ tailWord_540573).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_540573).length < 2 ^ (prefixWord ++ tailWord_540573).sum := by decide
  have hdescent : baseEnd_540573 < baseStart_540573 := by decide
  rcases family_descends (prefixWord ++ tailWord_540573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_540643 : List Nat := [1, 1, 1, 6, 1, 11]
def baseStart_540643 : Nat := 118140960795 + 540643 * 2 ^ 59
def prefixEnd_540643 : Nat := 4983230072969 + 3 ^ 40 * 540643 * 2
def baseEnd_540643 : Nat := 4569707349610427415245

theorem tailTrace_540643 : CollatzResearch.WordTrace tailWord_540643 prefixEnd_540643 4569707349610427415245 := by
  unfold tailWord_540643
  simp only [CollatzResearch.WordTrace]
  refine ⟨19718870180350220318386583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13145913453566813545591055 19718870180350220318386583)
  ·
    refine ⟨29578305270525330477579875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19718870180350220318386583 29578305270525330477579875)
    ·
      refine ⟨44367457905787995716369813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29578305270525330477579875 44367457905787995716369813)
      ·
        refine ⟨2079724589333812299204835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 44367457905787995716369813 2079724589333812299204835)
        ·
          refine ⟨3119586884000718448807253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2079724589333812299204835 3119586884000718448807253)
          ·
            refine ⟨4569707349610427415245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 3119586884000718448807253 4569707349610427415245)
            ·
              rfl

theorem cell21_540643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 11].length) (baseStart_540643 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_540643 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_540643 prefixEnd_540643 := by exact prefixLift 540643
  have htrace : WordTrace (prefixWord ++ tailWord_540643) baseStart_540643 baseEnd_540643 := by
    simpa [prefixWord, tailWord_540643, baseEnd_540643] using wordTrace_append hprefix tailTrace_540643
  have hstable : (prefixWord ++ tailWord_540643).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_540643).length < 2 ^ (prefixWord ++ tailWord_540643).sum := by decide
  have hdescent : baseEnd_540643 < baseStart_540643 := by decide
  rcases family_descends (prefixWord ++ tailWord_540643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_540688 : List Nat := [2, 1, 1, 1, 1, 1, 1, 5, 8]
def baseStart_540688 : Nat := 118140960795 + 540688 * 2 ^ 59
def prefixEnd_540688 : Nat := 4983230072969 + 3 ^ 40 * 540688 * 2
def baseEnd_540688 : Nat := 123392368052571461961523

theorem tailTrace_540688 : CollatzResearch.WordTrace tailWord_540688 prefixEnd_540688 123392368052571461961523 := by
  unfold tailWord_540688
  simp only [CollatzResearch.WordTrace]
  refine ⟨9860255732593596501887359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13147007643458128669183145 9860255732593596501887359)
  ·
    refine ⟨14790383598890394752831039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9860255732593596501887359 14790383598890394752831039)
    ·
      refine ⟨22185575398335592129246559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14790383598890394752831039 22185575398335592129246559)
      ·
        refine ⟨33278363097503388193869839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22185575398335592129246559 33278363097503388193869839)
        ·
          refine ⟨49917544646255082290804759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33278363097503388193869839 49917544646255082290804759)
          ·
            refine ⟨74876316969382623436207139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49917544646255082290804759 74876316969382623436207139)
            ·
              refine ⟨112314475454073935154310709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74876316969382623436207139 112314475454073935154310709)
              ·
                refine ⟨10529482073819431420716629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 112314475454073935154310709 10529482073819431420716629)
                ·
                  refine ⟨123392368052571461961523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10529482073819431420716629 123392368052571461961523)
                  ·
                    rfl

theorem cell21_540688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 5, 8].length) (baseStart_540688 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_540688 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_540688 prefixEnd_540688 := by exact prefixLift 540688
  have htrace : WordTrace (prefixWord ++ tailWord_540688) baseStart_540688 baseEnd_540688 := by
    simpa [prefixWord, tailWord_540688, baseEnd_540688] using wordTrace_append hprefix tailTrace_540688
  have hstable : (prefixWord ++ tailWord_540688).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_540688).length < 2 ^ (prefixWord ++ tailWord_540688).sum := by decide
  have hdescent : baseEnd_540688 < baseStart_540688 := by decide
  rcases family_descends (prefixWord ++ tailWord_540688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_540691 : List Nat := [1, 1, 1, 2, 1, 4, 3, 5, 3]
def baseStart_540691 : Nat := 118140960795 + 540691 * 2 ^ 59
def prefixEnd_540691 : Nat := 4983230072969 + 3 ^ 40 * 540691 * 2
def baseEnd_540691 : Nat := 123393052693444123411517

theorem tailTrace_540691 : CollatzResearch.WordTrace tailWord_540691 prefixEnd_540691 123393052693444123411517 := by
  unfold tailWord_540691
  simp only [CollatzResearch.WordTrace]
  refine ⟨19720620884176324516133927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13147080589450883010755951 19720620884176324516133927)
  ·
    refine ⟨29580931326264486774200891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19720620884176324516133927 29580931326264486774200891)
    ·
      refine ⟨44371396989396730161301337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29580931326264486774200891 44371396989396730161301337)
      ·
        refine ⟨33278547742047547620976003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44371396989396730161301337 33278547742047547620976003)
        ·
          refine ⟨49917821613071321431464005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33278547742047547620976003 49917821613071321431464005)
          ·
            refine ⟨9359591552450872768399501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49917821613071321431464005 9359591552450872768399501)
            ·
              refine ⟨3509846832169077288149813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9359591552450872768399501 3509846832169077288149813)
              ·
                refine ⟨329048140515850995764045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3509846832169077288149813 329048140515850995764045)
                ·
                  refine ⟨123393052693444123411517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 329048140515850995764045 123393052693444123411517)
                  ·
                    rfl

theorem cell21_540691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 5, 3].length) (baseStart_540691 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_540691 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_540691 prefixEnd_540691 := by exact prefixLift 540691
  have htrace : WordTrace (prefixWord ++ tailWord_540691) baseStart_540691 baseEnd_540691 := by
    simpa [prefixWord, tailWord_540691, baseEnd_540691] using wordTrace_append hprefix tailTrace_540691
  have hstable : (prefixWord ++ tailWord_540691).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_540691).length < 2 ^ (prefixWord ++ tailWord_540691).sum := by decide
  have hdescent : baseEnd_540691 < baseStart_540691 := by decide
  rcases family_descends (prefixWord ++ tailWord_540691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_540708 : List Nat := [2, 3, 1, 4, 2, 1, 2, 1, 5]
def baseStart_540708 : Nat := 118140960795 + 540708 * 2 ^ 59
def prefixEnd_540708 : Nat := 4983230072969 + 3 ^ 40 * 540708 * 2
def baseEnd_540708 : Nat := 123396932325055871628149

theorem tailTrace_540708 : CollatzResearch.WordTrace tailWord_540708 prefixEnd_540708 123396932325055871628149 := by
  unfold tailWord_540708
  simp only [CollatzResearch.WordTrace]
  refine ⟨9860620462557368209751389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13147493950076490946335185 9860620462557368209751389)
  ·
    refine ⟨3697732673459013078656771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9860620462557368209751389 3697732673459013078656771)
    ·
      refine ⟨5546599010188519617985157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3697732673459013078656771 5546599010188519617985157)
      ·
        refine ⟨1039987314410347428372217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5546599010188519617985157 1039987314410347428372217)
        ·
          refine ⟨779990485807760571279163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1039987314410347428372217 779990485807760571279163)
          ·
            refine ⟨1169985728711640856918745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 779990485807760571279163 1169985728711640856918745)
            ·
              refine ⟨877489296533730642689059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1169985728711640856918745 877489296533730642689059)
              ·
                refine ⟨1316233944800595964033589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 877489296533730642689059 1316233944800595964033589)
                ·
                  refine ⟨123396932325055871628149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1316233944800595964033589 123396932325055871628149)
                  ·
                    rfl

theorem cell21_540708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 2, 1, 5].length) (baseStart_540708 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_540708 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_540708 prefixEnd_540708 := by exact prefixLift 540708
  have htrace : WordTrace (prefixWord ++ tailWord_540708) baseStart_540708 baseEnd_540708 := by
    simpa [prefixWord, tailWord_540708, baseEnd_540708] using wordTrace_append hprefix tailTrace_540708
  have hstable : (prefixWord ++ tailWord_540708).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_540708).length < 2 ^ (prefixWord ++ tailWord_540708).sum := by decide
  have hdescent : baseEnd_540708 < baseStart_540708 := by decide
  rcases family_descends (prefixWord ++ tailWord_540708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_540736 : List Nat := [2, 1, 1, 2, 2, 4, 4, 5]
def baseStart_540736 : Nat := 118140960795 + 540736 * 2 ^ 59
def prefixEnd_540736 : Nat := 4983230072969 + 3 ^ 40 * 540736 * 2
def baseEnd_540736 : Nat := 41134440768844681720475

theorem tailTrace_540736 : CollatzResearch.WordTrace tailWord_540736 prefixEnd_540736 41134440768844681720475 := by
  unfold tailWord_540736
  simp only [CollatzResearch.WordTrace]
  refine ⟨9861131084506648600761031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13148174779342198134348041 9861131084506648600761031)
  ·
    refine ⟨14791696626759972901141547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9861131084506648600761031 14791696626759972901141547)
    ·
      refine ⟨22187544940139959351712321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14791696626759972901141547 22187544940139959351712321)
      ·
        refine ⟨16640658705104969513784241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22187544940139959351712321 16640658705104969513784241)
        ·
          refine ⟨12480494028828727135338181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16640658705104969513784241 12480494028828727135338181)
          ·
            refine ⟨2340092630405386337875909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12480494028828727135338181 2340092630405386337875909)
            ·
              refine ⟨438767368201009938351733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2340092630405386337875909 438767368201009938351733)
              ·
                refine ⟨41134440768844681720475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 438767368201009938351733 41134440768844681720475)
                ·
                  rfl

theorem cell21_540736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 4, 5].length) (baseStart_540736 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_540736 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_540736 prefixEnd_540736 := by exact prefixLift 540736
  have htrace : WordTrace (prefixWord ++ tailWord_540736) baseStart_540736 baseEnd_540736 := by
    simpa [prefixWord, tailWord_540736, baseEnd_540736] using wordTrace_append hprefix tailTrace_540736
  have hstable : (prefixWord ++ tailWord_540736).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_540736).length < 2 ^ (prefixWord ++ tailWord_540736).sum := by decide
  have hdescent : baseEnd_540736 < baseStart_540736 := by decide
  rcases family_descends (prefixWord ++ tailWord_540736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541009 : List Nat := [1, 2, 2, 1, 4, 2, 2, 3, 4]
def baseStart_541009 : Nat := 118140960795 + 541009 * 2 ^ 59
def prefixEnd_541009 : Nat := 4983230072969 + 3 ^ 40 * 541009 * 2
def baseEnd_541009 : Nat := 123465624625946237110867

theorem tailTrace_541009 : CollatzResearch.WordTrace tailWord_541009 prefixEnd_541009 123465624625946237110867 := by
  unfold tailWord_541009
  simp only [CollatzResearch.WordTrace]
  refine ⟨19732219297024264826210081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13154812864682843217473387 19732219297024264826210081)
  ·
    refine ⟨14799164472768198619657561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19732219297024264826210081 14799164472768198619657561)
    ·
      refine ⟨11099373354576148964743171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14799164472768198619657561 11099373354576148964743171)
      ·
        refine ⟨16649060031864223447114757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11099373354576148964743171 16649060031864223447114757)
        ·
          refine ⟨3121698755974541896334017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16649060031864223447114757 3121698755974541896334017)
          ·
            refine ⟨2341274066980906422250513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3121698755974541896334017 2341274066980906422250513)
            ·
              refine ⟨1755955550235679816687885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2341274066980906422250513 1755955550235679816687885)
              ·
                refine ⟨658483331338379931257957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1755955550235679816687885 658483331338379931257957)
                ·
                  refine ⟨123465624625946237110867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 658483331338379931257957 123465624625946237110867)
                  ·
                    rfl

theorem cell21_541009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 3, 4].length) (baseStart_541009 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_541009 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_541009 prefixEnd_541009 := by exact prefixLift 541009
  have htrace : WordTrace (prefixWord ++ tailWord_541009) baseStart_541009 baseEnd_541009 := by
    simpa [prefixWord, tailWord_541009, baseEnd_541009] using wordTrace_append hprefix tailTrace_541009
  have hstable : (prefixWord ++ tailWord_541009).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541009).length < 2 ^ (prefixWord ++ tailWord_541009).sum := by decide
  have hdescent : baseEnd_541009 < baseStart_541009 := by decide
  rcases family_descends (prefixWord ++ tailWord_541009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541088 : List Nat := [2, 1, 1, 4, 1, 5, 1, 3, 3]
def baseStart_541088 : Nat := 118140960795 + 541088 * 2 ^ 59
def prefixEnd_541088 : Nat := 4983230072969 + 3 ^ 40 * 541088 * 2
def baseEnd_541088 : Nat := 123483653502259655294039

theorem tailTrace_541088 : CollatzResearch.WordTrace tailWord_541088 prefixEnd_541088 123483653502259655294039 := by
  unfold tailWord_541088
  simp only [CollatzResearch.WordTrace]
  refine ⟨9867550331869030659167959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13156733775825374212223945 9867550331869030659167959)
  ·
    refine ⟨14801325497803545988751939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9867550331869030659167959 14801325497803545988751939)
    ·
      refine ⟨22201988246705318983127909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14801325497803545988751939 22201988246705318983127909)
      ·
        refine ⟨4162872796257247309336483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22201988246705318983127909 4162872796257247309336483)
        ·
          refine ⟨6244309194385870964004725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4162872796257247309336483 6244309194385870964004725)
          ·
            refine ⟨585403986973675402875443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6244309194385870964004725 585403986973675402875443)
            ·
              refine ⟨878105980460513104313165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 585403986973675402875443 878105980460513104313165)
              ·
                refine ⟨329289742672692414117437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 878105980460513104313165 329289742672692414117437)
                ·
                  refine ⟨123483653502259655294039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 329289742672692414117437 123483653502259655294039)
                  ·
                    rfl

theorem cell21_541088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 1, 3, 3].length) (baseStart_541088 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_541088 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_541088 prefixEnd_541088 := by exact prefixLift 541088
  have htrace : WordTrace (prefixWord ++ tailWord_541088) baseStart_541088 baseEnd_541088 := by
    simpa [prefixWord, tailWord_541088, baseEnd_541088] using wordTrace_append hprefix tailTrace_541088
  have hstable : (prefixWord ++ tailWord_541088).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541088).length < 2 ^ (prefixWord ++ tailWord_541088).sum := by decide
  have hdescent : baseEnd_541088 < baseStart_541088 := by decide
  rcases family_descends (prefixWord ++ tailWord_541088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541116 : List Nat := [2, 2, 2, 4, 1, 2, 2, 6]
def baseStart_541116 : Nat := 118140960795 + 541116 * 2 ^ 59
def prefixEnd_541116 : Nat := 4983230072969 + 3 ^ 40 * 541116 * 2
def baseEnd_541116 : Nat := 41163347827912609609105

theorem tailTrace_541116 : CollatzResearch.WordTrace tailWord_541116 prefixEnd_541116 41163347827912609609105 := by
  unfold tailWord_541116
  simp only [CollatzResearch.WordTrace]
  refine ⟨9868060953818311050177601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13157414605091081400236801 9868060953818311050177601)
  ·
    refine ⟨7401045715363733287633201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9868060953818311050177601 7401045715363733287633201)
    ·
      refine ⟨5550784286522799965724901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7401045715363733287633201 5550784286522799965724901)
      ·
        refine ⟨1040772053723024993573419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5550784286522799965724901 1040772053723024993573419)
        ·
          refine ⟨1561158080584537490360129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1040772053723024993573419 1561158080584537490360129)
          ·
            refine ⟨1170868560438403117770097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1561158080584537490360129 1170868560438403117770097)
            ·
              refine ⟨878151420328802338327573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1170868560438403117770097 878151420328802338327573)
              ·
                refine ⟨41163347827912609609105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 878151420328802338327573 41163347827912609609105)
                ·
                  rfl

theorem cell21_541116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 2, 6].length) (baseStart_541116 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_541116 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_541116 prefixEnd_541116 := by exact prefixLift 541116
  have htrace : WordTrace (prefixWord ++ tailWord_541116) baseStart_541116 baseEnd_541116 := by
    simpa [prefixWord, tailWord_541116, baseEnd_541116] using wordTrace_append hprefix tailTrace_541116
  have hstable : (prefixWord ++ tailWord_541116).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541116).length < 2 ^ (prefixWord ++ tailWord_541116).sum := by decide
  have hdescent : baseEnd_541116 < baseStart_541116 := by decide
  rcases family_descends (prefixWord ++ tailWord_541116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541189 : List Nat := [1, 3, 1, 1, 2, 2, 3, 1, 7]
def baseStart_541189 : Nat := 118140960795 + 541189 * 2 ^ 59
def prefixEnd_541189 : Nat := 4983230072969 + 3 ^ 40 * 541189 * 2
def baseEnd_541189 : Nat := 123506703078305924110499

theorem tailTrace_541189 : CollatzResearch.WordTrace tailWord_541189 prefixEnd_541189 123506703078305924110499 := by
  unfold tailWord_541189
  simp only [CollatzResearch.WordTrace]
  refine ⟨19738784436372155567762621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13159189624248103711841747 19738784436372155567762621)
  ·
    refine ⟨7402044163639558337910983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19738784436372155567762621 7402044163639558337910983)
    ·
      refine ⟨11103066245459337506866475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7402044163639558337910983 11103066245459337506866475)
      ·
        refine ⟨16654599368189006260299713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11103066245459337506866475 16654599368189006260299713)
        ·
          refine ⟨12490949526141754695224785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16654599368189006260299713 12490949526141754695224785)
          ·
            refine ⟨9368212144606316021418589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12490949526141754695224785 9368212144606316021418589)
            ·
              refine ⟨3513079554227368508031971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9368212144606316021418589 3513079554227368508031971)
              ·
                refine ⟨5269619331341052762047957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3513079554227368508031971 5269619331341052762047957)
                ·
                  refine ⟨123506703078305924110499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5269619331341052762047957 123506703078305924110499)
                  ·
                    rfl

theorem cell21_541189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 1, 7].length) (baseStart_541189 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_541189 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_541189 prefixEnd_541189 := by exact prefixLift 541189
  have htrace : WordTrace (prefixWord ++ tailWord_541189) baseStart_541189 baseEnd_541189 := by
    simpa [prefixWord, tailWord_541189, baseEnd_541189] using wordTrace_append hprefix tailTrace_541189
  have hstable : (prefixWord ++ tailWord_541189).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541189).length < 2 ^ (prefixWord ++ tailWord_541189).sum := by decide
  have hdescent : baseEnd_541189 < baseStart_541189 := by decide
  rcases family_descends (prefixWord ++ tailWord_541189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541229 : List Nat := [1, 5, 4, 1, 1, 1, 3, 1, 4]
def baseStart_541229 : Nat := 118140960795 + 541229 * 2 ^ 59
def prefixEnd_541229 : Nat := 4983230072969 + 3 ^ 40 * 541229 * 2
def baseEnd_541229 : Nat := 123515831623274743443751

theorem tailTrace_541229 : CollatzResearch.WordTrace tailWord_541229 prefixEnd_541229 123515831623274743443751 := by
  unfold tailWord_541229
  simp only [CollatzResearch.WordTrace]
  refine ⟨19740243356227242399218741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13160162237484828266145827 19740243356227242399218741)
  ·
    refine ⟨1850647814646303974926757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19740243356227242399218741 1850647814646303974926757)
    ·
      refine ⟨346996465246181995298767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1850647814646303974926757 346996465246181995298767)
      ·
        refine ⟨520494697869272992948151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 346996465246181995298767 520494697869272992948151)
        ·
          refine ⟨780742046803909489422227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 520494697869272992948151 780742046803909489422227)
          ·
            refine ⟨1171113070205864234133341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 780742046803909489422227 1171113070205864234133341)
            ·
              refine ⟨439167401327199087800003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1171113070205864234133341 439167401327199087800003)
              ·
                refine ⟨658751101990798631700005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 439167401327199087800003 658751101990798631700005)
                ·
                  refine ⟨123515831623274743443751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 658751101990798631700005 123515831623274743443751)
                  ·
                    rfl

theorem cell21_541229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 3, 1, 4].length) (baseStart_541229 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_541229 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_541229 prefixEnd_541229 := by exact prefixLift 541229
  have htrace : WordTrace (prefixWord ++ tailWord_541229) baseStart_541229 baseEnd_541229 := by
    simpa [prefixWord, tailWord_541229, baseEnd_541229] using wordTrace_append hprefix tailTrace_541229
  have hstable : (prefixWord ++ tailWord_541229).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541229).length < 2 ^ (prefixWord ++ tailWord_541229).sum := by decide
  have hdescent : baseEnd_541229 < baseStart_541229 := by decide
  rcases family_descends (prefixWord ++ tailWord_541229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541254 : List Nat := [6, 1, 1, 1, 2, 1, 1, 2, 6]
def baseStart_541254 : Nat := 118140960795 + 541254 * 2 ^ 59
def prefixEnd_541254 : Nat := 4983230072969 + 3 ^ 40 * 541254 * 2
def baseEnd_541254 : Nat := 123521536963880255527033

theorem tailTrace_541254 : CollatzResearch.WordTrace tailWord_541254 prefixEnd_541254 123521536963880255527033 := by
  unfold tailWord_541254
  simp only [CollatzResearch.WordTrace]
  refine ⟨616911099410520989652463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 13160770120757781112585877 616911099410520989652463)
  ·
    refine ⟨925366649115781484478695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 616911099410520989652463 925366649115781484478695)
    ·
      refine ⟨1388049973673672226718043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 925366649115781484478695 1388049973673672226718043)
      ·
        refine ⟨2082074960510508340077065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1388049973673672226718043 2082074960510508340077065)
        ·
          refine ⟨1561556220382881255057799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2082074960510508340077065 1561556220382881255057799)
          ·
            refine ⟨2342334330574321882586699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1561556220382881255057799 2342334330574321882586699)
            ·
              refine ⟨3513501495861482823880049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2342334330574321882586699 3513501495861482823880049)
              ·
                refine ⟨2635126121896112117910037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3513501495861482823880049 2635126121896112117910037)
                ·
                  refine ⟨123521536963880255527033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2635126121896112117910037 123521536963880255527033)
                  ·
                    rfl

theorem cell21_541254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 2, 6].length) (baseStart_541254 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_541254 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_541254 prefixEnd_541254 := by exact prefixLift 541254
  have htrace : WordTrace (prefixWord ++ tailWord_541254) baseStart_541254 baseEnd_541254 := by
    simpa [prefixWord, tailWord_541254, baseEnd_541254] using wordTrace_append hprefix tailTrace_541254
  have hstable : (prefixWord ++ tailWord_541254).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541254).length < 2 ^ (prefixWord ++ tailWord_541254).sum := by decide
  have hdescent : baseEnd_541254 < baseStart_541254 := by decide
  rcases family_descends (prefixWord ++ tailWord_541254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541288 : List Nat := [2, 1, 4, 3, 3, 1, 2, 1, 4]
def baseStart_541288 : Nat := 118140960795 + 541288 * 2 ^ 59
def prefixEnd_541288 : Nat := 4983230072969 + 3 ^ 40 * 541288 * 2
def baseEnd_541288 : Nat := 123529296227103751960297

theorem tailTrace_541288 : CollatzResearch.WordTrace tailWord_541288 prefixEnd_541288 123529296227103751960297 := by
  unfold tailWord_541288
  simp only [CollatzResearch.WordTrace]
  refine ⟨9871197631506747737808259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13161596842008996983744345 9871197631506747737808259)
  ·
    refine ⟨14806796447260121606712389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9871197631506747737808259 14806796447260121606712389)
    ·
      refine ⟨2776274333861272801258573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14806796447260121606712389 2776274333861272801258573)
      ·
        refine ⟨1041102875197977300471965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2776274333861272801258573 1041102875197977300471965)
        ·
          refine ⟨390413578199241487676987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1041102875197977300471965 390413578199241487676987)
          ·
            refine ⟨585620367298862231515481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 390413578199241487676987 585620367298862231515481)
            ·
              refine ⟨439215275474146673636611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 585620367298862231515481 439215275474146673636611)
              ·
                refine ⟨658822913211220010454917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 439215275474146673636611 658822913211220010454917)
                ·
                  refine ⟨123529296227103751960297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 658822913211220010454917 123529296227103751960297)
                  ·
                    rfl

theorem cell21_541288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 2, 1, 4].length) (baseStart_541288 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_541288 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_541288 prefixEnd_541288 := by exact prefixLift 541288
  have htrace : WordTrace (prefixWord ++ tailWord_541288) baseStart_541288 baseEnd_541288 := by
    simpa [prefixWord, tailWord_541288, baseEnd_541288] using wordTrace_append hprefix tailTrace_541288
  have hstable : (prefixWord ++ tailWord_541288).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541288).length < 2 ^ (prefixWord ++ tailWord_541288).sum := by decide
  have hdescent : baseEnd_541288 < baseStart_541288 := by decide
  rcases family_descends (prefixWord ++ tailWord_541288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541330 : List Nat := [3, 2, 3, 1, 2, 2, 2, 2, 4]
def baseStart_541330 : Nat := 118140960795 + 541330 * 2 ^ 59
def prefixEnd_541330 : Nat := 4983230072969 + 3 ^ 40 * 541330 * 2
def baseEnd_541330 : Nat := 123538881199321012260211

theorem tailTrace_541330 : CollatzResearch.WordTrace tailWord_541330 prefixEnd_541330 123538881199321012260211 := by
  unfold tailWord_541330
  simp only [CollatzResearch.WordTrace]
  refine ⟨4935981782215334162161361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13162618085907557765763629 4935981782215334162161361)
  ·
    refine ⟨3701986336661500621621021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4935981782215334162161361 3701986336661500621621021)
    ·
      refine ⟨1388244876248062733107883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3701986336661500621621021 1388244876248062733107883)
      ·
        refine ⟨2082367314372094099661825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1388244876248062733107883 2082367314372094099661825)
        ·
          refine ⟨1561775485779070574746369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2082367314372094099661825 1561775485779070574746369)
          ·
            refine ⟨1171331614334302931059777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1561775485779070574746369 1171331614334302931059777)
            ·
              refine ⟨878498710750727198294833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1171331614334302931059777 878498710750727198294833)
              ·
                refine ⟨658874033063045398721125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 878498710750727198294833 658874033063045398721125)
                ·
                  refine ⟨123538881199321012260211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 658874033063045398721125 123538881199321012260211)
                  ·
                    rfl

theorem cell21_541330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 2, 2, 4].length) (baseStart_541330 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_541330 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_541330 prefixEnd_541330 := by exact prefixLift 541330
  have htrace : WordTrace (prefixWord ++ tailWord_541330) baseStart_541330 baseEnd_541330 := by
    simpa [prefixWord, tailWord_541330, baseEnd_541330] using wordTrace_append hprefix tailTrace_541330
  have hstable : (prefixWord ++ tailWord_541330).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541330).length < 2 ^ (prefixWord ++ tailWord_541330).sum := by decide
  have hdescent : baseEnd_541330 < baseStart_541330 := by decide
  rcases family_descends (prefixWord ++ tailWord_541330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541344 : List Nat := [2, 1, 1, 4, 4, 2, 1, 6]
def baseStart_541344 : Nat := 118140960795 + 541344 * 2 ^ 59
def prefixEnd_541344 : Nat := 4983230072969 + 3 ^ 40 * 541344 * 2
def baseEnd_541344 : Nat := 41180692063353366342283

theorem tailTrace_541344 : CollatzResearch.WordTrace tailWord_541344 prefixEnd_541344 41180692063353366342283 := by
  unfold tailWord_541344
  simp only [CollatzResearch.WordTrace]
  refine ⟨9872218875405308519827543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13162958500540411359770057 9872218875405308519827543)
  ·
    refine ⟨14808328313107962779741315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9872218875405308519827543 14808328313107962779741315)
    ·
      refine ⟨22212492469661944169611973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14808328313107962779741315 22212492469661944169611973)
      ·
        refine ⟨4164842338061614531802245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22212492469661944169611973 4164842338061614531802245)
        ·
          refine ⟨780907938386552724712921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4164842338061614531802245 780907938386552724712921)
          ·
            refine ⟨585680953789914543534691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 780907938386552724712921 585680953789914543534691)
            ·
              refine ⟨878521430684871815302037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 585680953789914543534691 878521430684871815302037)
              ·
                refine ⟨41180692063353366342283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 878521430684871815302037 41180692063353366342283)
                ·
                  rfl

theorem cell21_541344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 1, 6].length) (baseStart_541344 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_541344 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_541344 prefixEnd_541344 := by exact prefixLift 541344
  have htrace : WordTrace (prefixWord ++ tailWord_541344) baseStart_541344 baseEnd_541344 := by
    simpa [prefixWord, tailWord_541344, baseEnd_541344] using wordTrace_append hprefix tailTrace_541344
  have hstable : (prefixWord ++ tailWord_541344).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541344).length < 2 ^ (prefixWord ++ tailWord_541344).sum := by decide
  have hdescent : baseEnd_541344 < baseStart_541344 := by decide
  rcases family_descends (prefixWord ++ tailWord_541344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541361 : List Nat := [1, 2, 2, 6, 1, 1, 3, 5]
def baseStart_541361 : Nat := 118140960795 + 541361 * 2 ^ 59
def prefixEnd_541361 : Nat := 4983230072969 + 3 ^ 40 * 541361 * 2
def baseEnd_541361 : Nat := 41181985273890615747827

theorem tailTrace_541361 : CollatzResearch.WordTrace tailWord_541361 prefixEnd_541361 41181985273890615747827 := by
  unfold tailWord_541361
  simp only [CollatzResearch.WordTrace]
  refine ⟨19745057791749028943023937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13163371861166019295349291 19745057791749028943023937)
  ·
    refine ⟨14808793343811771707267953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19745057791749028943023937 14808793343811771707267953)
    ·
      refine ⟨11106595007858828780450965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14808793343811771707267953 11106595007858828780450965)
      ·
        refine ⟨520621640993382599083639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 11106595007858828780450965 520621640993382599083639)
        ·
          refine ⟨780932461490073898625459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 520621640993382599083639 780932461490073898625459)
          ·
            refine ⟨1171398692235110847938189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 780932461490073898625459 1171398692235110847938189)
            ·
              refine ⟨439274509588166567976821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1171398692235110847938189 439274509588166567976821)
              ·
                refine ⟨41181985273890615747827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 439274509588166567976821 41181985273890615747827)
                ·
                  rfl

theorem cell21_541361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 3, 5].length) (baseStart_541361 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_541361 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_541361 prefixEnd_541361 := by exact prefixLift 541361
  have htrace : WordTrace (prefixWord ++ tailWord_541361) baseStart_541361 baseEnd_541361 := by
    simpa [prefixWord, tailWord_541361, baseEnd_541361] using wordTrace_append hprefix tailTrace_541361
  have hstable : (prefixWord ++ tailWord_541361).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541361).length < 2 ^ (prefixWord ++ tailWord_541361).sum := by decide
  have hdescent : baseEnd_541361 < baseStart_541361 := by decide
  rcases family_descends (prefixWord ++ tailWord_541361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541372 : List Nat := [2, 2, 2, 3, 1, 1, 2, 2, 6]
def baseStart_541372 : Nat := 118140960795 + 541372 * 2 ^ 59
def prefixEnd_541372 : Nat := 4983230072969 + 3 ^ 40 * 541372 * 2
def baseEnd_541372 : Nat := 123548466171538272560125

theorem tailTrace_541372 : CollatzResearch.WordTrace tailWord_541372 prefixEnd_541372 123548466171538272560125 := by
  unfold tailWord_541372
  simp only [CollatzResearch.WordTrace]
  refine ⟨9872729497354588910837185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13163639329806118547782913 9872729497354588910837185)
  ·
    refine ⟨7404547123015941683127889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9872729497354588910837185 7404547123015941683127889)
    ·
      refine ⟨5553410342261956262345917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7404547123015941683127889 5553410342261956262345917)
      ·
        refine ⟨2082528878348233598379719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5553410342261956262345917 2082528878348233598379719)
        ·
          refine ⟨3123793317522350397569579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2082528878348233598379719 3123793317522350397569579)
          ·
            refine ⟨4685689976283525596354369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3123793317522350397569579 4685689976283525596354369)
            ·
              refine ⟨3514267482212644197265777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4685689976283525596354369 3514267482212644197265777)
              ·
                refine ⟨2635700611659483147949333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3514267482212644197265777 2635700611659483147949333)
                ·
                  refine ⟨123548466171538272560125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2635700611659483147949333 123548466171538272560125)
                  ·
                    rfl

theorem cell21_541372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 2, 6].length) (baseStart_541372 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_541372 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_541372 prefixEnd_541372 := by exact prefixLift 541372
  have htrace : WordTrace (prefixWord ++ tailWord_541372) baseStart_541372 baseEnd_541372 := by
    simpa [prefixWord, tailWord_541372, baseEnd_541372] using wordTrace_append hprefix tailTrace_541372
  have hstable : (prefixWord ++ tailWord_541372).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541372).length < 2 ^ (prefixWord ++ tailWord_541372).sum := by decide
  have hdescent : baseEnd_541372 < baseStart_541372 := by decide
  rcases family_descends (prefixWord ++ tailWord_541372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541375 : List Nat := [1, 1, 2, 2, 2, 5, 2, 3, 3]
def baseStart_541375 : Nat := 118140960795 + 541375 * 2 ^ 59
def prefixEnd_541375 : Nat := 4983230072969 + 3 ^ 40 * 541375 * 2
def baseEnd_541375 : Nat := 123549150812410934010119

theorem tailTrace_541375 : CollatzResearch.WordTrace tailWord_541375 prefixEnd_541375 123549150812410934010119 := by
  unfold tailWord_541375
  simp only [CollatzResearch.WordTrace]
  refine ⟨19745568413698309334033579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13163712275798872889355719 19745568413698309334033579)
  ·
    refine ⟨29618352620547464001050369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19745568413698309334033579 29618352620547464001050369)
    ·
      refine ⟨22213764465410598000787777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29618352620547464001050369 22213764465410598000787777)
      ·
        refine ⟨16660323349057948500590833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22213764465410598000787777 16660323349057948500590833)
        ·
          refine ⟨12495242511793461375443125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16660323349057948500590833 12495242511793461375443125)
          ·
            refine ⟨1171428985480637003947793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12495242511793461375443125 1171428985480637003947793)
            ·
              refine ⟨878571739110477752960845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1171428985480637003947793 878571739110477752960845)
              ·
                refine ⟨329464402166429157360317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 878571739110477752960845 329464402166429157360317)
                ·
                  refine ⟨123549150812410934010119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 329464402166429157360317 123549150812410934010119)
                  ·
                    rfl

theorem cell21_541375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 2, 3, 3].length) (baseStart_541375 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_541375 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_541375 prefixEnd_541375 := by exact prefixLift 541375
  have htrace : WordTrace (prefixWord ++ tailWord_541375) baseStart_541375 baseEnd_541375 := by
    simpa [prefixWord, tailWord_541375, baseEnd_541375] using wordTrace_append hprefix tailTrace_541375
  have hstable : (prefixWord ++ tailWord_541375).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541375).length < 2 ^ (prefixWord ++ tailWord_541375).sum := by decide
  have hdescent : baseEnd_541375 < baseStart_541375 := by decide
  rcases family_descends (prefixWord ++ tailWord_541375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541417 : List Nat := [1, 2, 1, 1, 1, 2, 6, 2, 5]
def baseStart_541417 : Nat := 118140960795 + 541417 * 2 ^ 59
def prefixEnd_541417 : Nat := 4983230072969 + 3 ^ 40 * 541417 * 2
def baseEnd_541417 : Nat := 123558735784628194310033

theorem tailTrace_541417 : CollatzResearch.WordTrace tailWord_541417 prefixEnd_541417 123558735784628194310033 := by
  unfold tailWord_541417
  simp only [CollatzResearch.WordTrace]
  refine ⟨19747100279546150507062505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13164733519697433671375003 19747100279546150507062505)
  ·
    refine ⟨14810325209659612880296879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19747100279546150507062505 14810325209659612880296879)
    ·
      refine ⟨22215487814489419320445319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14810325209659612880296879 22215487814489419320445319)
      ·
        refine ⟨33323231721734128980667979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22215487814489419320445319 33323231721734128980667979)
        ·
          refine ⟨49984847582601193471001969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33323231721734128980667979 49984847582601193471001969)
          ·
            refine ⟨37488635686950895103251477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49984847582601193471001969 37488635686950895103251477)
            ·
              refine ⟨1757279797825823207964913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 37488635686950895103251477 1757279797825823207964913)
              ·
                refine ⟨1317959848369367405973685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1757279797825823207964913 1317959848369367405973685)
                ·
                  refine ⟨123558735784628194310033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1317959848369367405973685 123558735784628194310033)
                  ·
                    rfl

theorem cell21_541417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 2, 5].length) (baseStart_541417 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_541417 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_541417 prefixEnd_541417 := by exact prefixLift 541417
  have htrace : WordTrace (prefixWord ++ tailWord_541417) baseStart_541417 baseEnd_541417 := by
    simpa [prefixWord, tailWord_541417, baseEnd_541417] using wordTrace_append hprefix tailTrace_541417
  have hstable : (prefixWord ++ tailWord_541417).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541417).length < 2 ^ (prefixWord ++ tailWord_541417).sum := by decide
  have hdescent : baseEnd_541417 < baseStart_541417 := by decide
  rcases family_descends (prefixWord ++ tailWord_541417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541448 : List Nat := [2, 1, 3, 2, 2, 2, 2, 1, 6]
def baseStart_541448 : Nat := 118140960795 + 541448 * 2 ^ 59
def prefixEnd_541448 : Nat := 4983230072969 + 3 ^ 40 * 541448 * 2
def baseEnd_541448 : Nat := 123565810406979029293303

theorem tailTrace_541448 : CollatzResearch.WordTrace tailWord_541448 prefixEnd_541448 123565810406979029293303 := by
  unfold tailWord_541448
  simp only [CollatzResearch.WordTrace]
  refine ⟨9874115471216921400720499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13165487294955895200960665 9874115471216921400720499)
  ·
    refine ⟨14811173206825382101080749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9874115471216921400720499 14811173206825382101080749)
    ·
      refine ⟨5554189952559518287905281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14811173206825382101080749 5554189952559518287905281)
      ·
        refine ⟨4165642464419638715928961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5554189952559518287905281 4165642464419638715928961)
        ·
          refine ⟨3124231848314729036946721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4165642464419638715928961 3124231848314729036946721)
          ·
            refine ⟨2343173886236046777710041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3124231848314729036946721 2343173886236046777710041)
            ·
              refine ⟨1757380414677035083282531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2343173886236046777710041 1757380414677035083282531)
              ·
                refine ⟨2636070622015552624923797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1757380414677035083282531 2636070622015552624923797)
                ·
                  refine ⟨123565810406979029293303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2636070622015552624923797 123565810406979029293303)
                  ·
                    rfl

theorem cell21_541448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 1, 6].length) (baseStart_541448 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_541448 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_541448 prefixEnd_541448 := by exact prefixLift 541448
  have htrace : WordTrace (prefixWord ++ tailWord_541448) baseStart_541448 baseEnd_541448 := by
    simpa [prefixWord, tailWord_541448, baseEnd_541448] using wordTrace_append hprefix tailTrace_541448
  have hstable : (prefixWord ++ tailWord_541448).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541448).length < 2 ^ (prefixWord ++ tailWord_541448).sum := by decide
  have hdescent : baseEnd_541448 < baseStart_541448 := by decide
  rcases family_descends (prefixWord ++ tailWord_541448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541502 : List Nat := [4, 2, 1, 2, 4, 1, 2, 2, 3]
def baseStart_541502 : Nat := 118140960795 + 541502 * 2 ^ 59
def prefixEnd_541502 : Nat := 4983230072969 + 3 ^ 40 * 541502 * 2
def baseEnd_541502 : Nat := 123578133942686935393193

theorem tailTrace_541502 : CollatzResearch.WordTrace tailWord_541502 prefixEnd_541502 123578133942686935393193 := by
  unfold tailWord_541502
  simp only [CollatzResearch.WordTrace]
  refine ⟨2468775060529776252988345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13166800322825473349271173 2468775060529776252988345)
  ·
    refine ⟨1851581295397332189741259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2468775060529776252988345 1851581295397332189741259)
    ·
      refine ⟨2777371943095998284611889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1851581295397332189741259 2777371943095998284611889)
      ·
        refine ⟨2083028957321998713458917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2777371943095998284611889 2083028957321998713458917)
        ·
          refine ⟨390567929497874758773547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2083028957321998713458917 390567929497874758773547)
          ·
            refine ⟨585851894246812138160321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 390567929497874758773547 585851894246812138160321)
            ·
              refine ⟨439388920685109103620241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 585851894246812138160321 439388920685109103620241)
              ·
                refine ⟨329541690513831827715181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 439388920685109103620241 329541690513831827715181)
                ·
                  refine ⟨123578133942686935393193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 329541690513831827715181 123578133942686935393193)
                  ·
                    rfl

theorem cell21_541502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 2, 2, 3].length) (baseStart_541502 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_541502 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_541502 prefixEnd_541502 := by exact prefixLift 541502
  have htrace : WordTrace (prefixWord ++ tailWord_541502) baseStart_541502 baseEnd_541502 := by
    simpa [prefixWord, tailWord_541502, baseEnd_541502] using wordTrace_append hprefix tailTrace_541502
  have hstable : (prefixWord ++ tailWord_541502).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541502).length < 2 ^ (prefixWord ++ tailWord_541502).sum := by decide
  have hdescent : baseEnd_541502 < baseStart_541502 := by decide
  rcases family_descends (prefixWord ++ tailWord_541502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541558 : List Nat := [5, 1, 1, 3, 1, 1, 3, 2, 4]
def baseStart_541558 : Nat := 118140960795 + 541558 * 2 ^ 59
def prefixEnd_541558 : Nat := 4983230072969 + 3 ^ 40 * 541558 * 2
def baseEnd_541558 : Nat := 123590913905643282459745

theorem tailTrace_541558 : CollatzResearch.WordTrace tailWord_541558 prefixEnd_541558 123590913905643282459745 := by
  unfold tailWord_541558
  simp only [CollatzResearch.WordTrace]
  refine ⟨1234515185752208224246583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13168161981356887725296885 1234515185752208224246583)
  ·
    refine ⟨1851772778628312336369875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1234515185752208224246583 1851772778628312336369875)
    ·
      refine ⟨2777659167942468504554813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1851772778628312336369875 2777659167942468504554813)
      ·
        refine ⟨1041622187978425689208055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2777659167942468504554813 1041622187978425689208055)
        ·
          refine ⟨1562433281967638533812083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1041622187978425689208055 1562433281967638533812083)
          ·
            refine ⟨2343649922951457800718125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1562433281967638533812083 2343649922951457800718125)
            ·
              refine ⟨878868721106796675269297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2343649922951457800718125 878868721106796675269297)
              ·
                refine ⟨659151540830097506451973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 878868721106796675269297 659151540830097506451973)
                ·
                  refine ⟨123590913905643282459745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 659151540830097506451973 123590913905643282459745)
                  ·
                    rfl

theorem cell21_541558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 3, 2, 4].length) (baseStart_541558 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_541558 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_541558 prefixEnd_541558 := by exact prefixLift 541558
  have htrace : WordTrace (prefixWord ++ tailWord_541558) baseStart_541558 baseEnd_541558 := by
    simpa [prefixWord, tailWord_541558, baseEnd_541558] using wordTrace_append hprefix tailTrace_541558
  have hstable : (prefixWord ++ tailWord_541558).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541558).length < 2 ^ (prefixWord ++ tailWord_541558).sum := by decide
  have hdescent : baseEnd_541558 < baseStart_541558 := by decide
  rcases family_descends (prefixWord ++ tailWord_541558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541620 : List Nat := [2, 5, 2, 1, 1, 3, 1, 1, 5]
def baseStart_541620 : Nat := 118140960795 + 541620 * 2 ^ 59
def prefixEnd_541620 : Nat := 4983230072969 + 3 ^ 40 * 541620 * 2
def baseEnd_541620 : Nat := 123605063150344952426285

theorem tailTrace_541620 : CollatzResearch.WordTrace tailWord_541620 prefixEnd_541620 123605063150344952426285 := by
  unfold tailWord_541620
  simp only [CollatzResearch.WordTrace]
  refine ⟨9877252148905358088351157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13169669531873810784468209 9877252148905358088351157)
  ·
    refine ⟨925992388959877320782921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9877252148905358088351157 925992388959877320782921)
    ·
      refine ⟨694494291719907990587191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 925992388959877320782921 694494291719907990587191)
      ·
        refine ⟨1041741437579861985880787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 694494291719907990587191 1041741437579861985880787)
        ·
          refine ⟨1562612156369792978821181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1041741437579861985880787 1562612156369792978821181)
          ·
            refine ⟨585979558638672367057943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1562612156369792978821181 585979558638672367057943)
            ·
              refine ⟨878969337958008550586915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 585979558638672367057943 878969337958008550586915)
              ·
                refine ⟨1318454006937012825880373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 878969337958008550586915 1318454006937012825880373)
                ·
                  refine ⟨123605063150344952426285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1318454006937012825880373 123605063150344952426285)
                  ·
                    rfl

theorem cell21_541620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 1, 1, 5].length) (baseStart_541620 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_541620 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_541620 prefixEnd_541620 := by exact prefixLift 541620
  have htrace : WordTrace (prefixWord ++ tailWord_541620) baseStart_541620 baseEnd_541620 := by
    simpa [prefixWord, tailWord_541620, baseEnd_541620] using wordTrace_append hprefix tailTrace_541620
  have hstable : (prefixWord ++ tailWord_541620).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541620).length < 2 ^ (prefixWord ++ tailWord_541620).sum := by decide
  have hdescent : baseEnd_541620 < baseStart_541620 := by decide
  rcases family_descends (prefixWord ++ tailWord_541620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541679 : List Nat := [1, 1, 2, 1, 4, 3, 4, 2, 3]
def baseStart_541679 : Nat := 118140960795 + 541679 * 2 ^ 59
def prefixEnd_541679 : Nat := 4983230072969 + 3 ^ 40 * 541679 * 2
def baseEnd_541679 : Nat := 123618527754173960942831

theorem tailTrace_541679 : CollatzResearch.WordTrace tailWord_541679 prefixEnd_541679 123618527754173960942831 := by
  unfold tailWord_541679
  simp only [CollatzResearch.WordTrace]
  refine ⟨19756656204596969253100091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13171104136397979502066727 19756656204596969253100091)
  ·
    refine ⟨29634984306895453879650137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19756656204596969253100091 29634984306895453879650137)
    ·
      refine ⟨22226238230171590409737603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29634984306895453879650137 22226238230171590409737603)
      ·
        refine ⟨33339357345257385614606405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22226238230171590409737603 33339357345257385614606405)
        ·
          refine ⟨6251129502235759802738701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33339357345257385614606405 6251129502235759802738701)
          ·
            refine ⟨2344173563338409926027013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6251129502235759802738701 2344173563338409926027013)
            ·
              refine ⟨439532543125951861130065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2344173563338409926027013 439532543125951861130065)
              ·
                refine ⟨329649407344463895847549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 439532543125951861130065 329649407344463895847549)
                ·
                  refine ⟨123618527754173960942831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 329649407344463895847549 123618527754173960942831)
                  ·
                    rfl

theorem cell21_541679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 4, 2, 3].length) (baseStart_541679 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_541679 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_541679 prefixEnd_541679 := by exact prefixLift 541679
  have htrace : WordTrace (prefixWord ++ tailWord_541679) baseStart_541679 baseEnd_541679 := by
    simpa [prefixWord, tailWord_541679, baseEnd_541679] using wordTrace_append hprefix tailTrace_541679
  have hstable : (prefixWord ++ tailWord_541679).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541679).length < 2 ^ (prefixWord ++ tailWord_541679).sum := by decide
  have hdescent : baseEnd_541679 < baseStart_541679 := by decide
  rcases family_descends (prefixWord ++ tailWord_541679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541707 : List Nat := [1, 1, 1, 1, 6, 3, 3, 5]
def baseStart_541707 : Nat := 118140960795 + 541707 * 2 ^ 59
def prefixEnd_541707 : Nat := 4983230072969 + 3 ^ 40 * 541707 * 2
def baseEnd_541707 : Nat := 41208305911884044825369

theorem tailTrace_541707 : CollatzResearch.WordTrace tailWord_541707 prefixEnd_541707 41208305911884044825369 := by
  unfold tailWord_541707
  simp only [CollatzResearch.WordTrace]
  refine ⟨19757677448495530035119375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13171784965663686690079583 19757677448495530035119375)
  ·
    refine ⟨29636516172743295052679063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19757677448495530035119375 29636516172743295052679063)
    ·
      refine ⟨44454774259114942579018595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29636516172743295052679063 44454774259114942579018595)
      ·
        refine ⟨66682161388672413868527893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44454774259114942579018595 66682161388672413868527893)
        ·
          refine ⟨3125726315094019400087245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 66682161388672413868527893 3125726315094019400087245)
          ·
            refine ⟨1172147368160257275032717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3125726315094019400087245 1172147368160257275032717)
            ·
              refine ⟨439555263060096478137269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1172147368160257275032717 439555263060096478137269)
              ·
                refine ⟨41208305911884044825369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 439555263060096478137269 41208305911884044825369)
                ·
                  rfl

theorem cell21_541707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 3, 5].length) (baseStart_541707 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_541707 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_541707 prefixEnd_541707 := by exact prefixLift 541707
  have htrace : WordTrace (prefixWord ++ tailWord_541707) baseStart_541707 baseEnd_541707 := by
    simpa [prefixWord, tailWord_541707, baseEnd_541707] using wordTrace_append hprefix tailTrace_541707
  have hstable : (prefixWord ++ tailWord_541707).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541707).length < 2 ^ (prefixWord ++ tailWord_541707).sum := by decide
  have hdescent : baseEnd_541707 < baseStart_541707 := by decide
  rcases family_descends (prefixWord ++ tailWord_541707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541789 : List Nat := [1, 4, 4, 1, 2, 1, 3, 2, 3]
def baseStart_541789 : Nat := 118140960795 + 541789 * 2 ^ 59
def prefixEnd_541789 : Nat := 4983230072969 + 3 ^ 40 * 541789 * 2
def baseEnd_541789 : Nat := 123643631252838214109273

theorem tailTrace_541789 : CollatzResearch.WordTrace tailWord_541789 prefixEnd_541789 123643631252838214109273 := by
  unfold tailWord_541789
  simp only [CollatzResearch.WordTrace]
  refine ⟨19760668234198458039604421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13173778822798972026402947 19760668234198458039604421)
  ·
    refine ⟨3705125293912210882425829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19760668234198458039604421 3705125293912210882425829)
    ·
      refine ⟨694710992608539540454843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3705125293912210882425829 694710992608539540454843)
      ·
        refine ⟨1042066488912809310682265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 694710992608539540454843 1042066488912809310682265)
        ·
          refine ⟨781549866684606983011699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1042066488912809310682265 781549866684606983011699)
          ·
            refine ⟨1172324800026910474517549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 781549866684606983011699 1172324800026910474517549)
            ·
              refine ⟨439621800010091427944081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1172324800026910474517549 439621800010091427944081)
              ·
                refine ⟨329716350007568570958061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 439621800010091427944081 329716350007568570958061)
                ·
                  refine ⟨123643631252838214109273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 329716350007568570958061 123643631252838214109273)
                  ·
                    rfl

theorem cell21_541789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 3, 2, 3].length) (baseStart_541789 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_541789 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_541789 prefixEnd_541789 := by exact prefixLift 541789
  have htrace : WordTrace (prefixWord ++ tailWord_541789) baseStart_541789 baseEnd_541789 := by
    simpa [prefixWord, tailWord_541789, baseEnd_541789] using wordTrace_append hprefix tailTrace_541789
  have hstable : (prefixWord ++ tailWord_541789).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541789).length < 2 ^ (prefixWord ++ tailWord_541789).sum := by decide
  have hdescent : baseEnd_541789 < baseStart_541789 := by decide
  rcases family_descends (prefixWord ++ tailWord_541789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541800 : List Nat := [2, 1, 4, 4, 1, 1, 2, 6]
def baseStart_541800 : Nat := 118140960795 + 541800 * 2 ^ 59
def prefixEnd_541800 : Nat := 4983230072969 + 3 ^ 40 * 541800 * 2
def baseEnd_541800 : Nat := 41215380534234879808639

theorem tailTrace_541800 : CollatzResearch.WordTrace tailWord_541800 prefixEnd_541800 41215380534234879808639 := by
  unfold tailWord_541800
  simp only [CollatzResearch.WordTrace]
  refine ⟨9880534718579303459127427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13174046291439071278836569 9880534718579303459127427)
  ·
    refine ⟨14820802077868955188691141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9880534718579303459127427 14820802077868955188691141)
    ·
      refine ⟨2778900389600429097879589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14820802077868955188691141 2778900389600429097879589)
      ·
        refine ⟨521043823050080455852423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2778900389600429097879589 521043823050080455852423)
        ·
          refine ⟨781565734575120683778635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 521043823050080455852423 781565734575120683778635)
          ·
            refine ⟨1172348601862681025667953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 781565734575120683778635 1172348601862681025667953)
            ·
              refine ⟨879261451397010769250965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1172348601862681025667953 879261451397010769250965)
              ·
                refine ⟨41215380534234879808639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 879261451397010769250965 41215380534234879808639)
                ·
                  rfl

theorem cell21_541800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 2, 6].length) (baseStart_541800 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_541800 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_541800 prefixEnd_541800 := by exact prefixLift 541800
  have htrace : WordTrace (prefixWord ++ tailWord_541800) baseStart_541800 baseEnd_541800 := by
    simpa [prefixWord, tailWord_541800, baseEnd_541800] using wordTrace_append hprefix tailTrace_541800
  have hstable : (prefixWord ++ tailWord_541800).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541800).length < 2 ^ (prefixWord ++ tailWord_541800).sum := by decide
  have hdescent : baseEnd_541800 < baseStart_541800 := by decide
  rcases family_descends (prefixWord ++ tailWord_541800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541842 : List Nat := [3, 2, 3, 1, 1, 11]
def baseStart_541842 : Nat := 118140960795 + 541842 * 2 ^ 59
def prefixEnd_541842 : Nat := 4983230072969 + 3 ^ 40 * 541842 * 2
def baseEnd_541842 : Nat := 4579841724997107397253

theorem tailTrace_541842 : CollatzResearch.WordTrace tailWord_541842 prefixEnd_541842 4579841724997107397253 := by
  unfold tailWord_541842
  simp only [CollatzResearch.WordTrace]
  refine ⟨4940650325751612022820945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13175067535337632060855853 4940650325751612022820945)
  ·
    refine ⟨3705487744313709017115709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4940650325751612022820945 3705487744313709017115709)
    ·
      refine ⟨1389557904117640881418391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3705487744313709017115709 1389557904117640881418391)
      ·
        refine ⟨2084336856176461322127587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1389557904117640881418391 2084336856176461322127587)
        ·
          refine ⟨3126505284264691983191381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2084336856176461322127587 3126505284264691983191381)
          ·
            refine ⟨4579841724997107397253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 3126505284264691983191381 4579841724997107397253)
            ·
              rfl

theorem cell21_541842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 11].length) (baseStart_541842 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_541842 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_541842 prefixEnd_541842 := by exact prefixLift 541842
  have htrace : WordTrace (prefixWord ++ tailWord_541842) baseStart_541842 baseEnd_541842 := by
    simpa [prefixWord, tailWord_541842, baseEnd_541842] using wordTrace_append hprefix tailTrace_541842
  have hstable : (prefixWord ++ tailWord_541842).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541842).length < 2 ^ (prefixWord ++ tailWord_541842).sum := by decide
  have hdescent : baseEnd_541842 < baseStart_541842 := by decide
  rcases family_descends (prefixWord ++ tailWord_541842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541848 : List Nat := [2, 1, 2, 4, 2, 3, 2, 2, 3]
def baseStart_541848 : Nat := 118140960795 + 541848 * 2 ^ 59
def prefixEnd_541848 : Nat := 4983230072969 + 3 ^ 40 * 541848 * 2
def baseEnd_541848 : Nat := 123657095856667222625819

theorem tailTrace_541848 : CollatzResearch.WordTrace tailWord_541848 prefixEnd_541848 123657095856667222625819 := by
  unfold tailWord_541848
  simp only [CollatzResearch.WordTrace]
  refine ⟨9881410070492355558001099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13175213427323140744001465 9881410070492355558001099)
  ·
    refine ⟨14822115105738533337001649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9881410070492355558001099 14822115105738533337001649)
    ·
      refine ⟨11116586329303900002751237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14822115105738533337001649 11116586329303900002751237)
      ·
        refine ⟨2084359936744481250515857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11116586329303900002751237 2084359936744481250515857)
        ·
          refine ⟨1563269952558360937886893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2084359936744481250515857 1563269952558360937886893)
          ·
            refine ⟨586226232209385351707585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1563269952558360937886893 586226232209385351707585)
            ·
              refine ⟨439669674157039013780689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 586226232209385351707585 439669674157039013780689)
              ·
                refine ⟨329752255617779260335517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 439669674157039013780689 329752255617779260335517)
                ·
                  refine ⟨123657095856667222625819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 329752255617779260335517 123657095856667222625819)
                  ·
                    rfl

theorem cell21_541848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 2, 2, 3].length) (baseStart_541848 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_541848 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_541848 prefixEnd_541848 := by exact prefixLift 541848
  have htrace : WordTrace (prefixWord ++ tailWord_541848) baseStart_541848 baseEnd_541848 := by
    simpa [prefixWord, tailWord_541848, baseEnd_541848] using wordTrace_append hprefix tailTrace_541848
  have hstable : (prefixWord ++ tailWord_541848).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541848).length < 2 ^ (prefixWord ++ tailWord_541848).sum := by decide
  have hdescent : baseEnd_541848 < baseStart_541848 := by decide
  rcases family_descends (prefixWord ++ tailWord_541848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541873 : List Nat := [1, 2, 2, 5, 1, 1, 1, 1, 7]
def baseStart_541873 : Nat := 118140960795 + 541873 * 2 ^ 59
def prefixEnd_541873 : Nat := 4983230072969 + 3 ^ 40 * 541873 * 2
def baseEnd_541873 : Nat := 123662801197272734709101

theorem tailTrace_541873 : CollatzResearch.WordTrace tailWord_541873 prefixEnd_541873 123662801197272734709101 := by
  unfold tailWord_541873
  simp only [CollatzResearch.WordTrace]
  refine ⟨19763731965894140385662273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13175821310596093590441515 19763731965894140385662273)
  ·
    refine ⟨14822798974420605289246705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19763731965894140385662273 14822798974420605289246705)
    ·
      refine ⟨11117099230815453966935029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14822798974420605289246705 11117099230815453966935029)
      ·
        refine ⟨1042228052888948809400159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11117099230815453966935029 1042228052888948809400159)
        ·
          refine ⟨1563342079333423214100239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1042228052888948809400159 1563342079333423214100239)
          ·
            refine ⟨2345013119000134821150359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1563342079333423214100239 2345013119000134821150359)
            ·
              refine ⟨3517519678500202231725539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2345013119000134821150359 3517519678500202231725539)
              ·
                refine ⟨5276279517750303347588309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3517519678500202231725539 5276279517750303347588309)
                ·
                  refine ⟨123662801197272734709101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5276279517750303347588309 123662801197272734709101)
                  ·
                    rfl

theorem cell21_541873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 1, 7].length) (baseStart_541873 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_541873 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_541873 prefixEnd_541873 := by exact prefixLift 541873
  have htrace : WordTrace (prefixWord ++ tailWord_541873) baseStart_541873 baseEnd_541873 := by
    simpa [prefixWord, tailWord_541873, baseEnd_541873] using wordTrace_append hprefix tailTrace_541873
  have hstable : (prefixWord ++ tailWord_541873).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541873).length < 2 ^ (prefixWord ++ tailWord_541873).sum := by decide
  have hdescent : baseEnd_541873 < baseStart_541873 := by decide
  rcases family_descends (prefixWord ++ tailWord_541873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541921 : List Nat := [1, 2, 3, 1, 3, 3, 3, 1, 4]
def baseStart_541921 : Nat := 118140960795 + 541921 * 2 ^ 59
def prefixEnd_541921 : Nat := 4983230072969 + 3 ^ 40 * 541921 * 2
def baseEnd_541921 : Nat := 123673755451235317909003

theorem tailTrace_541921 : CollatzResearch.WordTrace tailWord_541921 prefixEnd_541921 123673755451235317909003 := by
  unfold tailWord_541921
  simp only [CollatzResearch.WordTrace]
  refine ⟨19765482669720244583409617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13176988446480163055606411 19765482669720244583409617)
  ·
    refine ⟨14824112002290183437557213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19765482669720244583409617 14824112002290183437557213)
    ·
      refine ⟨5559042000858818789083955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14824112002290183437557213 5559042000858818789083955)
      ·
        refine ⟨8338563001288228183625933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5559042000858818789083955 8338563001288228183625933)
        ·
          refine ⟨3126961125483085568859725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8338563001288228183625933 3126961125483085568859725)
          ·
            refine ⟨1172610422056157088322397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3126961125483085568859725 1172610422056157088322397)
            ·
              refine ⟨439728908271058908120899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1172610422056157088322397 439728908271058908120899)
              ·
                refine ⟨659593362406588362181349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 439728908271058908120899 659593362406588362181349)
                ·
                  refine ⟨123673755451235317909003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 659593362406588362181349 123673755451235317909003)
                  ·
                    rfl

theorem cell21_541921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 3, 1, 4].length) (baseStart_541921 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_541921 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_541921 prefixEnd_541921 := by exact prefixLift 541921
  have htrace : WordTrace (prefixWord ++ tailWord_541921) baseStart_541921 baseEnd_541921 := by
    simpa [prefixWord, tailWord_541921, baseEnd_541921] using wordTrace_append hprefix tailTrace_541921
  have hstable : (prefixWord ++ tailWord_541921).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541921).length < 2 ^ (prefixWord ++ tailWord_541921).sum := by decide
  have hdescent : baseEnd_541921 < baseStart_541921 := by decide
  rcases family_descends (prefixWord ++ tailWord_541921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541963 : List Nat := [1, 1, 1, 1, 5, 3, 2, 1, 6]
def baseStart_541963 : Nat := 118140960795 + 541963 * 2 ^ 59
def prefixEnd_541963 : Nat := 4983230072969 + 3 ^ 40 * 541963 * 2
def baseEnd_541963 : Nat := 123683340423452578208917

theorem tailTrace_541963 : CollatzResearch.WordTrace tailWord_541963 prefixEnd_541963 123683340423452578208917 := by
  unfold tailWord_541963
  simp only [CollatzResearch.WordTrace]
  refine ⟨19767014535568085756438543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13178009690378723837625695 19767014535568085756438543)
  ·
    refine ⟨29650521803352128634657815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19767014535568085756438543 29650521803352128634657815)
    ·
      refine ⟨44475782705028192951986723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29650521803352128634657815 44475782705028192951986723)
      ·
        refine ⟨66713674057542289427980085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44475782705028192951986723 66713674057542289427980085)
        ·
          refine ⟨6254406942894589633873133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 66713674057542289427980085 6254406942894589633873133)
          ·
            refine ⟨2345402603585471112702425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6254406942894589633873133 2345402603585471112702425)
            ·
              refine ⟨1759051952689103334526819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2345402603585471112702425 1759051952689103334526819)
              ·
                refine ⟨2638577929033655001790229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1759051952689103334526819 2638577929033655001790229)
                ·
                  refine ⟨123683340423452578208917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2638577929033655001790229 123683340423452578208917)
                  ·
                    rfl

theorem cell21_541963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 1, 6].length) (baseStart_541963 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_541963 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_541963 prefixEnd_541963 := by exact prefixLift 541963
  have htrace : WordTrace (prefixWord ++ tailWord_541963) baseStart_541963 baseEnd_541963 := by
    simpa [prefixWord, tailWord_541963, baseEnd_541963] using wordTrace_append hprefix tailTrace_541963
  have hstable : (prefixWord ++ tailWord_541963).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541963).length < 2 ^ (prefixWord ++ tailWord_541963).sum := by decide
  have hdescent : baseEnd_541963 < baseStart_541963 := by decide
  rcases family_descends (prefixWord ++ tailWord_541963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541966 : List Nat := [4, 1, 1, 2, 1, 5, 1, 1, 5]
def baseStart_541966 : Nat := 118140960795 + 541966 * 2 ^ 59
def prefixEnd_541966 : Nat := 4983230072969 + 3 ^ 40 * 541966 * 2
def baseEnd_541966 : Nat := 123684025064325239658911

theorem tailTrace_541966 : CollatzResearch.WordTrace tailWord_541966 prefixEnd_541966 123684025064325239658911 := by
  unfold tailWord_541966
  simp only [CollatzResearch.WordTrace]
  refine ⟨2470890494319652158599719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13178082636371478179198501 2470890494319652158599719)
  ·
    refine ⟨3706335741479478237899579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2470890494319652158599719 3706335741479478237899579)
    ·
      refine ⟨5559503612219217356849369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3706335741479478237899579 5559503612219217356849369)
      ·
        refine ⟨4169627709164413017637027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5559503612219217356849369 4169627709164413017637027)
        ·
          refine ⟨6254441563746619526455541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4169627709164413017637027 6254441563746619526455541)
          ·
            refine ⟨586353896601245580605207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6254441563746619526455541 586353896601245580605207)
            ·
              refine ⟨879530844901868370907811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 586353896601245580605207 879530844901868370907811)
              ·
                refine ⟨1319296267352802556361717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 879530844901868370907811 1319296267352802556361717)
                ·
                  refine ⟨123684025064325239658911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1319296267352802556361717 123684025064325239658911)
                  ·
                    rfl

theorem cell21_541966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 1, 1, 5].length) (baseStart_541966 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_541966 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_541966 prefixEnd_541966 := by exact prefixLift 541966
  have htrace : WordTrace (prefixWord ++ tailWord_541966) baseStart_541966 baseEnd_541966 := by
    simpa [prefixWord, tailWord_541966, baseEnd_541966] using wordTrace_append hprefix tailTrace_541966
  have hstable : (prefixWord ++ tailWord_541966).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541966).length < 2 ^ (prefixWord ++ tailWord_541966).sum := by decide
  have hdescent : baseEnd_541966 < baseStart_541966 := by decide
  rcases family_descends (prefixWord ++ tailWord_541966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542104 : List Nat := [2, 1, 2, 5, 2, 2, 2, 5]
def baseStart_542104 : Nat := 118140960795 + 542104 * 2 ^ 59
def prefixEnd_542104 : Nat := 4983230072969 + 3 ^ 40 * 542104 * 2
def baseEnd_542104 : Nat := 41238506181489222119543

theorem tailTrace_542104 : CollatzResearch.WordTrace tailWord_542104 prefixEnd_542104 41238506181489222119543 := by
  unfold tailWord_542104
  simp only [CollatzResearch.WordTrace]
  refine ⟨9886078614028633418660683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13181438152038177891547577 9886078614028633418660683)
  ·
    refine ⟨14829117921042950127991025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9886078614028633418660683 14829117921042950127991025)
    ·
      refine ⟨11121838440782212595993269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14829117921042950127991025 11121838440782212595993269)
      ·
        refine ⟨1042672353823332430874369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11121838440782212595993269 1042672353823332430874369)
        ·
          refine ⟨782004265367499323155777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1042672353823332430874369 782004265367499323155777)
          ·
            refine ⟨586503199025624492366833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 782004265367499323155777 586503199025624492366833)
            ·
              refine ⟨439877399269218369275125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 586503199025624492366833 439877399269218369275125)
              ·
                refine ⟨41238506181489222119543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 439877399269218369275125 41238506181489222119543)
                ·
                  rfl

theorem cell21_542104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 2, 5].length) (baseStart_542104 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_542104 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_542104 prefixEnd_542104 := by exact prefixLift 542104
  have htrace : WordTrace (prefixWord ++ tailWord_542104) baseStart_542104 baseEnd_542104 := by
    simpa [prefixWord, tailWord_542104, baseEnd_542104] using wordTrace_append hprefix tailTrace_542104
  have hstable : (prefixWord ++ tailWord_542104).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542104).length < 2 ^ (prefixWord ++ tailWord_542104).sum := by decide
  have hdescent : baseEnd_542104 < baseStart_542104 := by decide
  rcases family_descends (prefixWord ++ tailWord_542104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542191 : List Nat := [1, 1, 2, 1, 4, 1, 3, 4, 4]
def baseStart_542191 : Nat := 118140960795 + 542191 * 2 ^ 59
def prefixEnd_542191 : Nat := 4983230072969 + 3 ^ 40 * 542191 * 2
def baseEnd_542191 : Nat := 123735373129774848408451

theorem tailTrace_542191 : CollatzResearch.WordTrace tailWord_542191 prefixEnd_542191 123735373129774848408451 := by
  unfold tailWord_542191
  simp only [CollatzResearch.WordTrace]
  refine ⟨19775330378742080695738427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13183553585828053797158951 19775330378742080695738427)
  ·
    refine ⟨29662995568113121043607641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19775330378742080695738427 29662995568113121043607641)
    ·
      refine ⟨22247246676084840782705731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29662995568113121043607641 22247246676084840782705731)
      ·
        refine ⟨33370870014127261174058597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22247246676084840782705731 33370870014127261174058597)
        ·
          refine ⟨6257038127648861470135987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33370870014127261174058597 6257038127648861470135987)
          ·
            refine ⟨9385557191473292205203981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6257038127648861470135987 9385557191473292205203981)
            ·
              refine ⟨3519583946802484576951493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9385557191473292205203981 3519583946802484576951493)
              ·
                refine ⟨659921990025465858178405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3519583946802484576951493 659921990025465858178405)
                ·
                  refine ⟨123735373129774848408451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 659921990025465858178405 123735373129774848408451)
                  ·
                    rfl

theorem cell21_542191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 4, 4].length) (baseStart_542191 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_542191 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_542191 prefixEnd_542191 := by exact prefixLift 542191
  have htrace : WordTrace (prefixWord ++ tailWord_542191) baseStart_542191 baseEnd_542191 := by
    simpa [prefixWord, tailWord_542191, baseEnd_542191] using wordTrace_append hprefix tailTrace_542191
  have hstable : (prefixWord ++ tailWord_542191).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542191).length < 2 ^ (prefixWord ++ tailWord_542191).sum := by decide
  have hdescent : baseEnd_542191 < baseStart_542191 := by decide
  rcases family_descends (prefixWord ++ tailWord_542191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542214 : List Nat := [6, 2, 1, 1, 2, 1, 3, 5]
def baseStart_542214 : Nat := 118140960795 + 542214 * 2 ^ 59
def prefixEnd_542214 : Nat := 4983230072969 + 3 ^ 40 * 542214 * 2
def baseEnd_542214 : Nat := 41246874014377306508357

theorem tailTrace_542214 : CollatzResearch.WordTrace tailWord_542214 prefixEnd_542214 41246874014377306508357 := by
  unfold tailWord_542214
  simp only [CollatzResearch.WordTrace]
  refine ⟨618005289301836113244553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 13184112838439170415883797 618005289301836113244553)
  ·
    refine ⟨463503966976377084933415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 618005289301836113244553 463503966976377084933415)
    ·
      refine ⟨695255950464565627400123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 463503966976377084933415 695255950464565627400123)
      ·
        refine ⟨1042883925696848441100185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 695255950464565627400123 1042883925696848441100185)
        ·
          refine ⟨782162944272636330825139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1042883925696848441100185 782162944272636330825139)
          ·
            refine ⟨1173244416408954496237709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 782162944272636330825139 1173244416408954496237709)
            ·
              refine ⟨439966656153357936089141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1173244416408954496237709 439966656153357936089141)
              ·
                refine ⟨41246874014377306508357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 439966656153357936089141 41246874014377306508357)
                ·
                  rfl

theorem cell21_542214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 3, 5].length) (baseStart_542214 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_542214 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_542214 prefixEnd_542214 := by exact prefixLift 542214
  have htrace : WordTrace (prefixWord ++ tailWord_542214) baseStart_542214 baseEnd_542214 := by
    simpa [prefixWord, tailWord_542214, baseEnd_542214] using wordTrace_append hprefix tailTrace_542214
  have hstable : (prefixWord ++ tailWord_542214).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542214).length < 2 ^ (prefixWord ++ tailWord_542214).sum := by decide
  have hdescent : baseEnd_542214 < baseStart_542214 := by decide
  rcases family_descends (prefixWord ++ tailWord_542214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542228 : List Nat := [2, 4, 3, 1, 2, 1, 2, 3, 3]
def baseStart_542228 : Nat := 118140960795 + 542228 * 2 ^ 59
def prefixEnd_542228 : Nat := 4983230072969 + 3 ^ 40 * 542228 * 2
def baseEnd_542228 : Nat := 123743817033871006291709

theorem tailTrace_542228 : CollatzResearch.WordTrace tailWord_542228 prefixEnd_542228 123743817033871006291709 := by
  unfold tailWord_542228
  simp only [CollatzResearch.WordTrace]
  refine ⟨9888339939804018007417669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13184453253072024009890225 9888339939804018007417669)
  ·
    refine ⟨1854063738713253376390813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9888339939804018007417669 1854063738713253376390813)
    ·
      refine ⟨695273902017470016146555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1854063738713253376390813 695273902017470016146555)
      ·
        refine ⟨1042910853026205024219833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 695273902017470016146555 1042910853026205024219833)
        ·
          refine ⟨782183139769653768164875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1042910853026205024219833 782183139769653768164875)
          ·
            refine ⟨1173274709654480652247313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 782183139769653768164875 1173274709654480652247313)
            ·
              refine ⟨879956032240860489185485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1173274709654480652247313 879956032240860489185485)
              ·
                refine ⟨329983512090322683444557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 879956032240860489185485 329983512090322683444557)
                ·
                  refine ⟨123743817033871006291709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 329983512090322683444557 123743817033871006291709)
                  ·
                    rfl

theorem cell21_542228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 2, 3, 3].length) (baseStart_542228 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_542228 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_542228 prefixEnd_542228 := by exact prefixLift 542228
  have htrace : WordTrace (prefixWord ++ tailWord_542228) baseStart_542228 baseEnd_542228 := by
    simpa [prefixWord, tailWord_542228, baseEnd_542228] using wordTrace_append hprefix tailTrace_542228
  have hstable : (prefixWord ++ tailWord_542228).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542228).length < 2 ^ (prefixWord ++ tailWord_542228).sum := by decide
  have hdescent : baseEnd_542228 < baseStart_542228 := by decide
  rcases family_descends (prefixWord ++ tailWord_542228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542236 : List Nat := [2, 2, 3, 1, 2, 1, 1, 2, 7]
def baseStart_542236 : Nat := 118140960795 + 542236 * 2 ^ 59
def prefixEnd_542236 : Nat := 4983230072969 + 3 ^ 40 * 542236 * 2
def baseEnd_542236 : Nat := 123745642742864770158359

theorem tailTrace_542236 : CollatzResearch.WordTrace tailWord_542236 prefixEnd_542236 123745642742864770158359 := by
  unfold tailWord_542236
  simp only [CollatzResearch.WordTrace]
  refine ⟨9888485831789526690563281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13184647775719368920751041 9888485831789526690563281)
  ·
    refine ⟨7416364373842145017922461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9888485831789526690563281 7416364373842145017922461)
    ·
      refine ⟨2781136640190804381720923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7416364373842145017922461 2781136640190804381720923)
      ·
        refine ⟨4171704960286206572581385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2781136640190804381720923 4171704960286206572581385)
        ·
          refine ⟨3128778720214654929436039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4171704960286206572581385 3128778720214654929436039)
          ·
            refine ⟨4693168080321982394154059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3128778720214654929436039 4693168080321982394154059)
            ·
              refine ⟨7039752120482973591231089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4693168080321982394154059 7039752120482973591231089)
              ·
                refine ⟨5279814090362230193423317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7039752120482973591231089 5279814090362230193423317)
                ·
                  refine ⟨123745642742864770158359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5279814090362230193423317 123745642742864770158359)
                  ·
                    rfl

theorem cell21_542236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 2, 7].length) (baseStart_542236 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_542236 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_542236 prefixEnd_542236 := by exact prefixLift 542236
  have htrace : WordTrace (prefixWord ++ tailWord_542236) baseStart_542236 baseEnd_542236 := by
    simpa [prefixWord, tailWord_542236, baseEnd_542236] using wordTrace_append hprefix tailTrace_542236
  have hstable : (prefixWord ++ tailWord_542236).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542236).length < 2 ^ (prefixWord ++ tailWord_542236).sum := by decide
  have hdescent : baseEnd_542236 < baseStart_542236 := by decide
  rcases family_descends (prefixWord ++ tailWord_542236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542318 : List Nat := [4, 1, 2, 2, 3, 2, 2, 1, 4]
def baseStart_542318 : Nat := 118140960795 + 542318 * 2 ^ 59
def prefixEnd_542318 : Nat := 4983230072969 + 3 ^ 40 * 542318 * 2
def baseEnd_542318 : Nat := 123764356260050849791525

theorem tailTrace_542318 : CollatzResearch.WordTrace tailWord_542318 prefixEnd_542318 123764356260050849791525 := by
  unfold tailWord_542318
  simp only [CollatzResearch.WordTrace]
  refine ⟨2472495306160247673201451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13186641632854654257074405 2472495306160247673201451)
  ·
    refine ⟨3708742959240371509802177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2472495306160247673201451 3708742959240371509802177)
    ·
      refine ⟨2781557219430278632351633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3708742959240371509802177 2781557219430278632351633)
      ·
        refine ⟨2086167914572708974263725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2781557219430278632351633 2086167914572708974263725)
        ·
          refine ⟨782312967964765865348897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2086167914572708974263725 782312967964765865348897)
          ·
            refine ⟨586734725973574399011673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 782312967964765865348897 586734725973574399011673)
            ·
              refine ⟨440051044480180799258755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 586734725973574399011673 440051044480180799258755)
              ·
                refine ⟨660076566720271198888133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 440051044480180799258755 660076566720271198888133)
                ·
                  refine ⟨123764356260050849791525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 660076566720271198888133 123764356260050849791525)
                  ·
                    rfl

theorem cell21_542318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 2, 1, 4].length) (baseStart_542318 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_542318 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_542318 prefixEnd_542318 := by exact prefixLift 542318
  have htrace : WordTrace (prefixWord ++ tailWord_542318) baseStart_542318 baseEnd_542318 := by
    simpa [prefixWord, tailWord_542318, baseEnd_542318] using wordTrace_append hprefix tailTrace_542318
  have hstable : (prefixWord ++ tailWord_542318).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542318).length < 2 ^ (prefixWord ++ tailWord_542318).sum := by decide
  have hdescent : baseEnd_542318 < baseStart_542318 := by decide
  rcases family_descends (prefixWord ++ tailWord_542318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542360 : List Nat := [2, 1, 2, 4, 1, 3, 2, 2, 4]
def baseStart_542360 : Nat := 118140960795 + 542360 * 2 ^ 59
def prefixEnd_542360 : Nat := 4983230072969 + 3 ^ 40 * 542360 * 2
def baseEnd_542360 : Nat := 123773941232268110091439

theorem tailTrace_542360 : CollatzResearch.WordTrace tailWord_542360 prefixEnd_542360 123773941232268110091439 := by
  unfold tailWord_542360
  simp only [CollatzResearch.WordTrace]
  refine ⟨9890747157564911279320267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13187662876753215039093689 9890747157564911279320267)
  ·
    refine ⟨14836120736347366918980401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9890747157564911279320267 14836120736347366918980401)
    ·
      refine ⟨11127090552260525189235301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14836120736347366918980401 11127090552260525189235301)
      ·
        refine ⟨2086329478548848472981619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11127090552260525189235301 2086329478548848472981619)
        ·
          refine ⟨3129494217823272709472429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2086329478548848472981619 3129494217823272709472429)
          ·
            refine ⟨1173560331683727266052161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3129494217823272709472429 1173560331683727266052161)
            ·
              refine ⟨880170248762795449539121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1173560331683727266052161 880170248762795449539121)
              ·
                refine ⟨660127686572096587154341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 880170248762795449539121 660127686572096587154341)
                ·
                  refine ⟨123773941232268110091439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 660127686572096587154341 123773941232268110091439)
                  ·
                    rfl

theorem cell21_542360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 2, 2, 4].length) (baseStart_542360 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_542360 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_542360 prefixEnd_542360 := by exact prefixLift 542360
  have htrace : WordTrace (prefixWord ++ tailWord_542360) baseStart_542360 baseEnd_542360 := by
    simpa [prefixWord, tailWord_542360, baseEnd_542360] using wordTrace_append hprefix tailTrace_542360
  have hstable : (prefixWord ++ tailWord_542360).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542360).length < 2 ^ (prefixWord ++ tailWord_542360).sum := by decide
  have hdescent : baseEnd_542360 < baseStart_542360 := by decide
  rcases family_descends (prefixWord ++ tailWord_542360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542436 : List Nat := [2, 3, 1, 1, 1, 3, 5, 1, 4]
def baseStart_542436 : Nat := 118140960795 + 542436 * 2 ^ 59
def prefixEnd_542436 : Nat := 4983230072969 + 3 ^ 40 * 542436 * 2
def baseEnd_542436 : Nat := 123791285467708866824617

theorem tailTrace_542436 : CollatzResearch.WordTrace tailWord_542436 prefixEnd_542436 123791285467708866824617 := by
  unfold tailWord_542436
  simp only [CollatzResearch.WordTrace]
  refine ⟨9892133131427243769203581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13189510841902991692271441 9892133131427243769203581)
  ·
    refine ⟨3709549924285216413451343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9892133131427243769203581 3709549924285216413451343)
    ·
      refine ⟨5564324886427824620177015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3709549924285216413451343 5564324886427824620177015)
      ·
        refine ⟨8346487329641736930265523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5564324886427824620177015 8346487329641736930265523)
        ·
          refine ⟨12519730994462605395398285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8346487329641736930265523 12519730994462605395398285)
          ·
            refine ⟨4694899122923477023274357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12519730994462605395398285 4694899122923477023274357)
            ·
              refine ⟨440146792774075970931971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4694899122923477023274357 440146792774075970931971)
              ·
                refine ⟨660220189161113956397957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 440146792774075970931971 660220189161113956397957)
                ·
                  refine ⟨123791285467708866824617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 660220189161113956397957 123791285467708866824617)
                  ·
                    rfl

theorem cell21_542436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 5, 1, 4].length) (baseStart_542436 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_542436 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_542436 prefixEnd_542436 := by exact prefixLift 542436
  have htrace : WordTrace (prefixWord ++ tailWord_542436) baseStart_542436 baseEnd_542436 := by
    simpa [prefixWord, tailWord_542436, baseEnd_542436] using wordTrace_append hprefix tailTrace_542436
  have hstable : (prefixWord ++ tailWord_542436).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542436).length < 2 ^ (prefixWord ++ tailWord_542436).sum := by decide
  have hdescent : baseEnd_542436 < baseStart_542436 := by decide
  rcases family_descends (prefixWord ++ tailWord_542436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542495 : List Nat := [1, 1, 2, 4, 2, 1, 3, 3, 4]
def baseStart_542495 : Nat := 118140960795 + 542495 * 2 ^ 59
def prefixEnd_542495 : Nat := 4983230072969 + 3 ^ 40 * 542495 * 2
def baseEnd_542495 : Nat := 123804750071537875341163

theorem tailTrace_542495 : CollatzResearch.WordTrace tailWord_542495 prefixEnd_542495 123804750071537875341163 := by
  unfold tailWord_542495
  simp only [CollatzResearch.WordTrace]
  refine ⟨19786418169640740614804939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13190945446427160409869959 19786418169640740614804939)
  ·
    refine ⟨29679627254461110922207409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19786418169640740614804939 29679627254461110922207409)
    ·
      refine ⟨22259720440845833191655557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29679627254461110922207409 22259720440845833191655557)
      ·
        refine ⟨4173697582658593723435417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22259720440845833191655557 4173697582658593723435417)
        ·
          refine ⟨3130273186993945292576563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4173697582658593723435417 3130273186993945292576563)
          ·
            refine ⟨4695409780490917938864845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3130273186993945292576563 4695409780490917938864845)
            ·
              refine ⟨1760778667684094227074317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4695409780490917938864845 1760778667684094227074317)
              ·
                refine ⟨660292000381535335152869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1760778667684094227074317 660292000381535335152869)
                ·
                  refine ⟨123804750071537875341163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 660292000381535335152869 123804750071537875341163)
                  ·
                    rfl

theorem cell21_542495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 3, 4].length) (baseStart_542495 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_542495 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_542495 prefixEnd_542495 := by exact prefixLift 542495
  have htrace : WordTrace (prefixWord ++ tailWord_542495) baseStart_542495 baseEnd_542495 := by
    simpa [prefixWord, tailWord_542495, baseEnd_542495] using wordTrace_append hprefix tailTrace_542495
  have hstable : (prefixWord ++ tailWord_542495).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542495).length < 2 ^ (prefixWord ++ tailWord_542495).sum := by decide
  have hdescent : baseEnd_542495 < baseStart_542495 := by decide
  rcases family_descends (prefixWord ++ tailWord_542495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542574 : List Nat := [4, 1, 2, 3, 1, 1, 1, 5, 3]
def baseStart_542574 : Nat := 118140960795 + 542574 * 2 ^ 59
def prefixEnd_542574 : Nat := 4983230072969 + 3 ^ 40 * 542574 * 2
def baseEnd_542574 : Nat := 123822778947851293524335

theorem tailTrace_542574 : CollatzResearch.WordTrace tailWord_542574 prefixEnd_542574 123822778947851293524335 := by
  unfold tailWord_542574
  simp only [CollatzResearch.WordTrace]
  refine ⟨2473662442044317138366347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13192866357569691404620517 2473662442044317138366347)
  ·
    refine ⟨3710493663066475707549521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2473662442044317138366347 3710493663066475707549521)
    ·
      refine ⟨2782870247299856780662141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3710493663066475707549521 2782870247299856780662141)
      ·
        refine ⟨1043576342737446292748303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2782870247299856780662141 1043576342737446292748303)
        ·
          refine ⟨1565364514106169439122455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1043576342737446292748303 1565364514106169439122455)
          ·
            refine ⟨2348046771159254158683683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1565364514106169439122455 2348046771159254158683683)
            ·
              refine ⟨3522070156738881238025525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2348046771159254158683683 3522070156738881238025525)
              ·
                refine ⟨330194077194270116064893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3522070156738881238025525 330194077194270116064893)
                ·
                  refine ⟨123822778947851293524335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 330194077194270116064893 123822778947851293524335)
                  ·
                    rfl

theorem cell21_542574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 5, 3].length) (baseStart_542574 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_542574 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_542574 prefixEnd_542574 := by exact prefixLift 542574
  have htrace : WordTrace (prefixWord ++ tailWord_542574) baseStart_542574 baseEnd_542574 := by
    simpa [prefixWord, tailWord_542574, baseEnd_542574] using wordTrace_append hprefix tailTrace_542574
  have hstable : (prefixWord ++ tailWord_542574).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542574).length < 2 ^ (prefixWord ++ tailWord_542574).sum := by decide
  have hdescent : baseEnd_542574 < baseStart_542574 := by decide
  rcases family_descends (prefixWord ++ tailWord_542574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542664 : List Nat := [2, 1, 3, 1, 4, 1, 4, 1, 4]
def baseStart_542664 : Nat := 118140960795 + 542664 * 2 ^ 59
def prefixEnd_542664 : Nat := 4983230072969 + 3 ^ 40 * 542664 * 2
def baseEnd_542664 : Nat := 123843318174031137024151

theorem tailTrace_542664 : CollatzResearch.WordTrace tailWord_542664 prefixEnd_542664 123843318174031137024151 := by
  unfold tailWord_542664
  simp only [CollatzResearch.WordTrace]
  refine ⟨9896291053014241238853523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13195054737352321651804697 9896291053014241238853523)
  ·
    refine ⟨14844436579521361858280285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9896291053014241238853523 14844436579521361858280285)
    ·
      refine ⟨5566663717320510696855107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14844436579521361858280285 5566663717320510696855107)
      ·
        refine ⟨8349995575980766045282661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5566663717320510696855107 8349995575980766045282661)
        ·
          refine ⟨1565624170496393633490499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8349995575980766045282661 1565624170496393633490499)
          ·
            refine ⟨2348436255744590450235749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1565624170496393633490499 2348436255744590450235749)
            ·
              refine ⟨440331797952110709419203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2348436255744590450235749 440331797952110709419203)
              ·
                refine ⟨660497696928166064128805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 440331797952110709419203 660497696928166064128805)
                ·
                  refine ⟨123843318174031137024151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 660497696928166064128805 123843318174031137024151)
                  ·
                    rfl

theorem cell21_542664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 4, 1, 4].length) (baseStart_542664 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_542664 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_542664 prefixEnd_542664 := by exact prefixLift 542664
  have htrace : WordTrace (prefixWord ++ tailWord_542664) baseStart_542664 baseEnd_542664 := by
    simpa [prefixWord, tailWord_542664, baseEnd_542664] using wordTrace_append hprefix tailTrace_542664
  have hstable : (prefixWord ++ tailWord_542664).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542664).length < 2 ^ (prefixWord ++ tailWord_542664).sum := by decide
  have hdescent : baseEnd_542664 < baseStart_542664 := by decide
  rcases family_descends (prefixWord ++ tailWord_542664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542701 : List Nat := [1, 5, 1, 4, 2, 1, 2, 2, 3]
def baseStart_542701 : Nat := 118140960795 + 542701 * 2 ^ 59
def prefixEnd_542701 : Nat := 4983230072969 + 3 ^ 40 * 542701 * 2
def baseEnd_542701 : Nat := 123851762078127294907409

theorem tailTrace_542701 : CollatzResearch.WordTrace tailWord_542701 prefixEnd_542701 123851762078127294907409 := by
  unfold tailWord_542701
  simp only [CollatzResearch.WordTrace]
  refine ⟨19793931606894437796803957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13195954404596291864535971 19793931606894437796803957)
  ·
    refine ⟨1855681088146353543450371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19793931606894437796803957 1855681088146353543450371)
    ·
      refine ⟨2783521632219530315175557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1855681088146353543450371 2783521632219530315175557)
      ·
        refine ⟨521910306041161934095417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2783521632219530315175557 521910306041161934095417)
        ·
          refine ⟨391432729530871450571563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 521910306041161934095417 391432729530871450571563)
          ·
            refine ⟨587149094296307175857345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 391432729530871450571563 587149094296307175857345)
            ·
              refine ⟨440361820722230381893009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 587149094296307175857345 440361820722230381893009)
              ·
                refine ⟨330271365541672786419757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 440361820722230381893009 330271365541672786419757)
                ·
                  refine ⟨123851762078127294907409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 330271365541672786419757 123851762078127294907409)
                  ·
                    rfl

theorem cell21_542701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 2, 2, 3].length) (baseStart_542701 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_542701 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_542701 prefixEnd_542701 := by exact prefixLift 542701
  have htrace : WordTrace (prefixWord ++ tailWord_542701) baseStart_542701 baseEnd_542701 := by
    simpa [prefixWord, tailWord_542701, baseEnd_542701] using wordTrace_append hprefix tailTrace_542701
  have hstable : (prefixWord ++ tailWord_542701).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542701).length < 2 ^ (prefixWord ++ tailWord_542701).sum := by decide
  have hdescent : baseEnd_542701 < baseStart_542701 := by decide
  rcases family_descends (prefixWord ++ tailWord_542701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542720 : List Nat := [2, 1, 1, 2, 1, 1, 1, 12]
def baseStart_542720 : Nat := 118140960795 + 542720 * 2 ^ 59
def prefixEnd_542720 : Nat := 4983230072969 + 3 ^ 40 * 542720 * 2
def baseEnd_542720 : Nat := 41285366045662494696901

theorem tailTrace_542720 : CollatzResearch.WordTrace tailWord_542720 prefixEnd_542720 41285366045662494696901 := by
  unfold tailWord_542720
  simp only [CollatzResearch.WordTrace]
  refine ⟨9897312296912802020872807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13196416395883736027830409 9897312296912802020872807)
  ·
    refine ⟨14845968445369203031309211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9897312296912802020872807 14845968445369203031309211)
    ·
      refine ⟨22268952668053804546963817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14845968445369203031309211 22268952668053804546963817)
      ·
        refine ⟨16701714501040353410222863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22268952668053804546963817 16701714501040353410222863)
        ·
          refine ⟨25052571751560530115334295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16701714501040353410222863 25052571751560530115334295)
          ·
            refine ⟨37578857627340795173001443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25052571751560530115334295 37578857627340795173001443)
            ·
              refine ⟨56368286441011192759502165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37578857627340795173001443 56368286441011192759502165)
              ·
                refine ⟨41285366045662494696901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 56368286441011192759502165 41285366045662494696901)
                ·
                  rfl

theorem cell21_542720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 12].length) (baseStart_542720 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_542720 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_542720 prefixEnd_542720 := by exact prefixLift 542720
  have htrace : WordTrace (prefixWord ++ tailWord_542720) baseStart_542720 baseEnd_542720 := by
    simpa [prefixWord, tailWord_542720, baseEnd_542720] using wordTrace_append hprefix tailTrace_542720
  have hstable : (prefixWord ++ tailWord_542720).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542720).length < 2 ^ (prefixWord ++ tailWord_542720).sum := by decide
  have hdescent : baseEnd_542720 < baseStart_542720 := by decide
  rcases family_descends (prefixWord ++ tailWord_542720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542751 : List Nat := [1, 1, 2, 4, 1, 2, 1, 2, 7]
def baseStart_542751 : Nat := 118140960795 + 542751 * 2 ^ 59
def prefixEnd_542751 : Nat := 4983230072969 + 3 ^ 40 * 542751 * 2
def baseEnd_542751 : Nat := 123863172759338319073973

theorem tailTrace_542751 : CollatzResearch.WordTrace tailWord_542751 prefixEnd_542751 123863172759338319073973 := by
  unfold tailWord_542751
  simp only [CollatzResearch.WordTrace]
  refine ⟨19795755256713296336124107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13197170171142197557416071 19795755256713296336124107)
  ·
    refine ⟨29693632885069944504186161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19795755256713296336124107 29693632885069944504186161)
    ·
      refine ⟨22270224663802458378139621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29693632885069944504186161 22270224663802458378139621)
      ·
        refine ⟨4175667124462960945901179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22270224663802458378139621 4175667124462960945901179)
        ·
          refine ⟨6263500686694441418851769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4175667124462960945901179 6263500686694441418851769)
          ·
            refine ⟨4697625515020831064138827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6263500686694441418851769 4697625515020831064138827)
            ·
              refine ⟨7046438272531246596208241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4697625515020831064138827 7046438272531246596208241)
              ·
                refine ⟨5284828704398434947156181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7046438272531246596208241 5284828704398434947156181)
                ·
                  refine ⟨123863172759338319073973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5284828704398434947156181 123863172759338319073973)
                  ·
                    rfl

theorem cell21_542751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 2, 7].length) (baseStart_542751 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_542751 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_542751 prefixEnd_542751 := by exact prefixLift 542751
  have htrace : WordTrace (prefixWord ++ tailWord_542751) baseStart_542751 baseEnd_542751 := by
    simpa [prefixWord, tailWord_542751, baseEnd_542751] using wordTrace_append hprefix tailTrace_542751
  have hstable : (prefixWord ++ tailWord_542751).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542751).length < 2 ^ (prefixWord ++ tailWord_542751).sum := by decide
  have hdescent : baseEnd_542751 < baseStart_542751 := by decide
  rcases family_descends (prefixWord ++ tailWord_542751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542768 : List Nat := [2, 1, 1, 1, 2, 6, 2, 1, 5]
def baseStart_542768 : Nat := 118140960795 + 542768 * 2 ^ 59
def prefixEnd_542768 : Nat := 4983230072969 + 3 ^ 40 * 542768 * 2
def baseEnd_542768 : Nat := 123867052390950067290605

theorem tailTrace_542768 : CollatzResearch.WordTrace tailWord_542768 prefixEnd_542768 123867052390950067290605 := by
  unfold tailWord_542768
  simp only [CollatzResearch.WordTrace]
  refine ⟨9898187648825854119746479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13197583531767805492995305 9898187648825854119746479)
  ·
    refine ⟨14847281473238781179619719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9898187648825854119746479 14847281473238781179619719)
    ·
      refine ⟨22270922209858171769429579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14847281473238781179619719 22270922209858171769429579)
      ·
        refine ⟨33406383314787257654144369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22270922209858171769429579 33406383314787257654144369)
        ·
          refine ⟨25054787486090443240608277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33406383314787257654144369 25054787486090443240608277)
          ·
            refine ⟨1174443163410489526903513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 25054787486090443240608277 1174443163410489526903513)
            ·
              refine ⟨880832372557867145177635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1174443163410489526903513 880832372557867145177635)
              ·
                refine ⟨1321248558836800717766453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 880832372557867145177635 1321248558836800717766453)
                ·
                  refine ⟨123867052390950067290605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1321248558836800717766453 123867052390950067290605)
                  ·
                    rfl

theorem cell21_542768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 2, 1, 5].length) (baseStart_542768 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_542768 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_542768 prefixEnd_542768 := by exact prefixLift 542768
  have htrace : WordTrace (prefixWord ++ tailWord_542768) baseStart_542768 baseEnd_542768 := by
    simpa [prefixWord, tailWord_542768, baseEnd_542768] using wordTrace_append hprefix tailTrace_542768
  have hstable : (prefixWord ++ tailWord_542768).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542768).length < 2 ^ (prefixWord ++ tailWord_542768).sum := by decide
  have hdescent : baseEnd_542768 < baseStart_542768 := by decide
  rcases family_descends (prefixWord ++ tailWord_542768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542872 : List Nat := [2, 1, 2, 4, 12]
def baseStart_542872 : Nat := 118140960795 + 542872 * 2 ^ 59
def prefixEnd_542872 : Nat := 4983230072969 + 3 ^ 40 * 542872 * 2
def baseEnd_542872 : Nat := 1529515884047765401939

theorem tailTrace_542872 : CollatzResearch.WordTrace tailWord_542872 prefixEnd_542872 1529515884047765401939 := by
  unfold tailWord_542872
  simp only [CollatzResearch.WordTrace]
  refine ⟨9900084244637467000639435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13200112326183289334185913 9900084244637467000639435)
  ·
    refine ⟨14850126366956200500959153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9900084244637467000639435 14850126366956200500959153)
    ·
      refine ⟨11137594775217150375719365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14850126366956200500959153 11137594775217150375719365)
      ·
        refine ⟨2088299020353215695447381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11137594775217150375719365 2088299020353215695447381)
        ·
          refine ⟨1529515884047765401939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 2088299020353215695447381 1529515884047765401939)
          ·
            rfl

theorem cell21_542872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 12].length) (baseStart_542872 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_542872 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_542872 prefixEnd_542872 := by exact prefixLift 542872
  have htrace : WordTrace (prefixWord ++ tailWord_542872) baseStart_542872 baseEnd_542872 := by
    simpa [prefixWord, tailWord_542872, baseEnd_542872] using wordTrace_append hprefix tailTrace_542872
  have hstable : (prefixWord ++ tailWord_542872).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542872).length < 2 ^ (prefixWord ++ tailWord_542872).sum := by decide
  have hdescent : baseEnd_542872 < baseStart_542872 := by decide
  rcases family_descends (prefixWord ++ tailWord_542872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542903 : List Nat := [1, 1, 3, 1, 4, 2, 1, 1, 7]
def baseStart_542903 : Nat := 118140960795 + 542903 * 2 ^ 59
def prefixEnd_542903 : Nat := 4983230072969 + 3 ^ 40 * 542903 * 2
def baseEnd_542903 : Nat := 123897861230219832540329

theorem tailTrace_542903 : CollatzResearch.WordTrace tailWord_542903 prefixEnd_542903 123897861230219832540329 := by
  unfold tailWord_542903
  simp only [CollatzResearch.WordTrace]
  refine ⟨19801299152162626295657363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13200866101441750863771575 19801299152162626295657363)
  ·
    refine ⟨29701948728243939443486045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19801299152162626295657363 29701948728243939443486045)
    ·
      refine ⟨11138230773091477291307267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29701948728243939443486045 11138230773091477291307267)
      ·
        refine ⟨16707346159637215936960901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11138230773091477291307267 16707346159637215936960901)
        ·
          refine ⟨3132627404931977988180169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16707346159637215936960901 3132627404931977988180169)
          ·
            refine ⟨2349470553698983491135127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3132627404931977988180169 2349470553698983491135127)
            ·
              refine ⟨3524205830548475236702691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2349470553698983491135127 3524205830548475236702691)
              ·
                refine ⟨5286308745822712855054037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3524205830548475236702691 5286308745822712855054037)
                ·
                  refine ⟨123897861230219832540329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5286308745822712855054037 123897861230219832540329)
                  ·
                    rfl

theorem cell21_542903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 1, 7].length) (baseStart_542903 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_542903 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_542903 prefixEnd_542903 := by exact prefixLift 542903
  have htrace : WordTrace (prefixWord ++ tailWord_542903) baseStart_542903 baseEnd_542903 := by
    simpa [prefixWord, tailWord_542903, baseEnd_542903] using wordTrace_append hprefix tailTrace_542903
  have hstable : (prefixWord ++ tailWord_542903).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542903).length < 2 ^ (prefixWord ++ tailWord_542903).sum := by decide
  have hdescent : baseEnd_542903 < baseStart_542903 := by decide
  rcases family_descends (prefixWord ++ tailWord_542903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542948 : List Nat := [2, 3, 1, 1, 1, 2, 1, 10]
def baseStart_542948 : Nat := 118140960795 + 542948 * 2 ^ 59
def prefixEnd_542948 : Nat := 4983230072969 + 3 ^ 40 * 542948 * 2
def baseEnd_542948 : Nat := 41302710281103251430079

theorem tailTrace_542948 : CollatzResearch.WordTrace tailWord_542948 prefixEnd_542948 41302710281103251430079 := by
  unfold tailWord_542948
  simp only [CollatzResearch.WordTrace]
  refine ⟨9901470218499799490522749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13201960291333065987363665 9901470218499799490522749)
  ·
    refine ⟨3713051331937424808946031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9901470218499799490522749 3713051331937424808946031)
    ·
      refine ⟨5569576997906137213419047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3713051331937424808946031 5569576997906137213419047)
      ·
        refine ⟨8354365496859205820128571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5569576997906137213419047 8354365496859205820128571)
        ·
          refine ⟨12531548245288808730192857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8354365496859205820128571 12531548245288808730192857)
          ·
            refine ⟨9398661183966606547644643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12531548245288808730192857 9398661183966606547644643)
            ·
              refine ⟨14097991775949909821466965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9398661183966606547644643 14097991775949909821466965)
              ·
                refine ⟨41302710281103251430079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 14097991775949909821466965 41302710281103251430079)
                ·
                  rfl

theorem cell21_542948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 10].length) (baseStart_542948 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_542948 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_542948 prefixEnd_542948 := by exact prefixLift 542948
  have htrace : WordTrace (prefixWord ++ tailWord_542948) baseStart_542948 baseEnd_542948 := by
    simpa [prefixWord, tailWord_542948, baseEnd_542948] using wordTrace_append hprefix tailTrace_542948
  have hstable : (prefixWord ++ tailWord_542948).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542948).length < 2 ^ (prefixWord ++ tailWord_542948).sum := by decide
  have hdescent : baseEnd_542948 < baseStart_542948 := by decide
  rcases family_descends (prefixWord ++ tailWord_542948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543041 : List Nat := [1, 2, 5, 2, 2, 9]
def baseStart_543041 : Nat := 118140960795 + 543041 * 2 ^ 59
def prefixEnd_543041 : Nat := 4983230072969 + 3 ^ 40 * 543041 * 2
def baseEnd_543041 : Nat := 4589976100383787379261

theorem tailTrace_543041 : CollatzResearch.WordTrace tailWord_543041 prefixEnd_543041 4589976100383787379261 := by
  unfold tailWord_543041
  simp only [CollatzResearch.WordTrace]
  refine ⟨19806332425662675864180977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13204221617108450576120651 19806332425662675864180977)
  ·
    refine ⟨14854749319247006898135733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19806332425662675864180977 14854749319247006898135733)
    ·
      refine ⟨1392632748679406896700225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14854749319247006898135733 1392632748679406896700225)
      ·
        refine ⟨1044474561509555172525169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1392632748679406896700225 1044474561509555172525169)
        ·
          refine ⟨783355921132166379393877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1044474561509555172525169 783355921132166379393877)
          ·
            refine ⟨4589976100383787379261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 783355921132166379393877 4589976100383787379261)
            ·
              rfl

theorem cell21_543041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 9].length) (baseStart_543041 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_543041 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_543041 prefixEnd_543041 := by exact prefixLift 543041
  have htrace : WordTrace (prefixWord ++ tailWord_543041) baseStart_543041 baseEnd_543041 := by
    simpa [prefixWord, tailWord_543041, baseEnd_543041] using wordTrace_append hprefix tailTrace_543041
  have hstable : (prefixWord ++ tailWord_543041).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543041).length < 2 ^ (prefixWord ++ tailWord_543041).sum := by decide
  have hdescent : baseEnd_543041 < baseStart_543041 := by decide
  rcases family_descends (prefixWord ++ tailWord_543041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543072 : List Nat := [2, 1, 1, 3, 5, 1, 1, 2, 5]
def baseStart_543072 : Nat := 118140960795 + 543072 * 2 ^ 59
def prefixEnd_543072 : Nat := 4983230072969 + 3 ^ 40 * 543072 * 2
def baseEnd_543072 : Nat := 123936429332713094223317

theorem tailTrace_543072 : CollatzResearch.WordTrace tailWord_543072 prefixEnd_543072 123936429332713094223317 := by
  unfold tailWord_543072
  simp only [CollatzResearch.WordTrace]
  refine ⟨9903731544275184079279735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13204975392366912105706313 9903731544275184079279735)
  ·
    refine ⟨14855597316412776118919603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9903731544275184079279735 14855597316412776118919603)
    ·
      refine ⟨22283395974619164178379405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14855597316412776118919603 22283395974619164178379405)
      ·
        refine ⟨8356273490482186566892277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22283395974619164178379405 8356273490482186566892277)
        ·
          refine ⟨783400639732704990646151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8356273490482186566892277 783400639732704990646151)
          ·
            refine ⟨1175100959599057485969227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 783400639732704990646151 1175100959599057485969227)
            ·
              refine ⟨1762651439398586228953841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1175100959599057485969227 1762651439398586228953841)
              ·
                refine ⟨1321988579548939671715381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1762651439398586228953841 1321988579548939671715381)
                ·
                  refine ⟨123936429332713094223317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1321988579548939671715381 123936429332713094223317)
                  ·
                    rfl

theorem cell21_543072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 2, 5].length) (baseStart_543072 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_543072 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_543072 prefixEnd_543072 := by exact prefixLift 543072
  have htrace : WordTrace (prefixWord ++ tailWord_543072) baseStart_543072 baseEnd_543072 := by
    simpa [prefixWord, tailWord_543072, baseEnd_543072] using wordTrace_append hprefix tailTrace_543072
  have hstable : (prefixWord ++ tailWord_543072).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543072).length < 2 ^ (prefixWord ++ tailWord_543072).sum := by decide
  have hdescent : baseEnd_543072 < baseStart_543072 := by decide
  rcases family_descends (prefixWord ++ tailWord_543072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543106 : List Nat := [3, 4, 2, 1, 2, 1, 2, 1, 5]
def baseStart_543106 : Nat := 118140960795 + 543106 * 2 ^ 59
def prefixEnd_543106 : Nat := 4983230072969 + 3 ^ 40 * 543106 * 2
def baseEnd_543106 : Nat := 123944188595936590656581

theorem tailTrace_543106 : CollatzResearch.WordTrace tailWord_543106 prefixEnd_543106 123944188595936590656581 := by
  unfold tailWord_543106
  simp only [CollatzResearch.WordTrace]
  refine ⟨4952175792606797991324293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13205802113618127976864781 4952175792606797991324293)
  ·
    refine ⟨928532961113774623373305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4952175792606797991324293 928532961113774623373305)
    ·
      refine ⟨696399720835330967529979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 928532961113774623373305 696399720835330967529979)
      ·
        refine ⟨1044599581252996451294969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 696399720835330967529979 1044599581252996451294969)
        ·
          refine ⟨783449685939747338471227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1044599581252996451294969 783449685939747338471227)
          ·
            refine ⟨1175174528909621007706841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 783449685939747338471227 1175174528909621007706841)
            ·
              refine ⟨881380896682215755780131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1175174528909621007706841 881380896682215755780131)
              ·
                refine ⟨1322071345023323633670197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 881380896682215755780131 1322071345023323633670197)
                ·
                  refine ⟨123944188595936590656581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1322071345023323633670197 123944188595936590656581)
                  ·
                    rfl

theorem cell21_543106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 2, 1, 5].length) (baseStart_543106 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_543106 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_543106 prefixEnd_543106 := by exact prefixLift 543106
  have htrace : WordTrace (prefixWord ++ tailWord_543106) baseStart_543106 baseEnd_543106 := by
    simpa [prefixWord, tailWord_543106, baseEnd_543106] using wordTrace_append hprefix tailTrace_543106
  have hstable : (prefixWord ++ tailWord_543106).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543106).length < 2 ^ (prefixWord ++ tailWord_543106).sum := by decide
  have hdescent : baseEnd_543106 < baseStart_543106 := by decide
  rcases family_descends (prefixWord ++ tailWord_543106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543126 : List Nat := [5, 3, 1, 2, 2, 1, 2, 5]
def baseStart_543126 : Nat := 118140960795 + 543126 * 2 ^ 59
def prefixEnd_543126 : Nat := 4983230072969 + 3 ^ 40 * 543126 * 2
def baseEnd_543126 : Nat := 41316250956140333441069

theorem tailTrace_543126 : CollatzResearch.WordTrace tailWord_543126 prefixEnd_543126 41316250956140333441069 := by
  unfold tailWord_543126
  simp only [CollatzResearch.WordTrace]
  refine ⟨1238089539397170961314077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13206288420236490254016821 1238089539397170961314077)
  ·
    refine ⟨464283577273939110492779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1238089539397170961314077 464283577273939110492779)
    ·
      refine ⟨696425365910908665739169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 464283577273939110492779 696425365910908665739169)
      ·
        refine ⟨522319024433181499304377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 696425365910908665739169 522319024433181499304377)
        ·
          refine ⟨391739268324886124478283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 522319024433181499304377 391739268324886124478283)
          ·
            refine ⟨587608902487329186717425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 391739268324886124478283 587608902487329186717425)
            ·
              refine ⟨440706676865496890038069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 587608902487329186717425 440706676865496890038069)
              ·
                refine ⟨41316250956140333441069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 440706676865496890038069 41316250956140333441069)
                ·
                  rfl

theorem cell21_543126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 2, 5].length) (baseStart_543126 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_543126 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_543126 prefixEnd_543126 := by exact prefixLift 543126
  have htrace : WordTrace (prefixWord ++ tailWord_543126) baseStart_543126 baseEnd_543126 := by
    simpa [prefixWord, tailWord_543126, baseEnd_543126] using wordTrace_append hprefix tailTrace_543126
  have hstable : (prefixWord ++ tailWord_543126).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543126).length < 2 ^ (prefixWord ++ tailWord_543126).sum := by decide
  have hdescent : baseEnd_543126 < baseStart_543126 := by decide
  rcases family_descends (prefixWord ++ tailWord_543126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543134 : List Nat := [4, 3, 1, 2, 1, 2, 1, 7]
def baseStart_543134 : Nat := 118140960795 + 543134 * 2 ^ 59
def prefixEnd_543134 : Nat := 4983230072969 + 3 ^ 40 * 543134 * 2
def baseEnd_543134 : Nat := 41316859525804921396619

theorem tailTrace_543134 : CollatzResearch.WordTrace tailWord_543134 prefixEnd_543134 41316859525804921396619 := by
  unfold tailWord_543134
  simp only [CollatzResearch.WordTrace]
  refine ⟨2476215551790719093414557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13206482942883835164877637 2476215551790719093414557)
  ·
    refine ⟨928580831921519660030459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2476215551790719093414557 928580831921519660030459)
    ·
      refine ⟨1392871247882279490045689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 928580831921519660030459 1392871247882279490045689)
      ·
        refine ⟨1044653435911709617534267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1392871247882279490045689 1044653435911709617534267)
        ·
          refine ⟨1566980153867564426301401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1044653435911709617534267 1566980153867564426301401)
          ·
            refine ⟨1175235115400673319726051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1566980153867564426301401 1175235115400673319726051)
            ·
              refine ⟨1762852673101009979589077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1175235115400673319726051 1762852673101009979589077)
              ·
                refine ⟨41316859525804921396619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1762852673101009979589077 41316859525804921396619)
                ·
                  rfl

theorem cell21_543134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 7].length) (baseStart_543134 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_543134 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_543134 prefixEnd_543134 := by exact prefixLift 543134
  have htrace : WordTrace (prefixWord ++ tailWord_543134) baseStart_543134 baseEnd_543134 := by
    simpa [prefixWord, tailWord_543134, baseEnd_543134] using wordTrace_append hprefix tailTrace_543134
  have hstable : (prefixWord ++ tailWord_543134).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543134).length < 2 ^ (prefixWord ++ tailWord_543134).sum := by decide
  have hdescent : baseEnd_543134 < baseStart_543134 := by decide
  rcases family_descends (prefixWord ++ tailWord_543134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543176 : List Nat := [2, 1, 3, 1, 3, 2, 1, 8]
def baseStart_543176 : Nat := 118140960795 + 543176 * 2 ^ 59
def prefixEnd_543176 : Nat := 4983230072969 + 3 ^ 40 * 543176 * 2
def baseEnd_543176 : Nat := 41320054516544008163257

theorem tailTrace_543176 : CollatzResearch.WordTrace tailWord_543176 prefixEnd_543176 41320054516544008163257 := by
  unfold tailWord_543176
  simp only [CollatzResearch.WordTrace]
  refine ⟨9905628140086796960172691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13207504186782395946896921 9905628140086796960172691)
  ·
    refine ⟨14858442210130195440259037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9905628140086796960172691 14858442210130195440259037)
    ·
      refine ⟨5571915828798823290097139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14858442210130195440259037 5571915828798823290097139)
      ·
        refine ⟨8357873743198234935145709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5571915828798823290097139 8357873743198234935145709)
        ·
          refine ⟨3134202653699338100679641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8357873743198234935145709 3134202653699338100679641)
          ·
            refine ⟨2350651990274503575509731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3134202653699338100679641 2350651990274503575509731)
            ·
              refine ⟨3525977985411755363264597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2350651990274503575509731 3525977985411755363264597)
              ·
                refine ⟨41320054516544008163257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3525977985411755363264597 41320054516544008163257)
                ·
                  rfl

theorem cell21_543176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 8].length) (baseStart_543176 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_543176 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_543176 prefixEnd_543176 := by exact prefixLift 543176
  have htrace : WordTrace (prefixWord ++ tailWord_543176) baseStart_543176 baseEnd_543176 := by
    simpa [prefixWord, tailWord_543176, baseEnd_543176] using wordTrace_append hprefix tailTrace_543176
  have hstable : (prefixWord ++ tailWord_543176).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543176).length < 2 ^ (prefixWord ++ tailWord_543176).sum := by decide
  have hdescent : baseEnd_543176 < baseStart_543176 := by decide
  rcases family_descends (prefixWord ++ tailWord_543176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543224 : List Nat := [2, 1, 2, 1, 1, 4, 3, 4, 3]
def baseStart_543224 : Nat := 118140960795 + 543224 * 2 ^ 59
def prefixEnd_543224 : Nat := 4983230072969 + 3 ^ 40 * 543224 * 2
def baseEnd_543224 : Nat := 123971117803594607689673

theorem tailTrace_543224 : CollatzResearch.WordTrace tailWord_543224 prefixEnd_543224 123971117803594607689673 := by
  unfold tailWord_543224
  simp only [CollatzResearch.WordTrace]
  refine ⟨9906503491999849059046363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13208671322666465412061817 9906503491999849059046363)
  ·
    refine ⟨14859755237999773588569545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9906503491999849059046363 14859755237999773588569545)
    ·
      refine ⟨11144816428499830191427159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14859755237999773588569545 11144816428499830191427159)
      ·
        refine ⟨16717224642749745287140739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11144816428499830191427159 16717224642749745287140739)
        ·
          refine ⟨25075836964124617930711109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16717224642749745287140739 25075836964124617930711109)
          ·
            refine ⟨4701719430773365862008333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25075836964124617930711109 4701719430773365862008333)
            ·
              refine ⟨1763144786540012198253125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4701719430773365862008333 1763144786540012198253125)
              ·
                refine ⟨330589647476252287172461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1763144786540012198253125 330589647476252287172461)
                ·
                  refine ⟨123971117803594607689673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 330589647476252287172461 123971117803594607689673)
                  ·
                    rfl

theorem cell21_543224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 4, 3].length) (baseStart_543224 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_543224 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_543224 prefixEnd_543224 := by exact prefixLift 543224
  have htrace : WordTrace (prefixWord ++ tailWord_543224) baseStart_543224 baseEnd_543224 := by
    simpa [prefixWord, tailWord_543224, baseEnd_543224] using wordTrace_append hprefix tailTrace_543224
  have hstable : (prefixWord ++ tailWord_543224).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543224).length < 2 ^ (prefixWord ++ tailWord_543224).sum := by decide
  have hdescent : baseEnd_543224 < baseStart_543224 := by decide
  rcases family_descends (prefixWord ++ tailWord_543224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543272 : List Nat := [2, 1, 5, 2, 1, 3, 1, 2, 4]
def baseStart_543272 : Nat := 118140960795 + 543272 * 2 ^ 59
def prefixEnd_543272 : Nat := 4983230072969 + 3 ^ 40 * 543272 * 2
def baseEnd_543272 : Nat := 123982072057557190889575

theorem tailTrace_543272 : CollatzResearch.WordTrace tailWord_543272 prefixEnd_543272 123982072057557190889575 := by
  unfold tailWord_543272
  simp only [CollatzResearch.WordTrace]
  refine ⟨9907378843912901157920035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13209838458550534877226713 9907378843912901157920035)
  ·
    refine ⟨14861068265869351736880053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9907378843912901157920035 14861068265869351736880053)
    ·
      refine ⟨1393225149925251725332505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14861068265869351736880053 1393225149925251725332505)
      ·
        refine ⟨1044918862443938793999379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1393225149925251725332505 1044918862443938793999379)
        ·
          refine ⟨1567378293665908190999069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1044918862443938793999379 1567378293665908190999069)
          ·
            refine ⟨587766860124715571624651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1567378293665908190999069 587766860124715571624651)
            ·
              refine ⟨881650290187073357436977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 587766860124715571624651 881650290187073357436977)
              ·
                refine ⟨661237717640305018077733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 881650290187073357436977 661237717640305018077733)
                ·
                  refine ⟨123982072057557190889575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 661237717640305018077733 123982072057557190889575)
                  ·
                    rfl

theorem cell21_543272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 1, 2, 4].length) (baseStart_543272 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_543272 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_543272 prefixEnd_543272 := by exact prefixLift 543272
  have htrace : WordTrace (prefixWord ++ tailWord_543272) baseStart_543272 baseEnd_543272 := by
    simpa [prefixWord, tailWord_543272, baseEnd_543272] using wordTrace_append hprefix tailTrace_543272
  have hstable : (prefixWord ++ tailWord_543272).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543272).length < 2 ^ (prefixWord ++ tailWord_543272).sum := by decide
  have hdescent : baseEnd_543272 < baseStart_543272 := by decide
  rcases family_descends (prefixWord ++ tailWord_543272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543283 : List Nat := [1, 1, 1, 2, 4, 2, 4, 1, 5]
def baseStart_543283 : Nat := 118140960795 + 543283 * 2 ^ 59
def prefixEnd_543283 : Nat := 4983230072969 + 3 ^ 40 * 543283 * 2
def baseEnd_543283 : Nat := 123984582407423616206219

theorem tailTrace_543283 : CollatzResearch.WordTrace tailWord_543283 prefixEnd_543283 123984582407423616206219 := by
  unfold tailWord_543283
  simp only [CollatzResearch.WordTrace]
  refine ⟨19815158890785951194490503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13210105927190634129660335 19815158890785951194490503)
  ·
    refine ⟨29722738336178926791735755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19815158890785951194490503 29722738336178926791735755)
    ·
      refine ⟨44584107504268390187603633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29722738336178926791735755 44584107504268390187603633)
      ·
        refine ⟨33438080628201292640702725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44584107504268390187603633 33438080628201292640702725)
        ·
          refine ⟨6269640117787742370131761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33438080628201292640702725 6269640117787742370131761)
          ·
            refine ⟨4702230088340806777598821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6269640117787742370131761 4702230088340806777598821)
            ·
              refine ⟨881668141563901270799779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4702230088340806777598821 881668141563901270799779)
              ·
                refine ⟨1322502212345851906199669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 881668141563901270799779 1322502212345851906199669)
                ·
                  refine ⟨123984582407423616206219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1322502212345851906199669 123984582407423616206219)
                  ·
                    rfl

theorem cell21_543283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 4, 1, 5].length) (baseStart_543283 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_543283 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_543283 prefixEnd_543283 := by exact prefixLift 543283
  have htrace : WordTrace (prefixWord ++ tailWord_543283) baseStart_543283 baseEnd_543283 := by
    simpa [prefixWord, tailWord_543283, baseEnd_543283] using wordTrace_append hprefix tailTrace_543283
  have hstable : (prefixWord ++ tailWord_543283).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543283).length < 2 ^ (prefixWord ++ tailWord_543283).sum := by decide
  have hdescent : baseEnd_543283 < baseStart_543283 := by decide
  rcases family_descends (prefixWord ++ tailWord_543283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543393 : List Nat := [1, 2, 3, 3, 3, 1, 1, 4, 3]
def baseStart_543393 : Nat := 118140960795 + 543393 * 2 ^ 59
def prefixEnd_543393 : Nat := 4983230072969 + 3 ^ 40 * 543393 * 2
def baseEnd_543393 : Nat := 124009685906087869372661

theorem tailTrace_543393 : CollatzResearch.WordTrace tailWord_543393 prefixEnd_543393 124009685906087869372661 := by
  unfold tailWord_543393
  simp only [CollatzResearch.WordTrace]
  refine ⟨19819170920387439980994833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13212780613591626653996555 19819170920387439980994833)
  ·
    refine ⟨14864378190290579985746125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19819170920387439980994833 14864378190290579985746125)
    ·
      refine ⟨5574141821358967494654797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14864378190290579985746125 5574141821358967494654797)
      ·
        refine ⟨2090303183009612810495549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5574141821358967494654797 2090303183009612810495549)
        ·
          refine ⟨783863693628604803935831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2090303183009612810495549 783863693628604803935831)
          ·
            refine ⟨1175795540442907205903747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 783863693628604803935831 1175795540442907205903747)
            ·
              refine ⟨1763693310664360808855621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1175795540442907205903747 1763693310664360808855621)
              ·
                refine ⟨330692495749567651660429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1763693310664360808855621 330692495749567651660429)
                ·
                  refine ⟨124009685906087869372661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 330692495749567651660429 124009685906087869372661)
                  ·
                    rfl

theorem cell21_543393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 4, 3].length) (baseStart_543393 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_543393 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_543393 prefixEnd_543393 := by exact prefixLift 543393
  have htrace : WordTrace (prefixWord ++ tailWord_543393) baseStart_543393 baseEnd_543393 := by
    simpa [prefixWord, tailWord_543393, baseEnd_543393] using wordTrace_append hprefix tailTrace_543393
  have hstable : (prefixWord ++ tailWord_543393).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543393).length < 2 ^ (prefixWord ++ tailWord_543393).sum := by decide
  have hdescent : baseEnd_543393 < baseStart_543393 := by decide
  rcases family_descends (prefixWord ++ tailWord_543393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543421 : List Nat := [1, 4, 1, 2, 1, 4, 3, 5]
def baseStart_543421 : Nat := 118140960795 + 543421 * 2 ^ 59
def prefixEnd_543421 : Nat := 4983230072969 + 3 ^ 40 * 543421 * 2
def baseEnd_543421 : Nat := 41338691962522014301979

theorem tailTrace_543421 : CollatzResearch.WordTrace tailWord_543421 prefixEnd_543421 41338691962522014301979 := by
  unfold tailWord_543421
  simp only [CollatzResearch.WordTrace]
  refine ⟨19820192164286000763014117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13213461442857333842009411 19820192164286000763014117)
  ·
    refine ⟨3716286030803625143065147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19820192164286000763014117 3716286030803625143065147)
    ·
      refine ⟨5574429046205437714597721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3716286030803625143065147 5574429046205437714597721)
      ·
        refine ⟨4180821784654078285948291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5574429046205437714597721 4180821784654078285948291)
        ·
          refine ⟨6271232676981117428922437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4180821784654078285948291 6271232676981117428922437)
          ·
            refine ⟨1175856126933959517922957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6271232676981117428922437 1175856126933959517922957)
            ·
              refine ⟨440946047600234819221109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1175856126933959517922957 440946047600234819221109)
              ·
                refine ⟨41338691962522014301979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 440946047600234819221109 41338691962522014301979)
                ·
                  rfl

theorem cell21_543421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 3, 5].length) (baseStart_543421 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_543421 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_543421 prefixEnd_543421 := by exact prefixLift 543421
  have htrace : WordTrace (prefixWord ++ tailWord_543421) baseStart_543421 baseEnd_543421 := by
    simpa [prefixWord, tailWord_543421, baseEnd_543421] using wordTrace_append hprefix tailTrace_543421
  have hstable : (prefixWord ++ tailWord_543421).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543421).length < 2 ^ (prefixWord ++ tailWord_543421).sum := by decide
  have hdescent : baseEnd_543421 < baseStart_543421 := by decide
  rcases family_descends (prefixWord ++ tailWord_543421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543449 : List Nat := [1, 2, 1, 2, 3, 2, 3, 1, 6]
def baseStart_543449 : Nat := 118140960795 + 543449 * 2 ^ 59
def prefixEnd_543449 : Nat := 4983230072969 + 3 ^ 40 * 543449 * 2
def baseEnd_543449 : Nat := 124022465869044216439213

theorem tailTrace_543449 : CollatzResearch.WordTrace tailWord_543449 prefixEnd_543449 124022465869044216439213 := by
  unfold tailWord_543449
  simp only [CollatzResearch.WordTrace]
  refine ⟨19821213408184561545033401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13214142272123041030022267 19821213408184561545033401)
  ·
    refine ⟨14865910056138421158775051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19821213408184561545033401 14865910056138421158775051)
    ·
      refine ⟨22298865084207631738162577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14865910056138421158775051 22298865084207631738162577)
      ·
        refine ⟨16724148813155723803621933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22298865084207631738162577 16724148813155723803621933)
        ·
          refine ⟨6271555804933396426358225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16724148813155723803621933 6271555804933396426358225)
          ·
            refine ⟨4703666853700047319768669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6271555804933396426358225 4703666853700047319768669)
            ·
              refine ⟨1763875070137517744913251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4703666853700047319768669 1763875070137517744913251)
              ·
                refine ⟨2645812605206276617369877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1763875070137517744913251 2645812605206276617369877)
                ·
                  refine ⟨124022465869044216439213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2645812605206276617369877 124022465869044216439213)
                  ·
                    rfl

theorem cell21_543449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 1, 6].length) (baseStart_543449 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_543449 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_543449 prefixEnd_543449 := by exact prefixLift 543449
  have htrace : WordTrace (prefixWord ++ tailWord_543449) baseStart_543449 baseEnd_543449 := by
    simpa [prefixWord, tailWord_543449, baseEnd_543449] using wordTrace_append hprefix tailTrace_543449
  have hstable : (prefixWord ++ tailWord_543449).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543449).length < 2 ^ (prefixWord ++ tailWord_543449).sum := by decide
  have hdescent : baseEnd_543449 < baseStart_543449 := by decide
  rcases family_descends (prefixWord ++ tailWord_543449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543452 : List Nat := [2, 2, 5, 1, 1, 1, 1, 3, 5]
def baseStart_543452 : Nat := 118140960795 + 543452 * 2 ^ 59
def prefixEnd_543452 : Nat := 4983230072969 + 3 ^ 40 * 543452 * 2
def baseEnd_543452 : Nat := 124023150509916877889207

theorem tailTrace_543452 : CollatzResearch.WordTrace tailWord_543452 prefixEnd_543452 124023150509916877889207 := by
  unfold tailWord_543452
  simp only [CollatzResearch.WordTrace]
  refine ⟨9910661413586846528696305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13214215218115795371595073 9910661413586846528696305)
  ·
    refine ⟨7432996060190134896522229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9910661413586846528696305 7432996060190134896522229)
    ·
      refine ⟨696843380642825146548959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7432996060190134896522229 696843380642825146548959)
      ·
        refine ⟨1045265070964237719823439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 696843380642825146548959 1045265070964237719823439)
        ·
          refine ⟨1567897606446356579735159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1045265070964237719823439 1567897606446356579735159)
          ·
            refine ⟨2351846409669534869602739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1567897606446356579735159 2351846409669534869602739)
            ·
              refine ⟨3527769614504302304404109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2351846409669534869602739 3527769614504302304404109)
              ·
                refine ⟨1322913605439113364151541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3527769614504302304404109 1322913605439113364151541)
                ·
                  refine ⟨124023150509916877889207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1322913605439113364151541 124023150509916877889207)
                  ·
                    rfl

theorem cell21_543452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 3, 5].length) (baseStart_543452 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_543452 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_543452 prefixEnd_543452 := by exact prefixLift 543452
  have htrace : WordTrace (prefixWord ++ tailWord_543452) baseStart_543452 baseEnd_543452 := by
    simpa [prefixWord, tailWord_543452, baseEnd_543452] using wordTrace_append hprefix tailTrace_543452
  have hstable : (prefixWord ++ tailWord_543452).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543452).length < 2 ^ (prefixWord ++ tailWord_543452).sum := by decide
  have hdescent : baseEnd_543452 < baseStart_543452 := by decide
  rcases family_descends (prefixWord ++ tailWord_543452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543486 : List Nat := [4, 2, 2, 1, 2, 3, 1, 3, 3]
def baseStart_543486 : Nat := 118140960795 + 543486 * 2 ^ 59
def prefixEnd_543486 : Nat := 4983230072969 + 3 ^ 40 * 543486 * 2
def baseEnd_543486 : Nat := 124030909773140374322471

theorem tailTrace_543486 : CollatzResearch.WordTrace tailWord_543486 prefixEnd_543486 124030909773140374322471 := by
  unfold tailWord_543486
  simp only [CollatzResearch.WordTrace]
  refine ⟨2477820363631314608016289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13215041939367011242753541 2477820363631314608016289)
  ·
    refine ⟨1858365272723485956012217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2477820363631314608016289 1858365272723485956012217)
    ·
      refine ⟨1393773954542614467009163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1858365272723485956012217 1393773954542614467009163)
      ·
        refine ⟨2090660931813921700513745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1393773954542614467009163 2090660931813921700513745)
        ·
          refine ⟨1567995698860441275385309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2090660931813921700513745 1567995698860441275385309)
          ·
            refine ⟨587998387072665478269491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1567995698860441275385309 587998387072665478269491)
            ·
              refine ⟨881997580608998217404237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 587998387072665478269491 881997580608998217404237)
              ·
                refine ⟨330749092728374331526589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 881997580608998217404237 330749092728374331526589)
                ·
                  refine ⟨124030909773140374322471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 330749092728374331526589 124030909773140374322471)
                  ·
                    rfl

theorem cell21_543486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 1, 3, 3].length) (baseStart_543486 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_543486 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_543486 prefixEnd_543486 := by exact prefixLift 543486
  have htrace : WordTrace (prefixWord ++ tailWord_543486) baseStart_543486 baseEnd_543486 := by
    simpa [prefixWord, tailWord_543486, baseEnd_543486] using wordTrace_append hprefix tailTrace_543486
  have hstable : (prefixWord ++ tailWord_543486).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543486).length < 2 ^ (prefixWord ++ tailWord_543486).sum := by decide
  have hdescent : baseEnd_543486 < baseStart_543486 := by decide
  rcases family_descends (prefixWord ++ tailWord_543486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543517 : List Nat := [1, 4, 2, 4, 1, 2, 2, 1, 4]
def baseStart_543517 : Nat := 118140960795 + 543517 * 2 ^ 59
def prefixEnd_543517 : Nat := 4983230072969 + 3 ^ 40 * 543517 * 2
def baseEnd_543517 : Nat := 124037984395491209305741

theorem tailTrace_543517 : CollatzResearch.WordTrace tailWord_543517 prefixEnd_543517 124037984395491209305741 := by
  unfold tailWord_543517
  simp only [CollatzResearch.WordTrace]
  refine ⟨19823693571938209158508805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13215795714625472772339203 19823693571938209158508805)
  ·
    refine ⟨3716942544738414217220401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19823693571938209158508805 3716942544738414217220401)
    ·
      refine ⟨2787706908553810662915301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3716942544738414217220401 2787706908553810662915301)
      ·
        refine ⟨522695045353839499296619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2787706908553810662915301 522695045353839499296619)
        ·
          refine ⟨784042568030759248944929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 522695045353839499296619 784042568030759248944929)
          ·
            refine ⟨588031926023069436708697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 784042568030759248944929 588031926023069436708697)
            ·
              refine ⟨441023944517302077531523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 588031926023069436708697 441023944517302077531523)
              ·
                refine ⟨661535916775953116297285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 441023944517302077531523 661535916775953116297285)
                ·
                  refine ⟨124037984395491209305741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 661535916775953116297285 124037984395491209305741)
                  ·
                    rfl

theorem cell21_543517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 2, 1, 4].length) (baseStart_543517 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_543517 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_543517 prefixEnd_543517 := by exact prefixLift 543517
  have htrace : WordTrace (prefixWord ++ tailWord_543517) baseStart_543517 baseEnd_543517 := by
    simpa [prefixWord, tailWord_543517, baseEnd_543517] using wordTrace_append hprefix tailTrace_543517
  have hstable : (prefixWord ++ tailWord_543517).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543517).length < 2 ^ (prefixWord ++ tailWord_543517).sum := by decide
  have hdescent : baseEnd_543517 < baseStart_543517 := by decide
  rcases family_descends (prefixWord ++ tailWord_543517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543587 : List Nat := [1, 1, 1, 5, 3, 2, 1, 2, 5]
def baseStart_543587 : Nat := 118140960795 + 543587 * 2 ^ 59
def prefixEnd_543587 : Nat := 4983230072969 + 3 ^ 40 * 543587 * 2
def baseEnd_543587 : Nat := 124053959349186643138931

theorem tailTrace_543587 : CollatzResearch.WordTrace tailWord_543587 prefixEnd_543587 124053959349186643138931 := by
  unfold tailWord_543587
  simp only [CollatzResearch.WordTrace]
  refine ⟨19826246681684611113557015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13217497787789740742371343 19826246681684611113557015)
  ·
    refine ⟨29739370022526916670335523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19826246681684611113557015 29739370022526916670335523)
    ·
      refine ⟨44609055033790375005503285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29739370022526916670335523 44609055033790375005503285)
      ·
        refine ⟨4182098909417847656765933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 44609055033790375005503285 4182098909417847656765933)
        ·
          refine ⟨1568287091031692871287225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4182098909417847656765933 1568287091031692871287225)
          ·
            refine ⟨1176215318273769653465419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1568287091031692871287225 1176215318273769653465419)
            ·
              refine ⟨1764322977410654480198129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1176215318273769653465419 1764322977410654480198129)
              ·
                refine ⟨1323242233057990860148597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1764322977410654480198129 1323242233057990860148597)
                ·
                  refine ⟨124053959349186643138931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1323242233057990860148597 124053959349186643138931)
                  ·
                    rfl

theorem cell21_543587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 2, 5].length) (baseStart_543587 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_543587 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_543587 prefixEnd_543587 := by exact prefixLift 543587
  have htrace : WordTrace (prefixWord ++ tailWord_543587) baseStart_543587 baseEnd_543587 := by
    simpa [prefixWord, tailWord_543587, baseEnd_543587] using wordTrace_append hprefix tailTrace_543587
  have hstable : (prefixWord ++ tailWord_543587).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543587).length < 2 ^ (prefixWord ++ tailWord_543587).sum := by decide
  have hdescent : baseEnd_543587 < baseStart_543587 := by decide
  rcases family_descends (prefixWord ++ tailWord_543587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543649 : List Nat := [1, 2, 3, 4, 1, 1, 4, 5]
def baseStart_543649 : Nat := 118140960795 + 543649 * 2 ^ 59
def prefixEnd_543649 : Nat := 4983230072969 + 3 ^ 40 * 543649 * 2
def baseEnd_543649 : Nat := 41356036197962771035157

theorem tailTrace_543649 : CollatzResearch.WordTrace tailWord_543649 prefixEnd_543649 41356036197962771035157 := by
  unfold tailWord_543649
  simp only [CollatzResearch.WordTrace]
  refine ⟨19828508007459995702314001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13219005338306663801542667 19828508007459995702314001)
  ·
    refine ⟨14871381005594996776735501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19828508007459995702314001 14871381005594996776735501)
    ·
      refine ⟨5576767877098123791275813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14871381005594996776735501 5576767877098123791275813)
      ·
        refine ⟨1045643976955898210864215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5576767877098123791275813 1045643976955898210864215)
        ·
          refine ⟨1568465965433847316296323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1045643976955898210864215 1568465965433847316296323)
          ·
            refine ⟨2352698948150770974444485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1568465965433847316296323 2352698948150770974444485)
            ·
              refine ⟨441131052778269557708341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2352698948150770974444485 441131052778269557708341)
              ·
                refine ⟨41356036197962771035157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 441131052778269557708341 41356036197962771035157)
                ·
                  rfl

theorem cell21_543649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 4, 5].length) (baseStart_543649 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_543649 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_543649 prefixEnd_543649 := by exact prefixLift 543649
  have htrace : WordTrace (prefixWord ++ tailWord_543649) baseStart_543649 baseEnd_543649 := by
    simpa [prefixWord, tailWord_543649, baseEnd_543649] using wordTrace_append hprefix tailTrace_543649
  have hstable : (prefixWord ++ tailWord_543649).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543649).length < 2 ^ (prefixWord ++ tailWord_543649).sum := by decide
  have hdescent : baseEnd_543649 < baseStart_543649 := by decide
  rcases family_descends (prefixWord ++ tailWord_543649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543663 : List Nat := [1, 1, 2, 1, 2, 2, 2, 7, 3]
def baseStart_543663 : Nat := 118140960795 + 543663 * 2 ^ 59
def prefixEnd_543663 : Nat := 4983230072969 + 3 ^ 40 * 543663 * 2
def baseEnd_543663 : Nat := 124071303584627399872109

theorem tailTrace_543663 : CollatzResearch.WordTrace tailWord_543663 prefixEnd_543663 124071303584627399872109 := by
  unfold tailWord_543663
  simp only [CollatzResearch.WordTrace]
  refine ⟨19829018629409276093323643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13219345752939517395549095 19829018629409276093323643)
  ·
    refine ⟨29743527944113914139985465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19829018629409276093323643 29743527944113914139985465)
    ·
      refine ⟨22307645958085435604989099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29743527944113914139985465 22307645958085435604989099)
      ·
        refine ⟨33461468937128153407483649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22307645958085435604989099 33461468937128153407483649)
        ·
          refine ⟨25096101702846115055612737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33461468937128153407483649 25096101702846115055612737)
          ·
            refine ⟨18822076277134586291709553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25096101702846115055612737 18822076277134586291709553)
            ·
              refine ⟨14116557207850939718782165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18822076277134586291709553 14116557207850939718782165)
              ·
                refine ⟨330856809559006399658957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 14116557207850939718782165 330856809559006399658957)
                ·
                  refine ⟨124071303584627399872109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 330856809559006399658957 124071303584627399872109)
                  ·
                    rfl

theorem cell21_543663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 7, 3].length) (baseStart_543663 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_543663 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_543663 prefixEnd_543663 := by exact prefixLift 543663
  have htrace : WordTrace (prefixWord ++ tailWord_543663) baseStart_543663 baseEnd_543663 := by
    simpa [prefixWord, tailWord_543663, baseEnd_543663] using wordTrace_append hprefix tailTrace_543663
  have hstable : (prefixWord ++ tailWord_543663).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543663).length < 2 ^ (prefixWord ++ tailWord_543663).sum := by decide
  have hdescent : baseEnd_543663 < baseStart_543663 := by decide
  rcases family_descends (prefixWord ++ tailWord_543663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543686 : List Nat := [6, 1, 3, 1, 1, 1, 1, 3, 4]
def baseStart_543686 : Nat := 118140960795 + 543686 * 2 ^ 59
def prefixEnd_543686 : Nat := 4983230072969 + 3 ^ 40 * 543686 * 2
def baseEnd_543686 : Nat := 124076552497984470988729

theorem tailTrace_543686 : CollatzResearch.WordTrace tailWord_543686 prefixEnd_543686 124076552497984470988729 := by
  unfold tailWord_543686
  simp only [CollatzResearch.WordTrace]
  refine ⟨619683047135185969419091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 13219905005550634014273941 619683047135185969419091)
  ·
    refine ⟨929524570702778954128637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 619683047135185969419091 929524570702778954128637)
    ·
      refine ⟨348571714013542107798239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 929524570702778954128637 348571714013542107798239)
      ·
        refine ⟨522857571020313161697359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 348571714013542107798239 522857571020313161697359)
        ·
          refine ⟨784286356530469742546039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 522857571020313161697359 784286356530469742546039)
          ·
            refine ⟨1176429534795704613819059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 784286356530469742546039 1176429534795704613819059)
            ·
              refine ⟨1764644302193556920728589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1176429534795704613819059 1764644302193556920728589)
              ·
                refine ⟨661741613322583845273221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1764644302193556920728589 661741613322583845273221)
                ·
                  refine ⟨124076552497984470988729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 661741613322583845273221 124076552497984470988729)
                  ·
                    rfl

theorem cell21_543686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 3, 4].length) (baseStart_543686 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_543686 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_543686 prefixEnd_543686 := by exact prefixLift 543686
  have htrace : WordTrace (prefixWord ++ tailWord_543686) baseStart_543686 baseEnd_543686 := by
    simpa [prefixWord, tailWord_543686, baseEnd_543686] using wordTrace_append hprefix tailTrace_543686
  have hstable : (prefixWord ++ tailWord_543686).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543686).length < 2 ^ (prefixWord ++ tailWord_543686).sum := by decide
  have hdescent : baseEnd_543686 < baseStart_543686 := by decide
  rcases family_descends (prefixWord ++ tailWord_543686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543691 : List Nat := [1, 1, 1, 1, 3, 5, 1, 8]
def baseStart_543691 : Nat := 118140960795 + 543691 * 2 ^ 59
def prefixEnd_543691 : Nat := 4983230072969 + 3 ^ 40 * 543691 * 2
def baseEnd_543691 : Nat := 41359231188701857801795

theorem tailTrace_543691 : CollatzResearch.WordTrace tailWord_543691 prefixEnd_543691 41359231188701857801795 := by
  unfold tailWord_543691
  simp only [CollatzResearch.WordTrace]
  refine ⟨19830039873307836875342927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13220026582205224583561951 19830039873307836875342927)
  ·
    refine ⟨29745059809961755313014391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19830039873307836875342927 29745059809961755313014391)
    ·
      refine ⟨44617589714942632969521587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29745059809961755313014391 44617589714942632969521587)
      ·
        refine ⟨66926384572413949454282381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44617589714942632969521587 66926384572413949454282381)
        ·
          refine ⟨25097394214655231045355893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66926384572413949454282381 25097394214655231045355893)
          ·
            refine ⟨2352880707623927910502115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 25097394214655231045355893 2352880707623927910502115)
            ·
              refine ⟨3529321061435891865753173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2352880707623927910502115 3529321061435891865753173)
              ·
                refine ⟨41359231188701857801795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3529321061435891865753173 41359231188701857801795)
                ·
                  rfl

theorem cell21_543691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 8].length) (baseStart_543691 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_543691 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_543691 prefixEnd_543691 := by exact prefixLift 543691
  have htrace : WordTrace (prefixWord ++ tailWord_543691) baseStart_543691 baseEnd_543691 := by
    simpa [prefixWord, tailWord_543691, baseEnd_543691] using wordTrace_append hprefix tailTrace_543691
  have hstable : (prefixWord ++ tailWord_543691).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543691).length < 2 ^ (prefixWord ++ tailWord_543691).sum := by decide
  have hdescent : baseEnd_543691 < baseStart_543691 := by decide
  rcases family_descends (prefixWord ++ tailWord_543691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543694 : List Nat := [4, 1, 1, 1, 2, 4, 1, 3, 4]
def baseStart_543694 : Nat := 118140960795 + 543694 * 2 ^ 59
def prefixEnd_543694 : Nat := 4983230072969 + 3 ^ 40 * 543694 * 2
def baseEnd_543694 : Nat := 124078378206978234855379

theorem tailTrace_543694 : CollatzResearch.WordTrace tailWord_543694 prefixEnd_543694 124078378206978234855379 := by
  unfold tailWord_543694
  simp only [CollatzResearch.WordTrace]
  refine ⟨2478768661537121048462767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13220099528197978925134757 2478768661537121048462767)
  ·
    refine ⟨3718152992305681572694151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2478768661537121048462767 3718152992305681572694151)
    ·
      refine ⟨5577229488458522359041227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3718152992305681572694151 5577229488458522359041227)
      ·
        refine ⟨8365844232687783538561841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5577229488458522359041227 8365844232687783538561841)
        ·
          refine ⟨6274383174515837653921381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8365844232687783538561841 6274383174515837653921381)
          ·
            refine ⟨1176446845221719560110259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6274383174515837653921381 1176446845221719560110259)
            ·
              refine ⟨1764670267832579340165389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1176446845221719560110259 1764670267832579340165389)
              ·
                refine ⟨661751350437217252562021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1764670267832579340165389 661751350437217252562021)
                ·
                  refine ⟨124078378206978234855379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 661751350437217252562021 124078378206978234855379)
                  ·
                    rfl

theorem cell21_543694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 3, 4].length) (baseStart_543694 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_543694 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_543694 prefixEnd_543694 := by exact prefixLift 543694
  have htrace : WordTrace (prefixWord ++ tailWord_543694) baseStart_543694 baseEnd_543694 := by
    simpa [prefixWord, tailWord_543694, baseEnd_543694] using wordTrace_append hprefix tailTrace_543694
  have hstable : (prefixWord ++ tailWord_543694).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543694).length < 2 ^ (prefixWord ++ tailWord_543694).sum := by decide
  have hdescent : baseEnd_543694 < baseStart_543694 := by decide
  rcases family_descends (prefixWord ++ tailWord_543694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543742 : List Nat := [4, 2, 2, 2, 2, 2, 1, 6]
def baseStart_543742 : Nat := 118140960795 + 543742 * 2 ^ 59
def prefixEnd_543742 : Nat := 4983230072969 + 3 ^ 40 * 543742 * 2
def baseEnd_543742 : Nat := 41363110820313606018427

theorem tailTrace_543742 : CollatzResearch.WordTrace tailWord_543742 prefixEnd_543742 41363110820313606018427 := by
  unfold tailWord_543742
  simp only [CollatzResearch.WordTrace]
  refine ⟨2478987499515384073181185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13221266664082048390299653 2478987499515384073181185)
  ·
    refine ⟨1859240624636538054885889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2478987499515384073181185 1859240624636538054885889)
    ·
      refine ⟨1394430468477403541164417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1859240624636538054885889 1394430468477403541164417)
      ·
        refine ⟨1045822851358052655873313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1394430468477403541164417 1045822851358052655873313)
        ·
          refine ⟨784367138518539491904985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1045822851358052655873313 784367138518539491904985)
          ·
            refine ⟨588275353888904618928739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 784367138518539491904985 588275353888904618928739)
            ·
              refine ⟨882413030833356928393109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 588275353888904618928739 882413030833356928393109)
              ·
                refine ⟨41363110820313606018427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 882413030833356928393109 41363110820313606018427)
                ·
                  rfl

theorem cell21_543742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 1, 6].length) (baseStart_543742 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_543742 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_543742 prefixEnd_543742 := by exact prefixLift 543742
  have htrace : WordTrace (prefixWord ++ tailWord_543742) baseStart_543742 baseEnd_543742 := by
    simpa [prefixWord, tailWord_543742, baseEnd_543742] using wordTrace_append hprefix tailTrace_543742
  have hstable : (prefixWord ++ tailWord_543742).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543742).length < 2 ^ (prefixWord ++ tailWord_543742).sum := by decide
  have hdescent : baseEnd_543742 < baseStart_543742 := by decide
  rcases family_descends (prefixWord ++ tailWord_543742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543773 : List Nat := [1, 4, 2, 2, 3, 1, 2, 3, 3]
def baseStart_543773 : Nat := 118140960795 + 543773 * 2 ^ 59
def prefixEnd_543773 : Nat := 4983230072969 + 3 ^ 40 * 543773 * 2
def baseEnd_543773 : Nat := 124096407083291653038551

theorem tailTrace_543773 : CollatzResearch.WordTrace tailWord_543773 prefixEnd_543773 124096407083291653038551 := by
  unfold tailWord_543773
  simp only [CollatzResearch.WordTrace]
  refine ⟨19833030659010764879827973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13222020439340509919885315 19833030659010764879827973)
  ·
    refine ⟨3718693248564518414967745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19833030659010764879827973 3718693248564518414967745)
    ·
      refine ⟨2789019936423388811225809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3718693248564518414967745 2789019936423388811225809)
      ·
        refine ⟨2091764952317541608419357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2789019936423388811225809 2091764952317541608419357)
        ·
          refine ⟨784411857119078103157259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2091764952317541608419357 784411857119078103157259)
          ·
            refine ⟨1176617785678617154735889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 784411857119078103157259 1176617785678617154735889)
            ·
              refine ⟨882463339258962866051917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1176617785678617154735889 882463339258962866051917)
              ·
                refine ⟨330923752222111074769469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 882463339258962866051917 330923752222111074769469)
                ·
                  refine ⟨124096407083291653038551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 330923752222111074769469 124096407083291653038551)
                  ·
                    rfl

theorem cell21_543773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 2, 3, 3].length) (baseStart_543773 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_543773 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_543773 prefixEnd_543773 := by exact prefixLift 543773
  have htrace : WordTrace (prefixWord ++ tailWord_543773) baseStart_543773 baseEnd_543773 := by
    simpa [prefixWord, tailWord_543773, baseEnd_543773] using wordTrace_append hprefix tailTrace_543773
  have hstable : (prefixWord ++ tailWord_543773).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543773).length < 2 ^ (prefixWord ++ tailWord_543773).sum := by decide
  have hdescent : baseEnd_543773 < baseStart_543773 := by decide
  rcases family_descends (prefixWord ++ tailWord_543773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543888 : List Nat := [2, 1, 1, 1, 1, 1, 4, 4, 6]
def baseStart_543888 : Nat := 118140960795 + 543888 * 2 ^ 59
def prefixEnd_543888 : Nat := 4983230072969 + 3 ^ 40 * 543888 * 2
def baseEnd_543888 : Nat := 124122651650077008621649

theorem tailTrace_543888 : CollatzResearch.WordTrace tailWord_543888 prefixEnd_543888 124122651650077008621649 := by
  unfold tailWord_543888
  simp only [CollatzResearch.WordTrace]
  refine ⟨9918612526797069760132159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13224816702396093013509545 9918612526797069760132159)
  ·
    refine ⟨14877918790195604640198239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9918612526797069760132159 14877918790195604640198239)
    ·
      refine ⟨22316878185293406960297359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14877918790195604640198239 22316878185293406960297359)
      ·
        refine ⟨33475317277940110440446039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22316878185293406960297359 33475317277940110440446039)
        ·
          refine ⟨50212975916910165660669059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33475317277940110440446039 50212975916910165660669059)
          ·
            refine ⟨75319463875365248491003589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50212975916910165660669059 75319463875365248491003589)
            ·
              refine ⟨14122399476630984092063173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 75319463875365248491003589 14122399476630984092063173)
              ·
                refine ⟨2647949901868309517261845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14122399476630984092063173 2647949901868309517261845)
                ·
                  refine ⟨124122651650077008621649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2647949901868309517261845 124122651650077008621649)
                  ·
                    rfl

theorem cell21_543888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 4, 6].length) (baseStart_543888 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_543888 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_543888 prefixEnd_543888 := by exact prefixLift 543888
  have htrace : WordTrace (prefixWord ++ tailWord_543888) baseStart_543888 baseEnd_543888 := by
    simpa [prefixWord, tailWord_543888, baseEnd_543888] using wordTrace_append hprefix tailTrace_543888
  have hstable : (prefixWord ++ tailWord_543888).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543888).length < 2 ^ (prefixWord ++ tailWord_543888).sum := by decide
  have hdescent : baseEnd_543888 < baseStart_543888 := by decide
  rcases family_descends (prefixWord ++ tailWord_543888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543908 : List Nat := [2, 3, 1, 2, 3, 2, 1, 4, 3]
def baseStart_543908 : Nat := 118140960795 + 543908 * 2 ^ 59
def prefixEnd_543908 : Nat := 4983230072969 + 3 ^ 40 * 543908 * 2
def baseEnd_543908 : Nat := 124127215922561418288275

theorem tailTrace_543908 : CollatzResearch.WordTrace tailWord_543908 prefixEnd_543908 124127215922561418288275 := by
  unfold tailWord_543908
  simp only [CollatzResearch.WordTrace]
  refine ⟨9918977256760841467996189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13225303009014455290661585 9918977256760841467996189)
  ·
    refine ⟨3719616471285315550498571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9918977256760841467996189 3719616471285315550498571)
    ·
      refine ⟨5579424706927973325747857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3719616471285315550498571 5579424706927973325747857)
      ·
        refine ⟨4184568530195979994310893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5579424706927973325747857 4184568530195979994310893)
        ·
          refine ⟨1569213198823492497866585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4184568530195979994310893 1569213198823492497866585)
          ·
            refine ⟨1176909899117619373399939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1569213198823492497866585 1176909899117619373399939)
            ·
              refine ⟨1765364848676429060099909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1176909899117619373399939 1765364848676429060099909)
              ·
                refine ⟨331005909126830448768733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1765364848676429060099909 331005909126830448768733)
                ·
                  refine ⟨124127215922561418288275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 331005909126830448768733 124127215922561418288275)
                  ·
                    rfl

theorem cell21_543908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 4, 3].length) (baseStart_543908 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_543908 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_543908 prefixEnd_543908 := by exact prefixLift 543908
  have htrace : WordTrace (prefixWord ++ tailWord_543908) baseStart_543908 baseEnd_543908 := by
    simpa [prefixWord, tailWord_543908, baseEnd_543908] using wordTrace_append hprefix tailTrace_543908
  have hstable : (prefixWord ++ tailWord_543908).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543908).length < 2 ^ (prefixWord ++ tailWord_543908).sum := by decide
  have hdescent : baseEnd_543908 < baseStart_543908 := by decide
  rcases family_descends (prefixWord ++ tailWord_543908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543919 : List Nat := [1, 1, 2, 1, 2, 3, 5, 6]
def baseStart_543919 : Nat := 118140960795 + 543919 * 2 ^ 59
def prefixEnd_543919 : Nat := 4983230072969 + 3 ^ 40 * 543919 * 2
def baseEnd_543919 : Nat := 41376575424142614534973

theorem tailTrace_543919 : CollatzResearch.WordTrace tailWord_543919 prefixEnd_543919 41376575424142614534973 := by
  unfold tailWord_543919
  simp only [CollatzResearch.WordTrace]
  refine ⟨19838355716481831814642811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13225570477654554543095207 19838355716481831814642811)
  ·
    refine ⟨29757533574722747721964217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19838355716481831814642811 29757533574722747721964217)
    ·
      refine ⟨22318150181042060791473163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29757533574722747721964217 22318150181042060791473163)
      ·
        refine ⟨33477225271563091187209745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22318150181042060791473163 33477225271563091187209745)
        ·
          refine ⟨25107918953672318390407309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33477225271563091187209745 25107918953672318390407309)
          ·
            refine ⟨9415469607627119396402741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25107918953672318390407309 9415469607627119396402741)
            ·
              refine ⟨882700275715042443412757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9415469607627119396402741 882700275715042443412757)
              ·
                refine ⟨41376575424142614534973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 882700275715042443412757 41376575424142614534973)
                ·
                  rfl

theorem cell21_543919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 5, 6].length) (baseStart_543919 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_543919 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_543919 prefixEnd_543919 := by exact prefixLift 543919
  have htrace : WordTrace (prefixWord ++ tailWord_543919) baseStart_543919 baseEnd_543919 := by
    simpa [prefixWord, tailWord_543919, baseEnd_543919] using wordTrace_append hprefix tailTrace_543919
  have hstable : (prefixWord ++ tailWord_543919).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543919).length < 2 ^ (prefixWord ++ tailWord_543919).sum := by decide
  have hdescent : baseEnd_543919 < baseStart_543919 := by decide
  rcases family_descends (prefixWord ++ tailWord_543919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543956 : List Nat := [2, 4, 1, 4, 1, 2, 1, 2, 4]
def baseStart_543956 : Nat := 118140960795 + 543956 * 2 ^ 59
def prefixEnd_543956 : Nat := 4983230072969 + 3 ^ 40 * 543956 * 2
def baseEnd_543956 : Nat := 124138170176524001488177

theorem tailTrace_543956 : CollatzResearch.WordTrace tailWord_543956 prefixEnd_543956 124138170176524001488177 := by
  unfold tailWord_543956
  simp only [CollatzResearch.WordTrace]
  refine ⟨9919852608673893566869861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13226470144898524755826481 9919852608673893566869861)
  ·
    refine ⟨1859972364126355043788099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9919852608673893566869861 1859972364126355043788099)
    ·
      refine ⟨2789958546189532565682149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1859972364126355043788099 2789958546189532565682149)
      ·
        refine ⟨523117227410537356065403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2789958546189532565682149 523117227410537356065403)
        ·
          refine ⟨784675841115806034098105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 523117227410537356065403 784675841115806034098105)
          ·
            refine ⟨588506880836854525573579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 784675841115806034098105 588506880836854525573579)
            ·
              refine ⟨882760321255281788360369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 588506880836854525573579 882760321255281788360369)
              ·
                refine ⟨662070240941461341270277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 882760321255281788360369 662070240941461341270277)
                ·
                  refine ⟨124138170176524001488177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 662070240941461341270277 124138170176524001488177)
                  ·
                    rfl

theorem cell21_543956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 1, 2, 4].length) (baseStart_543956 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_543956 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_543956 prefixEnd_543956 := by exact prefixLift 543956
  have htrace : WordTrace (prefixWord ++ tailWord_543956) baseStart_543956 baseEnd_543956 := by
    simpa [prefixWord, tailWord_543956, baseEnd_543956] using wordTrace_append hprefix tailTrace_543956
  have hstable : (prefixWord ++ tailWord_543956).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543956).length < 2 ^ (prefixWord ++ tailWord_543956).sum := by decide
  have hdescent : baseEnd_543956 < baseStart_543956 := by decide
  rcases family_descends (prefixWord ++ tailWord_543956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543967 : List Nat := [1, 1, 2, 3, 2, 1, 4, 4, 3]
def baseStart_543967 : Nat := 118140960795 + 543967 * 2 ^ 59
def prefixEnd_543967 : Nat := 4983230072969 + 3 ^ 40 * 543967 * 2
def baseEnd_543967 : Nat := 124140680526390426804821

theorem tailTrace_543967 : CollatzResearch.WordTrace tailWord_543967 prefixEnd_543967 124140680526390426804821 := by
  unfold tailWord_543967
  simp only [CollatzResearch.WordTrace]
  refine ⟨19840106420307936012390155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13226737613538624008260103 19840106420307936012390155)
  ·
    refine ⟨29760159630461904018585233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19840106420307936012390155 29760159630461904018585233)
    ·
      refine ⟨22320119722846428013938925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29760159630461904018585233 22320119722846428013938925)
      ·
        refine ⟨8370044896067410505227097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22320119722846428013938925 8370044896067410505227097)
        ·
          refine ⟨6277533672050557878920323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8370044896067410505227097 6277533672050557878920323)
          ·
            refine ⟨9416300508075836818380485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6277533672050557878920323 9416300508075836818380485)
            ·
              refine ⟨1765556345264219403446341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9416300508075836818380485 1765556345264219403446341)
              ·
                refine ⟨331041814737041138146189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1765556345264219403446341 331041814737041138146189)
                ·
                  refine ⟨124140680526390426804821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 331041814737041138146189 124140680526390426804821)
                  ·
                    rfl

theorem cell21_543967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 4, 3].length) (baseStart_543967 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_543967 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_543967 prefixEnd_543967 := by exact prefixLift 543967
  have htrace : WordTrace (prefixWord ++ tailWord_543967) baseStart_543967 baseEnd_543967 := by
    simpa [prefixWord, tailWord_543967, baseEnd_543967] using wordTrace_append hprefix tailTrace_543967
  have hstable : (prefixWord ++ tailWord_543967).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543967).length < 2 ^ (prefixWord ++ tailWord_543967).sum := by decide
  have hdescent : baseEnd_543967 < baseStart_543967 := by decide
  rcases family_descends (prefixWord ++ tailWord_543967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544018 : List Nat := [3, 2, 4, 2, 2, 1, 1, 1, 5]
def baseStart_544018 : Nat := 118140960795 + 544018 * 2 ^ 59
def prefixEnd_544018 : Nat := 4983230072969 + 3 ^ 40 * 544018 * 2
def baseEnd_544018 : Nat := 124152319421225671454717

theorem tailTrace_544018 : CollatzResearch.WordTrace tailWord_544018 prefixEnd_544018 124152319421225671454717 := by
  unfold tailWord_544018
  simp only [CollatzResearch.WordTrace]
  refine ⟨4960491635780792930624177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13227977695415447814997805 4960491635780792930624177)
  ·
    refine ⟨3720368726835594697968133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4960491635780792930624177 3720368726835594697968133)
    ·
      refine ⟨697569136281674005869025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3720368726835594697968133 697569136281674005869025)
      ·
        refine ⟨523176852211255504401769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 697569136281674005869025 523176852211255504401769)
        ·
          refine ⟨392382639158441628301327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 523176852211255504401769 392382639158441628301327)
          ·
            refine ⟨588573958737662442451991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 392382639158441628301327 588573958737662442451991)
            ·
              refine ⟨882860938106493663677987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 588573958737662442451991 882860938106493663677987)
              ·
                refine ⟨1324291407159740495516981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 882860938106493663677987 1324291407159740495516981)
                ·
                  refine ⟨124152319421225671454717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1324291407159740495516981 124152319421225671454717)
                  ·
                    rfl

theorem cell21_544018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 1, 1, 5].length) (baseStart_544018 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_544018 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_544018 prefixEnd_544018 := by exact prefixLift 544018
  have htrace : WordTrace (prefixWord ++ tailWord_544018) baseStart_544018 baseEnd_544018 := by
    simpa [prefixWord, tailWord_544018, baseEnd_544018] using wordTrace_append hprefix tailTrace_544018
  have hstable : (prefixWord ++ tailWord_544018).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544018).length < 2 ^ (prefixWord ++ tailWord_544018).sum := by decide
  have hdescent : baseEnd_544018 < baseStart_544018 := by decide
  rcases family_descends (prefixWord ++ tailWord_544018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544032 : List Nat := [2, 1, 1, 5, 4, 1, 2, 1, 4]
def baseStart_544032 : Nat := 118140960795 + 544032 * 2 ^ 59
def prefixEnd_544032 : Nat := 4983230072969 + 3 ^ 40 * 544032 * 2
def baseEnd_544032 : Nat := 124155514411964758221355

theorem tailTrace_544032 : CollatzResearch.WordTrace tailWord_544032 prefixEnd_544032 124155514411964758221355 := by
  unfold tailWord_544032
  simp only [CollatzResearch.WordTrace]
  refine ⟨9921238582536226056753175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13228318110048301409004233 9921238582536226056753175)
  ·
    refine ⟨14881857873804339085129763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9921238582536226056753175 14881857873804339085129763)
    ·
      refine ⟨22322786810706508627694645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14881857873804339085129763 22322786810706508627694645)
      ·
        refine ⟨2092761263503735183846373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 22322786810706508627694645 2092761263503735183846373)
        ·
          refine ⟨392392736906950346971195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2092761263503735183846373 392392736906950346971195)
          ·
            refine ⟨588589105360425520456793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 392392736906950346971195 588589105360425520456793)
            ·
              refine ⟨441441829020319140342595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 588589105360425520456793 441441829020319140342595)
              ·
                refine ⟨662162743530478710513893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 441441829020319140342595 662162743530478710513893)
                ·
                  refine ⟨124155514411964758221355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 662162743530478710513893 124155514411964758221355)
                  ·
                    rfl

theorem cell21_544032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 2, 1, 4].length) (baseStart_544032 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_544032 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_544032 prefixEnd_544032 := by exact prefixLift 544032
  have htrace : WordTrace (prefixWord ++ tailWord_544032) baseStart_544032 baseEnd_544032 := by
    simpa [prefixWord, tailWord_544032, baseEnd_544032] using wordTrace_append hprefix tailTrace_544032
  have hstable : (prefixWord ++ tailWord_544032).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544032).length < 2 ^ (prefixWord ++ tailWord_544032).sum := by decide
  have hdescent : baseEnd_544032 < baseStart_544032 := by decide
  rcases family_descends (prefixWord ++ tailWord_544032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544119 : List Nat := [1, 1, 3, 1, 1, 2, 6, 3, 3]
def baseStart_544119 : Nat := 118140960795 + 544119 * 2 ^ 59
def prefixEnd_544119 : Nat := 4983230072969 + 3 ^ 40 * 544119 * 2
def baseEnd_544119 : Nat := 124175368997271940271177

theorem tailTrace_544119 : CollatzResearch.WordTrace tailWord_544119 prefixEnd_544119 124175368997271940271177 := by
  unfold tailWord_544119
  simp only [CollatzResearch.WordTrace]
  refine ⟨19845650315757265971923411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13230433543838177314615607 19845650315757265971923411)
  ·
    refine ⟨29768475473635898957885117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19845650315757265971923411 29768475473635898957885117)
    ·
      refine ⟨11163178302613462109206919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29768475473635898957885117 11163178302613462109206919)
      ·
        refine ⟨16744767453920193163810379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11163178302613462109206919 16744767453920193163810379)
        ·
          refine ⟨25117151180880289745715569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16744767453920193163810379 25117151180880289745715569)
          ·
            refine ⟨18837863385660217309286677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25117151180880289745715569 18837863385660217309286677)
            ·
              refine ⟨883024846202822686372813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 18837863385660217309286677 883024846202822686372813)
              ·
                refine ⟨331134317326058507389805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 883024846202822686372813 331134317326058507389805)
                ·
                  refine ⟨124175368997271940271177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 331134317326058507389805 124175368997271940271177)
                  ·
                    rfl

theorem cell21_544119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 6, 3, 3].length) (baseStart_544119 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_544119 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_544119 prefixEnd_544119 := by exact prefixLift 544119
  have htrace : WordTrace (prefixWord ++ tailWord_544119) baseStart_544119 baseEnd_544119 := by
    simpa [prefixWord, tailWord_544119, baseEnd_544119] using wordTrace_append hprefix tailTrace_544119
  have hstable : (prefixWord ++ tailWord_544119).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544119).length < 2 ^ (prefixWord ++ tailWord_544119).sum := by decide
  have hdescent : baseEnd_544119 < baseStart_544119 := by decide
  rcases family_descends (prefixWord ++ tailWord_544119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544133 : List Nat := [1, 3, 1, 1, 3, 1, 5, 2, 4]
def baseStart_544133 : Nat := 118140960795 + 544133 * 2 ^ 59
def prefixEnd_544133 : Nat := 4983230072969 + 3 ^ 40 * 544133 * 2
def baseEnd_544133 : Nat := 124178563988011027037815

theorem tailTrace_544133 : CollatzResearch.WordTrace tailWord_544133 prefixEnd_544133 124178563988011027037815 := by
  unfold tailWord_544133
  simp only [CollatzResearch.WordTrace]
  refine ⟨19846160937706546362933053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13230773958471030908622035 19846160937706546362933053)
  ·
    refine ⟨7442310351639954886099895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19846160937706546362933053 7442310351639954886099895)
    ·
      refine ⟨11163465527459932329149843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7442310351639954886099895 11163465527459932329149843)
      ·
        refine ⟨16745198291189898493724765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11163465527459932329149843 16745198291189898493724765)
        ·
          refine ⟨6279449359196211935146787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16745198291189898493724765 6279449359196211935146787)
          ·
            refine ⟨9419174038794317902720181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6279449359196211935146787 9419174038794317902720181)
            ·
              refine ⟨883047566136967303380017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9419174038794317902720181 883047566136967303380017)
              ·
                refine ⟨662285674602725477535013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 883047566136967303380017 662285674602725477535013)
                ·
                  refine ⟨124178563988011027037815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 662285674602725477535013 124178563988011027037815)
                  ·
                    rfl

theorem cell21_544133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 5, 2, 4].length) (baseStart_544133 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_544133 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_544133 prefixEnd_544133 := by exact prefixLift 544133
  have htrace : WordTrace (prefixWord ++ tailWord_544133) baseStart_544133 baseEnd_544133 := by
    simpa [prefixWord, tailWord_544133, baseEnd_544133] using wordTrace_append hprefix tailTrace_544133
  have hstable : (prefixWord ++ tailWord_544133).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544133).length < 2 ^ (prefixWord ++ tailWord_544133).sum := by decide
  have hdescent : baseEnd_544133 < baseStart_544133 := by decide
  rcases family_descends (prefixWord ++ tailWord_544133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
