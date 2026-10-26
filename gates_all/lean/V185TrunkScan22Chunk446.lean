import V185TrunkScan22Chunk445

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_3975843 : List Nat := [1, 1, 1, 4, 1, 1, 2, 3, 2, 6]
def baseStart_3975843 : Nat := 118140960795 + 3975843 * 2 ^ 59
def prefixEnd_3975843 : Nat := 4983230072969 + 3 ^ 40 * 3975843 * 2
def baseEnd_3975843 : Nat := 1361012310542528819785291

theorem tailTrace_3975843 : CollatzResearch.WordTrace tailWord_3975843 prefixEnd_3975843 1361012310542528819785291 := by
  unfold tailWord_3975843
  simp only [CollatzResearch.WordTrace]
  refine ⟨145010907335207305769972183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96673938223471537179981455 145010907335207305769972183)
  ·
    refine ⟨217516361002810958654958275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145010907335207305769972183 217516361002810958654958275)
    ·
      refine ⟨326274541504216437982437413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217516361002810958654958275 326274541504216437982437413)
      ·
        refine ⟨61176476532040582121707015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 326274541504216437982437413 61176476532040582121707015)
        ·
          refine ⟨91764714798060873182560523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61176476532040582121707015 91764714798060873182560523)
          ·
            refine ⟨137647072197091309773840785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91764714798060873182560523 137647072197091309773840785)
            ·
              refine ⟨103235304147818482330380589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137647072197091309773840785 103235304147818482330380589)
              ·
                refine ⟨38713239055431930873892721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103235304147818482330380589 38713239055431930873892721)
                ·
                  refine ⟨29034929291573948155419541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38713239055431930873892721 29034929291573948155419541)
                  ·
                    refine ⟨1361012310542528819785291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29034929291573948155419541 1361012310542528819785291)
                    ·
                      rfl

theorem cell22_3975843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 3, 2, 6].length) (baseStart_3975843 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3975843 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3975843 prefixEnd_3975843 := by exact prefixLift 3975843
  have htrace : WordTrace (prefixWord ++ tailWord_3975843) baseStart_3975843 baseEnd_3975843 := by
    simpa [prefixWord, tailWord_3975843, baseEnd_3975843] using wordTrace_append hprefix tailTrace_3975843
  have hstable : (prefixWord ++ tailWord_3975843).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3975843).length < 2 ^ (prefixWord ++ tailWord_3975843).sum := by decide
  have hdescent : baseEnd_3975843 < baseStart_3975843 := by decide
  rcases family_descends (prefixWord ++ tailWord_3975843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3975888 : List Nat := [2, 1, 1, 1, 1, 2, 1, 2, 1, 10]
def baseStart_3975888 : Nat := 118140960795 + 3975888 * 2 ^ 59
def prefixEnd_3975888 : Nat := 4983230072969 + 3 ^ 40 * 3975888 * 2
def baseEnd_3975888 : Nat := 1361027714962163702410153

theorem tailTrace_3975888 : CollatzResearch.WordTrace tailWord_3975888 prefixEnd_3975888 1361027714962163702410153 := by
  unfold tailWord_3975888
  simp only [CollatzResearch.WordTrace]
  refine ⟨72506274310022139227680159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96675032413362852303573545 72506274310022139227680159)
  ·
    refine ⟨108759411465033208841520239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72506274310022139227680159 108759411465033208841520239)
    ·
      refine ⟨163139117197549813262280359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108759411465033208841520239 163139117197549813262280359)
      ·
        refine ⟨244708675796324719893420539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163139117197549813262280359 244708675796324719893420539)
        ·
          refine ⟨367063013694487079840130809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244708675796324719893420539 367063013694487079840130809)
          ·
            refine ⟨275297260270865309880098107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 367063013694487079840130809 275297260270865309880098107)
            ·
              refine ⟨412945890406297964820147161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 275297260270865309880098107 412945890406297964820147161)
              ·
                refine ⟨309709417804723473615110371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 412945890406297964820147161 309709417804723473615110371)
                ·
                  refine ⟨464564126707085210422665557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 309709417804723473615110371 464564126707085210422665557)
                  ·
                    refine ⟨1361027714962163702410153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 464564126707085210422665557 1361027714962163702410153)
                    ·
                      rfl

theorem cell22_3975888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 1, 10].length) (baseStart_3975888 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3975888 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3975888 prefixEnd_3975888 := by exact prefixLift 3975888
  have htrace : WordTrace (prefixWord ++ tailWord_3975888) baseStart_3975888 baseEnd_3975888 := by
    simpa [prefixWord, tailWord_3975888, baseEnd_3975888] using wordTrace_append hprefix tailTrace_3975888
  have hstable : (prefixWord ++ tailWord_3975888).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3975888).length < 2 ^ (prefixWord ++ tailWord_3975888).sum := by decide
  have hdescent : baseEnd_3975888 < baseStart_3975888 := by decide
  rcases family_descends (prefixWord ++ tailWord_3975888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3975896 : List Nat := [2, 1, 2, 2, 3, 3, 3, 2, 1, 3]
def baseStart_3975896 : Nat := 118140960795 + 3975896 * 2 ^ 59
def prefixEnd_3975896 : Nat := 4983230072969 + 3 ^ 40 * 3975896 * 2
def baseEnd_3975896 : Nat := 1361030453525654348210129

theorem tailTrace_3975896 : CollatzResearch.WordTrace tailWord_3975896 prefixEnd_3975896 1361030453525654348210129 := by
  unfold tailWord_3975896
  simp only [CollatzResearch.WordTrace]
  refine ⟨72506420202007647910825771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96675226936010197214434361 72506420202007647910825771)
  ·
    refine ⟨108759630303011471866238657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72506420202007647910825771 108759630303011471866238657)
    ·
      refine ⟨81569722727258603899678993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108759630303011471866238657 81569722727258603899678993)
      ·
        refine ⟨61177292045443952924759245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81569722727258603899678993 61177292045443952924759245)
        ·
          refine ⟨22941484517041482346784717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61177292045443952924759245 22941484517041482346784717)
          ·
            refine ⟨8603056693890555880044269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22941484517041482346784717 8603056693890555880044269)
            ·
              refine ⟨3226146260208958455016601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8603056693890555880044269 3226146260208958455016601)
              ·
                refine ⟨2419609695156718841262451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3226146260208958455016601 2419609695156718841262451)
                ·
                  refine ⟨3629414542735078261893677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2419609695156718841262451 3629414542735078261893677)
                  ·
                    refine ⟨1361030453525654348210129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3629414542735078261893677 1361030453525654348210129)
                    ·
                      rfl

theorem cell22_3975896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 3, 2, 1, 3].length) (baseStart_3975896 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3975896 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3975896 prefixEnd_3975896 := by exact prefixLift 3975896
  have htrace : WordTrace (prefixWord ++ tailWord_3975896) baseStart_3975896 baseEnd_3975896 := by
    simpa [prefixWord, tailWord_3975896, baseEnd_3975896] using wordTrace_append hprefix tailTrace_3975896
  have hstable : (prefixWord ++ tailWord_3975896).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3975896).length < 2 ^ (prefixWord ++ tailWord_3975896).sum := by decide
  have hdescent : baseEnd_3975896 < baseStart_3975896 := by decide
  rcases family_descends (prefixWord ++ tailWord_3975896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3975909 : List Nat := [1, 3, 1, 4, 1, 4, 2, 1, 5]
def baseStart_3975909 : Nat := 118140960795 + 3975909 * 2 ^ 59
def prefixEnd_3975909 : Nat := 4983230072969 + 3 ^ 40 * 3975909 * 2
def baseEnd_3975909 : Nat := 453678301230442215878363

theorem tailTrace_3975909 : CollatzResearch.WordTrace tailWord_3975909 prefixEnd_3975909 453678301230442215878363 := by
  unfold tailWord_3975909
  simp only [CollatzResearch.WordTrace]
  refine ⟨145013314552968199041874781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96675543035312132694583187 145013314552968199041874781)
  ·
    refine ⟨54379992957363074640703043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145013314552968199041874781 54379992957363074640703043)
    ·
      refine ⟨81569989436044611961054565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54379992957363074640703043 81569989436044611961054565)
      ·
        refine ⟨15294373019258364742697731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81569989436044611961054565 15294373019258364742697731)
        ·
          refine ⟨22941559528887547114046597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15294373019258364742697731 22941559528887547114046597)
          ·
            refine ⟨4301542411666415083883737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22941559528887547114046597 4301542411666415083883737)
            ·
              refine ⟨3226156808749811312912803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4301542411666415083883737 3226156808749811312912803)
              ·
                refine ⟨4839235213124716969369205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3226156808749811312912803 4839235213124716969369205)
                ·
                  refine ⟨453678301230442215878363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4839235213124716969369205 453678301230442215878363)
                  ·
                    rfl

theorem cell22_3975909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 2, 1, 5].length) (baseStart_3975909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3975909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3975909 prefixEnd_3975909 := by exact prefixLift 3975909
  have htrace : WordTrace (prefixWord ++ tailWord_3975909) baseStart_3975909 baseEnd_3975909 := by
    simpa [prefixWord, tailWord_3975909, baseEnd_3975909] using wordTrace_append hprefix tailTrace_3975909
  have hstable : (prefixWord ++ tailWord_3975909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3975909).length < 2 ^ (prefixWord ++ tailWord_3975909).sum := by decide
  have hdescent : baseEnd_3975909 < baseStart_3975909 := by decide
  rcases family_descends (prefixWord ++ tailWord_3975909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3975922 : List Nat := [3, 2, 1, 3, 1, 3, 1, 1, 3, 4]
def baseStart_3975922 : Nat := 118140960795 + 3975922 * 2 ^ 59
def prefixEnd_3975922 : Nat := 4983230072969 + 3 ^ 40 * 3975922 * 2
def baseEnd_3975922 : Nat := 1361039353856998947060049

theorem tailTrace_3975922 : CollatzResearch.WordTrace tailWord_3975922 prefixEnd_3975922 1361039353856998947060049 := by
  unfold tailWord_3975922
  simp only [CollatzResearch.WordTrace]
  refine ⟨36253447175480275565524505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96675859134614068174732013 36253447175480275565524505)
  ·
    refine ⟨27190085381610206674143379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36253447175480275565524505 27190085381610206674143379)
    ·
      refine ⟨40785128072415310011215069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27190085381610206674143379 40785128072415310011215069)
      ·
        refine ⟨15294423027155741254205651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40785128072415310011215069 15294423027155741254205651)
        ·
          refine ⟨22941634540733611881308477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15294423027155741254205651 22941634540733611881308477)
          ·
            refine ⟨8603112952775104455490679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22941634540733611881308477 8603112952775104455490679)
            ·
              refine ⟨12904669429162656683236019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8603112952775104455490679 12904669429162656683236019)
              ·
                refine ⟨19357004143743985024854029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12904669429162656683236019 19357004143743985024854029)
                ·
                  refine ⟨7258876553903994384320261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19357004143743985024854029 7258876553903994384320261)
                  ·
                    refine ⟨1361039353856998947060049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7258876553903994384320261 1361039353856998947060049)
                    ·
                      rfl

theorem cell22_3975922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 1, 3, 4].length) (baseStart_3975922 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3975922 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3975922 prefixEnd_3975922 := by exact prefixLift 3975922
  have htrace : WordTrace (prefixWord ++ tailWord_3975922) baseStart_3975922 baseEnd_3975922 := by
    simpa [prefixWord, tailWord_3975922, baseEnd_3975922] using wordTrace_append hprefix tailTrace_3975922
  have hstable : (prefixWord ++ tailWord_3975922).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3975922).length < 2 ^ (prefixWord ++ tailWord_3975922).sum := by decide
  have hdescent : baseEnd_3975922 < baseStart_3975922 := by decide
  rcases family_descends (prefixWord ++ tailWord_3975922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3975937 : List Nat := [1, 2, 4, 1, 1, 1, 1, 7, 4]
def baseStart_3975937 : Nat := 118140960795 + 3975937 * 2 ^ 59
def prefixEnd_3975937 : Nat := 4983230072969 + 3 ^ 40 * 3975937 * 2
def baseEnd_3975937 : Nat := 453681496221181302645001

theorem tailTrace_3975937 : CollatzResearch.WordTrace tailWord_3975937 prefixEnd_3975937 453681496221181302645001 := by
  unfold tailWord_3975937
  simp only [CollatzResearch.WordTrace]
  refine ⟨145014335796866759823894065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96676223864577839882596043 145014335796866759823894065)
  ·
    refine ⟨108760751847650069867920549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145014335796866759823894065 108760751847650069867920549)
    ·
      refine ⟨20392640971434388100235103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108760751847650069867920549 20392640971434388100235103)
      ·
        refine ⟨30588961457151582150352655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20392640971434388100235103 30588961457151582150352655)
        ·
          refine ⟨45883442185727373225528983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30588961457151582150352655 45883442185727373225528983)
          ·
            refine ⟨68825163278591059838293475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45883442185727373225528983 68825163278591059838293475)
            ·
              refine ⟨103237744917886589757440213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68825163278591059838293475 103237744917886589757440213)
              ·
                refine ⟨2419634646512966947440005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 103237744917886589757440213 2419634646512966947440005)
                ·
                  refine ⟨453681496221181302645001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2419634646512966947440005 453681496221181302645001)
                  ·
                    rfl

theorem cell22_3975937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 7, 4].length) (baseStart_3975937 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3975937 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3975937 prefixEnd_3975937 := by exact prefixLift 3975937
  have htrace : WordTrace (prefixWord ++ tailWord_3975937) baseStart_3975937 baseEnd_3975937 := by
    simpa [prefixWord, tailWord_3975937, baseEnd_3975937] using wordTrace_append hprefix tailTrace_3975937
  have hstable : (prefixWord ++ tailWord_3975937).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3975937).length < 2 ^ (prefixWord ++ tailWord_3975937).sum := by decide
  have hdescent : baseEnd_3975937 < baseStart_3975937 := by decide
  rcases family_descends (prefixWord ++ tailWord_3975937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3975950 : List Nat := [4, 1, 1, 2, 1, 1, 1, 2, 3, 6]
def baseStart_3975950 : Nat := 118140960795 + 3975950 * 2 ^ 59
def prefixEnd_3975950 : Nat := 4983230072969 + 3 ^ 40 * 3975950 * 2
def baseEnd_3975950 : Nat := 1361048938829216207359963

theorem tailTrace_3975950 : CollatzResearch.WordTrace tailWord_3975950 prefixEnd_3975950 1361048938829216207359963 := by
  unfold tailWord_3975950
  simp only [CollatzResearch.WordTrace]
  refine ⟨18126851243227457880514663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96676539963879775362744869 18126851243227457880514663)
  ·
    refine ⟨27190276864841186820771995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18126851243227457880514663 27190276864841186820771995)
    ·
      refine ⟨40785415297261780231157993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27190276864841186820771995 40785415297261780231157993)
      ·
        refine ⟨30589061472946335173368495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40785415297261780231157993 30589061472946335173368495)
        ·
          refine ⟨45883592209419502760052743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30589061472946335173368495 45883592209419502760052743)
          ·
            refine ⟨68825388314129254140079115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45883592209419502760052743 68825388314129254140079115)
            ·
              refine ⟨103238082471193881210118673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68825388314129254140079115 103238082471193881210118673)
              ·
                refine ⟨77428561853395410907589005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103238082471193881210118673 77428561853395410907589005)
                ·
                  refine ⟨29035710695023279090345877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77428561853395410907589005 29035710695023279090345877)
                  ·
                    refine ⟨1361048938829216207359963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29035710695023279090345877 1361048938829216207359963)
                    ·
                      rfl

theorem cell22_3975950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 2, 3, 6].length) (baseStart_3975950 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3975950 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3975950 prefixEnd_3975950 := by exact prefixLift 3975950
  have htrace : WordTrace (prefixWord ++ tailWord_3975950) baseStart_3975950 baseEnd_3975950 := by
    simpa [prefixWord, tailWord_3975950, baseEnd_3975950] using wordTrace_append hprefix tailTrace_3975950
  have hstable : (prefixWord ++ tailWord_3975950).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3975950).length < 2 ^ (prefixWord ++ tailWord_3975950).sum := by decide
  have hdescent : baseEnd_3975950 < baseStart_3975950 := by decide
  rcases family_descends (prefixWord ++ tailWord_3975950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3975990 : List Nat := [5, 1, 2, 2, 3, 1, 2, 1, 1, 4]
def baseStart_3975990 : Nat := 118140960795 + 3975990 * 2 ^ 59
def prefixEnd_3975990 : Nat := 4983230072969 + 3 ^ 40 * 3975990 * 2
def baseEnd_3975990 : Nat := 1361062631646669436359841

theorem tailTrace_3975990 : CollatzResearch.WordTrace tailWord_3975990 prefixEnd_3975990 1361062631646669436359841 := by
  unfold tailWord_3975990
  simp only [CollatzResearch.WordTrace]
  refine ⟨9063516804104671867223339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 96677512577116499917048949 9063516804104671867223339)
  ·
    refine ⟨13595275206157007800835009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9063516804104671867223339 13595275206157007800835009)
    ·
      refine ⟨10196456404617755850626257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13595275206157007800835009 10196456404617755850626257)
      ·
        refine ⟨7647342303463316887969693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10196456404617755850626257 7647342303463316887969693)
        ·
          refine ⟨2867753363798743832988635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7647342303463316887969693 2867753363798743832988635)
          ·
            refine ⟨4301630045698115749482953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2867753363798743832988635 4301630045698115749482953)
            ·
              refine ⟨3226222534273586812112215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4301630045698115749482953 3226222534273586812112215)
              ·
                refine ⟨4839333801410380218168323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3226222534273586812112215 4839333801410380218168323)
                ·
                  refine ⟨7259000702115570327252485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4839333801410380218168323 7259000702115570327252485)
                  ·
                    refine ⟨1361062631646669436359841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7259000702115570327252485 1361062631646669436359841)
                    ·
                      rfl

theorem cell22_3975990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 2, 1, 1, 4].length) (baseStart_3975990 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3975990 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3975990 prefixEnd_3975990 := by exact prefixLift 3975990
  have htrace : WordTrace (prefixWord ++ tailWord_3975990) baseStart_3975990 baseEnd_3975990 := by
    simpa [prefixWord, tailWord_3975990, baseEnd_3975990] using wordTrace_append hprefix tailTrace_3975990
  have hstable : (prefixWord ++ tailWord_3975990).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3975990).length < 2 ^ (prefixWord ++ tailWord_3975990).sum := by decide
  have hdescent : baseEnd_3975990 < baseStart_3975990 := by decide
  rcases family_descends (prefixWord ++ tailWord_3975990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3976055 : List Nat := [1, 1, 3, 1, 1, 2, 1, 4, 8]
def baseStart_3976055 : Nat := 118140960795 + 3976055 * 2 ^ 59
def prefixEnd_3976055 : Nat := 4983230072969 + 3 ^ 40 * 3976055 * 2
def baseEnd_3976055 : Nat := 453694960825010311161547

theorem tailTrace_3976055 : CollatzResearch.WordTrace tailWord_3976055 prefixEnd_3976055 453694960825010311161547 := by
  unfold tailWord_3976055
  simp only [CollatzResearch.WordTrace]
  refine ⟨145018639610439265976689619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96679093073626177317793079 145018639610439265976689619)
  ·
    refine ⟨217527959415658898965034429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145018639610439265976689619 217527959415658898965034429)
    ·
      refine ⟨81572984780872087111887911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 217527959415658898965034429 81572984780872087111887911)
      ·
        refine ⟨122359477171308130667831867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81572984780872087111887911 122359477171308130667831867)
        ·
          refine ⟨183539215756962196001747801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122359477171308130667831867 183539215756962196001747801)
          ·
            refine ⟨137654411817721647001310851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183539215756962196001747801 137654411817721647001310851)
            ·
              refine ⟨206481617726582470501966277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137654411817721647001310851 206481617726582470501966277)
              ·
                refine ⟨38715303323734213219118677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 206481617726582470501966277 38715303323734213219118677)
                ·
                  refine ⟨453694960825010311161547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38715303323734213219118677 453694960825010311161547)
                  ·
                    rfl

theorem cell22_3976055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 4, 8].length) (baseStart_3976055 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3976055 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3976055 prefixEnd_3976055 := by exact prefixLift 3976055
  have htrace : WordTrace (prefixWord ++ tailWord_3976055) baseStart_3976055 baseEnd_3976055 := by
    simpa [prefixWord, tailWord_3976055, baseEnd_3976055] using wordTrace_append hprefix tailTrace_3976055
  have hstable : (prefixWord ++ tailWord_3976055).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3976055).length < 2 ^ (prefixWord ++ tailWord_3976055).sum := by decide
  have hdescent : baseEnd_3976055 < baseStart_3976055 := by decide
  rcases family_descends (prefixWord ++ tailWord_3976055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3976087 : List Nat := [1, 1, 3, 3, 1, 2, 2, 3, 1, 5]
def baseStart_3976087 : Nat := 118140960795 + 3976087 * 2 ^ 59
def prefixEnd_3976087 : Nat := 4983230072969 + 3 ^ 40 * 3976087 * 2
def baseEnd_3976087 : Nat := 1361095836728993516684543

theorem tailTrace_3976087 : CollatzResearch.WordTrace tailWord_3976087 prefixEnd_3976087 1361095836728993516684543 := by
  unfold tailWord_3976087
  simp only [CollatzResearch.WordTrace]
  refine ⟨145019806746323335441854515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96679871164215556961236343 145019806746323335441854515)
  ·
    refine ⟨217529710119485003162781773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145019806746323335441854515 217529710119485003162781773)
    ·
      refine ⟨81573641294806876186043165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 217529710119485003162781773 81573641294806876186043165)
      ·
        refine ⟨30590115485552578569766187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81573641294806876186043165 30590115485552578569766187)
        ·
          refine ⟨45885173228328867854649281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30590115485552578569766187 45885173228328867854649281)
          ·
            refine ⟨34413879921246650890986961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45885173228328867854649281 34413879921246650890986961)
            ·
              refine ⟨25810409940934988168240221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34413879921246650890986961 25810409940934988168240221)
              ·
                refine ⟨9678903727850620563090083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25810409940934988168240221 9678903727850620563090083)
                ·
                  refine ⟨14518355591775930844635125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9678903727850620563090083 14518355591775930844635125)
                  ·
                    refine ⟨1361095836728993516684543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14518355591775930844635125 1361095836728993516684543)
                    ·
                      rfl

theorem cell22_3976087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 3, 1, 5].length) (baseStart_3976087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3976087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3976087 prefixEnd_3976087 := by exact prefixLift 3976087
  have htrace : WordTrace (prefixWord ++ tailWord_3976087) baseStart_3976087 baseEnd_3976087 := by
    simpa [prefixWord, tailWord_3976087, baseEnd_3976087] using wordTrace_append hprefix tailTrace_3976087
  have hstable : (prefixWord ++ tailWord_3976087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3976087).length < 2 ^ (prefixWord ++ tailWord_3976087).sum := by decide
  have hdescent : baseEnd_3976087 < baseStart_3976087 := by decide
  rcases family_descends (prefixWord ++ tailWord_3976087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3976121 : List Nat := [1, 2, 1, 4, 2, 3, 2, 2, 2, 3]
def baseStart_3976121 : Nat := 118140960795 + 3976121 * 2 ^ 59
def prefixEnd_3976121 : Nat := 4983230072969 + 3 ^ 40 * 3976121 * 2
def baseEnd_3976121 : Nat := 1361107475623828761334439

theorem tailTrace_3976121 : CollatzResearch.WordTrace tailWord_3976121 prefixEnd_3976121 1361107475623828761334439 := by
  unfold tailWord_3976121
  simp only [CollatzResearch.WordTrace]
  refine ⟨145021046828200159248592217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96680697885466772832394811 145021046828200159248592217)
  ·
    refine ⟨108765785121150119436444163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145021046828200159248592217 108765785121150119436444163)
    ·
      refine ⟨163148677681725179154666245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108765785121150119436444163 163148677681725179154666245)
      ·
        refine ⟨30590377065323471091499921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 163148677681725179154666245 30590377065323471091499921)
        ·
          refine ⟨22942782798992603318624941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30590377065323471091499921 22942782798992603318624941)
          ·
            refine ⟨8603543549622226244484353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22942782798992603318624941 8603543549622226244484353)
            ·
              refine ⟨6452657662216669683363265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8603543549622226244484353 6452657662216669683363265)
              ·
                refine ⟨4839493246662502262522449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6452657662216669683363265 4839493246662502262522449)
                ·
                  refine ⟨3629619934996876696891837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4839493246662502262522449 3629619934996876696891837)
                  ·
                    refine ⟨1361107475623828761334439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3629619934996876696891837 1361107475623828761334439)
                    ·
                      rfl

theorem cell22_3976121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 2, 2, 2, 3].length) (baseStart_3976121 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3976121 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3976121 prefixEnd_3976121 := by exact prefixLift 3976121
  have htrace : WordTrace (prefixWord ++ tailWord_3976121) baseStart_3976121 baseEnd_3976121 := by
    simpa [prefixWord, tailWord_3976121, baseEnd_3976121] using wordTrace_append hprefix tailTrace_3976121
  have hstable : (prefixWord ++ tailWord_3976121).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3976121).length < 2 ^ (prefixWord ++ tailWord_3976121).sum := by decide
  have hdescent : baseEnd_3976121 < baseStart_3976121 := by decide
  rcases family_descends (prefixWord ++ tailWord_3976121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3976226 : List Nat := [3, 3, 1, 1, 1, 3, 2, 3, 1, 4]
def baseStart_3976226 : Nat := 118140960795 + 3976226 * 2 ^ 59
def prefixEnd_3976226 : Nat := 4983230072969 + 3 ^ 40 * 3976226 * 2
def baseEnd_3976226 : Nat := 1361143419269643487459117

theorem tailTrace_3976226 : CollatzResearch.WordTrace tailWord_3976226 prefixEnd_3976226 1361143419269643487459117 := by
  unfold tailWord_3976226
  simp only [CollatzResearch.WordTrace]
  refine ⟨36256219123204940545291133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96683250995213174787443021 36256219123204940545291133)
  ·
    refine ⟨13596082171201852704484175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36256219123204940545291133 13596082171201852704484175)
    ·
      refine ⟨20394123256802779056726263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13596082171201852704484175 20394123256802779056726263)
      ·
        refine ⟨30591184885204168585089395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20394123256802779056726263 30591184885204168585089395)
        ·
          refine ⟨45886777327806252877634093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30591184885204168585089395 45886777327806252877634093)
          ·
            refine ⟨17207541497927344829112785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45886777327806252877634093 17207541497927344829112785)
            ·
              refine ⟨12905656123445508621834589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17207541497927344829112785 12905656123445508621834589)
              ·
                refine ⟨4839621046292065733187971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12905656123445508621834589 4839621046292065733187971)
                ·
                  refine ⟨7259431569438098599781957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4839621046292065733187971 7259431569438098599781957)
                  ·
                    refine ⟨1361143419269643487459117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7259431569438098599781957 1361143419269643487459117)
                    ·
                      rfl

theorem cell22_3976226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 3, 1, 4].length) (baseStart_3976226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3976226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3976226 prefixEnd_3976226 := by exact prefixLift 3976226
  have htrace : WordTrace (prefixWord ++ tailWord_3976226) baseStart_3976226 baseEnd_3976226 := by
    simpa [prefixWord, tailWord_3976226, baseEnd_3976226] using wordTrace_append hprefix tailTrace_3976226
  have hstable : (prefixWord ++ tailWord_3976226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3976226).length < 2 ^ (prefixWord ++ tailWord_3976226).sum := by decide
  have hdescent : baseEnd_3976226 < baseStart_3976226 := by decide
  rcases family_descends (prefixWord ++ tailWord_3976226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3976256 : List Nat := [2, 1, 1, 2, 2, 3, 3, 3, 2, 3]
def baseStart_3976256 : Nat := 118140960795 + 3976256 * 2 ^ 59
def prefixEnd_3976256 : Nat := 4983230072969 + 3 ^ 40 * 3976256 * 2
def baseEnd_3976256 : Nat := 1361153688882733409209025

theorem tailTrace_3976256 : CollatzResearch.WordTrace tailWord_3976256 prefixEnd_3976256 1361153688882733409209025 := by
  unfold tailWord_3976256
  simp only [CollatzResearch.WordTrace]
  refine ⟨72512985341355538652378311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96683980455140718203171081 72512985341355538652378311)
  ·
    refine ⟨108769478012033307978567467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72512985341355538652378311 108769478012033307978567467)
    ·
      refine ⟨163154217018049961967851201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108769478012033307978567467 163154217018049961967851201)
      ·
        refine ⟨122365662763537471475888401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163154217018049961967851201 122365662763537471475888401)
        ·
          refine ⟨91774247072653103606916301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122365662763537471475888401 91774247072653103606916301)
          ·
            refine ⟨34415342652244913852593613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91774247072653103606916301 34415342652244913852593613)
            ·
              refine ⟨12905753494591842694722605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34415342652244913852593613 12905753494591842694722605)
              ·
                refine ⟨4839657560471941010520977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12905753494591842694722605 4839657560471941010520977)
                ·
                  refine ⟨3629743170353955757890733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4839657560471941010520977 3629743170353955757890733)
                  ·
                    refine ⟨1361153688882733409209025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3629743170353955757890733 1361153688882733409209025)
                    ·
                      rfl

theorem cell22_3976256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 3, 2, 3].length) (baseStart_3976256 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3976256 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3976256 prefixEnd_3976256 := by exact prefixLift 3976256
  have htrace : WordTrace (prefixWord ++ tailWord_3976256) baseStart_3976256 baseEnd_3976256 := by
    simpa [prefixWord, tailWord_3976256, baseEnd_3976256] using wordTrace_append hprefix tailTrace_3976256
  have hstable : (prefixWord ++ tailWord_3976256).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3976256).length < 2 ^ (prefixWord ++ tailWord_3976256).sum := by decide
  have hdescent : baseEnd_3976256 < baseStart_3976256 := by decide
  rcases family_descends (prefixWord ++ tailWord_3976256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3976290 : List Nat := [3, 3, 2, 2, 1, 2, 2, 2, 2, 3]
def baseStart_3976290 : Nat := 118140960795 + 3976290 * 2 ^ 59
def prefixEnd_3976290 : Nat := 4983230072969 + 3 ^ 40 * 3976290 * 2
def baseEnd_3976290 : Nat := 1361165327777568653858921

theorem tailTrace_3976290 : CollatzResearch.WordTrace tailWord_3976290 prefixEnd_3976290 1361165327777568653858921 := by
  unfold tailWord_3976290
  simp only [CollatzResearch.WordTrace]
  refine ⟨36256802691146975277873581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96684807176391934074329549 36256802691146975277873581)
  ·
    refine ⟨13596301009180115729202593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36256802691146975277873581 13596301009180115729202593)
    ·
      refine ⟨10197225756885086796901945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13596301009180115729202593 10197225756885086796901945)
      ·
        refine ⟨7647919317663815097676459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10197225756885086796901945 7647919317663815097676459)
        ·
          refine ⟨11471878976495722646514689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7647919317663815097676459 11471878976495722646514689)
          ·
            refine ⟨8603909232371791984886017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11471878976495722646514689 8603909232371791984886017)
            ·
              refine ⟨6452931924278843988664513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8603909232371791984886017 6452931924278843988664513)
              ·
                refine ⟨4839698943209132991498385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6452931924278843988664513 4839698943209132991498385)
                ·
                  refine ⟨3629774207406849743623789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4839698943209132991498385 3629774207406849743623789)
                  ·
                    refine ⟨1361165327777568653858921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3629774207406849743623789 1361165327777568653858921)
                    ·
                      rfl

theorem cell22_3976290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 2, 2, 2, 3].length) (baseStart_3976290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3976290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3976290 prefixEnd_3976290 := by exact prefixLift 3976290
  have htrace : WordTrace (prefixWord ++ tailWord_3976290) baseStart_3976290 baseEnd_3976290 := by
    simpa [prefixWord, tailWord_3976290, baseEnd_3976290] using wordTrace_append hprefix tailTrace_3976290
  have hstable : (prefixWord ++ tailWord_3976290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3976290).length < 2 ^ (prefixWord ++ tailWord_3976290).sum := by decide
  have hdescent : baseEnd_3976290 < baseStart_3976290 := by decide
  rcases family_descends (prefixWord ++ tailWord_3976290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3976346 : List Nat := [3, 1, 1, 5, 1, 1, 1, 2, 2, 5]
def baseStart_3976346 : Nat := 118140960795 + 3976346 * 2 ^ 59
def prefixEnd_3976346 : Nat := 4983230072969 + 3 ^ 40 * 3976346 * 2
def baseEnd_3976346 : Nat := 1361184497722003174458749

theorem tailTrace_3976346 : CollatzResearch.WordTrace tailWord_3976346 prefixEnd_3976346 1361184497722003174458749 := by
  unfold tailWord_3976346
  simp only [CollatzResearch.WordTrace]
  refine ⟨36257313313096255668883223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96686168834923348450355261 36257313313096255668883223)
  ·
    refine ⟨54385969969644383503324835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36257313313096255668883223 54385969969644383503324835)
    ·
      refine ⟨81578954954466575254987253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54385969969644383503324835 81578954954466575254987253)
      ·
        refine ⟨7648027026981241430155055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 81578954954466575254987253 7648027026981241430155055)
        ·
          refine ⟨11472040540471862145232583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7648027026981241430155055 11472040540471862145232583)
          ·
            refine ⟨17208060810707793217848875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11472040540471862145232583 17208060810707793217848875)
            ·
              refine ⟨25812091216061689826773313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17208060810707793217848875 25812091216061689826773313)
              ·
                refine ⟨19359068412046267370079985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25812091216061689826773313 19359068412046267370079985)
                ·
                  refine ⟨14519301309034700527559989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19359068412046267370079985 14519301309034700527559989)
                  ·
                    refine ⟨1361184497722003174458749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14519301309034700527559989 1361184497722003174458749)
                    ·
                      rfl

theorem cell22_3976346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 2, 2, 5].length) (baseStart_3976346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3976346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3976346 prefixEnd_3976346 := by exact prefixLift 3976346
  have htrace : WordTrace (prefixWord ++ tailWord_3976346) baseStart_3976346 baseEnd_3976346 := by
    simpa [prefixWord, tailWord_3976346, baseEnd_3976346] using wordTrace_append hprefix tailTrace_3976346
  have hstable : (prefixWord ++ tailWord_3976346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3976346).length < 2 ^ (prefixWord ++ tailWord_3976346).sum := by decide
  have hdescent : baseEnd_3976346 < baseStart_3976346 := by decide
  rcases family_descends (prefixWord ++ tailWord_3976346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3976348 : List Nat := [2, 2, 3, 2, 1, 4, 1, 2, 5]
def baseStart_3976348 : Nat := 118140960795 + 3976348 * 2 ^ 59
def prefixEnd_3976348 : Nat := 4983230072969 + 3 ^ 40 * 3976348 * 2
def baseEnd_3976348 : Nat := 453728394120958611969581

theorem tailTrace_3976348 : CollatzResearch.WordTrace tailWord_3976348 prefixEnd_3976348 453728394120958611969581 := by
  unfold tailWord_3976348
  simp only [CollatzResearch.WordTrace]
  refine ⟨72514663099188888508552849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96686217465585184678070465 72514663099188888508552849)
  ·
    refine ⟨54385997324391666381414637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72514663099188888508552849 54385997324391666381414637)
    ·
      refine ⟨20394748996646874893030489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54385997324391666381414637 20394748996646874893030489)
      ·
        refine ⟨15296061747485156169772867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20394748996646874893030489 15296061747485156169772867)
        ·
          refine ⟨22944092621227734254659301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15296061747485156169772867 22944092621227734254659301)
          ·
            refine ⟨4302017366480200172748619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22944092621227734254659301 4302017366480200172748619)
            ·
              refine ⟨6453026049720300259122929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4302017366480200172748619 6453026049720300259122929)
              ·
                refine ⟨4839769537290225194342197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6453026049720300259122929 4839769537290225194342197)
                ·
                  refine ⟨453728394120958611969581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4839769537290225194342197 453728394120958611969581)
                  ·
                    rfl

theorem cell22_3976348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 1, 2, 5].length) (baseStart_3976348 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3976348 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3976348 prefixEnd_3976348 := by exact prefixLift 3976348
  have htrace : WordTrace (prefixWord ++ tailWord_3976348) baseStart_3976348 baseEnd_3976348 := by
    simpa [prefixWord, tailWord_3976348, baseEnd_3976348] using wordTrace_append hprefix tailTrace_3976348
  have hstable : (prefixWord ++ tailWord_3976348).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3976348).length < 2 ^ (prefixWord ++ tailWord_3976348).sum := by decide
  have hdescent : baseEnd_3976348 < baseStart_3976348 := by decide
  rcases family_descends (prefixWord ++ tailWord_3976348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3976365 : List Nat := [1, 5, 2, 1, 3, 1, 3, 1, 5]
def baseStart_3976365 : Nat := 118140960795 + 3976365 * 2 ^ 59
def prefixEnd_3976365 : Nat := 4983230072969 + 3 ^ 40 * 3976365 * 2
def baseEnd_3976365 : Nat := 453730333936764486077897

theorem tailTrace_3976365 : CollatzResearch.WordTrace tailWord_3976365 prefixEnd_3976365 453730333936764486077897 := by
  unfold tailWord_3976365
  simp only [CollatzResearch.WordTrace]
  refine ⟨145029946239316188920474549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96686630826210792613649699 145029946239316188920474549)
  ·
    refine ⟨13596557459935892711294489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 145029946239316188920474549 13596557459935892711294489)
    ·
      refine ⟨10197418094951919533470867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13596557459935892711294489 10197418094951919533470867)
      ·
        refine ⟨15296127142427879300206301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10197418094951919533470867 15296127142427879300206301)
        ·
          refine ⟨5736047678410454737577363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15296127142427879300206301 5736047678410454737577363)
          ·
            refine ⟨8604071517615682106366045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5736047678410454737577363 8604071517615682106366045)
            ·
              refine ⟨3226526819105880789887267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8604071517615682106366045 3226526819105880789887267)
              ·
                refine ⟨4839790228658821184830901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3226526819105880789887267 4839790228658821184830901)
                ·
                  refine ⟨453730333936764486077897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4839790228658821184830901 453730333936764486077897)
                  ·
                    rfl

theorem cell22_3976365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 3, 1, 5].length) (baseStart_3976365 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3976365 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3976365 prefixEnd_3976365 := by exact prefixLift 3976365
  have htrace : WordTrace (prefixWord ++ tailWord_3976365) baseStart_3976365 baseEnd_3976365 := by
    simpa [prefixWord, tailWord_3976365, baseEnd_3976365] using wordTrace_append hprefix tailTrace_3976365
  have hstable : (prefixWord ++ tailWord_3976365).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3976365).length < 2 ^ (prefixWord ++ tailWord_3976365).sum := by decide
  have hdescent : baseEnd_3976365 < baseStart_3976365 := by decide
  rcases family_descends (prefixWord ++ tailWord_3976365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3976386 : List Nat := [3, 5, 1, 1, 2, 2, 1, 3, 1, 3]
def baseStart_3976386 : Nat := 118140960795 + 3976386 * 2 ^ 59
def prefixEnd_3976386 : Nat := 4983230072969 + 3 ^ 40 * 3976386 * 2
def baseEnd_3976386 : Nat := 1361198190539456403458627

theorem tailTrace_3976386 : CollatzResearch.WordTrace tailWord_3976386 prefixEnd_3976386 1361198190539456403458627 := by
  unfold tailWord_3976386
  simp only [CollatzResearch.WordTrace]
  refine ⟨36257678043060027376747253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96687141448160073004659341 36257678043060027376747253)
  ·
    refine ⟨3399157316536877566570055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 36257678043060027376747253 3399157316536877566570055)
    ·
      refine ⟨5098735974805316349855083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3399157316536877566570055 5098735974805316349855083)
      ·
        refine ⟨7648103962207974524782625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5098735974805316349855083 7648103962207974524782625)
        ·
          refine ⟨5736077971655980893586969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7648103962207974524782625 5736077971655980893586969)
          ·
            refine ⟨4302058478741985670190227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5736077971655980893586969 4302058478741985670190227)
            ·
              refine ⟨6453087718112978505285341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4302058478741985670190227 6453087718112978505285341)
              ·
                refine ⟨2419907894292366939482003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6453087718112978505285341 2419907894292366939482003)
                ·
                  refine ⟨3629861841438550409223005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2419907894292366939482003 3629861841438550409223005)
                  ·
                    refine ⟨1361198190539456403458627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3629861841438550409223005 1361198190539456403458627)
                    ·
                      rfl

theorem cell22_3976386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 1, 3, 1, 3].length) (baseStart_3976386 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3976386 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3976386 prefixEnd_3976386 := by exact prefixLift 3976386
  have htrace : WordTrace (prefixWord ++ tailWord_3976386) baseStart_3976386 baseEnd_3976386 := by
    simpa [prefixWord, tailWord_3976386, baseEnd_3976386] using wordTrace_append hprefix tailTrace_3976386
  have hstable : (prefixWord ++ tailWord_3976386).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3976386).length < 2 ^ (prefixWord ++ tailWord_3976386).sum := by decide
  have hdescent : baseEnd_3976386 < baseStart_3976386 := by decide
  rcases family_descends (prefixWord ++ tailWord_3976386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3976496 : List Nat := [2, 1, 1, 1, 2, 2, 3, 3, 3, 4]
def baseStart_3976496 : Nat := 118140960795 + 3976496 * 2 ^ 59
def prefixEnd_3976496 : Nat := 4983230072969 + 3 ^ 40 * 3976496 * 2
def baseEnd_3976496 : Nat := 1361235845787452783208289

theorem tailTrace_3976496 : CollatzResearch.WordTrace tailWord_3976496 prefixEnd_3976496 1361235845787452783208289 := by
  unfold tailWord_3976496
  simp only [CollatzResearch.WordTrace]
  refine ⟨72517362100920799146746671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96689816134561065528995561 72517362100920799146746671)
  ·
    refine ⟨108776043151381198720120007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72517362100920799146746671 108776043151381198720120007)
    ·
      refine ⟨163164064727071798080180011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108776043151381198720120007 163164064727071798080180011)
      ·
        refine ⟨244746097090607697120270017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163164064727071798080180011 244746097090607697120270017)
        ·
          refine ⟨183559572817955772840202513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 244746097090607697120270017 183559572817955772840202513)
          ·
            refine ⟨137669679613466829630151885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183559572817955772840202513 137669679613466829630151885)
            ·
              refine ⟨51626129855050061111306957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 137669679613466829630151885 51626129855050061111306957)
              ·
                refine ⟨19359798695643772916740109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51626129855050061111306957 19359798695643772916740109)
                ·
                  refine ⟨7259924510866414843777541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19359798695643772916740109 7259924510866414843777541)
                  ·
                    refine ⟨1361235845787452783208289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7259924510866414843777541 1361235845787452783208289)
                    ·
                      rfl

theorem cell22_3976496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 3, 3, 4].length) (baseStart_3976496 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3976496 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3976496 prefixEnd_3976496 := by exact prefixLift 3976496
  have htrace : WordTrace (prefixWord ++ tailWord_3976496) baseStart_3976496 baseEnd_3976496 := by
    simpa [prefixWord, tailWord_3976496, baseEnd_3976496] using wordTrace_append hprefix tailTrace_3976496
  have hstable : (prefixWord ++ tailWord_3976496).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3976496).length < 2 ^ (prefixWord ++ tailWord_3976496).sum := by decide
  have hdescent : baseEnd_3976496 < baseStart_3976496 := by decide
  rcases family_descends (prefixWord ++ tailWord_3976496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3976528 : List Nat := [2, 1, 1, 1, 1, 5, 1, 6, 4]
def baseStart_3976528 : Nat := 118140960795 + 3976528 * 2 ^ 59
def prefixEnd_3976528 : Nat := 4983230072969 + 3 ^ 40 * 3976528 * 2
def baseEnd_3976528 : Nat := 453748933347138455469397

theorem tailTrace_3976528 : CollatzResearch.WordTrace tailWord_3976528 prefixEnd_3976528 453748933347138455469397 := by
  unfold tailWord_3976528
  simp only [CollatzResearch.WordTrace]
  refine ⟨72517945668862833879329119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96690594225150445172438825 72517945668862833879329119)
  ·
    refine ⟨108776918503294250818993679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72517945668862833879329119 108776918503294250818993679)
    ·
      refine ⟨163165377754941376228490519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108776918503294250818993679 163165377754941376228490519)
      ·
        refine ⟨244748066632412064342735779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163165377754941376228490519 244748066632412064342735779)
        ·
          refine ⟨367122099948618096514103669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244748066632412064342735779 367122099948618096514103669)
          ·
            refine ⟨34417696870182946548197219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 367122099948618096514103669 34417696870182946548197219)
            ·
              refine ⟨51626545305274419822295829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34417696870182946548197219 51626545305274419822295829)
              ·
                refine ⟨2419994311184738429170117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 51626545305274419822295829 2419994311184738429170117)
                ·
                  refine ⟨453748933347138455469397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2419994311184738429170117 453748933347138455469397)
                  ·
                    rfl

theorem cell22_3976528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 6, 4].length) (baseStart_3976528 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3976528 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3976528 prefixEnd_3976528 := by exact prefixLift 3976528
  have htrace : WordTrace (prefixWord ++ tailWord_3976528) baseStart_3976528 baseEnd_3976528 := by
    simpa [prefixWord, tailWord_3976528, baseEnd_3976528] using wordTrace_append hprefix tailTrace_3976528
  have hstable : (prefixWord ++ tailWord_3976528).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3976528).length < 2 ^ (prefixWord ++ tailWord_3976528).sum := by decide
  have hdescent : baseEnd_3976528 < baseStart_3976528 := by decide
  rcases family_descends (prefixWord ++ tailWord_3976528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3976590 : List Nat := [4, 1, 1, 4, 2, 1, 2, 7]
def baseStart_3976590 : Nat := 118140960795 + 3976590 * 2 ^ 59
def prefixEnd_3976590 : Nat := 4983230072969 + 3 ^ 40 * 3976590 * 2
def baseEnd_3976590 : Nat := 151252002656496430150889

theorem tailTrace_3976590 : CollatzResearch.WordTrace tailWord_3976590 prefixEnd_3976590 151252002656496430150889 := by
  unfold tailWord_3976590
  simp only [CollatzResearch.WordTrace]
  refine ⟨18129769082937631543426903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96692101775667368231610149 18129769082937631543426903)
  ·
    refine ⟨27194653624406447315140355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18129769082937631543426903 27194653624406447315140355)
    ·
      refine ⟨40791980436609670972710533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27194653624406447315140355 40791980436609670972710533)
      ·
        refine ⟨7648496331864313307383225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40791980436609670972710533 7648496331864313307383225)
        ·
          refine ⟨5736372248898234980537419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7648496331864313307383225 5736372248898234980537419)
          ·
            refine ⟨8604558373347352470806129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5736372248898234980537419 8604558373347352470806129)
            ·
              refine ⟨6453418780010514353104597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8604558373347352470806129 6453418780010514353104597)
              ·
                refine ⟨151252002656496430150889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6453418780010514353104597 151252002656496430150889)
                ·
                  rfl

theorem cell22_3976590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 2, 7].length) (baseStart_3976590 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3976590 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3976590 prefixEnd_3976590 := by exact prefixLift 3976590
  have htrace : WordTrace (prefixWord ++ tailWord_3976590) baseStart_3976590 baseEnd_3976590 := by
    simpa [prefixWord, tailWord_3976590, baseEnd_3976590] using wordTrace_append hprefix tailTrace_3976590
  have hstable : (prefixWord ++ tailWord_3976590).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3976590).length < 2 ^ (prefixWord ++ tailWord_3976590).sum := by decide
  have hdescent : baseEnd_3976590 < baseStart_3976590 := by decide
  rcases family_descends (prefixWord ++ tailWord_3976590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3976594 : List Nat := [3, 2, 3, 3, 1, 1, 1, 3, 2, 3]
def baseStart_3976594 : Nat := 118140960795 + 3976594 * 2 ^ 59
def prefixEnd_3976594 : Nat := 4983230072969 + 3 ^ 40 * 3976594 * 2
def baseEnd_3976594 : Nat := 1361269393190213194257989

theorem tailTrace_3976594 : CollatzResearch.WordTrace tailWord_3976594 prefixEnd_3976594 1361269393190213194257989 := by
  unfold tailWord_3976594
  simp only [CollatzResearch.WordTrace]
  refine ⟨36259574638871640257640209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96692199036991040687040557 36259574638871640257640209)
  ·
    refine ⟨27194680979153730193230157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36259574638871640257640209 27194680979153730193230157)
    ·
      refine ⟨10198005367182648822461309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27194680979153730193230157 10198005367182648822461309)
      ·
        refine ⟨3824252012693493308422991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10198005367182648822461309 3824252012693493308422991)
        ·
          refine ⟨5736378019040239962634487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3824252012693493308422991 5736378019040239962634487)
          ·
            refine ⟨8604567028560359943951731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5736378019040239962634487 8604567028560359943951731)
            ·
              refine ⟨12906850542840539915927597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8604567028560359943951731 12906850542840539915927597)
              ·
                refine ⟨4840068953565202468472849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12906850542840539915927597 4840068953565202468472849)
                ·
                  refine ⟨3630051715173901851354637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4840068953565202468472849 3630051715173901851354637)
                  ·
                    refine ⟨1361269393190213194257989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3630051715173901851354637 1361269393190213194257989)
                    ·
                      rfl

theorem cell22_3976594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 3, 2, 3].length) (baseStart_3976594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3976594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3976594 prefixEnd_3976594 := by exact prefixLift 3976594
  have htrace : WordTrace (prefixWord ++ tailWord_3976594) baseStart_3976594 baseEnd_3976594 := by
    simpa [prefixWord, tailWord_3976594, baseEnd_3976594] using wordTrace_append hprefix tailTrace_3976594
  have hstable : (prefixWord ++ tailWord_3976594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3976594).length < 2 ^ (prefixWord ++ tailWord_3976594).sum := by decide
  have hdescent : baseEnd_3976594 < baseStart_3976594 := by decide
  rcases family_descends (prefixWord ++ tailWord_3976594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3976648 : List Nat := [2, 1, 3, 1, 3, 1, 1, 1, 5, 4]
def baseStart_3976648 : Nat := 118140960795 + 3976648 * 2 ^ 59
def prefixEnd_3976648 : Nat := 4983230072969 + 3 ^ 40 * 3976648 * 2
def baseEnd_3976648 : Nat := 1361287878493775053407823

theorem tailTrace_3976648 : CollatzResearch.WordTrace tailWord_3976648 prefixEnd_3976648 1361287878493775053407823 := by
  unfold tailWord_3976648
  simp only [CollatzResearch.WordTrace]
  refine ⟨72520134048645464126513299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96693512064860618835351065 72520134048645464126513299)
  ·
    refine ⟨108780201072968196189769949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72520134048645464126513299 108780201072968196189769949)
    ·
      refine ⟨40792575402363073571163731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108780201072968196189769949 40792575402363073571163731)
      ·
        refine ⟨61188863103544610356745597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40792575402363073571163731 61188863103544610356745597)
        ·
          refine ⟨22945823663829228883779599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61188863103544610356745597 22945823663829228883779599)
          ·
            refine ⟨34418735495743843325669399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22945823663829228883779599 34418735495743843325669399)
            ·
              refine ⟨51628103243615764988504099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34418735495743843325669399 51628103243615764988504099)
              ·
                refine ⟨77442154865423647482756149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51628103243615764988504099 77442154865423647482756149)
                ·
                  refine ⟨7260202018633466951508389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 77442154865423647482756149 7260202018633466951508389)
                  ·
                    refine ⟨1361287878493775053407823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7260202018633466951508389 1361287878493775053407823)
                    ·
                      rfl

theorem cell22_3976648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 1, 5, 4].length) (baseStart_3976648 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3976648 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3976648 prefixEnd_3976648 := by exact prefixLift 3976648
  have htrace : WordTrace (prefixWord ++ tailWord_3976648) baseStart_3976648 baseEnd_3976648 := by
    simpa [prefixWord, tailWord_3976648, baseEnd_3976648] using wordTrace_append hprefix tailTrace_3976648
  have hstable : (prefixWord ++ tailWord_3976648).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3976648).length < 2 ^ (prefixWord ++ tailWord_3976648).sum := by decide
  have hdescent : baseEnd_3976648 < baseStart_3976648 := by decide
  rcases family_descends (prefixWord ++ tailWord_3976648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3976682 : List Nat := [3, 1, 3, 1, 4, 1, 1, 3, 1, 4]
def baseStart_3976682 : Nat := 118140960795 + 3976682 * 2 ^ 59
def prefixEnd_3976682 : Nat := 4983230072969 + 3 ^ 40 * 3976682 * 2
def baseEnd_3976682 : Nat := 1361299517388610298057719

theorem tailTrace_3976682 : CollatzResearch.WordTrace tailWord_3976682 prefixEnd_3976682 1361299517388610298057719 := by
  unfold tailWord_3976682
  simp only [CollatzResearch.WordTrace]
  refine ⟨36260377044791938014941075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96694338786111834706509533 36260377044791938014941075)
  ·
    refine ⟨54390565567187907022411613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36260377044791938014941075 54390565567187907022411613)
    ·
      refine ⟨20396462087695465133404355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54390565567187907022411613 20396462087695465133404355)
      ·
        refine ⟨30594693131543197700106533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20396462087695465133404355 30594693131543197700106533)
        ·
          refine ⟨5736504962164349568769975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30594693131543197700106533 5736504962164349568769975)
          ·
            refine ⟨8604757443246524353154963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5736504962164349568769975 8604757443246524353154963)
            ·
              refine ⟨12907136164869786529732445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8604757443246524353154963 12907136164869786529732445)
              ·
                refine ⟨4840176061826169948649667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12907136164869786529732445 4840176061826169948649667)
                ·
                  refine ⟨7260264092739254922974501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4840176061826169948649667 7260264092739254922974501)
                  ·
                    refine ⟨1361299517388610298057719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7260264092739254922974501 1361299517388610298057719)
                    ·
                      rfl

theorem cell22_3976682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 3, 1, 4].length) (baseStart_3976682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3976682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3976682 prefixEnd_3976682 := by exact prefixLift 3976682
  have htrace : WordTrace (prefixWord ++ tailWord_3976682) baseStart_3976682 baseEnd_3976682 := by
    simpa [prefixWord, tailWord_3976682, baseEnd_3976682] using wordTrace_append hprefix tailTrace_3976682
  have hstable : (prefixWord ++ tailWord_3976682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3976682).length < 2 ^ (prefixWord ++ tailWord_3976682).sum := by decide
  have hdescent : baseEnd_3976682 < baseStart_3976682 := by decide
  rcases family_descends (prefixWord ++ tailWord_3976682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3976695 : List Nat := [1, 1, 3, 1, 1, 1, 1, 8, 2, 3]
def baseStart_3976695 : Nat := 118140960795 + 3976695 * 2 ^ 59
def prefixEnd_3976695 : Nat := 4983230072969 + 3 ^ 40 * 3976695 * 2
def baseEnd_3976695 : Nat := 1361303967554282597482679

theorem tailTrace_3976695 : CollatzResearch.WordTrace tailWord_3976695 prefixEnd_3976695 1361303967554282597482679 := by
  unfold tailWord_3976695
  simp only [CollatzResearch.WordTrace]
  refine ⟨145041982328120655279987539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96694654885413770186658359 145041982328120655279987539)
  ·
    refine ⟨217562973492180982919981309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145041982328120655279987539 217562973492180982919981309)
    ·
      refine ⟨81586115059567868594992991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 217562973492180982919981309 81586115059567868594992991)
      ·
        refine ⟨122379172589351802892489487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81586115059567868594992991 122379172589351802892489487)
        ·
          refine ⟨183568758884027704338734231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122379172589351802892489487 183568758884027704338734231)
          ·
            refine ⟨275353138326041556508101347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183568758884027704338734231 275353138326041556508101347)
            ·
              refine ⟨413029707489062334762152021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 275353138326041556508101347 413029707489062334762152021)
              ·
                refine ⟨4840191884637449235493969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 413029707489062334762152021 4840191884637449235493969)
                ·
                  refine ⟨3630143913478086926620477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4840191884637449235493969 3630143913478086926620477)
                  ·
                    refine ⟨1361303967554282597482679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3630143913478086926620477 1361303967554282597482679)
                    ·
                      rfl

theorem cell22_3976695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 8, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 8, 2, 3].length) (baseStart_3976695 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3976695 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3976695 prefixEnd_3976695 := by exact prefixLift 3976695
  have htrace : WordTrace (prefixWord ++ tailWord_3976695) baseStart_3976695 baseEnd_3976695 := by
    simpa [prefixWord, tailWord_3976695, baseEnd_3976695] using wordTrace_append hprefix tailTrace_3976695
  have hstable : (prefixWord ++ tailWord_3976695).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3976695).length < 2 ^ (prefixWord ++ tailWord_3976695).sum := by decide
  have hdescent : baseEnd_3976695 < baseStart_3976695 := by decide
  rcases family_descends (prefixWord ++ tailWord_3976695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3976725 : List Nat := [1, 3, 2, 1, 3, 2, 4, 6]
def baseStart_3976725 : Nat := 118140960795 + 3976725 * 2 ^ 59
def prefixEnd_3976725 : Nat := 4983230072969 + 3 ^ 40 * 3976725 * 2
def baseEnd_3976725 : Nat := 151257137463041391025843

theorem tailTrace_3976725 : CollatzResearch.WordTrace tailWord_3976725 prefixEnd_3976725 151257137463041391025843 := by
  unfold tailWord_3976725
  simp only [CollatzResearch.WordTrace]
  refine ⟨145043076518011970403579629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96695384345341313602386419 145043076518011970403579629)
  ·
    refine ⟨54391153694254488901342361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145043076518011970403579629 54391153694254488901342361)
    ·
      refine ⟨40793365270690866676006771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54391153694254488901342361 40793365270690866676006771)
      ·
        refine ⟨61190047906036300014010157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40793365270690866676006771 61190047906036300014010157)
        ·
          refine ⟨22946267964763612505253809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61190047906036300014010157 22946267964763612505253809)
          ·
            refine ⟨17209700973572709378940357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22946267964763612505253809 17209700973572709378940357)
            ·
              refine ⟨3226818932544883008551317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17209700973572709378940357 3226818932544883008551317)
              ·
                refine ⟨151257137463041391025843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3226818932544883008551317 151257137463041391025843)
                ·
                  rfl

theorem cell22_3976725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 4, 6].length) (baseStart_3976725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3976725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3976725 prefixEnd_3976725 := by exact prefixLift 3976725
  have htrace : WordTrace (prefixWord ++ tailWord_3976725) baseStart_3976725 baseEnd_3976725 := by
    simpa [prefixWord, tailWord_3976725, baseEnd_3976725] using wordTrace_append hprefix tailTrace_3976725
  have hstable : (prefixWord ++ tailWord_3976725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3976725).length < 2 ^ (prefixWord ++ tailWord_3976725).sum := by decide
  have hdescent : baseEnd_3976725 < baseStart_3976725 := by decide
  rcases family_descends (prefixWord ++ tailWord_3976725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3976757 : List Nat := [1, 3, 3, 1, 1, 3, 3, 1, 3, 3]
def baseStart_3976757 : Nat := 118140960795 + 3976757 * 2 ^ 59
def prefixEnd_3976757 : Nat := 4983230072969 + 3 ^ 40 * 3976757 * 2
def baseEnd_3976757 : Nat := 1361325191421335102432489

theorem tailTrace_3976757 : CollatzResearch.WordTrace tailWord_3976757 prefixEnd_3976757 1361325191421335102432489 := by
  unfold tailWord_3976757
  simp only [CollatzResearch.WordTrace]
  refine ⟨145044243653896039868744525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96696162435930693245829683 145044243653896039868744525)
  ·
    refine ⟨54391591370211014950779197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145044243653896039868744525 54391591370211014950779197)
    ·
      refine ⟨20396846763829130606542199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54391591370211014950779197 20396846763829130606542199)
      ·
        refine ⟨30595270145743695909813299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20396846763829130606542199 30595270145743695909813299)
        ·
          refine ⟨45892905218615543864719949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30595270145743695909813299 45892905218615543864719949)
          ·
            refine ⟨17209839456980828949269981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45892905218615543864719949 17209839456980828949269981)
            ·
              refine ⟨6453689796367810855976243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17209839456980828949269981 6453689796367810855976243)
              ·
                refine ⟨9680534694551716283964365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6453689796367810855976243 9680534694551716283964365)
                ·
                  refine ⟨3630200510456893606486637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9680534694551716283964365 3630200510456893606486637)
                  ·
                    refine ⟨1361325191421335102432489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3630200510456893606486637 1361325191421335102432489)
                    ·
                      rfl

theorem cell22_3976757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 3, 1, 3, 3].length) (baseStart_3976757 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3976757 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3976757 prefixEnd_3976757 := by exact prefixLift 3976757
  have htrace : WordTrace (prefixWord ++ tailWord_3976757) baseStart_3976757 baseEnd_3976757 := by
    simpa [prefixWord, tailWord_3976757, baseEnd_3976757] using wordTrace_append hprefix tailTrace_3976757
  have hstable : (prefixWord ++ tailWord_3976757).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3976757).length < 2 ^ (prefixWord ++ tailWord_3976757).sum := by decide
  have hdescent : baseEnd_3976757 < baseStart_3976757 := by decide
  rcases family_descends (prefixWord ++ tailWord_3976757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3976768 : List Nat := [2, 1, 1, 2, 2, 2, 1, 3, 1, 7]
def baseStart_3976768 : Nat := 118140960795 + 3976768 * 2 ^ 59
def prefixEnd_3976768 : Nat := 4983230072969 + 3 ^ 40 * 3976768 * 2
def baseEnd_3976768 : Nat := 1361328956946134740407455

theorem tailTrace_3976768 : CollatzResearch.WordTrace tailWord_3976768 prefixEnd_3976768 1361328956946134740407455 := by
  unfold tailWord_3976768
  simp only [CollatzResearch.WordTrace]
  refine ⟨72522322428428094373697479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96696429904570792498263305 72522322428428094373697479)
  ·
    refine ⟨108783483642642141560546219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72522322428428094373697479 108783483642642141560546219)
    ·
      refine ⟨163175225463963212340819329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108783483642642141560546219 163175225463963212340819329)
      ·
        refine ⟨122381419097972409255614497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163175225463963212340819329 122381419097972409255614497)
        ·
          refine ⟨91786064323479306941710873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122381419097972409255614497 91786064323479306941710873)
          ·
            refine ⟨68839548242609480206283155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91786064323479306941710873 68839548242609480206283155)
            ·
              refine ⟨103259322363914220309424733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68839548242609480206283155 103259322363914220309424733)
              ·
                refine ⟨38722245886467832616034275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103259322363914220309424733 38722245886467832616034275)
                ·
                  refine ⟨58083368829701748924051413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38722245886467832616034275 58083368829701748924051413)
                  ·
                    refine ⟨1361328956946134740407455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58083368829701748924051413 1361328956946134740407455)
                    ·
                      rfl

theorem cell22_3976768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 3, 1, 7].length) (baseStart_3976768 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3976768 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3976768 prefixEnd_3976768 := by exact prefixLift 3976768
  have htrace : WordTrace (prefixWord ++ tailWord_3976768) baseStart_3976768 baseEnd_3976768 := by
    simpa [prefixWord, tailWord_3976768, baseEnd_3976768] using wordTrace_append hprefix tailTrace_3976768
  have hstable : (prefixWord ++ tailWord_3976768).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3976768).length < 2 ^ (prefixWord ++ tailWord_3976768).sum := by decide
  have hdescent : baseEnd_3976768 < baseStart_3976768 := by decide
  rcases family_descends (prefixWord ++ tailWord_3976768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3976808 : List Nat := [2, 1, 4, 3, 1, 3, 2, 2, 1, 3]
def baseStart_3976808 : Nat := 118140960795 + 3976808 * 2 ^ 59
def prefixEnd_3976808 : Nat := 4983230072969 + 3 ^ 40 * 3976808 * 2
def baseEnd_3976808 : Nat := 1361342649763587969407333

theorem tailTrace_3976808 : CollatzResearch.WordTrace tailWord_3976808 prefixEnd_3976808 1361342649763587969407333 := by
  unfold tailWord_3976808
  simp only [CollatzResearch.WordTrace]
  refine ⟨72523051888355637789425539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96697402517807517052567385 72523051888355637789425539)
  ·
    refine ⟨108784577832533456684138309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72523051888355637789425539 108784577832533456684138309)
    ·
      refine ⟨20397108343600023128275933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108784577832533456684138309 20397108343600023128275933)
      ·
        refine ⟨7648915628850008673103475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20397108343600023128275933 7648915628850008673103475)
        ·
          refine ⟨11473373443275013009655213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7648915628850008673103475 11473373443275013009655213)
          ·
            refine ⟨4302515041228129878620705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11473373443275013009655213 4302515041228129878620705)
            ·
              refine ⟨3226886280921097408965529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4302515041228129878620705 3226886280921097408965529)
              ·
                refine ⟨2420164710690823056724147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3226886280921097408965529 2420164710690823056724147)
                ·
                  refine ⟨3630247066036234585086221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2420164710690823056724147 3630247066036234585086221)
                  ·
                    refine ⟨1361342649763587969407333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3630247066036234585086221 1361342649763587969407333)
                    ·
                      rfl

theorem cell22_3976808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 2, 2, 1, 3].length) (baseStart_3976808 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3976808 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3976808 prefixEnd_3976808 := by exact prefixLift 3976808
  have htrace : WordTrace (prefixWord ++ tailWord_3976808) baseStart_3976808 baseEnd_3976808 := by
    simpa [prefixWord, tailWord_3976808, baseEnd_3976808] using wordTrace_append hprefix tailTrace_3976808
  have hstable : (prefixWord ++ tailWord_3976808).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3976808).length < 2 ^ (prefixWord ++ tailWord_3976808).sum := by decide
  have hdescent : baseEnd_3976808 < baseStart_3976808 := by decide
  rcases family_descends (prefixWord ++ tailWord_3976808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3976864 : List Nat := [2, 1, 1, 4, 3, 1, 3, 2, 2, 3]
def baseStart_3976864 : Nat := 118140960795 + 3976864 * 2 ^ 59
def prefixEnd_3976864 : Nat := 4983230072969 + 3 ^ 40 * 3976864 * 2
def baseEnd_3976864 : Nat := 1361361819708022490007161

theorem tailTrace_3976864 : CollatzResearch.WordTrace tailWord_3976864 prefixEnd_3976864 1361361819708022490007161 := by
  unfold tailWord_3976864
  simp only [CollatzResearch.WordTrace]
  refine ⟨72524073132254198571444823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96698764176338931428593097 72524073132254198571444823)
  ·
    refine ⟨108786109698381297857167235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72524073132254198571444823 108786109698381297857167235)
    ·
      refine ⟨163179164547571946785750853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108786109698381297857167235 163179164547571946785750853)
      ·
        refine ⟨30596093352669740022328285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 163179164547571946785750853 30596093352669740022328285)
        ·
          refine ⟨11473535007251152508373107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30596093352669740022328285 11473535007251152508373107)
          ·
            refine ⟨17210302510876728762559661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11473535007251152508373107 17210302510876728762559661)
            ·
              refine ⟨6453863441578773285959873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17210302510876728762559661 6453863441578773285959873)
              ·
                refine ⟨4840397581184079964469905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6453863441578773285959873 4840397581184079964469905)
                ·
                  refine ⟨3630298185888059973352429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4840397581184079964469905 3630298185888059973352429)
                  ·
                    refine ⟨1361361819708022490007161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3630298185888059973352429 1361361819708022490007161)
                    ·
                      rfl

theorem cell22_3976864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 3, 2, 2, 3].length) (baseStart_3976864 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3976864 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3976864 prefixEnd_3976864 := by exact prefixLift 3976864
  have htrace : WordTrace (prefixWord ++ tailWord_3976864) baseStart_3976864 baseEnd_3976864 := by
    simpa [prefixWord, tailWord_3976864, baseEnd_3976864] using wordTrace_append hprefix tailTrace_3976864
  have hstable : (prefixWord ++ tailWord_3976864).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3976864).length < 2 ^ (prefixWord ++ tailWord_3976864).sum := by decide
  have hdescent : baseEnd_3976864 < baseStart_3976864 := by decide
  rcases family_descends (prefixWord ++ tailWord_3976864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3976894 : List Nat := [4, 2, 1, 1, 2, 4, 2, 6]
def baseStart_3976894 : Nat := 118140960795 + 3976894 * 2 ^ 59
def prefixEnd_3976894 : Nat := 4983230072969 + 3 ^ 40 * 3976894 * 2
def baseEnd_3976894 : Nat := 151263565480123601306341

theorem tailTrace_3976894 : CollatzResearch.WordTrace tailWord_3976894 prefixEnd_3976894 151263565480123601306341 := by
  unfold tailWord_3976894
  simp only [CollatzResearch.WordTrace]
  refine ⟨18131155056799964033310217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96699493636266474844321157 18131155056799964033310217)
  ·
    refine ⟨13598366292599973024982663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18131155056799964033310217 13598366292599973024982663)
    ·
      refine ⟨20397549438899959537473995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13598366292599973024982663 20397549438899959537473995)
      ·
        refine ⟨30596324158349939306210993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20397549438899959537473995 30596324158349939306210993)
        ·
          refine ⟨22947243118762454479658245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30596324158349939306210993 22947243118762454479658245)
          ·
            refine ⟨4302608084767960214935921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22947243118762454479658245 4302608084767960214935921)
            ·
              refine ⟨3226956063575970161201941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4302608084767960214935921 3226956063575970161201941)
              ·
                refine ⟨151263565480123601306341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3226956063575970161201941 151263565480123601306341)
                ·
                  rfl

theorem cell22_3976894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 2, 6].length) (baseStart_3976894 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3976894 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3976894 prefixEnd_3976894 := by exact prefixLift 3976894
  have htrace : WordTrace (prefixWord ++ tailWord_3976894) baseStart_3976894 baseEnd_3976894 := by
    simpa [prefixWord, tailWord_3976894, baseEnd_3976894] using wordTrace_append hprefix tailTrace_3976894
  have hstable : (prefixWord ++ tailWord_3976894).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3976894).length < 2 ^ (prefixWord ++ tailWord_3976894).sum := by decide
  have hdescent : baseEnd_3976894 < baseStart_3976894 := by decide
  rcases family_descends (prefixWord ++ tailWord_3976894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3976952 : List Nat := [2, 1, 2, 1, 1, 2, 2, 6, 1, 4]
def baseStart_3976952 : Nat := 118140960795 + 3976952 * 2 ^ 59
def prefixEnd_3976952 : Nat := 4983230072969 + 3 ^ 40 * 3976952 * 2
def baseEnd_3976952 : Nat := 1361391943906419593806891

theorem tailTrace_3976952 : CollatzResearch.WordTrace tailWord_3976952 prefixEnd_3976952 1361391943906419593806891 := by
  unfold tailWord_3976952
  simp only [CollatzResearch.WordTrace]
  refine ⟨72525677944094794086046555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96700903925459725448062073 72525677944094794086046555)
  ·
    refine ⟨108788516916142191129069833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72525677944094794086046555 108788516916142191129069833)
    ·
      refine ⟨81591387687106643346802375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108788516916142191129069833 81591387687106643346802375)
      ·
        refine ⟨122387081530659965020203563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81591387687106643346802375 122387081530659965020203563)
        ·
          refine ⟨183580622295989947530305345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122387081530659965020203563 183580622295989947530305345)
          ·
            refine ⟨137685466721992460647729009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183580622295989947530305345 137685466721992460647729009)
            ·
              refine ⟨103264100041494345485796757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137685466721992460647729009 103264100041494345485796757)
              ·
                refine ⟨4840504689445047444646723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 103264100041494345485796757 4840504689445047444646723)
                ·
                  refine ⟨7260757034167571166970085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4840504689445047444646723 7260757034167571166970085)
                  ·
                    refine ⟨1361391943906419593806891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7260757034167571166970085 1361391943906419593806891)
                    ·
                      rfl

theorem cell22_3976952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 6, 1, 4].length) (baseStart_3976952 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3976952 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3976952 prefixEnd_3976952 := by exact prefixLift 3976952
  have htrace : WordTrace (prefixWord ++ tailWord_3976952) baseStart_3976952 baseEnd_3976952 := by
    simpa [prefixWord, tailWord_3976952, baseEnd_3976952] using wordTrace_append hprefix tailTrace_3976952
  have hstable : (prefixWord ++ tailWord_3976952).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3976952).length < 2 ^ (prefixWord ++ tailWord_3976952).sum := by decide
  have hdescent : baseEnd_3976952 < baseStart_3976952 := by decide
  rcases family_descends (prefixWord ++ tailWord_3976952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3977087 : List Nat := [1, 1, 2, 2, 1, 1, 3, 2, 5, 4]
def baseStart_3977087 : Nat := 118140960795 + 3977087 * 2 ^ 59
def prefixEnd_3977087 : Nat := 4983230072969 + 3 ^ 40 * 3977087 * 2
def baseEnd_3977087 : Nat := 1361438157165324241681477

theorem tailTrace_3977087 : CollatzResearch.WordTrace tailWord_3977087 prefixEnd_3977087 1361438157165324241681477 := by
  unfold tailWord_3977087
  simp only [CollatzResearch.WordTrace]
  refine ⟨145056279742700506228257515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96704186495133670818838343 145056279742700506228257515)
  ·
    refine ⟨217584419614050759342386273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145056279742700506228257515 217584419614050759342386273)
    ·
      refine ⟨163188314710538069506789705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217584419614050759342386273 163188314710538069506789705)
      ·
        refine ⟨122391236032903552130092279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163188314710538069506789705 122391236032903552130092279)
        ·
          refine ⟨183586854049355328195138419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122391236032903552130092279 183586854049355328195138419)
          ·
            refine ⟨275380281074032992292707629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183586854049355328195138419 275380281074032992292707629)
            ·
              refine ⟨103267605402762372109765361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 275380281074032992292707629 103267605402762372109765361)
              ·
                refine ⟨77450704052071779082324021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103267605402762372109765361 77450704052071779082324021)
                ·
                  refine ⟨7261003504881729288967877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 77450704052071779082324021 7261003504881729288967877)
                  ·
                    refine ⟨1361438157165324241681477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7261003504881729288967877 1361438157165324241681477)
                    ·
                      rfl

theorem cell22_3977087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 2, 5, 4].length) (baseStart_3977087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3977087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3977087 prefixEnd_3977087 := by exact prefixLift 3977087
  have htrace : WordTrace (prefixWord ++ tailWord_3977087) baseStart_3977087 baseEnd_3977087 := by
    simpa [prefixWord, tailWord_3977087, baseEnd_3977087] using wordTrace_append hprefix tailTrace_3977087
  have hstable : (prefixWord ++ tailWord_3977087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3977087).length < 2 ^ (prefixWord ++ tailWord_3977087).sum := by decide
  have hdescent : baseEnd_3977087 < baseStart_3977087 := by decide
  rcases family_descends (prefixWord ++ tailWord_3977087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3977095 : List Nat := [1, 1, 4, 2, 4, 1, 3, 2, 1, 3]
def baseStart_3977095 : Nat := 118140960795 + 3977095 * 2 ^ 59
def prefixEnd_3977095 : Nat := 4983230072969 + 3 ^ 40 * 3977095 * 2
def baseEnd_3977095 : Nat := 1361440895728814887481453

theorem tailTrace_3977095 : CollatzResearch.WordTrace tailWord_3977095 prefixEnd_3977095 1361440895728814887481453 := by
  unfold tailWord_3977095
  simp only [CollatzResearch.WordTrace]
  refine ⟨145056571526671523594548739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96704381017781015729699159 145056571526671523594548739)
  ·
    refine ⟨217584857290007285391823109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145056571526671523594548739 217584857290007285391823109)
    ·
      refine ⟨40797160741876366010966833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 217584857290007285391823109 40797160741876366010966833)
      ·
        refine ⟨30597870556407274508225125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40797160741876366010966833 30597870556407274508225125)
        ·
          refine ⟨5737100729326363970292211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30597870556407274508225125 5737100729326363970292211)
          ·
            refine ⟨8605651093989545955438317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5737100729326363970292211 8605651093989545955438317)
            ·
              refine ⟨3227119160246079733289369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8605651093989545955438317 3227119160246079733289369)
              ·
                refine ⟨2420339370184559799967027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3227119160246079733289369 2420339370184559799967027)
                ·
                  refine ⟨3630509055276839699950541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2420339370184559799967027 3630509055276839699950541)
                  ·
                    refine ⟨1361440895728814887481453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3630509055276839699950541 1361440895728814887481453)
                    ·
                      rfl

theorem cell22_3977095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 3, 2, 1, 3].length) (baseStart_3977095 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3977095 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3977095 prefixEnd_3977095 := by exact prefixLift 3977095
  have htrace : WordTrace (prefixWord ++ tailWord_3977095) baseStart_3977095 baseEnd_3977095 := by
    simpa [prefixWord, tailWord_3977095, baseEnd_3977095] using wordTrace_append hprefix tailTrace_3977095
  have hstable : (prefixWord ++ tailWord_3977095).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3977095).length < 2 ^ (prefixWord ++ tailWord_3977095).sum := by decide
  have hdescent : baseEnd_3977095 < baseStart_3977095 := by decide
  rcases family_descends (prefixWord ++ tailWord_3977095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3977108 : List Nat := [2, 4, 2, 1, 1, 4, 2, 1, 5]
def baseStart_3977108 : Nat := 118140960795 + 3977108 * 2 ^ 59
def prefixEnd_3977108 : Nat := 4983230072969 + 3 ^ 40 * 3977108 * 2
def baseEnd_3977108 : Nat := 453815115298162395635471

theorem tailTrace_3977108 : CollatzResearch.WordTrace tailWord_3977108 prefixEnd_3977108 453815115298162395635471 := by
  unfold tailWord_3977108
  simp only [CollatzResearch.WordTrace]
  refine ⟨72528522837812213407385989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96704697117082951209847985 72528522837812213407385989)
  ·
    refine ⟨13599098032089790013884873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72528522837812213407385989 13599098032089790013884873)
    ·
      refine ⟨10199323524067342510413655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13599098032089790013884873 10199323524067342510413655)
      ·
        refine ⟨15298985286101013765620483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10199323524067342510413655 15298985286101013765620483)
        ·
          refine ⟨22948477929151520648430725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15298985286101013765620483 22948477929151520648430725)
          ·
            refine ⟨4302839611715910121580761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22948477929151520648430725 4302839611715910121580761)
            ·
              refine ⟨3227129708786932591185571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4302839611715910121580761 3227129708786932591185571)
              ·
                refine ⟨4840694563180398886778357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3227129708786932591185571 4840694563180398886778357)
                ·
                  refine ⟨453815115298162395635471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4840694563180398886778357 453815115298162395635471)
                  ·
                    rfl

theorem cell22_3977108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 2, 1, 5].length) (baseStart_3977108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3977108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3977108 prefixEnd_3977108 := by exact prefixLift 3977108
  have htrace : WordTrace (prefixWord ++ tailWord_3977108) baseStart_3977108 baseEnd_3977108 := by
    simpa [prefixWord, tailWord_3977108, baseEnd_3977108] using wordTrace_append hprefix tailTrace_3977108
  have hstable : (prefixWord ++ tailWord_3977108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3977108).length < 2 ^ (prefixWord ++ tailWord_3977108).sum := by decide
  have hdescent : baseEnd_3977108 < baseStart_3977108 := by decide
  rcases family_descends (prefixWord ++ tailWord_3977108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3977121 : List Nat := [1, 2, 3, 4, 2, 1, 1, 1, 3, 4]
def baseStart_3977121 : Nat := 118140960795 + 3977121 * 2 ^ 59
def prefixEnd_3977121 : Nat := 4983230072969 + 3 ^ 40 * 3977121 * 2
def baseEnd_3977121 : Nat := 1361449796060159486331373

theorem tailTrace_3977121 : CollatzResearch.WordTrace tailWord_3977121 prefixEnd_3977121 1361449796060159486331373 := by
  unfold tailWord_3977121
  simp only [CollatzResearch.WordTrace]
  refine ⟨145057519824577330034995217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96705013216384886689996811 145057519824577330034995217)
  ·
    refine ⟨108793139868432997526246413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145057519824577330034995217 108793139868432997526246413)
    ·
      refine ⟨40797427450662374072342405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108793139868432997526246413 40797427450662374072342405)
      ·
        refine ⟨7649517646999195138564201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40797427450662374072342405 7649517646999195138564201)
        ·
          refine ⟨5737138235249396353923151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7649517646999195138564201 5737138235249396353923151)
          ·
            refine ⟨8605707352874094530884727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5737138235249396353923151 8605707352874094530884727)
            ·
              refine ⟨12908561029311141796327091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8605707352874094530884727 12908561029311141796327091)
              ·
                refine ⟨19362841543966712694490637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12908561029311141796327091 19362841543966712694490637)
                ·
                  refine ⟨7261065578987517260433989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19362841543966712694490637 7261065578987517260433989)
                  ·
                    refine ⟨1361449796060159486331373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7261065578987517260433989 1361449796060159486331373)
                    ·
                      rfl

theorem cell22_3977121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 1, 3, 4].length) (baseStart_3977121 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3977121 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3977121 prefixEnd_3977121 := by exact prefixLift 3977121
  have htrace : WordTrace (prefixWord ++ tailWord_3977121) baseStart_3977121 baseEnd_3977121 := by
    simpa [prefixWord, tailWord_3977121, baseEnd_3977121] using wordTrace_append hprefix tailTrace_3977121
  have hstable : (prefixWord ++ tailWord_3977121).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3977121).length < 2 ^ (prefixWord ++ tailWord_3977121).sum := by decide
  have hdescent : baseEnd_3977121 < baseStart_3977121 := by decide
  rcases family_descends (prefixWord ++ tailWord_3977121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3977151 : List Nat := [1, 1, 2, 2, 2, 1, 6, 2, 2, 3]
def baseStart_3977151 : Nat := 118140960795 + 3977151 * 2 ^ 59
def prefixEnd_3977151 : Nat := 4983230072969 + 3 ^ 40 * 3977151 * 2
def baseEnd_3977151 : Nat := 1361460065673249408081281

theorem tailTrace_3977151 : CollatzResearch.WordTrace tailWord_3977151 prefixEnd_3977151 1361460065673249408081281 := by
  unfold tailWord_3977151
  simp only [CollatzResearch.WordTrace]
  refine ⟨145058614014468645158587307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96705742676312430105724871 145058614014468645158587307)
  ·
    refine ⟨217587921021702967737880961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145058614014468645158587307 217587921021702967737880961)
    ·
      refine ⟨163190940766277225803410721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217587921021702967737880961 163190940766277225803410721)
      ·
        refine ⟨122393205574707919352558041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163190940766277225803410721 122393205574707919352558041)
        ·
          refine ⟨91794904181030939514418531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122393205574707919352558041 91794904181030939514418531)
          ·
            refine ⟨137692356271546409271627797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91794904181030939514418531 137692356271546409271627797)
            ·
              refine ⟨6454329200228737934607553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 137692356271546409271627797 6454329200228737934607553)
              ·
                refine ⟨4840746900171553450955665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6454329200228737934607553 4840746900171553450955665)
                ·
                  refine ⟨3630560175128665088216749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4840746900171553450955665 3630560175128665088216749)
                  ·
                    refine ⟨1361460065673249408081281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3630560175128665088216749 1361460065673249408081281)
                    ·
                      rfl

theorem cell22_3977151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 6, 2, 2, 3].length) (baseStart_3977151 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3977151 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3977151 prefixEnd_3977151 := by exact prefixLift 3977151
  have htrace : WordTrace (prefixWord ++ tailWord_3977151) baseStart_3977151 baseEnd_3977151 := by
    simpa [prefixWord, tailWord_3977151, baseEnd_3977151] using wordTrace_append hprefix tailTrace_3977151
  have hstable : (prefixWord ++ tailWord_3977151).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3977151).length < 2 ^ (prefixWord ++ tailWord_3977151).sum := by decide
  have hdescent : baseEnd_3977151 < baseStart_3977151 := by decide
  rcases family_descends (prefixWord ++ tailWord_3977151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3977164 : List Nat := [2, 2, 1, 4, 1, 2, 3, 7]
def baseStart_3977164 : Nat := 118140960795 + 3977164 * 2 ^ 59
def prefixEnd_3977164 : Nat := 4983230072969 + 3 ^ 40 * 3977164 * 2
def baseEnd_3977164 : Nat := 151273835093213523056249

theorem tailTrace_3977164 : CollatzResearch.WordTrace tailWord_3977164 prefixEnd_3977164 151273835093213523056249 := by
  unfold tailWord_3977164
  simp only [CollatzResearch.WordTrace]
  refine ⟨72529544081710774189405273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96706058775614365585873697 72529544081710774189405273)
  ·
    refine ⟨54397158061283080642053955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72529544081710774189405273 54397158061283080642053955)
    ·
      refine ⟨81595737091924620963080933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54397158061283080642053955 81595737091924620963080933)
      ·
        refine ⟨15299200704735866430577675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81595737091924620963080933 15299200704735866430577675)
        ·
          refine ⟨22948801057103799645866513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15299200704735866430577675 22948801057103799645866513)
          ·
            refine ⟨17211600792827849734399885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22948801057103799645866513 17211600792827849734399885)
            ·
              refine ⟨6454350297310443650399957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17211600792827849734399885 6454350297310443650399957)
              ·
                refine ⟨151273835093213523056249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6454350297310443650399957 151273835093213523056249)
                ·
                  rfl

theorem cell22_3977164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 3, 7].length) (baseStart_3977164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3977164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3977164 prefixEnd_3977164 := by exact prefixLift 3977164
  have htrace : WordTrace (prefixWord ++ tailWord_3977164) baseStart_3977164 baseEnd_3977164 := by
    simpa [prefixWord, tailWord_3977164, baseEnd_3977164] using wordTrace_append hprefix tailTrace_3977164
  have hstable : (prefixWord ++ tailWord_3977164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3977164).length < 2 ^ (prefixWord ++ tailWord_3977164).sum := by decide
  have hdescent : baseEnd_3977164 < baseStart_3977164 := by decide
  rcases family_descends (prefixWord ++ tailWord_3977164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3977209 : List Nat := [1, 2, 1, 3, 1, 5, 1, 1, 7]
def baseStart_3977209 : Nat := 118140960795 + 3977209 * 2 ^ 59
def prefixEnd_3977209 : Nat := 4983230072969 + 3 ^ 40 * 3977209 * 2
def baseEnd_3977209 : Nat := 453826640086185530043701

theorem tailTrace_3977209 : CollatzResearch.WordTrace tailWord_3977209 prefixEnd_3977209 453826640086185530043701 := by
  unfold tailWord_3977209
  simp only [CollatzResearch.WordTrace]
  refine ⟨145060729448258521064198681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96707152965505680709465787 145060729448258521064198681)
  ·
    refine ⟨108795547086193890798149011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145060729448258521064198681 108795547086193890798149011)
    ·
      refine ⟨163193320629290836197223517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108795547086193890798149011 163193320629290836197223517)
      ·
        refine ⟨61197495235984063573958819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163193320629290836197223517 61197495235984063573958819)
        ·
          refine ⟨91796242853976095360938229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61197495235984063573958819 91796242853976095360938229)
          ·
            refine ⟨8605897767560258940087959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 91796242853976095360938229 8605897767560258940087959)
            ·
              refine ⟨12908846651340388410131939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8605897767560258940087959 12908846651340388410131939)
              ·
                refine ⟨19363269977010582615197909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12908846651340388410131939 19363269977010582615197909)
                ·
                  refine ⟨453826640086185530043701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19363269977010582615197909 453826640086185530043701)
                  ·
                    rfl

theorem cell22_3977209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 1, 7].length) (baseStart_3977209 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3977209 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3977209 prefixEnd_3977209 := by exact prefixLift 3977209
  have htrace : WordTrace (prefixWord ++ tailWord_3977209) baseStart_3977209 baseEnd_3977209 := by
    simpa [prefixWord, tailWord_3977209, baseEnd_3977209] using wordTrace_append hprefix tailTrace_3977209
  have hstable : (prefixWord ++ tailWord_3977209).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3977209).length < 2 ^ (prefixWord ++ tailWord_3977209).sum := by decide
  have hdescent : baseEnd_3977209 < baseStart_3977209 := by decide
  rcases family_descends (prefixWord ++ tailWord_3977209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3977213 : List Nat := [1, 4, 1, 1, 1, 2, 4, 4, 1, 3]
def baseStart_3977213 : Nat := 118140960795 + 3977213 * 2 ^ 59
def prefixEnd_3977213 : Nat := 4983230072969 + 3 ^ 40 * 3977213 * 2
def baseEnd_3977213 : Nat := 1361481289540301913031091

theorem tailTrace_3977213 : CollatzResearch.WordTrace tailWord_3977213 prefixEnd_3977213 1361481289540301913031091 := by
  unfold tailWord_3977213
  simp only [CollatzResearch.WordTrace]
  refine ⟨145060875340244029747344293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96707250226829353164896195 145060875340244029747344293)
  ·
    refine ⟨27198914126295755577627055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 145060875340244029747344293 27198914126295755577627055)
    ·
      refine ⟨40798371189443633366440583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27198914126295755577627055 40798371189443633366440583)
      ·
        refine ⟨61197556784165450049660875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40798371189443633366440583 61197556784165450049660875)
        ·
          refine ⟨91796335176248175074491313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61197556784165450049660875 91796335176248175074491313)
          ·
            refine ⟨68847251382186131305868485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91796335176248175074491313 68847251382186131305868485)
            ·
              refine ⟨12908859634159899619850341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68847251382186131305868485 12908859634159899619850341)
              ·
                refine ⟨2420411181404981178721939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12908859634159899619850341 2420411181404981178721939)
                ·
                  refine ⟨3630616772107471768082909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2420411181404981178721939 3630616772107471768082909)
                  ·
                    refine ⟨1361481289540301913031091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3630616772107471768082909 1361481289540301913031091)
                    ·
                      rfl

theorem cell22_3977213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 4, 1, 3].length) (baseStart_3977213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3977213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3977213 prefixEnd_3977213 := by exact prefixLift 3977213
  have htrace : WordTrace (prefixWord ++ tailWord_3977213) baseStart_3977213 baseEnd_3977213 := by
    simpa [prefixWord, tailWord_3977213, baseEnd_3977213] using wordTrace_append hprefix tailTrace_3977213
  have hstable : (prefixWord ++ tailWord_3977213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3977213).length < 2 ^ (prefixWord ++ tailWord_3977213).sum := by decide
  have hdescent : baseEnd_3977213 < baseStart_3977213 := by decide
  rcases family_descends (prefixWord ++ tailWord_3977213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3977224 : List Nat := [2, 1, 3, 2, 1, 2, 1, 3, 2, 5]
def baseStart_3977224 : Nat := 118140960795 + 3977224 * 2 ^ 59
def prefixEnd_3977224 : Nat := 4983230072969 + 3 ^ 40 * 3977224 * 2
def baseEnd_3977224 : Nat := 1361485055065101551006057

theorem tailTrace_3977224 : CollatzResearch.WordTrace tailWord_3977224 prefixEnd_3977224 1361485055065101551006057 := by
  unfold tailWord_3977224
  simp only [CollatzResearch.WordTrace]
  refine ⟨72530638271602089312997363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96707517695469452417329817 72530638271602089312997363)
  ·
    refine ⟨108795957407403133969496045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72530638271602089312997363 108795957407403133969496045)
    ·
      refine ⟨40798484027776175238561017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108795957407403133969496045 40798484027776175238561017)
      ·
        refine ⟨30598863020832131428920763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40798484027776175238561017 30598863020832131428920763)
        ·
          refine ⟨45898294531248197143381145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30598863020832131428920763 45898294531248197143381145)
          ·
            refine ⟨34423720898436147857535859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45898294531248197143381145 34423720898436147857535859)
            ·
              refine ⟨51635581347654221786303789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34423720898436147857535859 51635581347654221786303789)
              ·
                refine ⟨19363343005370333169863921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51635581347654221786303789 19363343005370333169863921)
                ·
                  refine ⟨14522507254027749877397941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19363343005370333169863921 14522507254027749877397941)
                  ·
                    refine ⟨1361485055065101551006057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14522507254027749877397941 1361485055065101551006057)
                    ·
                      rfl

theorem cell22_3977224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 3, 2, 5].length) (baseStart_3977224 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3977224 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3977224 prefixEnd_3977224 := by exact prefixLift 3977224
  have htrace : WordTrace (prefixWord ++ tailWord_3977224) baseStart_3977224 baseEnd_3977224 := by
    simpa [prefixWord, tailWord_3977224, baseEnd_3977224] using wordTrace_append hprefix tailTrace_3977224
  have hstable : (prefixWord ++ tailWord_3977224).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3977224).length < 2 ^ (prefixWord ++ tailWord_3977224).sum := by decide
  have hdescent : baseEnd_3977224 < baseStart_3977224 := by decide
  rcases family_descends (prefixWord ++ tailWord_3977224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3977271 : List Nat := [1, 1, 3, 1, 2, 2, 2, 6, 4]
def baseStart_3977271 : Nat := 118140960795 + 3977271 * 2 ^ 59
def prefixEnd_3977271 : Nat := 4983230072969 + 3 ^ 40 * 3977271 * 2
def baseEnd_3977271 : Nat := 453833714708536365026971

theorem tailTrace_3977271 : CollatzResearch.WordTrace tailWord_3977271 prefixEnd_3977271 453833714708536365026971 := by
  unfold tailWord_3977271
  simp only [CollatzResearch.WordTrace]
  refine ⟨145062990774033905652955667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96708660516022603768637111 145062990774033905652955667)
  ·
    refine ⟨217594486161050858479433501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145062990774033905652955667 217594486161050858479433501)
    ·
      refine ⟨81597932310394071929787563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 217594486161050858479433501 81597932310394071929787563)
      ·
        refine ⟨122396898465591107894681345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81597932310394071929787563 122396898465591107894681345)
        ·
          refine ⟨91797673849193330921011009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122396898465591107894681345 91797673849193330921011009)
          ·
            refine ⟨68848255386894998190758257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91797673849193330921011009 68848255386894998190758257)
            ·
              refine ⟨51636191540171248643068693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68848255386894998190758257 51636191540171248643068693)
              ·
                refine ⟨2420446478445527280143845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 51636191540171248643068693 2420446478445527280143845)
                ·
                  refine ⟨453833714708536365026971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2420446478445527280143845 453833714708536365026971)
                  ·
                    rfl

theorem cell22_3977271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 6, 4].length) (baseStart_3977271 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3977271 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3977271 prefixEnd_3977271 := by exact prefixLift 3977271
  have htrace : WordTrace (prefixWord ++ tailWord_3977271) baseStart_3977271 baseEnd_3977271 := by
    simpa [prefixWord, tailWord_3977271, baseEnd_3977271] using wordTrace_append hprefix tailTrace_3977271
  have hstable : (prefixWord ++ tailWord_3977271).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3977271).length < 2 ^ (prefixWord ++ tailWord_3977271).sum := by decide
  have hdescent : baseEnd_3977271 < baseStart_3977271 := by decide
  rcases family_descends (prefixWord ++ tailWord_3977271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3977301 : List Nat := [1, 3, 2, 2, 1, 3, 1, 3, 2, 4]
def baseStart_3977301 : Nat := 118140960795 + 3977301 * 2 ^ 59
def prefixEnd_3977301 : Nat := 4983230072969 + 3 ^ 40 * 3977301 * 2
def baseEnd_3977301 : Nat := 1361511413738699016830821

theorem tailTrace_3977301 : CollatzResearch.WordTrace tailWord_3977301 prefixEnd_3977301 1361511413738699016830821 := by
  unfold tailWord_3977301
  simp only [CollatzResearch.WordTrace]
  refine ⟨145064084963925220776547757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96709389975950147184365171 145064084963925220776547757)
  ·
    refine ⟨54399031861471957791205409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145064084963925220776547757 54399031861471957791205409)
    ·
      refine ⟨40799273896103968343404057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54399031861471957791205409 40799273896103968343404057)
      ·
        refine ⟨30599455422077976257553043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40799273896103968343404057 30599455422077976257553043)
        ·
          refine ⟨45899183133116964386329565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30599455422077976257553043 45899183133116964386329565)
          ·
            refine ⟨17212193674918861644873587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45899183133116964386329565 17212193674918861644873587)
            ·
              refine ⟨25818290512378292467310381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17212193674918861644873587 25818290512378292467310381)
              ·
                refine ⟨9681858942141859675241393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25818290512378292467310381 9681858942141859675241393)
                ·
                  refine ⟨7261394206606394756431045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9681858942141859675241393 7261394206606394756431045)
                  ·
                    refine ⟨1361511413738699016830821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7261394206606394756431045 1361511413738699016830821)
                    ·
                      rfl

theorem cell22_3977301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 3, 2, 4].length) (baseStart_3977301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3977301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3977301 prefixEnd_3977301 := by exact prefixLift 3977301
  have htrace : WordTrace (prefixWord ++ tailWord_3977301) baseStart_3977301 baseEnd_3977301 := by
    simpa [prefixWord, tailWord_3977301, baseEnd_3977301] using wordTrace_append hprefix tailTrace_3977301
  have hstable : (prefixWord ++ tailWord_3977301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3977301).length < 2 ^ (prefixWord ++ tailWord_3977301).sum := by decide
  have hdescent : baseEnd_3977301 < baseStart_3977301 := by decide
  rcases family_descends (prefixWord ++ tailWord_3977301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3977322 : List Nat := [3, 1, 3, 2, 3, 2, 2, 2, 4]
def baseStart_3977322 : Nat := 118140960795 + 3977322 * 2 ^ 59
def prefixEnd_3977322 : Nat := 4983230072969 + 3 ^ 40 * 3977322 * 2
def baseEnd_3977322 : Nat := 453839534155953987351919

theorem tailTrace_3977322 : CollatzResearch.WordTrace tailWord_3977322 prefixEnd_3977322 453839534155953987351919 := by
  unfold tailWord_3977322
  simp only [CollatzResearch.WordTrace]
  refine ⟨36266212724212285340765555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96709900597899427575374813 36266212724212285340765555)
  ·
    refine ⟨54399319086318428011148333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36266212724212285340765555 54399319086318428011148333)
    ·
      refine ⟨20399744657369410504180625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54399319086318428011148333 20399744657369410504180625)
      ·
        refine ⟨15299808493027057878135469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20399744657369410504180625 15299808493027057878135469)
        ·
          refine ⟨5737428184885146704300801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15299808493027057878135469 5737428184885146704300801)
          ·
            refine ⟨4303071138663860028225601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5737428184885146704300801 4303071138663860028225601)
            ·
              refine ⟨3227303353997895021169201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4303071138663860028225601 3227303353997895021169201)
              ·
                refine ⟨2420477515498421265876901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3227303353997895021169201 2420477515498421265876901)
                ·
                  refine ⟨453839534155953987351919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2420477515498421265876901 453839534155953987351919)
                  ·
                    rfl

theorem cell22_3977322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 2, 2, 4].length) (baseStart_3977322 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3977322 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3977322 prefixEnd_3977322 := by exact prefixLift 3977322
  have htrace : WordTrace (prefixWord ++ tailWord_3977322) baseStart_3977322 baseEnd_3977322 := by
    simpa [prefixWord, tailWord_3977322, baseEnd_3977322] using wordTrace_append hprefix tailTrace_3977322
  have hstable : (prefixWord ++ tailWord_3977322).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3977322).length < 2 ^ (prefixWord ++ tailWord_3977322).sum := by decide
  have hdescent : baseEnd_3977322 < baseStart_3977322 := by decide
  rcases family_descends (prefixWord ++ tailWord_3977322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3977329 : List Nat := [1, 2, 2, 2, 1, 1, 3, 1, 1, 8]
def baseStart_3977329 : Nat := 118140960795 + 3977329 * 2 ^ 59
def prefixEnd_3977329 : Nat := 4983230072969 + 3 ^ 40 * 3977329 * 2
def baseEnd_3977329 : Nat := 1361520998710916277130735

theorem tailTrace_3977329 : CollatzResearch.WordTrace tailWord_3977329 prefixEnd_3977329 1361520998710916277130735 := by
  unfold tailWord_3977329
  simp only [CollatzResearch.WordTrace]
  refine ⟨145065106207823781558567041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96710070805215854372378027 145065106207823781558567041)
  ·
    refine ⟨108798829655867836168925281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145065106207823781558567041 108798829655867836168925281)
    ·
      refine ⟨81599122241900877126693961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108798829655867836168925281 81599122241900877126693961)
      ·
        refine ⟨61199341681425657845020471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81599122241900877126693961 61199341681425657845020471)
        ·
          refine ⟨91799012522138486767530707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61199341681425657845020471 91799012522138486767530707)
          ·
            refine ⟨137698518783207730151296061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91799012522138486767530707 137698518783207730151296061)
            ·
              refine ⟨51636944543702898806736023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 137698518783207730151296061 51636944543702898806736023)
              ·
                refine ⟨77455416815554348210104035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51636944543702898806736023 77455416815554348210104035)
                ·
                  refine ⟨116183125223331522315156053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77455416815554348210104035 116183125223331522315156053)
                  ·
                    refine ⟨1361520998710916277130735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 116183125223331522315156053 1361520998710916277130735)
                    ·
                      rfl

theorem cell22_3977329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 1, 1, 8].length) (baseStart_3977329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3977329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3977329 prefixEnd_3977329 := by exact prefixLift 3977329
  have htrace : WordTrace (prefixWord ++ tailWord_3977329) baseStart_3977329 baseEnd_3977329 := by
    simpa [prefixWord, tailWord_3977329, baseEnd_3977329] using wordTrace_append hprefix tailTrace_3977329
  have hstable : (prefixWord ++ tailWord_3977329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3977329).length < 2 ^ (prefixWord ++ tailWord_3977329).sum := by decide
  have hdescent : baseEnd_3977329 < baseStart_3977329 := by decide
  rcases family_descends (prefixWord ++ tailWord_3977329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3977344 : List Nat := [2, 1, 1, 2, 1, 3, 1, 2, 9]
def baseStart_3977344 : Nat := 118140960795 + 3977344 * 2 ^ 59
def prefixEnd_3977344 : Nat := 4983230072969 + 3 ^ 40 * 3977344 * 2
def baseEnd_3977344 : Nat := 453842044505820412668563

theorem tailTrace_3977344 : CollatzResearch.WordTrace tailWord_3977344 prefixEnd_3977344 453842044505820412668563 := by
  unfold tailWord_3977344
  simp only [CollatzResearch.WordTrace]
  refine ⟨72532826651384719560181543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96710435535179626080242057 72532826651384719560181543)
  ·
    refine ⟨108799239977077079340272315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72532826651384719560181543 108799239977077079340272315)
    ·
      refine ⟨163198859965615619010408473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108799239977077079340272315 163198859965615619010408473)
      ·
        refine ⟨122399144974211714257806355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163198859965615619010408473 122399144974211714257806355)
        ·
          refine ⟨183598717461317571386709533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122399144974211714257806355 183598717461317571386709533)
          ·
            refine ⟨68849519047994089270016075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 183598717461317571386709533 68849519047994089270016075)
            ·
              refine ⟨103274278571991133905024113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68849519047994089270016075 103274278571991133905024113)
              ·
                refine ⟨77455708928993350428768085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103274278571991133905024113 77455708928993350428768085)
                ·
                  refine ⟨453842044505820412668563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 77455708928993350428768085 453842044505820412668563)
                  ·
                    rfl

theorem cell22_3977344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 2, 9].length) (baseStart_3977344 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3977344 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3977344 prefixEnd_3977344 := by exact prefixLift 3977344
  have htrace : WordTrace (prefixWord ++ tailWord_3977344) baseStart_3977344 baseEnd_3977344 := by
    simpa [prefixWord, tailWord_3977344, baseEnd_3977344] using wordTrace_append hprefix tailTrace_3977344
  have hstable : (prefixWord ++ tailWord_3977344).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3977344).length < 2 ^ (prefixWord ++ tailWord_3977344).sum := by decide
  have hdescent : baseEnd_3977344 < baseStart_3977344 := by decide
  rcases family_descends (prefixWord ++ tailWord_3977344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3977348 : List Nat := [2, 3, 2, 1, 2, 1, 3, 2, 3, 3]
def baseStart_3977348 : Nat := 118140960795 + 3977348 * 2 ^ 59
def prefixEnd_3977348 : Nat := 4983230072969 + 3 ^ 40 * 3977348 * 2
def baseEnd_3977348 : Nat := 1361527502799206560905677

theorem tailTrace_3977348 : CollatzResearch.WordTrace tailWord_3977348 prefixEnd_3977348 1361527502799206560905677 := by
  unfold tailWord_3977348
  simp only [CollatzResearch.WordTrace]
  refine ⟨72532899597377473901754349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96710532796503298535672465 72532899597377473901754349)
  ·
    refine ⟨27199837349016552713157881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72532899597377473901754349 27199837349016552713157881)
    ·
      refine ⟨20399878011762414534868411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27199837349016552713157881 20399878011762414534868411)
      ·
        refine ⟨30599817017643621802302617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20399878011762414534868411 30599817017643621802302617)
        ·
          refine ⟨22949862763232716351726963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30599817017643621802302617 22949862763232716351726963)
          ·
            refine ⟨34424794144849074527590445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22949862763232716351726963 34424794144849074527590445)
            ·
              refine ⟨12909297804318402947846417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34424794144849074527590445 12909297804318402947846417)
              ·
                refine ⟨9681973353238802210884813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12909297804318402947846417 9681973353238802210884813)
                ·
                  refine ⟨3630740007464550829081805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9681973353238802210884813 3630740007464550829081805)
                  ·
                    refine ⟨1361527502799206560905677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3630740007464550829081805 1361527502799206560905677)
                    ·
                      rfl

theorem cell22_3977348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 2, 3, 3].length) (baseStart_3977348 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3977348 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3977348 prefixEnd_3977348 := by exact prefixLift 3977348
  have htrace : WordTrace (prefixWord ++ tailWord_3977348) baseStart_3977348 baseEnd_3977348 := by
    simpa [prefixWord, tailWord_3977348, baseEnd_3977348] using wordTrace_append hprefix tailTrace_3977348
  have hstable : (prefixWord ++ tailWord_3977348).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3977348).length < 2 ^ (prefixWord ++ tailWord_3977348).sum := by decide
  have hdescent : baseEnd_3977348 < baseStart_3977348 := by decide
  rcases family_descends (prefixWord ++ tailWord_3977348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3977365 : List Nat := [1, 3, 2, 1, 1, 1, 6, 3, 1, 3]
def baseStart_3977365 : Nat := 118140960795 + 3977365 * 2 ^ 59
def prefixEnd_3977365 : Nat := 4983230072969 + 3 ^ 40 * 3977365 * 2
def baseEnd_3977365 : Nat := 1361533322246624183230625

theorem tailTrace_3977365 : CollatzResearch.WordTrace tailWord_3977365 prefixEnd_3977365 1361533322246624183230625 := by
  unfold tailWord_3977365
  simp only [CollatzResearch.WordTrace]
  refine ⟨145066419235693359706877549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96710946157128906471251699 145066419235693359706877549)
  ·
    refine ⟨54399907213385009890079081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145066419235693359706877549 54399907213385009890079081)
    ·
      refine ⟨40799930410038757417559311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54399907213385009890079081 40799930410038757417559311)
      ·
        refine ⟨61199895615058136126338967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40799930410038757417559311 61199895615058136126338967)
        ·
          refine ⟨91799843422587204189508451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61199895615058136126338967 91799843422587204189508451)
          ·
            refine ⟨137699765133880806284262677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91799843422587204189508451 137699765133880806284262677)
            ·
              refine ⟨6454676490650662794574813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 137699765133880806284262677 6454676490650662794574813)
              ·
                refine ⟨2420503683993998547965555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6454676490650662794574813 2420503683993998547965555)
                ·
                  refine ⟨3630755525990997821948333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2420503683993998547965555 3630755525990997821948333)
                  ·
                    refine ⟨1361533322246624183230625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3630755525990997821948333 1361533322246624183230625)
                    ·
                      rfl

theorem cell22_3977365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 6, 3, 1, 3].length) (baseStart_3977365 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3977365 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3977365 prefixEnd_3977365 := by exact prefixLift 3977365
  have htrace : WordTrace (prefixWord ++ tailWord_3977365) baseStart_3977365 baseEnd_3977365 := by
    simpa [prefixWord, tailWord_3977365, baseEnd_3977365] using wordTrace_append hprefix tailTrace_3977365
  have hstable : (prefixWord ++ tailWord_3977365).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3977365).length < 2 ^ (prefixWord ++ tailWord_3977365).sum := by decide
  have hdescent : baseEnd_3977365 < baseStart_3977365 := by decide
  rcases family_descends (prefixWord ++ tailWord_3977365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3977376 : List Nat := [2, 1, 1, 4, 2, 2, 1, 2, 2, 5]
def baseStart_3977376 : Nat := 118140960795 + 3977376 * 2 ^ 59
def prefixEnd_3977376 : Nat := 4983230072969 + 3 ^ 40 * 3977376 * 2
def baseEnd_3977376 : Nat := 1361537087771423821205591

theorem tailTrace_3977376 : CollatzResearch.WordTrace tailWord_3977376 prefixEnd_3977376 1361537087771423821205591 := by
  unfold tailWord_3977376
  simp only [CollatzResearch.WordTrace]
  refine ⟨72533410219326754292763991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96711213625769005723685321 72533410219326754292763991)
  ·
    refine ⟨108800115328990131439145987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72533410219326754292763991 108800115328990131439145987)
    ·
      refine ⟨163200172993485197158718981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108800115328990131439145987 163200172993485197158718981)
      ·
        refine ⟨30600032436278474467259809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 163200172993485197158718981 30600032436278474467259809)
        ·
          refine ⟨22950024327208855850444857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30600032436278474467259809 22950024327208855850444857)
          ·
            refine ⟨17212518245406641887833643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22950024327208855850444857 17212518245406641887833643)
            ·
              refine ⟨25818777368109962831750465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17212518245406641887833643 25818777368109962831750465)
              ·
                refine ⟨19364083026082472123812849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25818777368109962831750465 19364083026082472123812849)
                ·
                  refine ⟨14523062269561854092859637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19364083026082472123812849 14523062269561854092859637)
                  ·
                    refine ⟨1361537087771423821205591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14523062269561854092859637 1361537087771423821205591)
                    ·
                      rfl

theorem cell22_3977376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 2, 2, 5].length) (baseStart_3977376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3977376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3977376 prefixEnd_3977376 := by exact prefixLift 3977376
  have htrace : WordTrace (prefixWord ++ tailWord_3977376) baseStart_3977376 baseEnd_3977376 := by
    simpa [prefixWord, tailWord_3977376, baseEnd_3977376] using wordTrace_append hprefix tailTrace_3977376
  have hstable : (prefixWord ++ tailWord_3977376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3977376).length < 2 ^ (prefixWord ++ tailWord_3977376).sum := by decide
  have hdescent : baseEnd_3977376 < baseStart_3977376 := by decide
  rcases family_descends (prefixWord ++ tailWord_3977376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3977378 : List Nat := [3, 3, 1, 3, 1, 2, 1, 1, 7]
def baseStart_3977378 : Nat := 118140960795 + 3977378 * 2 ^ 59
def prefixEnd_3977378 : Nat := 4983230072969 + 3 ^ 40 * 3977378 * 2
def baseEnd_3977378 : Nat := 453845924137432160885195

theorem tailTrace_3977378 : CollatzResearch.WordTrace tailWord_3977378 prefixEnd_3977378 453845924137432160885195 := by
  unfold tailWord_3977378
  simp only [CollatzResearch.WordTrace]
  refine ⟨36266723346161565731775197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96711262256430841951400525 36266723346161565731775197)
  ·
    refine ⟨13600021254810587149415699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36266723346161565731775197 13600021254810587149415699)
    ·
      refine ⟨20400031882215880724123549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13600021254810587149415699 20400031882215880724123549)
      ·
        refine ⟨7650011955830955271546331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20400031882215880724123549 7650011955830955271546331)
        ·
          refine ⟨11475017933746432907319497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7650011955830955271546331 11475017933746432907319497)
          ·
            refine ⟨8606263450309824680489623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11475017933746432907319497 8606263450309824680489623)
            ·
              refine ⟨12909395175464737020734435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8606263450309824680489623 12909395175464737020734435)
              ·
                refine ⟨19364092763197105531101653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12909395175464737020734435 19364092763197105531101653)
                ·
                  refine ⟨453845924137432160885195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19364092763197105531101653 453845924137432160885195)
                  ·
                    rfl

theorem cell22_3977378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 1, 7].length) (baseStart_3977378 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3977378 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3977378 prefixEnd_3977378 := by exact prefixLift 3977378
  have htrace : WordTrace (prefixWord ++ tailWord_3977378) baseStart_3977378 baseEnd_3977378 := by
    simpa [prefixWord, tailWord_3977378, baseEnd_3977378] using wordTrace_append hprefix tailTrace_3977378
  have hstable : (prefixWord ++ tailWord_3977378).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3977378).length < 2 ^ (prefixWord ++ tailWord_3977378).sum := by decide
  have hdescent : baseEnd_3977378 < baseStart_3977378 := by decide
  rcases family_descends (prefixWord ++ tailWord_3977378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3977408 : List Nat := [2, 1, 1, 2, 5, 1, 1, 4, 1, 4]
def baseStart_3977408 : Nat := 118140960795 + 3977408 * 2 ^ 59
def prefixEnd_3977408 : Nat := 4983230072969 + 3 ^ 40 * 3977408 * 2
def baseEnd_3977408 : Nat := 1361548042025386404405493

theorem tailTrace_3977408 : CollatzResearch.WordTrace tailWord_3977408 prefixEnd_3977408 1361548042025386404405493 := by
  unfold tailWord_3977408
  simp only [CollatzResearch.WordTrace]
  refine ⟨72533993787268789025346439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96711991716358385367128585 72533993787268789025346439)
  ·
    refine ⟨108800990680903183538019659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72533993787268789025346439 108800990680903183538019659)
    ·
      refine ⟨163201486021354775307029489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108800990680903183538019659 163201486021354775307029489)
      ·
        refine ⟨122401114516016081480272117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163201486021354775307029489 122401114516016081480272117)
        ·
          refine ⟨11475104485876507638775511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 122401114516016081480272117 11475104485876507638775511)
          ·
            refine ⟨17212656728814761458163267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11475104485876507638775511 17212656728814761458163267)
            ·
              refine ⟨25818985093222142187244901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17212656728814761458163267 25818985093222142187244901)
              ·
                refine ⟨4841059704979151660108419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25818985093222142187244901 4841059704979151660108419)
                ·
                  refine ⟨7261589557468727490162629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4841059704979151660108419 7261589557468727490162629)
                  ·
                    refine ⟨1361548042025386404405493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7261589557468727490162629 1361548042025386404405493)
                    ·
                      rfl

theorem cell22_3977408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 4, 1, 4].length) (baseStart_3977408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3977408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3977408 prefixEnd_3977408 := by exact prefixLift 3977408
  have htrace : WordTrace (prefixWord ++ tailWord_3977408) baseStart_3977408 baseEnd_3977408 := by
    simpa [prefixWord, tailWord_3977408, baseEnd_3977408] using wordTrace_append hprefix tailTrace_3977408
  have hstable : (prefixWord ++ tailWord_3977408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3977408).length < 2 ^ (prefixWord ++ tailWord_3977408).sum := by decide
  have hdescent : baseEnd_3977408 < baseStart_3977408 := by decide
  rcases family_descends (prefixWord ++ tailWord_3977408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3977440 : List Nat := [2, 1, 1, 3, 1, 3, 5, 2, 4]
def baseStart_3977440 : Nat := 118140960795 + 3977440 * 2 ^ 59
def prefixEnd_3977440 : Nat := 4983230072969 + 3 ^ 40 * 3977440 * 2
def baseEnd_3977440 : Nat := 453852998759782995868465

theorem tailTrace_3977440 : CollatzResearch.WordTrace tailWord_3977440 prefixEnd_3977440 453852998759782995868465 := by
  unfold tailWord_3977440
  simp only [CollatzResearch.WordTrace]
  refine ⟨72534577355210823757928887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96712769806947765010571849 72534577355210823757928887)
  ·
    refine ⟨108801866032816235636893331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72534577355210823757928887 108801866032816235636893331)
    ·
      refine ⟨163202799049224353455339997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108801866032816235636893331 163202799049224353455339997)
      ·
        refine ⟨61201049643459132545752499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163202799049224353455339997 61201049643459132545752499)
        ·
          refine ⟨91801574465188698818628749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61201049643459132545752499 91801574465188698818628749)
          ·
            refine ⟨34425590424445762056985781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91801574465188698818628749 34425590424445762056985781)
            ·
              refine ⟨3227399102291790192842417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34425590424445762056985781 3227399102291790192842417)
              ·
                refine ⟨2420549326718842644631813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3227399102291790192842417 2420549326718842644631813)
                ·
                  refine ⟨453852998759782995868465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2420549326718842644631813 453852998759782995868465)
                  ·
                    rfl

theorem cell22_3977440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 5, 2, 4].length) (baseStart_3977440 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3977440 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3977440 prefixEnd_3977440 := by exact prefixLift 3977440
  have htrace : WordTrace (prefixWord ++ tailWord_3977440) baseStart_3977440 baseEnd_3977440 := by
    simpa [prefixWord, tailWord_3977440, baseEnd_3977440] using wordTrace_append hprefix tailTrace_3977440
  have hstable : (prefixWord ++ tailWord_3977440).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3977440).length < 2 ^ (prefixWord ++ tailWord_3977440).sum := by decide
  have hdescent : baseEnd_3977440 < baseStart_3977440 := by decide
  rcases family_descends (prefixWord ++ tailWord_3977440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3977451 : List Nat := [1, 1, 1, 1, 2, 5, 4, 7]
def baseStart_3977451 : Nat := 118140960795 + 3977451 * 2 ^ 59
def prefixEnd_3977451 : Nat := 4983230072969 + 3 ^ 40 * 3977451 * 2
def baseEnd_3977451 : Nat := 151284751311572069508929

theorem tailTrace_3977451 : CollatzResearch.WordTrace tailWord_3977451 prefixEnd_3977451 151284751311572069508929 := by
  unfold tailWord_3977451
  simp only [CollatzResearch.WordTrace]
  refine ⟨145069555913381796394508207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96713037275587864263005471 145069555913381796394508207)
  ·
    refine ⟨217604333870072694591762311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145069555913381796394508207 217604333870072694591762311)
    ·
      refine ⟨326406500805109041887643467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217604333870072694591762311 326406500805109041887643467)
      ·
        refine ⟨489609751207663562831465201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 326406500805109041887643467 489609751207663562831465201)
        ·
          refine ⟨367207313405747672123598901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 489609751207663562831465201 367207313405747672123598901)
          ·
            refine ⟨34425685631788844261587397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 367207313405747672123598901 34425685631788844261587397)
            ·
              refine ⟨6454816055960408299047637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34425685631788844261587397 6454816055960408299047637)
              ·
                refine ⟨151284751311572069508929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6454816055960408299047637 151284751311572069508929)
                ·
                  rfl

theorem cell22_3977451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 4, 7].length) (baseStart_3977451 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3977451 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3977451 prefixEnd_3977451 := by exact prefixLift 3977451
  have htrace : WordTrace (prefixWord ++ tailWord_3977451) baseStart_3977451 baseEnd_3977451 := by
    simpa [prefixWord, tailWord_3977451, baseEnd_3977451] using wordTrace_append hprefix tailTrace_3977451
  have hstable : (prefixWord ++ tailWord_3977451).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3977451).length < 2 ^ (prefixWord ++ tailWord_3977451).sum := by decide
  have hdescent : baseEnd_3977451 < baseStart_3977451 := by decide
  rcases family_descends (prefixWord ++ tailWord_3977451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3977455 : List Nat := [1, 1, 2, 1, 6, 2, 1, 3, 2, 3]
def baseStart_3977455 : Nat := 118140960795 + 3977455 * 2 ^ 59
def prefixEnd_3977455 : Nat := 4983230072969 + 3 ^ 40 * 3977455 * 2
def baseEnd_3977455 : Nat := 1361564131085893948480349

theorem tailTrace_3977455 : CollatzResearch.WordTrace tailWord_3977455 prefixEnd_3977455 1361564131085893948480349 := by
  unfold tailWord_3977455
  simp only [CollatzResearch.WordTrace]
  refine ⟨145069701805367305077653819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96713134536911536718435879 145069701805367305077653819)
  ·
    refine ⟨217604552708050957616480729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145069701805367305077653819 217604552708050957616480729)
    ·
      refine ⟨163203414531038218212360547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217604552708050957616480729 163203414531038218212360547)
      ·
        refine ⟨244805121796557327318540821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163203414531038218212360547 244805121796557327318540821)
        ·
          refine ⟨11475240084213624718056601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 244805121796557327318540821 11475240084213624718056601)
          ·
            refine ⟨8606430063160218538542451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11475240084213624718056601 8606430063160218538542451)
            ·
              refine ⟨12909645094740327807813677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8606430063160218538542451 12909645094740327807813677)
              ·
                refine ⟨4841116910527622927930129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12909645094740327807813677 4841116910527622927930129)
                ·
                  refine ⟨3630837682895717195947597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4841116910527622927930129 3630837682895717195947597)
                  ·
                    refine ⟨1361564131085893948480349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3630837682895717195947597 1361564131085893948480349)
                    ·
                      rfl

theorem cell22_3977455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 3, 2, 3].length) (baseStart_3977455 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3977455 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3977455 prefixEnd_3977455 := by exact prefixLift 3977455
  have htrace : WordTrace (prefixWord ++ tailWord_3977455) baseStart_3977455 baseEnd_3977455 := by
    simpa [prefixWord, tailWord_3977455, baseEnd_3977455] using wordTrace_append hprefix tailTrace_3977455
  have hstable : (prefixWord ++ tailWord_3977455).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3977455).length < 2 ^ (prefixWord ++ tailWord_3977455).sum := by decide
  have hdescent : baseEnd_3977455 < baseStart_3977455 := by decide
  rcases family_descends (prefixWord ++ tailWord_3977455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3977470 : List Nat := [4, 2, 2, 1, 1, 1, 4, 1, 2, 4]
def baseStart_3977470 : Nat := 118140960795 + 3977470 * 2 ^ 59
def prefixEnd_3977470 : Nat := 4983230072969 + 3 ^ 40 * 3977470 * 2
def baseEnd_3977470 : Nat := 1361569265892438909355303

theorem tailTrace_3977470 : CollatzResearch.WordTrace tailWord_3977470 prefixEnd_3977470 1361569265892438909355303 := by
  unfold tailWord_3977470
  simp only [CollatzResearch.WordTrace]
  refine ⟨18133781112539120329931233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96713499266875308426299909 18133781112539120329931233)
  ·
    refine ⟨13600335834404340247448425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18133781112539120329931233 13600335834404340247448425)
    ·
      refine ⟨10200251875803255185586319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13600335834404340247448425 10200251875803255185586319)
      ·
        refine ⟨15300377813704882778379479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10200251875803255185586319 15300377813704882778379479)
        ·
          refine ⟨22950566720557324167569219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15300377813704882778379479 22950566720557324167569219)
          ·
            refine ⟨34425850080835986251353829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22950566720557324167569219 34425850080835986251353829)
            ·
              refine ⟨6454846890156747422128843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34425850080835986251353829 6454846890156747422128843)
              ·
                refine ⟨9682270335235121133193265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6454846890156747422128843 9682270335235121133193265)
                ·
                  refine ⟨7261702751426340849894949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9682270335235121133193265 7261702751426340849894949)
                  ·
                    refine ⟨1361569265892438909355303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7261702751426340849894949 1361569265892438909355303)
                    ·
                      rfl

theorem cell22_3977470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 4, 1, 2, 4].length) (baseStart_3977470 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3977470 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3977470 prefixEnd_3977470 := by exact prefixLift 3977470
  have htrace : WordTrace (prefixWord ++ tailWord_3977470) baseStart_3977470 baseEnd_3977470 := by
    simpa [prefixWord, tailWord_3977470, baseEnd_3977470] using wordTrace_append hprefix tailTrace_3977470
  have hstable : (prefixWord ++ tailWord_3977470).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3977470).length < 2 ^ (prefixWord ++ tailWord_3977470).sum := by decide
  have hdescent : baseEnd_3977470 < baseStart_3977470 := by decide
  rcases family_descends (prefixWord ++ tailWord_3977470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3977502 : List Nat := [4, 3, 2, 1, 1, 3, 1, 7]
def baseStart_3977502 : Nat := 118140960795 + 3977502 * 2 ^ 59
def prefixEnd_3977502 : Nat := 4983230072969 + 3 ^ 40 * 3977502 * 2
def baseEnd_3977502 : Nat := 151286691127377943617245

theorem tailTrace_3977502 : CollatzResearch.WordTrace tailWord_3977502 prefixEnd_3977502 151286691127377943617245 := by
  unfold tailWord_3977502
  simp only [CollatzResearch.WordTrace]
  refine ⟨18133927004524629013076845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96714277357464688069743173 18133927004524629013076845)
  ·
    refine ⟨6800222626696735879903817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18133927004524629013076845 6800222626696735879903817)
    ·
      refine ⟨5100166970022551909927863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6800222626696735879903817 5100166970022551909927863)
      ·
        refine ⟨7650250455033827864891795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5100166970022551909927863 7650250455033827864891795)
        ·
          refine ⟨11475375682550741797337693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7650250455033827864891795 11475375682550741797337693)
          ·
            refine ⟨4303265880956528174001635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11475375682550741797337693 4303265880956528174001635)
            ·
              refine ⟨6454898821434792261002453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4303265880956528174001635 6454898821434792261002453)
              ·
                refine ⟨151286691127377943617245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6454898821434792261002453 151286691127377943617245)
                ·
                  rfl

theorem cell22_3977502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 1, 7].length) (baseStart_3977502 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3977502 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3977502 prefixEnd_3977502 := by exact prefixLift 3977502
  have htrace : WordTrace (prefixWord ++ tailWord_3977502) baseStart_3977502 baseEnd_3977502 := by
    simpa [prefixWord, tailWord_3977502, baseEnd_3977502] using wordTrace_append hprefix tailTrace_3977502
  have hstable : (prefixWord ++ tailWord_3977502).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3977502).length < 2 ^ (prefixWord ++ tailWord_3977502).sum := by decide
  have hdescent : baseEnd_3977502 < baseStart_3977502 := by decide
  rcases family_descends (prefixWord ++ tailWord_3977502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3977534 : List Nat := [4, 2, 1, 2, 1, 3, 2, 3, 1, 3]
def baseStart_3977534 : Nat := 118140960795 + 3977534 * 2 ^ 59
def prefixEnd_3977534 : Nat := 4983230072969 + 3 ^ 40 * 3977534 * 2
def baseEnd_3977534 : Nat := 1361591174400364075755107

theorem tailTrace_3977534 : CollatzResearch.WordTrace tailWord_3977534 prefixEnd_3977534 1361591174400364075755107 := by
  unfold tailWord_3977534
  simp only [CollatzResearch.WordTrace]
  refine ⟨18134072896510137696222457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96715055448054067713186437 18134072896510137696222457)
  ·
    refine ⟨13600554672382603272166843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18134072896510137696222457 13600554672382603272166843)
    ·
      refine ⟨20400832008573904908250265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13600554672382603272166843 20400832008573904908250265)
      ·
        refine ⟨15300624006430428681187699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20400832008573904908250265 15300624006430428681187699)
        ·
          refine ⟨22950936009645643021781549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15300624006430428681187699 22950936009645643021781549)
          ·
            refine ⟨8606601003617116133168081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22950936009645643021781549 8606601003617116133168081)
            ·
              refine ⟨6454950752712837099876061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8606601003617116133168081 6454950752712837099876061)
              ·
                refine ⟨2420606532267313912453523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6454950752712837099876061 2420606532267313912453523)
                ·
                  refine ⟨3630909798400970868680285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2420606532267313912453523 3630909798400970868680285)
                  ·
                    refine ⟨1361591174400364075755107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3630909798400970868680285 1361591174400364075755107)
                    ·
                      rfl

theorem cell22_3977534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 2, 3, 1, 3].length) (baseStart_3977534 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3977534 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3977534 prefixEnd_3977534 := by exact prefixLift 3977534
  have htrace : WordTrace (prefixWord ++ tailWord_3977534) baseStart_3977534 baseEnd_3977534 := by
    simpa [prefixWord, tailWord_3977534, baseEnd_3977534] using wordTrace_append hprefix tailTrace_3977534
  have hstable : (prefixWord ++ tailWord_3977534).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3977534).length < 2 ^ (prefixWord ++ tailWord_3977534).sum := by decide
  have hdescent : baseEnd_3977534 < baseStart_3977534 := by decide
  rcases family_descends (prefixWord ++ tailWord_3977534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3977564 : List Nat := [2, 2, 4, 3, 1, 1, 3, 1, 5]
def baseStart_3977564 : Nat := 118140960795 + 3977564 * 2 ^ 59
def prefixEnd_3977564 : Nat := 4983230072969 + 3 ^ 40 * 3977564 * 2
def baseEnd_3977564 : Nat := 453867148004484665835005

theorem tailTrace_3977564 : CollatzResearch.WordTrace tailWord_3977564 prefixEnd_3977564 453867148004484665835005 := by
  unfold tailWord_3977564
  simp only [CollatzResearch.WordTrace]
  refine ⟨72536838680986208346685873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96715784907981611128914497 72536838680986208346685873)
  ·
    refine ⟨54402629010739656260014405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72536838680986208346685873 54402629010739656260014405)
    ·
      refine ⟨10200492939513685548752701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54402629010739656260014405 10200492939513685548752701)
      ·
        refine ⟨3825184852317632080782263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10200492939513685548752701 3825184852317632080782263)
        ·
          refine ⟨5737777278476448121173395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3825184852317632080782263 5737777278476448121173395)
          ·
            refine ⟨8606665917714672181760093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5737777278476448121173395 8606665917714672181760093)
            ·
              refine ⟨3227499719143002068160035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8606665917714672181760093 3227499719143002068160035)
              ·
                refine ⟨4841249578714503102240053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3227499719143002068160035 4841249578714503102240053)
                ·
                  refine ⟨453867148004484665835005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4841249578714503102240053 453867148004484665835005)
                  ·
                    rfl

theorem cell22_3977564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 3, 1, 5].length) (baseStart_3977564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3977564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3977564 prefixEnd_3977564 := by exact prefixLift 3977564
  have htrace : WordTrace (prefixWord ++ tailWord_3977564) baseStart_3977564 baseEnd_3977564 := by
    simpa [prefixWord, tailWord_3977564, baseEnd_3977564] using wordTrace_append hprefix tailTrace_3977564
  have hstable : (prefixWord ++ tailWord_3977564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3977564).length < 2 ^ (prefixWord ++ tailWord_3977564).sum := by decide
  have hdescent : baseEnd_3977564 < baseStart_3977564 := by decide
  rcases family_descends (prefixWord ++ tailWord_3977564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3977624 : List Nat := [2, 1, 2, 5, 1, 1, 4, 1, 2, 3]
def baseStart_3977624 : Nat := 118140960795 + 3977624 * 2 ^ 59
def prefixEnd_3977624 : Nat := 4983230072969 + 3 ^ 40 * 3977624 * 2
def baseEnd_3977624 : Nat := 1361621983239633841004831

theorem tailTrace_3977624 : CollatzResearch.WordTrace tailWord_3977624 prefixEnd_3977624 1361621983239633841004831 := by
  unfold tailWord_3977624
  simp only [CollatzResearch.WordTrace]
  refine ⟨72537932870877523470277963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96717243827836697960370617 72537932870877523470277963)
  ·
    refine ⟨108806899306316285205416945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72537932870877523470277963 108806899306316285205416945)
    ·
      refine ⟨81605174479737213904062709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108806899306316285205416945 81605174479737213904062709)
      ·
        refine ⟨7650485107475363803505879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 81605174479737213904062709 7650485107475363803505879)
        ·
          refine ⟨11475727661213045705258819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7650485107475363803505879 11475727661213045705258819)
          ·
            refine ⟨17213591491819568557888229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11475727661213045705258819 17213591491819568557888229)
            ·
              refine ⟨3227548404716169104604043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17213591491819568557888229 3227548404716169104604043)
              ·
                refine ⟨4841322607074253656906065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3227548404716169104604043 4841322607074253656906065)
                ·
                  refine ⟨3630991955305690242679549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4841322607074253656906065 3630991955305690242679549)
                  ·
                    refine ⟨1361621983239633841004831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3630991955305690242679549 1361621983239633841004831)
                    ·
                      rfl

theorem cell22_3977624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 4, 1, 2, 3].length) (baseStart_3977624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3977624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3977624 prefixEnd_3977624 := by exact prefixLift 3977624
  have htrace : WordTrace (prefixWord ++ tailWord_3977624) baseStart_3977624 baseEnd_3977624 := by
    simpa [prefixWord, tailWord_3977624, baseEnd_3977624] using wordTrace_append hprefix tailTrace_3977624
  have hstable : (prefixWord ++ tailWord_3977624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3977624).length < 2 ^ (prefixWord ++ tailWord_3977624).sum := by decide
  have hdescent : baseEnd_3977624 < baseStart_3977624 := by decide
  rcases family_descends (prefixWord ++ tailWord_3977624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3977695 : List Nat := [1, 1, 2, 3, 3, 2, 2, 1, 3, 4]
def baseStart_3977695 : Nat := 118140960795 + 3977695 * 2 ^ 59
def prefixEnd_3977695 : Nat := 4983230072969 + 3 ^ 40 * 3977695 * 2
def baseEnd_3977695 : Nat := 1361646287990613322479613

theorem tailTrace_3977695 : CollatzResearch.WordTrace tailWord_3977695 prefixEnd_3977695 1361646287990613322479613 := by
  unfold tailWord_3977695
  simp only [CollatzResearch.WordTrace]
  refine ⟨145078455324497826066390539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96718970216331884044260359 145078455324497826066390539)
  ·
    refine ⟨217617682986746739099585809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145078455324497826066390539 217617682986746739099585809)
    ·
      refine ⟨163213262240060054324689357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217617682986746739099585809 163213262240060054324689357)
      ·
        refine ⟨61204973340022520371758509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163213262240060054324689357 61204973340022520371758509)
        ·
          refine ⟨22951865002508445139409441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61204973340022520371758509 22951865002508445139409441)
          ·
            refine ⟨17213898751881333854557081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22951865002508445139409441 17213898751881333854557081)
            ·
              refine ⟨12910424063911000390917811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17213898751881333854557081 12910424063911000390917811)
              ·
                refine ⟨19365636095866500586376717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12910424063911000390917811 19365636095866500586376717)
                ·
                  refine ⟨7262113535949937719891269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19365636095866500586376717 7262113535949937719891269)
                  ·
                    refine ⟨1361646287990613322479613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7262113535949937719891269 1361646287990613322479613)
                    ·
                      rfl

theorem cell22_3977695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 1, 3, 4].length) (baseStart_3977695 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3977695 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3977695 prefixEnd_3977695 := by exact prefixLift 3977695
  have htrace : WordTrace (prefixWord ++ tailWord_3977695) baseStart_3977695 baseEnd_3977695 := by
    simpa [prefixWord, tailWord_3977695, baseEnd_3977695] using wordTrace_append hprefix tailTrace_3977695
  have hstable : (prefixWord ++ tailWord_3977695).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3977695).length < 2 ^ (prefixWord ++ tailWord_3977695).sum := by decide
  have hdescent : baseEnd_3977695 < baseStart_3977695 := by decide
  rcases family_descends (prefixWord ++ tailWord_3977695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3977723 : List Nat := [1, 1, 1, 1, 1, 3, 2, 1, 5, 6]
def baseStart_3977723 : Nat := 118140960795 + 3977723 * 2 ^ 59
def prefixEnd_3977723 : Nat := 4983230072969 + 3 ^ 40 * 3977723 * 2
def baseEnd_3977723 : Nat := 1361655872962830582779527

theorem tailTrace_3977723 : CollatzResearch.WordTrace tailWord_3977723 prefixEnd_3977723 1361655872962830582779527 := by
  unfold tailWord_3977723
  simp only [CollatzResearch.WordTrace]
  refine ⟨145079476568396386848409823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96719651045597591232273215 145079476568396386848409823)
  ·
    refine ⟨217619214852594580272614735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145079476568396386848409823 217619214852594580272614735)
    ·
      refine ⟨326428822278891870408922103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217619214852594580272614735 326428822278891870408922103)
      ·
        refine ⟨489643233418337805613383155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 326428822278891870408922103 489643233418337805613383155)
        ·
          refine ⟨734464850127506708420074733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 489643233418337805613383155 734464850127506708420074733)
          ·
            refine ⟨275424318797815015657528025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 734464850127506708420074733 275424318797815015657528025)
            ·
              refine ⟨206568239098361261743146019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 275424318797815015657528025 206568239098361261743146019)
              ·
                refine ⟨309852358647541892614719029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 206568239098361261743146019 309852358647541892614719029)
                ·
                  refine ⟨29048658623207052432629909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 309852358647541892614719029 29048658623207052432629909)
                  ·
                    refine ⟨1361655872962830582779527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29048658623207052432629909 1361655872962830582779527)
                    ·
                      rfl

theorem cell22_3977723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 5, 6].length) (baseStart_3977723 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3977723 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3977723 prefixEnd_3977723 := by exact prefixLift 3977723
  have htrace : WordTrace (prefixWord ++ tailWord_3977723) baseStart_3977723 baseEnd_3977723 := by
    simpa [prefixWord, tailWord_3977723, baseEnd_3977723] using wordTrace_append hprefix tailTrace_3977723
  have hstable : (prefixWord ++ tailWord_3977723).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3977723).length < 2 ^ (prefixWord ++ tailWord_3977723).sum := by decide
  have hdescent : baseEnd_3977723 < baseStart_3977723 := by decide
  rcases family_descends (prefixWord ++ tailWord_3977723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3977740 : List Nat := [2, 2, 1, 2, 4, 1, 1, 2, 1, 6]
def baseStart_3977740 : Nat := 118140960795 + 3977740 * 2 ^ 59
def prefixEnd_3977740 : Nat := 4983230072969 + 3 ^ 40 * 3977740 * 2
def baseEnd_3977740 : Nat := 1361661692410248205104475

theorem tailTrace_3977740 : CollatzResearch.WordTrace tailWord_3977740 prefixEnd_3977740 1361661692410248205104475 := by
  unfold tailWord_3977740
  simp only [CollatzResearch.WordTrace]
  refine ⟨72540048304667399375889337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96720064406223199167852449 72540048304667399375889337)
  ·
    refine ⟨54405036228500549531917003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72540048304667399375889337 54405036228500549531917003)
    ·
      refine ⟨81607554342750824297875505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54405036228500549531917003 81607554342750824297875505)
      ·
        refine ⟨61205665757063118223406629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81607554342750824297875505 61205665757063118223406629)
        ·
          refine ⟨11476062329449334666888743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61205665757063118223406629 11476062329449334666888743)
          ·
            refine ⟨17214093494174002000333115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11476062329449334666888743 17214093494174002000333115)
            ·
              refine ⟨25821140241261003000499673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17214093494174002000333115 25821140241261003000499673)
              ·
                refine ⟨19365855180945752250374755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25821140241261003000499673 19365855180945752250374755)
                ·
                  refine ⟨29048782771418628375562133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19365855180945752250374755 29048782771418628375562133)
                  ·
                    refine ⟨1361661692410248205104475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29048782771418628375562133 1361661692410248205104475)
                    ·
                      rfl

theorem cell22_3977740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 2, 1, 6].length) (baseStart_3977740 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3977740 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3977740 prefixEnd_3977740 := by exact prefixLift 3977740
  have htrace : WordTrace (prefixWord ++ tailWord_3977740) baseStart_3977740 baseEnd_3977740 := by
    simpa [prefixWord, tailWord_3977740, baseEnd_3977740] using wordTrace_append hprefix tailTrace_3977740
  have hstable : (prefixWord ++ tailWord_3977740).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3977740).length < 2 ^ (prefixWord ++ tailWord_3977740).sum := by decide
  have hdescent : baseEnd_3977740 < baseStart_3977740 := by decide
  rcases family_descends (prefixWord ++ tailWord_3977740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3977742 : List Nat := [4, 1, 1, 2, 3, 1, 3, 1, 1, 5]
def baseStart_3977742 : Nat := 118140960795 + 3977742 * 2 ^ 59
def prefixEnd_3977742 : Nat := 4983230072969 + 3 ^ 40 * 3977742 * 2
def baseEnd_3977742 : Nat := 1361662377051120866554469

theorem tailTrace_3977742 : CollatzResearch.WordTrace tailWord_3977742 prefixEnd_3977742 1361662377051120866554469 := by
  unfold tailWord_3977742
  simp only [CollatzResearch.WordTrace]
  refine ⟨18135021194415944136668935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96720113036885035395567653 18135021194415944136668935)
  ·
    refine ⟨27202531791623916205003403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18135021194415944136668935 27202531791623916205003403)
    ·
      refine ⟨40803797687435874307505105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27202531791623916205003403 40803797687435874307505105)
      ·
        refine ⟨30602848265576905730628829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40803797687435874307505105 30602848265576905730628829)
        ·
          refine ⟨11476068099591339648985811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30602848265576905730628829 11476068099591339648985811)
          ·
            refine ⟨17214102149387009473478717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11476068099591339648985811 17214102149387009473478717)
            ·
              refine ⟨6455288306020128552554519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17214102149387009473478717 6455288306020128552554519)
              ·
                refine ⟨9682932459030192828831779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6455288306020128552554519 9682932459030192828831779)
                ·
                  refine ⟨14524398688545289243247669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9682932459030192828831779 14524398688545289243247669)
                  ·
                    refine ⟨1361662377051120866554469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14524398688545289243247669 1361662377051120866554469)
                    ·
                      rfl

theorem cell22_3977742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 3, 1, 1, 5].length) (baseStart_3977742 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3977742 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3977742 prefixEnd_3977742 := by exact prefixLift 3977742
  have htrace : WordTrace (prefixWord ++ tailWord_3977742) baseStart_3977742 baseEnd_3977742 := by
    simpa [prefixWord, tailWord_3977742, baseEnd_3977742] using wordTrace_append hprefix tailTrace_3977742
  have hstable : (prefixWord ++ tailWord_3977742).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3977742).length < 2 ^ (prefixWord ++ tailWord_3977742).sum := by decide
  have hdescent : baseEnd_3977742 < baseStart_3977742 := by decide
  rcases family_descends (prefixWord ++ tailWord_3977742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3977774 : List Nat := [4, 1, 3, 1, 3, 1, 1, 2, 2, 4]
def baseStart_3977774 : Nat := 118140960795 + 3977774 * 2 ^ 59
def prefixEnd_3977774 : Nat := 4983230072969 + 3 ^ 40 * 3977774 * 2
def baseEnd_3977774 : Nat := 1361673331305083449754371

theorem tailTrace_3977774 : CollatzResearch.WordTrace tailWord_3977774 prefixEnd_3977774 1361673331305083449754371 := by
  unfold tailWord_3977774
  simp only [CollatzResearch.WordTrace]
  refine ⟨18135167086401452819814547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96720891127474415039010917 18135167086401452819814547)
  ·
    refine ⟨27202750629602179229721821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18135167086401452819814547 27202750629602179229721821)
    ·
      refine ⟨10201031486100817211145683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27202750629602179229721821 10201031486100817211145683)
      ·
        refine ⟨15301547229151225816718525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10201031486100817211145683 15301547229151225816718525)
        ·
          refine ⟨5738080210931709681269447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15301547229151225816718525 5738080210931709681269447)
          ·
            refine ⟨8607120316397564521904171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5738080210931709681269447 8607120316397564521904171)
            ·
              refine ⟨12910680474596346782856257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8607120316397564521904171 12910680474596346782856257)
              ·
                refine ⟨9683010355947260087142193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12910680474596346782856257 9683010355947260087142193)
                ·
                  refine ⟨7262257766960445065356645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9683010355947260087142193 7262257766960445065356645)
                  ·
                    refine ⟨1361673331305083449754371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7262257766960445065356645 1361673331305083449754371)
                    ·
                      rfl

theorem cell22_3977774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 2, 2, 4].length) (baseStart_3977774 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3977774 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3977774 prefixEnd_3977774 := by exact prefixLift 3977774
  have htrace : WordTrace (prefixWord ++ tailWord_3977774) baseStart_3977774 baseEnd_3977774 := by
    simpa [prefixWord, tailWord_3977774, baseEnd_3977774] using wordTrace_append hprefix tailTrace_3977774
  have hstable : (prefixWord ++ tailWord_3977774).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3977774).length < 2 ^ (prefixWord ++ tailWord_3977774).sum := by decide
  have hdescent : baseEnd_3977774 < baseStart_3977774 := by decide
  rcases family_descends (prefixWord ++ tailWord_3977774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3977785 : List Nat := [1, 2, 1, 5, 1, 1, 2, 1, 2, 6]
def baseStart_3977785 : Nat := 118140960795 + 3977785 * 2 ^ 59
def prefixEnd_3977785 : Nat := 4983230072969 + 3 ^ 40 * 3977785 * 2
def baseEnd_3977785 : Nat := 1361677096829883087729337

theorem tailTrace_3977785 : CollatzResearch.WordTrace tailWord_3977785 prefixEnd_3977785 1361677096829883087729337 := by
  unfold tailWord_3977785
  simp only [CollatzResearch.WordTrace]
  refine ⟨145081737894171771437166809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96721158596114514291444539 145081737894171771437166809)
  ·
    refine ⟨108811303420628828577875107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145081737894171771437166809 108811303420628828577875107)
    ·
      refine ⟨163216955130943242866812661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108811303420628828577875107 163216955130943242866812661)
      ·
        refine ⟨15301589543525929018763687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 163216955130943242866812661 15301589543525929018763687)
        ·
          refine ⟨22952384315288893528145531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15301589543525929018763687 22952384315288893528145531)
          ·
            refine ⟨34428576472933340292218297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22952384315288893528145531 34428576472933340292218297)
            ·
              refine ⟨25821432354700005219163723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34428576472933340292218297 25821432354700005219163723)
              ·
                refine ⟨38732148532050007828745585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25821432354700005219163723 38732148532050007828745585)
                ·
                  refine ⟨29049111399037505871559189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38732148532050007828745585 29049111399037505871559189)
                  ·
                    refine ⟨1361677096829883087729337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29049111399037505871559189 1361677096829883087729337)
                    ·
                      rfl

theorem cell22_3977785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 1, 2, 6].length) (baseStart_3977785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3977785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3977785 prefixEnd_3977785 := by exact prefixLift 3977785
  have htrace : WordTrace (prefixWord ++ tailWord_3977785) baseStart_3977785 baseEnd_3977785 := by
    simpa [prefixWord, tailWord_3977785, baseEnd_3977785] using wordTrace_append hprefix tailTrace_3977785
  have hstable : (prefixWord ++ tailWord_3977785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3977785).length < 2 ^ (prefixWord ++ tailWord_3977785).sum := by decide
  have hdescent : baseEnd_3977785 < baseStart_3977785 := by decide
  rcases family_descends (prefixWord ++ tailWord_3977785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3977838 : List Nat := [4, 1, 2, 2, 2, 1, 4, 2, 1, 3]
def baseStart_3977838 : Nat := 118140960795 + 3977838 * 2 ^ 59
def prefixEnd_3977838 : Nat := 4983230072969 + 3 ^ 40 * 3977838 * 2
def baseEnd_3977838 : Nat := 1361695239813008616154175

theorem tailTrace_3977838 : CollatzResearch.WordTrace tailWord_3977838 prefixEnd_3977838 1361695239813008616154175 := by
  unfold tailWord_3977838
  simp only [CollatzResearch.WordTrace]
  refine ⟨18135458870372470186105771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96722447308653174325897445 18135458870372470186105771)
  ·
    refine ⟨27203188305558705279158657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18135458870372470186105771 27203188305558705279158657)
    ·
      refine ⟨20402391229169028959368993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27203188305558705279158657 20402391229169028959368993)
      ·
        refine ⟨15301793421876771719526745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20402391229169028959368993 15301793421876771719526745)
        ·
          refine ⟨11476345066407578789645059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15301793421876771719526745 11476345066407578789645059)
          ·
            refine ⟨17214517599611368184467589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11476345066407578789645059 17214517599611368184467589)
            ·
              refine ⟨3227722049927131534587673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17214517599611368184467589 3227722049927131534587673)
              ·
                refine ⟨2420791537445348650940755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3227722049927131534587673 2420791537445348650940755)
                ·
                  refine ⟨3631187306168022976411133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2420791537445348650940755 3631187306168022976411133)
                  ·
                    refine ⟨1361695239813008616154175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3631187306168022976411133 1361695239813008616154175)
                    ·
                      rfl

theorem cell22_3977838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 4, 2, 1, 3].length) (baseStart_3977838 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3977838 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3977838 prefixEnd_3977838 := by exact prefixLift 3977838
  have htrace : WordTrace (prefixWord ++ tailWord_3977838) baseStart_3977838 baseEnd_3977838 := by
    simpa [prefixWord, tailWord_3977838, baseEnd_3977838] using wordTrace_append hprefix tailTrace_3977838
  have hstable : (prefixWord ++ tailWord_3977838).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3977838).length < 2 ^ (prefixWord ++ tailWord_3977838).sum := by decide
  have hdescent : baseEnd_3977838 < baseStart_3977838 := by decide
  rcases family_descends (prefixWord ++ tailWord_3977838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3977875 : List Nat := [1, 1, 1, 2, 1, 2, 2, 5, 1, 6]
def baseStart_3977875 : Nat := 118140960795 + 3977875 * 2 ^ 59
def prefixEnd_3977875 : Nat := 4983230072969 + 3 ^ 40 * 3977875 * 2
def baseEnd_3977875 : Nat := 1361707905669152852979061

theorem tailTrace_3977875 : CollatzResearch.WordTrace tailWord_3977875 prefixEnd_3977875 1361707905669152852979061 := by
  unfold tailWord_3977875
  simp only [CollatzResearch.WordTrace]
  refine ⟨145085020463845716807943079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96723346975897144538628719 145085020463845716807943079)
  ·
    refine ⟨217627530695768575211914619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145085020463845716807943079 217627530695768575211914619)
    ·
      refine ⟨326441296043652862817871929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217627530695768575211914619 326441296043652862817871929)
      ·
        refine ⟨244830972032739647113403947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 326441296043652862817871929 244830972032739647113403947)
        ·
          refine ⟨367246458049109470670105921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244830972032739647113403947 367246458049109470670105921)
          ·
            refine ⟨275434843536832103002579441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 367246458049109470670105921 275434843536832103002579441)
            ·
              refine ⟨206576132652624077251934581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 275434843536832103002579441 206576132652624077251934581)
              ·
                refine ⟨19366512436183507242368867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 206576132652624077251934581 19366512436183507242368867)
                ·
                  refine ⟨29049768654275260863553301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19366512436183507242368867 29049768654275260863553301)
                  ·
                    refine ⟨1361707905669152852979061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29049768654275260863553301 1361707905669152852979061)
                    ·
                      rfl

theorem cell22_3977875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 5, 1, 6].length) (baseStart_3977875 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3977875 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3977875 prefixEnd_3977875 := by exact prefixLift 3977875
  have htrace : WordTrace (prefixWord ++ tailWord_3977875) baseStart_3977875 baseEnd_3977875 := by
    simpa [prefixWord, tailWord_3977875, baseEnd_3977875] using wordTrace_append hprefix tailTrace_3977875
  have hstable : (prefixWord ++ tailWord_3977875).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3977875).length < 2 ^ (prefixWord ++ tailWord_3977875).sum := by decide
  have hdescent : baseEnd_3977875 < baseStart_3977875 := by decide
  rcases family_descends (prefixWord ++ tailWord_3977875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3977879 : List Nat := [1, 1, 3, 3, 2, 1, 4, 3, 4]
def baseStart_3977879 : Nat := 118140960795 + 3977879 * 2 ^ 59
def prefixEnd_3977879 : Nat := 4983230072969 + 3 ^ 40 * 3977879 * 2
def baseEnd_3977879 : Nat := 453903091650299391959683

theorem tailTrace_3977879 : CollatzResearch.WordTrace tailWord_3977879 prefixEnd_3977879 453903091650299391959683 := by
  unfold tailWord_3977879
  simp only [CollatzResearch.WordTrace]
  refine ⟨145085166355831225491088691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96723444237220816994059127 145085166355831225491088691)
  ·
    refine ⟨217627749533746838236633037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145085166355831225491088691 217627749533746838236633037)
    ·
      refine ⟨81610406075155064338737389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 217627749533746838236633037 81610406075155064338737389)
      ·
        refine ⟨30603902278183149127026521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81610406075155064338737389 30603902278183149127026521)
        ·
          refine ⟨22952926708637361845269891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30603902278183149127026521 22952926708637361845269891)
          ·
            refine ⟨34429390062956042767904837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22952926708637361845269891 34429390062956042767904837)
            ·
              refine ⟨6455510636804258018982157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34429390062956042767904837 6455510636804258018982157)
              ·
                refine ⟨2420816488801596757118309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6455510636804258018982157 2420816488801596757118309)
                ·
                  refine ⟨453903091650299391959683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2420816488801596757118309 453903091650299391959683)
                  ·
                    rfl

theorem cell22_3977879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 4, 3, 4].length) (baseStart_3977879 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3977879 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3977879 prefixEnd_3977879 := by exact prefixLift 3977879
  have htrace : WordTrace (prefixWord ++ tailWord_3977879) baseStart_3977879 baseEnd_3977879 := by
    simpa [prefixWord, tailWord_3977879, baseEnd_3977879] using wordTrace_append hprefix tailTrace_3977879
  have hstable : (prefixWord ++ tailWord_3977879).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3977879).length < 2 ^ (prefixWord ++ tailWord_3977879).sum := by decide
  have hdescent : baseEnd_3977879 < baseStart_3977879 := by decide
  rcases family_descends (prefixWord ++ tailWord_3977879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3977892 : List Nat := [2, 3, 1, 2, 2, 1, 2, 1, 4, 4]
def baseStart_3977892 : Nat := 118140960795 + 3977892 * 2 ^ 59
def prefixEnd_3977892 : Nat := 4983230072969 + 3 ^ 40 * 3977892 * 2
def baseEnd_3977892 : Nat := 1361713725116570475304009

theorem tailTrace_3977892 : CollatzResearch.WordTrace tailWord_3977892 prefixEnd_3977892 1361713725116570475304009 := by
  unfold tailWord_3977892
  simp only [CollatzResearch.WordTrace]
  refine ⟨72542820252392064355655965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96723760336522752474207953 72542820252392064355655965)
  ·
    refine ⟨27203557594647024133370987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72542820252392064355655965 27203557594647024133370987)
    ·
      refine ⟨40805336391970536200056481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27203557594647024133370987 40805336391970536200056481)
      ·
        refine ⟨30604002293977902150042361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40805336391970536200056481 30604002293977902150042361)
        ·
          refine ⟨22953001720483426612531771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30604002293977902150042361 22953001720483426612531771)
          ·
            refine ⟨34429502580725139918797657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22953001720483426612531771 34429502580725139918797657)
            ·
              refine ⟨25822126935543854939098243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34429502580725139918797657 25822126935543854939098243)
              ·
                refine ⟨38733190403315782408647365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25822126935543854939098243 38733190403315782408647365)
                ·
                  refine ⟨7262473200621709201621381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38733190403315782408647365 7262473200621709201621381)
                  ·
                    refine ⟨1361713725116570475304009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7262473200621709201621381 1361713725116570475304009)
                    ·
                      rfl

theorem cell22_3977892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 1, 4, 4].length) (baseStart_3977892 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3977892 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3977892 prefixEnd_3977892 := by exact prefixLift 3977892
  have htrace : WordTrace (prefixWord ++ tailWord_3977892) baseStart_3977892 baseEnd_3977892 := by
    simpa [prefixWord, tailWord_3977892, baseEnd_3977892] using wordTrace_append hprefix tailTrace_3977892
  have hstable : (prefixWord ++ tailWord_3977892).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3977892).length < 2 ^ (prefixWord ++ tailWord_3977892).sum := by decide
  have hdescent : baseEnd_3977892 < baseStart_3977892 := by decide
  rcases family_descends (prefixWord ++ tailWord_3977892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3977911 : List Nat := [1, 1, 3, 1, 7, 1, 1, 1, 1, 5]
def baseStart_3977911 : Nat := 118140960795 + 3977911 * 2 ^ 59
def prefixEnd_3977911 : Nat := 4983230072969 + 3 ^ 40 * 3977911 * 2
def baseEnd_3977911 : Nat := 1361720229204860759078951

theorem tailTrace_3977911 : CollatzResearch.WordTrace tailWord_3977911 prefixEnd_3977911 1361720229204860759078951 := by
  unfold tailWord_3977911
  simp only [CollatzResearch.WordTrace]
  refine ⟨145086333491715294956253587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96724222327810196637502391 145086333491715294956253587)
  ·
    refine ⟨217629500237572942434380381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145086333491715294956253587 217629500237572942434380381)
    ·
      refine ⟨81611062589089853412892643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 217629500237572942434380381 81611062589089853412892643)
      ·
        refine ⟨122416593883634780119338965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81611062589089853412892643 122416593883634780119338965)
        ·
          refine ⟨2869138919147690159047007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 122416593883634780119338965 2869138919147690159047007)
          ·
            refine ⟨4303708378721535238570511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2869138919147690159047007 4303708378721535238570511)
            ·
              refine ⟨6455562568082302857855767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4303708378721535238570511 6455562568082302857855767)
              ·
                refine ⟨9683343852123454286783651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6455562568082302857855767 9683343852123454286783651)
                ·
                  refine ⟨14525015778185181430175477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9683343852123454286783651 14525015778185181430175477)
                  ·
                    refine ⟨1361720229204860759078951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14525015778185181430175477 1361720229204860759078951)
                    ·
                      rfl

theorem cell22_3977911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 1, 1, 1, 5].length) (baseStart_3977911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3977911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3977911 prefixEnd_3977911 := by exact prefixLift 3977911
  have htrace : WordTrace (prefixWord ++ tailWord_3977911) baseStart_3977911 baseEnd_3977911 := by
    simpa [prefixWord, tailWord_3977911, baseEnd_3977911] using wordTrace_append hprefix tailTrace_3977911
  have hstable : (prefixWord ++ tailWord_3977911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3977911).length < 2 ^ (prefixWord ++ tailWord_3977911).sum := by decide
  have hdescent : baseEnd_3977911 < baseStart_3977911 := by decide
  rcases family_descends (prefixWord ++ tailWord_3977911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3977924 : List Nat := [2, 3, 3, 1, 1, 2, 4, 6]
def baseStart_3977924 : Nat := 118140960795 + 3977924 * 2 ^ 59
def prefixEnd_3977924 : Nat := 4983230072969 + 3 ^ 40 * 3977924 * 2
def baseEnd_3977924 : Nat := 151302742152281450944879

theorem tailTrace_3977924 : CollatzResearch.WordTrace tailWord_3977924 prefixEnd_3977924 151302742152281450944879 := by
  unfold tailWord_3977924
  simp only [CollatzResearch.WordTrace]
  refine ⟨72543403820334099088238413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96724538427112132117651217 72543403820334099088238413)
  ·
    refine ⟨27203776432625287158089405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72543403820334099088238413 27203776432625287158089405)
    ·
      refine ⟨10201416162234482684283527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27203776432625287158089405 10201416162234482684283527)
      ·
        refine ⟨15302124243351724026425291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10201416162234482684283527 15302124243351724026425291)
        ·
          refine ⟨22953186365027586039637937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15302124243351724026425291 22953186365027586039637937)
          ·
            refine ⟨17214889773770689529728453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22953186365027586039637937 17214889773770689529728453)
            ·
              refine ⟨3227791832582004286824085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17214889773770689529728453 3227791832582004286824085)
              ·
                refine ⟨151302742152281450944879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3227791832582004286824085 151302742152281450944879)
                ·
                  rfl

theorem cell22_3977924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 4, 6].length) (baseStart_3977924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3977924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3977924 prefixEnd_3977924 := by exact prefixLift 3977924
  have htrace : WordTrace (prefixWord ++ tailWord_3977924) baseStart_3977924 baseEnd_3977924 := by
    simpa [prefixWord, tailWord_3977924, baseEnd_3977924] using wordTrace_append hprefix tailTrace_3977924
  have hstable : (prefixWord ++ tailWord_3977924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3977924).length < 2 ^ (prefixWord ++ tailWord_3977924).sum := by decide
  have hdescent : baseEnd_3977924 < baseStart_3977924 := by decide
  rcases family_descends (prefixWord ++ tailWord_3977924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3977941 : List Nat := [1, 3, 2, 5, 2, 1, 8]
def baseStart_3977941 : Nat := 118140960795 + 3977941 * 2 ^ 59
def prefixEnd_3977941 : Nat := 4983230072969 + 3 ^ 40 * 3977941 * 2
def baseEnd_3977941 : Nat := 50434462919183358549217

theorem tailTrace_3977941 : CollatzResearch.WordTrace tailWord_3977941 prefixEnd_3977941 50434462919183358549217 := by
  unfold tailWord_3977941
  simp only [CollatzResearch.WordTrace]
  refine ⟨145087427681606610079845677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96724951787737740053230451 145087427681606610079845677)
  ·
    refine ⟨54407785380602478779942129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145087427681606610079845677 54407785380602478779942129)
    ·
      refine ⟨40805839035451859084956597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54407785380602478779942129 40805839035451859084956597)
      ·
        refine ⟨3825547409573611789214681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 40805839035451859084956597 3825547409573611789214681)
        ·
          refine ⟨2869160557180208841911011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3825547409573611789214681 2869160557180208841911011)
          ·
            refine ⟨4303740835770313262866517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2869160557180208841911011 4303740835770313262866517)
            ·
              refine ⟨50434462919183358549217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4303740835770313262866517 50434462919183358549217)
              ·
                rfl

theorem cell22_3977941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 8].length) (baseStart_3977941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3977941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3977941 prefixEnd_3977941 := by exact prefixLift 3977941
  have htrace : WordTrace (prefixWord ++ tailWord_3977941) baseStart_3977941 baseEnd_3977941 := by
    simpa [prefixWord, tailWord_3977941, baseEnd_3977941] using wordTrace_append hprefix tailTrace_3977941
  have hstable : (prefixWord ++ tailWord_3977941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3977941).length < 2 ^ (prefixWord ++ tailWord_3977941).sum := by decide
  have hdescent : baseEnd_3977941 < baseStart_3977941 := by decide
  rcases family_descends (prefixWord ++ tailWord_3977941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3977952 : List Nat := [2, 1, 1, 3, 1, 2, 1, 6, 5]
def baseStart_3977952 : Nat := 118140960795 + 3977952 * 2 ^ 59
def prefixEnd_3977952 : Nat := 4983230072969 + 3 ^ 40 * 3977952 * 2
def baseEnd_3977952 : Nat := 453911421447583439601275

theorem tailTrace_3977952 : CollatzResearch.WordTrace tailWord_3977952 prefixEnd_3977952 453911421447583439601275 := by
  unfold tailWord_3977952
  simp only [CollatzResearch.WordTrace]
  refine ⟨72543914442283379479248055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96725219256377839305664073 72543914442283379479248055)
  ·
    refine ⟨108815871663425069218872083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72543914442283379479248055 108815871663425069218872083)
    ·
      refine ⟨163223807495137603828308125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108815871663425069218872083 163223807495137603828308125)
      ·
        refine ⟨61208927810676601435615547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163223807495137603828308125 61208927810676601435615547)
        ·
          refine ⟨91813391716014902153423321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61208927810676601435615547 91813391716014902153423321)
          ·
            refine ⟨68860043787011176615067491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91813391716014902153423321 68860043787011176615067491)
            ·
              refine ⟨103290065680516764922601237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68860043787011176615067491 103290065680516764922601237)
              ·
                refine ⟨4841721828774223355746933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 103290065680516764922601237 4841721828774223355746933)
                ·
                  refine ⟨453911421447583439601275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4841721828774223355746933 453911421447583439601275)
                  ·
                    rfl

theorem cell22_3977952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 6, 5].length) (baseStart_3977952 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3977952 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3977952 prefixEnd_3977952 := by exact prefixLift 3977952
  have htrace : WordTrace (prefixWord ++ tailWord_3977952) baseStart_3977952 baseEnd_3977952 := by
    simpa [prefixWord, tailWord_3977952, baseEnd_3977952] using wordTrace_append hprefix tailTrace_3977952
  have hstable : (prefixWord ++ tailWord_3977952).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3977952).length < 2 ^ (prefixWord ++ tailWord_3977952).sum := by decide
  have hdescent : baseEnd_3977952 < baseStart_3977952 := by decide
  rcases family_descends (prefixWord ++ tailWord_3977952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3977956 : List Nat := [2, 3, 1, 1, 1, 6, 1, 1, 3, 3]
def baseStart_3977956 : Nat := 118140960795 + 3977956 * 2 ^ 59
def prefixEnd_3977956 : Nat := 4983230072969 + 3 ^ 40 * 3977956 * 2
def baseEnd_3977956 : Nat := 1361735633624495641703813

theorem tailTrace_3977956 : CollatzResearch.WordTrace tailWord_3977956 prefixEnd_3977956 1361735633624495641703813 := by
  unfold tailWord_3977956
  simp only [CollatzResearch.WordTrace]
  refine ⟨72543987388276133820820861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96725316517701511761094481 72543987388276133820820861)
  ·
    refine ⟨27203995270603550182807823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72543987388276133820820861 27203995270603550182807823)
    ·
      refine ⟨40805992905905325274211735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27203995270603550182807823 40805992905905325274211735)
      ·
        refine ⟨61208989358857987911317603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40805992905905325274211735 61208989358857987911317603)
        ·
          refine ⟨91813484038286981866976405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61208989358857987911317603 91813484038286981866976405)
          ·
            refine ⟨4303757064294702275014519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 91813484038286981866976405 4303757064294702275014519)
            ·
              refine ⟨6455635596442053412521779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4303757064294702275014519 6455635596442053412521779)
              ·
                refine ⟨9683453394663080118782669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6455635596442053412521779 9683453394663080118782669)
                ·
                  refine ⟨3631295022998655044543501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9683453394663080118782669 3631295022998655044543501)
                  ·
                    refine ⟨1361735633624495641703813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3631295022998655044543501 1361735633624495641703813)
                    ·
                      rfl

theorem cell22_3977956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 1, 1, 3, 3].length) (baseStart_3977956 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3977956 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3977956 prefixEnd_3977956 := by exact prefixLift 3977956
  have htrace : WordTrace (prefixWord ++ tailWord_3977956) baseStart_3977956 baseEnd_3977956 := by
    simpa [prefixWord, tailWord_3977956, baseEnd_3977956] using wordTrace_append hprefix tailTrace_3977956
  have hstable : (prefixWord ++ tailWord_3977956).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3977956).length < 2 ^ (prefixWord ++ tailWord_3977956).sum := by decide
  have hdescent : baseEnd_3977956 < baseStart_3977956 := by decide
  rcases family_descends (prefixWord ++ tailWord_3977956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3978007 : List Nat := [1, 1, 3, 4, 4, 1, 2, 2, 1, 3]
def baseStart_3978007 : Nat := 118140960795 + 3978007 * 2 ^ 59
def prefixEnd_3978007 : Nat := 4983230072969 + 3 ^ 40 * 3978007 * 2
def baseEnd_3978007 : Nat := 1361753091966748508678657

theorem tailTrace_3978007 : CollatzResearch.WordTrace tailWord_3978007 prefixEnd_3978007 1361753091966748508678657 := by
  unfold tailWord_3978007
  simp only [CollatzResearch.WordTrace]
  refine ⟨145089834899367503351748275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96726556599578335567832183 145089834899367503351748275)
  ·
    refine ⟨217634752349051255027622413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145089834899367503351748275 217634752349051255027622413)
    ·
      refine ⟨81613032130894220635358405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 217634752349051255027622413 81613032130894220635358405)
      ·
        refine ⟨15302443524542666369129701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81613032130894220635358405 15302443524542666369129701)
        ·
          refine ⟨2869208160851749944211819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15302443524542666369129701 2869208160851749944211819)
          ·
            refine ⟨4303812241277624916317729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2869208160851749944211819 4303812241277624916317729)
            ·
              refine ⟨3227859180958218687238297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4303812241277624916317729 3227859180958218687238297)
              ·
                refine ⟨2420894385718664015428723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3227859180958218687238297 2420894385718664015428723)
                ·
                  refine ⟨3631341578577996023143085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2420894385718664015428723 3631341578577996023143085)
                  ·
                    refine ⟨1361753091966748508678657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3631341578577996023143085 1361753091966748508678657)
                    ·
                      rfl

theorem cell22_3978007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 2, 2, 1, 3].length) (baseStart_3978007 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3978007 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3978007 prefixEnd_3978007 := by exact prefixLift 3978007
  have htrace : WordTrace (prefixWord ++ tailWord_3978007) baseStart_3978007 baseEnd_3978007 := by
    simpa [prefixWord, tailWord_3978007, baseEnd_3978007] using wordTrace_append hprefix tailTrace_3978007
  have hstable : (prefixWord ++ tailWord_3978007).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3978007).length < 2 ^ (prefixWord ++ tailWord_3978007).sum := by decide
  have hdescent : baseEnd_3978007 < baseStart_3978007 := by decide
  rcases family_descends (prefixWord ++ tailWord_3978007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3978027 : List Nat := [1, 1, 1, 1, 2, 1, 2, 3, 6, 4]
def baseStart_3978027 : Nat := 118140960795 + 3978027 * 2 ^ 59
def prefixEnd_3978027 : Nat := 4983230072969 + 3 ^ 40 * 3978027 * 2
def baseEnd_3978027 : Nat := 1361759938375475123178595

theorem tailTrace_3978027 : CollatzResearch.WordTrace tailWord_3978027 prefixEnd_3978027 1361759938375475123178595 := by
  unfold tailWord_3978027
  simp only [CollatzResearch.WordTrace]
  refine ⟨145090564359295046767476335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96727042906196697844984223 145090564359295046767476335)
  ·
    refine ⟨217635846538942570151214503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145090564359295046767476335 217635846538942570151214503)
    ·
      refine ⟨326453769808413855226821755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217635846538942570151214503 326453769808413855226821755)
      ·
        refine ⟨489680654712620782840232633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 326453769808413855226821755 489680654712620782840232633)
        ·
          refine ⟨367260491034465587130174475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 489680654712620782840232633 367260491034465587130174475)
          ·
            refine ⟨550890736551698380695261713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 367260491034465587130174475 550890736551698380695261713)
            ·
              refine ⟨413168052413773785521446285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 550890736551698380695261713 413168052413773785521446285)
              ·
                refine ⟨154938019655165169570542357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 413168052413773785521446285 154938019655165169570542357)
                ·
                  refine ⟨7262719671335867323619173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 154938019655165169570542357 7262719671335867323619173)
                  ·
                    refine ⟨1361759938375475123178595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7262719671335867323619173 1361759938375475123178595)
                    ·
                      rfl

theorem cell22_3978027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 6, 4].length) (baseStart_3978027 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3978027 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3978027 prefixEnd_3978027 := by exact prefixLift 3978027
  have htrace : WordTrace (prefixWord ++ tailWord_3978027) baseStart_3978027 baseEnd_3978027 := by
    simpa [prefixWord, tailWord_3978027, baseEnd_3978027] using wordTrace_append hprefix tailTrace_3978027
  have hstable : (prefixWord ++ tailWord_3978027).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3978027).length < 2 ^ (prefixWord ++ tailWord_3978027).sum := by decide
  have hdescent : baseEnd_3978027 < baseStart_3978027 := by decide
  rcases family_descends (prefixWord ++ tailWord_3978027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3978072 : List Nat := [2, 1, 2, 2, 1, 1, 1, 3, 1, 8]
def baseStart_3978072 : Nat := 118140960795 + 3978072 * 2 ^ 59
def prefixEnd_3978072 : Nat := 4983230072969 + 3 ^ 40 * 3978072 * 2
def baseEnd_3978072 : Nat := 1361775342795110005803457

theorem tailTrace_3978072 : CollatzResearch.WordTrace tailWord_3978072 prefixEnd_3978072 1361775342795110005803457 := by
  unfold tailWord_3978072
  simp only [CollatzResearch.WordTrace]
  refine ⟨72546102822066009726432235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96728137096088012968576313 72546102822066009726432235)
  ·
    refine ⟨108819154233099014589648353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72546102822066009726432235 108819154233099014589648353)
    ·
      refine ⟨81614365674824260942236265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108819154233099014589648353 81614365674824260942236265)
      ·
        refine ⟨61210774256118195706677199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81614365674824260942236265 61210774256118195706677199)
        ·
          refine ⟨91816161384177293560015799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61210774256118195706677199 91816161384177293560015799)
          ·
            refine ⟨137724242076265940340023699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91816161384177293560015799 137724242076265940340023699)
            ·
              refine ⟨206586363114398910510035549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137724242076265940340023699 206586363114398910510035549)
              ·
                refine ⟨77469886167899591441263331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 206586363114398910510035549 77469886167899591441263331)
                ·
                  refine ⟨116204829251849387161894997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77469886167899591441263331 116204829251849387161894997)
                  ·
                    refine ⟨1361775342795110005803457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 116204829251849387161894997 1361775342795110005803457)
                    ·
                      rfl

theorem cell22_3978072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 3, 1, 8].length) (baseStart_3978072 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3978072 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3978072 prefixEnd_3978072 := by exact prefixLift 3978072
  have htrace : WordTrace (prefixWord ++ tailWord_3978072) baseStart_3978072 baseEnd_3978072 := by
    simpa [prefixWord, tailWord_3978072, baseEnd_3978072] using wordTrace_append hprefix tailTrace_3978072
  have hstable : (prefixWord ++ tailWord_3978072).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3978072).length < 2 ^ (prefixWord ++ tailWord_3978072).sum := by decide
  have hdescent : baseEnd_3978072 < baseStart_3978072 := by decide
  rcases family_descends (prefixWord ++ tailWord_3978072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3978168 : List Nat := [2, 1, 2, 1, 2, 5, 3, 1, 1, 4]
def baseStart_3978168 : Nat := 118140960795 + 3978168 * 2 ^ 59
def prefixEnd_3978168 : Nat := 4983230072969 + 3 ^ 40 * 3978168 * 2
def baseEnd_3978168 : Nat := 1361808205556997755403163

theorem tailTrace_3978168 : CollatzResearch.WordTrace tailWord_3978168 prefixEnd_3978168 1361808205556997755403163 := by
  unfold tailWord_3978168
  simp only [CollatzResearch.WordTrace]
  refine ⟨72547853525892113924179579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96730471367856151898906105 72547853525892113924179579)
  ·
    refine ⟨108821780288838170886269369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72547853525892113924179579 108821780288838170886269369)
    ·
      refine ⟨81616335216628628164702027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108821780288838170886269369 81616335216628628164702027)
      ·
        refine ⟨122424502824942942247053041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81616335216628628164702027 122424502824942942247053041)
        ·
          refine ⟨91818377118707206685289781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122424502824942942247053041 91818377118707206685289781)
          ·
            refine ⟨8607972854878800626745917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 91818377118707206685289781 8607972854878800626745917)
            ·
              refine ⟨3227989820579550235029719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8607972854878800626745917 3227989820579550235029719)
              ·
                refine ⟨4841984730869325352544579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3227989820579550235029719 4841984730869325352544579)
                ·
                  refine ⟨7262977096303988028816869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4841984730869325352544579 7262977096303988028816869)
                  ·
                    refine ⟨1361808205556997755403163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7262977096303988028816869 1361808205556997755403163)
                    ·
                      rfl

theorem cell22_3978168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 3, 1, 1, 4].length) (baseStart_3978168 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3978168 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3978168 prefixEnd_3978168 := by exact prefixLift 3978168
  have htrace : WordTrace (prefixWord ++ tailWord_3978168) baseStart_3978168 baseEnd_3978168 := by
    simpa [prefixWord, tailWord_3978168, baseEnd_3978168] using wordTrace_append hprefix tailTrace_3978168
  have hstable : (prefixWord ++ tailWord_3978168).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3978168).length < 2 ^ (prefixWord ++ tailWord_3978168).sum := by decide
  have hdescent : baseEnd_3978168 < baseStart_3978168 := by decide
  rcases family_descends (prefixWord ++ tailWord_3978168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3978183 : List Nat := [1, 1, 4, 1, 1, 2, 6, 2, 4]
def baseStart_3978183 : Nat := 118140960795 + 3978183 * 2 ^ 59
def prefixEnd_3978183 : Nat := 4983230072969 + 3 ^ 40 * 3978183 * 2
def baseEnd_3978183 : Nat := 453937780121180905426039

theorem tailTrace_3978183 : CollatzResearch.WordTrace tailWord_3978183 prefixEnd_3978183 453937780121180905426039 := by
  unfold tailWord_3978183
  simp only [CollatzResearch.WordTrace]
  refine ⟨145096254146729885410155203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96730836097819923606770135 145096254146729885410155203)
  ·
    refine ⟨217644381220094828115232805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145096254146729885410155203 217644381220094828115232805)
    ·
      refine ⟨40808321478767780271606151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 217644381220094828115232805 40808321478767780271606151)
      ·
        refine ⟨61212482218151670407409227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40808321478767780271606151 61212482218151670407409227)
        ·
          refine ⟨91818723327227505611113841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61212482218151670407409227 91818723327227505611113841)
          ·
            refine ⟨68864042495420629208335381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91818723327227505611113841 68864042495420629208335381)
            ·
              refine ⟨3228001991972841994140721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 68864042495420629208335381 3228001991972841994140721)
              ·
                refine ⟨2421001493979631495605541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3228001991972841994140721 2421001493979631495605541)
                ·
                  refine ⟨453937780121180905426039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2421001493979631495605541 453937780121180905426039)
                  ·
                    rfl

theorem cell22_3978183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 6, 2, 4].length) (baseStart_3978183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3978183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3978183 prefixEnd_3978183 := by exact prefixLift 3978183
  have htrace : WordTrace (prefixWord ++ tailWord_3978183) baseStart_3978183 baseEnd_3978183 := by
    simpa [prefixWord, tailWord_3978183, baseEnd_3978183] using wordTrace_append hprefix tailTrace_3978183
  have hstable : (prefixWord ++ tailWord_3978183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3978183).length < 2 ^ (prefixWord ++ tailWord_3978183).sum := by decide
  have hdescent : baseEnd_3978183 < baseStart_3978183 := by decide
  rcases family_descends (prefixWord ++ tailWord_3978183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3978198 : List Nat := [5, 2, 1, 1, 2, 1, 1, 3, 1, 5]
def baseStart_3978198 : Nat := 118140960795 + 3978198 * 2 ^ 59
def prefixEnd_3978198 : Nat := 4983230072969 + 3 ^ 40 * 3978198 * 2
def baseEnd_3978198 : Nat := 1361818475170087677153071

theorem tailTrace_3978198 : CollatzResearch.WordTrace tailWord_3978198 prefixEnd_3978198 1361818475170087677153071 := by
  unfold tailWord_3978198
  simp only [CollatzResearch.WordTrace]
  refine ⟨9068550077604721435746953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 96731200827783695314634165 9068550077604721435746953)
  ·
    refine ⟨6801412558203541076810215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9068550077604721435746953 6801412558203541076810215)
    ·
      refine ⟨10202118837305311615215323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6801412558203541076810215 10202118837305311615215323)
      ·
        refine ⟨15303178255957967422822985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10202118837305311615215323 15303178255957967422822985)
        ·
          refine ⟨11477383691968475567117239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15303178255957967422822985 11477383691968475567117239)
          ·
            refine ⟨17216075537952713350675859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11477383691968475567117239 17216075537952713350675859)
            ·
              refine ⟨25824113306929070026013789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17216075537952713350675859 25824113306929070026013789)
              ·
                refine ⟨9684042490098401259755171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25824113306929070026013789 9684042490098401259755171)
                ·
                  refine ⟨14526063735147601889632757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9684042490098401259755171 14526063735147601889632757)
                  ·
                    refine ⟨1361818475170087677153071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14526063735147601889632757 1361818475170087677153071)
                    ·
                      rfl

theorem cell22_3978198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 3, 1, 5].length) (baseStart_3978198 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3978198 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3978198 prefixEnd_3978198 := by exact prefixLift 3978198
  have htrace : WordTrace (prefixWord ++ tailWord_3978198) baseStart_3978198 baseEnd_3978198 := by
    simpa [prefixWord, tailWord_3978198, baseEnd_3978198] using wordTrace_append hprefix tailTrace_3978198
  have hstable : (prefixWord ++ tailWord_3978198).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3978198).length < 2 ^ (prefixWord ++ tailWord_3978198).sum := by decide
  have hdescent : baseEnd_3978198 < baseStart_3978198 := by decide
  rcases family_descends (prefixWord ++ tailWord_3978198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3978211 : List Nat := [1, 1, 1, 6, 1, 1, 5, 6]
def baseStart_3978211 : Nat := 118140960795 + 3978211 * 2 ^ 59
def prefixEnd_3978211 : Nat := 4983230072969 + 3 ^ 40 * 3978211 * 2
def baseEnd_3978211 : Nat := 151313658370639997397559

theorem tailTrace_3978211 : CollatzResearch.WordTrace tailWord_3978211 prefixEnd_3978211 151313658370639997397559 := by
  unfold tailWord_3978211
  simp only [CollatzResearch.WordTrace]
  refine ⟨145097275390628446192174487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96731516927085630794782991 145097275390628446192174487)
  ·
    refine ⟨217645913085942669288261731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145097275390628446192174487 217645913085942669288261731)
    ·
      refine ⟨326468869628914003932392597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217645913085942669288261731 326468869628914003932392597)
      ·
        refine ⟨15303228263855343934330903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 326468869628914003932392597 15303228263855343934330903)
        ·
          refine ⟨22954842395783015901496355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15303228263855343934330903 22954842395783015901496355)
          ·
            refine ⟨34432263593674523852244533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22954842395783015901496355 34432263593674523852244533)
            ·
              refine ⟨3228024711906986611147925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34432263593674523852244533 3228024711906986611147925)
              ·
                refine ⟨151313658370639997397559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3228024711906986611147925 151313658370639997397559)
                ·
                  rfl

theorem cell22_3978211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 5, 6].length) (baseStart_3978211 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3978211 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3978211 prefixEnd_3978211 := by exact prefixLift 3978211
  have htrace : WordTrace (prefixWord ++ tailWord_3978211) baseStart_3978211 baseEnd_3978211 := by
    simpa [prefixWord, tailWord_3978211, baseEnd_3978211] using wordTrace_append hprefix tailTrace_3978211
  have hstable : (prefixWord ++ tailWord_3978211).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3978211).length < 2 ^ (prefixWord ++ tailWord_3978211).sum := by decide
  have hdescent : baseEnd_3978211 < baseStart_3978211 := by decide
  rcases family_descends (prefixWord ++ tailWord_3978211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3978213 : List Nat := [1, 3, 1, 6, 1, 1, 1, 1, 1, 6]
def baseStart_3978213 : Nat := 118140960795 + 3978213 * 2 ^ 59
def prefixEnd_3978213 : Nat := 4983230072969 + 3 ^ 40 * 3978213 * 2
def baseEnd_3978213 : Nat := 1361823609976632638028025

theorem tailTrace_3978213 : CollatzResearch.WordTrace tailWord_3978213 prefixEnd_3978213 1361823609976632638028025 := by
  unfold tailWord_3978213
  simp only [CollatzResearch.WordTrace]
  refine ⟨145097348336621200533747293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96731565557747467022498195 145097348336621200533747293)
  ·
    refine ⟨54411505626232950200155235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145097348336621200533747293 54411505626232950200155235)
    ·
      refine ⟨81617258439349425300232853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54411505626232950200155235 81617258439349425300232853)
      ·
        refine ⟨3825808989344504310948415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 81617258439349425300232853 3825808989344504310948415)
        ·
          refine ⟨5738713484016756466422623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3825808989344504310948415 5738713484016756466422623)
          ·
            refine ⟨8608070226025134699633935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5738713484016756466422623 8608070226025134699633935)
            ·
              refine ⟨12912105339037702049450903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8608070226025134699633935 12912105339037702049450903)
              ·
                refine ⟨19368158008556553074176355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12912105339037702049450903 19368158008556553074176355)
                ·
                  refine ⟨29052237012834829611264533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19368158008556553074176355 29052237012834829611264533)
                  ·
                    refine ⟨1361823609976632638028025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29052237012834829611264533 1361823609976632638028025)
                    ·
                      rfl

theorem cell22_3978213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 1, 1, 6].length) (baseStart_3978213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3978213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3978213 prefixEnd_3978213 := by exact prefixLift 3978213
  have htrace : WordTrace (prefixWord ++ tailWord_3978213) baseStart_3978213 baseEnd_3978213 := by
    simpa [prefixWord, tailWord_3978213, baseEnd_3978213] using wordTrace_append hprefix tailTrace_3978213
  have hstable : (prefixWord ++ tailWord_3978213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3978213).length < 2 ^ (prefixWord ++ tailWord_3978213).sum := by decide
  have hdescent : baseEnd_3978213 < baseStart_3978213 := by decide
  rcases family_descends (prefixWord ++ tailWord_3978213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3978294 : List Nat := [5, 1, 2, 1, 1, 3, 3, 2, 1, 3]
def baseStart_3978294 : Nat := 118140960795 + 3978294 * 2 ^ 59
def prefixEnd_3978294 : Nat := 4983230072969 + 3 ^ 40 * 3978294 * 2
def baseEnd_3978294 : Nat := 1361851337931975426752777

theorem tailTrace_3978294 : CollatzResearch.WordTrace tailWord_3978294 prefixEnd_3978294 1361851337931975426752777 := by
  unfold tailWord_3978294
  simp only [CollatzResearch.WordTrace]
  refine ⟨9068768915582984460465371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 96733535099551834244963957 9068768915582984460465371)
  ·
    refine ⟨13603153373374476690698057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9068768915582984460465371 13603153373374476690698057)
    ·
      refine ⟨10202365030030857518023543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13603153373374476690698057 10202365030030857518023543)
      ·
        refine ⟨15303547545046286277035315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10202365030030857518023543 15303547545046286277035315)
        ·
          refine ⟨22955321317569429415552973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15303547545046286277035315 22955321317569429415552973)
          ·
            refine ⟨8608245494088536030832365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22955321317569429415552973 8608245494088536030832365)
            ·
              refine ⟨3228092060283201011562137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8608245494088536030832365 3228092060283201011562137)
              ·
                refine ⟨2421069045212400758671603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3228092060283201011562137 2421069045212400758671603)
                ·
                  refine ⟨3631603567818601138007405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2421069045212400758671603 3631603567818601138007405)
                  ·
                    refine ⟨1361851337931975426752777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3631603567818601138007405 1361851337931975426752777)
                    ·
                      rfl

theorem cell22_3978294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 3, 2, 1, 3].length) (baseStart_3978294 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3978294 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3978294 prefixEnd_3978294 := by exact prefixLift 3978294
  have htrace : WordTrace (prefixWord ++ tailWord_3978294) baseStart_3978294 baseEnd_3978294 := by
    simpa [prefixWord, tailWord_3978294, baseEnd_3978294] using wordTrace_append hprefix tailTrace_3978294
  have hstable : (prefixWord ++ tailWord_3978294).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3978294).length < 2 ^ (prefixWord ++ tailWord_3978294).sum := by decide
  have hdescent : baseEnd_3978294 < baseStart_3978294 := by decide
  rcases family_descends (prefixWord ++ tailWord_3978294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3978299 : List Nat := [1, 1, 1, 1, 1, 2, 1, 3, 2, 9]
def baseStart_3978299 : Nat := 118140960795 + 3978299 * 2 ^ 59
def prefixEnd_3978299 : Nat := 4983230072969 + 3 ^ 40 * 3978299 * 2
def baseEnd_3978299 : Nat := 1361853049534157080377761

theorem tailTrace_3978299 : CollatzResearch.WordTrace tailWord_3978299 prefixEnd_3978299 1361853049534157080377761 := by
  unfold tailWord_3978299
  simp only [CollatzResearch.WordTrace]
  refine ⟨145100485014309637221377951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96733656676206424814251967 145100485014309637221377951)
  ·
    refine ⟨217650727521464455832066927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145100485014309637221377951 217650727521464455832066927)
    ·
      refine ⟨326476091282196683748100391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217650727521464455832066927 326476091282196683748100391)
      ·
        refine ⟨489714136923295025622150587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 326476091282196683748100391 489714136923295025622150587)
        ·
          refine ⟨734571205384942538433225881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 489714136923295025622150587 734571205384942538433225881)
          ·
            refine ⟨550928404038706903824919411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 734571205384942538433225881 550928404038706903824919411)
            ·
              refine ⟨826392606058060355737379117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 550928404038706903824919411 826392606058060355737379117)
              ·
                refine ⟨309897227271772633401517169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 826392606058060355737379117 309897227271772633401517169)
                ·
                  refine ⟨232422920453829475051137877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 309897227271772633401517169 232422920453829475051137877)
                  ·
                    refine ⟨1361853049534157080377761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 232422920453829475051137877 1361853049534157080377761)
                    ·
                      rfl

theorem cell22_3978299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 2, 9].length) (baseStart_3978299 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3978299 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3978299 prefixEnd_3978299 := by exact prefixLift 3978299
  have htrace : WordTrace (prefixWord ++ tailWord_3978299) baseStart_3978299 baseEnd_3978299 := by
    simpa [prefixWord, tailWord_3978299, baseEnd_3978299] using wordTrace_append hprefix tailTrace_3978299
  have hstable : (prefixWord ++ tailWord_3978299).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3978299).length < 2 ^ (prefixWord ++ tailWord_3978299).sum := by decide
  have hdescent : baseEnd_3978299 < baseStart_3978299 := by decide
  rcases family_descends (prefixWord ++ tailWord_3978299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3978316 : List Nat := [2, 2, 1, 3, 1, 1, 1, 5, 1, 5]
def baseStart_3978316 : Nat := 118140960795 + 3978316 * 2 ^ 59
def prefixEnd_3978316 : Nat := 4983230072969 + 3 ^ 40 * 3978316 * 2
def baseEnd_3978316 : Nat := 1361858868981574702702709

theorem tailTrace_3978316 : CollatzResearch.WordTrace tailWord_3978316 prefixEnd_3978316 1361858868981574702702709 := by
  unfold tailWord_3978316
  simp only [CollatzResearch.WordTrace]
  refine ⟨72550552527624024562373401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96734070036832032749831201 72550552527624024562373401)
  ·
    refine ⟨54412914395718018421780051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72550552527624024562373401 54412914395718018421780051)
    ·
      refine ⟨81619371593577027632670077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54412914395718018421780051 81619371593577027632670077)
      ·
        refine ⟨30607264347591385362251279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81619371593577027632670077 30607264347591385362251279)
        ·
          refine ⟨45910896521387078043376919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30607264347591385362251279 45910896521387078043376919)
          ·
            refine ⟨68866344782080617065065379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45910896521387078043376919 68866344782080617065065379)
            ·
              refine ⟨103299517173120925597598069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68866344782080617065065379 103299517173120925597598069)
              ·
                refine ⟨9684329734980086774774819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 103299517173120925597598069 9684329734980086774774819)
                ·
                  refine ⟨14526494602470130162162229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9684329734980086774774819 14526494602470130162162229)
                  ·
                    refine ⟨1361858868981574702702709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14526494602470130162162229 1361858868981574702702709)
                    ·
                      rfl

theorem cell22_3978316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 5, 1, 5].length) (baseStart_3978316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3978316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3978316 prefixEnd_3978316 := by exact prefixLift 3978316
  have htrace : WordTrace (prefixWord ++ tailWord_3978316) baseStart_3978316 baseEnd_3978316 := by
    simpa [prefixWord, tailWord_3978316, baseEnd_3978316] using wordTrace_append hprefix tailTrace_3978316
  have hstable : (prefixWord ++ tailWord_3978316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3978316).length < 2 ^ (prefixWord ++ tailWord_3978316).sum := by decide
  have hdescent : baseEnd_3978316 < baseStart_3978316 := by decide
  rcases family_descends (prefixWord ++ tailWord_3978316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3978346 : List Nat := [3, 1, 3, 2, 2, 11]
def baseStart_3978346 : Nat := 118140960795 + 3978346 * 2 ^ 59
def prefixEnd_3978346 : Nat := 4983230072969 + 3 ^ 40 * 3978346 * 2
def baseEnd_3978346 : Nat := 16813199241909439808057

theorem tailTrace_3978346 : CollatzResearch.WordTrace tailWord_3978346 prefixEnd_3978346 16813199241909439808057 := by
  unfold tailWord_3978346
  simp only [CollatzResearch.WordTrace]
  refine ⟨36275549811284841062084723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96734799496759576165559261 36275549811284841062084723)
  ·
    refine ⟨54413324716927261593127085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36275549811284841062084723 54413324716927261593127085)
    ·
      refine ⟨20404996768847723097422657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54413324716927261593127085 20404996768847723097422657)
      ·
        refine ⟨15303747576635792323066993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20404996768847723097422657 15303747576635792323066993)
        ·
          refine ⟨11477810682476844242300245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15303747576635792323066993 11477810682476844242300245)
          ·
            refine ⟨16813199241909439808057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 11477810682476844242300245 16813199241909439808057)
            ·
              rfl

theorem cell22_3978346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 11].length) (baseStart_3978346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3978346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3978346 prefixEnd_3978346 := by exact prefixLift 3978346
  have htrace : WordTrace (prefixWord ++ tailWord_3978346) baseStart_3978346 baseEnd_3978346 := by
    simpa [prefixWord, tailWord_3978346, baseEnd_3978346] using wordTrace_append hprefix tailTrace_3978346
  have hstable : (prefixWord ++ tailWord_3978346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3978346).length < 2 ^ (prefixWord ++ tailWord_3978346).sum := by decide
  have hdescent : baseEnd_3978346 < baseStart_3978346 := by decide
  rcases family_descends (prefixWord ++ tailWord_3978346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3978350 : List Nat := [4, 1, 2, 2, 1, 2, 1, 4, 2, 3]
def baseStart_3978350 : Nat := 118140960795 + 3978350 * 2 ^ 59
def prefixEnd_3978350 : Nat := 4983230072969 + 3 ^ 40 * 3978350 * 2
def baseEnd_3978350 : Nat := 1361870507876409947352605

theorem tailTrace_3978350 : CollatzResearch.WordTrace tailWord_3978350 prefixEnd_3978350 1361870507876409947352605 := by
  unfold tailWord_3978350
  simp only [CollatzResearch.WordTrace]
  refine ⟨18137793142140609116435563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96734896758083248620989669 18137793142140609116435563)
  ·
    refine ⟨27206689713210913674653345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18137793142140609116435563 27206689713210913674653345)
    ·
      refine ⟨20405017284908185255990009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27206689713210913674653345 20405017284908185255990009)
      ·
        refine ⟨15303762963681138941992507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20405017284908185255990009 15303762963681138941992507)
        ·
          refine ⟨22955644445521708412988761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15303762963681138941992507 22955644445521708412988761)
          ·
            refine ⟨17216733334141281309741571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22955644445521708412988761 17216733334141281309741571)
            ·
              refine ⟨25825100001211921964612357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17216733334141281309741571 25825100001211921964612357)
              ·
                refine ⟨4842206250227235368364817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25825100001211921964612357 4842206250227235368364817)
                ·
                  refine ⟨3631654687670426526273613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4842206250227235368364817 3631654687670426526273613)
                  ·
                    refine ⟨1361870507876409947352605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3631654687670426526273613 1361870507876409947352605)
                    ·
                      rfl

theorem cell22_3978350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 4, 2, 3].length) (baseStart_3978350 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3978350 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3978350 prefixEnd_3978350 := by exact prefixLift 3978350
  have htrace : WordTrace (prefixWord ++ tailWord_3978350) baseStart_3978350 baseEnd_3978350 := by
    simpa [prefixWord, tailWord_3978350, baseEnd_3978350] using wordTrace_append hprefix tailTrace_3978350
  have hstable : (prefixWord ++ tailWord_3978350).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3978350).length < 2 ^ (prefixWord ++ tailWord_3978350).sum := by decide
  have hdescent : baseEnd_3978350 < baseStart_3978350 := by decide
  rcases family_descends (prefixWord ++ tailWord_3978350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3978425 : List Nat := [1, 2, 1, 4, 1, 4, 3, 1, 5]
def baseStart_3978425 : Nat := 118140960795 + 3978425 * 2 ^ 59
def prefixEnd_3978425 : Nat := 4983230072969 + 3 ^ 40 * 3978425 * 2
def baseEnd_3978425 : Nat := 453965393969711583909125

theorem tailTrace_3978425 : CollatzResearch.WordTrace tailWord_3978425 prefixEnd_3978425 453965393969711583909125 := by
  unfold tailWord_3978425
  simp only [CollatzResearch.WordTrace]
  refine ⟨145105080611853160740464729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96736720407902107160309819 145105080611853160740464729)
  ·
    refine ⟨108828810458889870555348547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145105080611853160740464729 108828810458889870555348547)
    ·
      refine ⟨163243215688334805833022821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108828810458889870555348547 163243215688334805833022821)
      ·
        refine ⟨30608102941562776093691779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 163243215688334805833022821 30608102941562776093691779)
        ·
          refine ⟨45912154412344164140537669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30608102941562776093691779 45912154412344164140537669)
          ·
            refine ⟨8608528952314530776350813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45912154412344164140537669 8608528952314530776350813)
            ·
              refine ⟨3228198357117949041131555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8608528952314530776350813 3228198357117949041131555)
              ·
                refine ⟨4842297535676923561697333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3228198357117949041131555 4842297535676923561697333)
                ·
                  refine ⟨453965393969711583909125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4842297535676923561697333 453965393969711583909125)
                  ·
                    rfl

theorem cell22_3978425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 3, 1, 5].length) (baseStart_3978425 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3978425 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3978425 prefixEnd_3978425 := by exact prefixLift 3978425
  have htrace : WordTrace (prefixWord ++ tailWord_3978425) baseStart_3978425 baseEnd_3978425 := by
    simpa [prefixWord, tailWord_3978425, baseEnd_3978425] using wordTrace_append hprefix tailTrace_3978425
  have hstable : (prefixWord ++ tailWord_3978425).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3978425).length < 2 ^ (prefixWord ++ tailWord_3978425).sum := by decide
  have hdescent : baseEnd_3978425 < baseStart_3978425 := by decide
  rcases family_descends (prefixWord ++ tailWord_3978425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3978446 : List Nat := [4, 1, 1, 1, 6, 1, 1, 3, 1, 3]
def baseStart_3978446 : Nat := 118140960795 + 3978446 * 2 ^ 59
def prefixEnd_3978446 : Nat := 4983230072969 + 3 ^ 40 * 3978446 * 2
def baseEnd_3978446 : Nat := 1361903370638297696952311

theorem tailTrace_3978446 : CollatzResearch.WordTrace tailWord_3978446 prefixEnd_3978446 1361903370638297696952311 := by
  unfold tailWord_3978446
  simp only [CollatzResearch.WordTrace]
  refine ⟨18138230818097135165872399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96737231029851387551319461 18138230818097135165872399)
  ·
    refine ⟨27207346227145702748808599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18138230818097135165872399 27207346227145702748808599)
    ·
      refine ⟨40811019340718554123212899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27207346227145702748808599 40811019340718554123212899)
      ·
        refine ⟨61216529011077831184819349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40811019340718554123212899 61216529011077831184819349)
        ·
          refine ⟨2869524797394273336788407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 61216529011077831184819349 2869524797394273336788407)
          ·
            refine ⟨4304287196091410005182611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2869524797394273336788407 4304287196091410005182611)
            ·
              refine ⟨6456430794137115007773917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4304287196091410005182611 6456430794137115007773917)
              ·
                refine ⟨2421161547801418127915219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6456430794137115007773917 2421161547801418127915219)
                ·
                  refine ⟨3631742321702127191872829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2421161547801418127915219 3631742321702127191872829)
                  ·
                    refine ⟨1361903370638297696952311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3631742321702127191872829 1361903370638297696952311)
                    ·
                      rfl

theorem cell22_3978446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 1, 3, 1, 3].length) (baseStart_3978446 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3978446 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3978446 prefixEnd_3978446 := by exact prefixLift 3978446
  have htrace : WordTrace (prefixWord ++ tailWord_3978446) baseStart_3978446 baseEnd_3978446 := by
    simpa [prefixWord, tailWord_3978446, baseEnd_3978446] using wordTrace_append hprefix tailTrace_3978446
  have hstable : (prefixWord ++ tailWord_3978446).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3978446).length < 2 ^ (prefixWord ++ tailWord_3978446).sum := by decide
  have hdescent : baseEnd_3978446 < baseStart_3978446 := by decide
  rcases family_descends (prefixWord ++ tailWord_3978446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3978500 : List Nat := [2, 3, 2, 2, 2, 1, 1, 3, 2, 4]
def baseStart_3978500 : Nat := 118140960795 + 3978500 * 2 ^ 59
def prefixEnd_3978500 : Nat := 4983230072969 + 3 ^ 40 * 3978500 * 2
def baseEnd_3978500 : Nat := 1361921855941859556102145

theorem tailTrace_3978500 : CollatzResearch.WordTrace tailWord_3978500 prefixEnd_3978500 1361921855941859556102145 := by
  unfold tailWord_3978500
  simp only [CollatzResearch.WordTrace]
  refine ⟨72553908043290724274722477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96738544057720965699629969 72553908043290724274722477)
  ·
    refine ⟨27207715516234021603020929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72553908043290724274722477 27207715516234021603020929)
    ·
      refine ⟨20405786637175516202265697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27207715516234021603020929 20405786637175516202265697)
      ·
        refine ⟨15304339977881637151699273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20405786637175516202265697 15304339977881637151699273)
        ·
          refine ⟨11478254983411227863774455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15304339977881637151699273 11478254983411227863774455)
          ·
            refine ⟨17217382475116841795661683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11478254983411227863774455 17217382475116841795661683)
            ·
              refine ⟨25826073712675262693492525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17217382475116841795661683 25826073712675262693492525)
              ·
                refine ⟨9684777642253223510059697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25826073712675262693492525 9684777642253223510059697)
                ·
                  refine ⟨7263583231689917632544773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9684777642253223510059697 7263583231689917632544773)
                  ·
                    refine ⟨1361921855941859556102145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7263583231689917632544773 1361921855941859556102145)
                    ·
                      rfl

theorem cell22_3978500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 3, 2, 4].length) (baseStart_3978500 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3978500 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3978500 prefixEnd_3978500 := by exact prefixLift 3978500
  have htrace : WordTrace (prefixWord ++ tailWord_3978500) baseStart_3978500 baseEnd_3978500 := by
    simpa [prefixWord, tailWord_3978500, baseEnd_3978500] using wordTrace_append hprefix tailTrace_3978500
  have hstable : (prefixWord ++ tailWord_3978500).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3978500).length < 2 ^ (prefixWord ++ tailWord_3978500).sum := by decide
  have hdescent : baseEnd_3978500 < baseStart_3978500 := by decide
  rcases family_descends (prefixWord ++ tailWord_3978500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3978605 : List Nat := [1, 5, 1, 1, 1, 3, 2, 2, 6]
def baseStart_3978605 : Nat := 118140960795 + 3978605 * 2 ^ 59
def prefixEnd_3978605 : Nat := 4983230072969 + 3 ^ 40 * 3978605 * 2
def baseEnd_3978605 : Nat := 453985933195891427408941

theorem tailTrace_3978605 : CollatzResearch.WordTrace tailWord_3978605 prefixEnd_3978605 453985933195891427408941 := by
  unfold tailWord_3978605
  simp only [CollatzResearch.WordTrace]
  refine ⟨145111645751201051482017269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96741097167467367654678179 145111645751201051482017269)
  ·
    refine ⟨13604216789175098576439119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 145111645751201051482017269 13604216789175098576439119)
    ·
      refine ⟨20406325183762647864658679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13604216789175098576439119 20406325183762647864658679)
      ·
        refine ⟨30609487775643971796988019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20406325183762647864658679 30609487775643971796988019)
        ·
          refine ⟨45914231663465957695482029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30609487775643971796988019 45914231663465957695482029)
          ·
            refine ⟨17217836873799734135805761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45914231663465957695482029 17217836873799734135805761)
            ·
              refine ⟨12913377655349800601854321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17217836873799734135805761 12913377655349800601854321)
              ·
                refine ⟨9685033241512350451390741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12913377655349800601854321 9685033241512350451390741)
                ·
                  refine ⟨453985933195891427408941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9685033241512350451390741 453985933195891427408941)
                  ·
                    rfl

theorem cell22_3978605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 2, 6].length) (baseStart_3978605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3978605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3978605 prefixEnd_3978605 := by exact prefixLift 3978605
  have htrace : WordTrace (prefixWord ++ tailWord_3978605) baseStart_3978605 baseEnd_3978605 := by
    simpa [prefixWord, tailWord_3978605, baseEnd_3978605] using wordTrace_append hprefix tailTrace_3978605
  have hstable : (prefixWord ++ tailWord_3978605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3978605).length < 2 ^ (prefixWord ++ tailWord_3978605).sum := by decide
  have hdescent : baseEnd_3978605 < baseStart_3978605 := by decide
  rcases family_descends (prefixWord ++ tailWord_3978605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3978620 : List Nat := [2, 2, 2, 1, 1, 1, 3, 1, 6, 3]
def baseStart_3978620 : Nat := 118140960795 + 3978620 * 2 ^ 59
def prefixEnd_3978620 : Nat := 4983230072969 + 3 ^ 40 * 3978620 * 2
def baseEnd_3978620 : Nat := 1361962934394219243101777

theorem tailTrace_3978620 : CollatzResearch.WordTrace tailWord_3978620 prefixEnd_3978620 1361962934394219243101777 := by
  unfold tailWord_3978620
  simp only [CollatzResearch.WordTrace]
  refine ⟨72556096423073354521906657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96741461897431139362542209 72556096423073354521906657)
  ·
    refine ⟨54417072317305015891429993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72556096423073354521906657 54417072317305015891429993)
    ·
      refine ⟨40812804237978761918572495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54417072317305015891429993 40812804237978761918572495)
      ·
        refine ⟨61219206356968142877858743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40812804237978761918572495 61219206356968142877858743)
        ·
          refine ⟨91828809535452214316788115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61219206356968142877858743 91828809535452214316788115)
          ·
            refine ⟨137743214303178321475182173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91828809535452214316788115 137743214303178321475182173)
            ·
              refine ⟨51653705363691870553193315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 137743214303178321475182173 51653705363691870553193315)
              ·
                refine ⟨77480558045537805829789973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51653705363691870553193315 77480558045537805829789973)
                ·
                  refine ⟨3631901158384584648271405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 77480558045537805829789973 3631901158384584648271405)
                  ·
                    refine ⟨1361962934394219243101777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3631901158384584648271405 1361962934394219243101777)
                    ·
                      rfl

theorem cell22_3978620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 1, 6, 3].length) (baseStart_3978620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3978620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3978620 prefixEnd_3978620 := by exact prefixLift 3978620
  have htrace : WordTrace (prefixWord ++ tailWord_3978620) baseStart_3978620 baseEnd_3978620 := by
    simpa [prefixWord, tailWord_3978620, baseEnd_3978620] using wordTrace_append hprefix tailTrace_3978620
  have hstable : (prefixWord ++ tailWord_3978620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3978620).length < 2 ^ (prefixWord ++ tailWord_3978620).sum := by decide
  have hdescent : baseEnd_3978620 < baseStart_3978620 := by decide
  rcases family_descends (prefixWord ++ tailWord_3978620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3978635 : List Nat := [1, 1, 1, 1, 4, 3, 3, 2, 2, 4]
def baseStart_3978635 : Nat := 118140960795 + 3978635 * 2 ^ 59
def prefixEnd_3978635 : Nat := 4983230072969 + 3 ^ 40 * 3978635 * 2
def baseEnd_3978635 : Nat := 1361968069200764203976731

theorem tailTrace_3978635 : CollatzResearch.WordTrace tailWord_3978635 prefixEnd_3978635 1361968069200764203976731 := by
  unfold tailWord_3978635
  simp only [CollatzResearch.WordTrace]
  refine ⟨145112739941092366605609359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96741826627394911070406239 145112739941092366605609359)
  ·
    refine ⟨217669109911638549908414039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145112739941092366605609359 217669109911638549908414039)
    ·
      refine ⟨326503664867457824862621059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217669109911638549908414039 326503664867457824862621059)
      ·
        refine ⟨489755497301186737293931589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 326503664867457824862621059 489755497301186737293931589)
        ·
          refine ⟨91829155743972513242612173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 489755497301186737293931589 91829155743972513242612173)
          ·
            refine ⟨34435933403989692465979565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91829155743972513242612173 34435933403989692465979565)
            ·
              refine ⟨12913475026496134674742337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34435933403989692465979565 12913475026496134674742337)
              ·
                refine ⟨9685106269872101006056753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12913475026496134674742337 9685106269872101006056753)
                ·
                  refine ⟨7263829702404075754542565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9685106269872101006056753 7263829702404075754542565)
                  ·
                    refine ⟨1361968069200764203976731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7263829702404075754542565 1361968069200764203976731)
                    ·
                      rfl

theorem cell22_3978635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 2, 2, 4].length) (baseStart_3978635 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3978635 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3978635 prefixEnd_3978635 := by exact prefixLift 3978635
  have htrace : WordTrace (prefixWord ++ tailWord_3978635) baseStart_3978635 baseEnd_3978635 := by
    simpa [prefixWord, tailWord_3978635, baseEnd_3978635] using wordTrace_append hprefix tailTrace_3978635
  have hstable : (prefixWord ++ tailWord_3978635).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3978635).length < 2 ^ (prefixWord ++ tailWord_3978635).sum := by decide
  have hdescent : baseEnd_3978635 < baseStart_3978635 := by decide
  rcases family_descends (prefixWord ++ tailWord_3978635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3978650 : List Nat := [3, 1, 1, 4, 1, 1, 4, 7]
def baseStart_3978650 : Nat := 118140960795 + 3978650 * 2 ^ 59
def prefixEnd_3978650 : Nat := 4983230072969 + 3 ^ 40 * 3978650 * 2
def baseEnd_3978650 : Nat := 151330356000812129427965

theorem tailTrace_3978650 : CollatzResearch.WordTrace tailWord_3978650 prefixEnd_3978650 151330356000812129427965 := by
  unfold tailWord_3978650
  simp only [CollatzResearch.WordTrace]
  refine ⟨36278321759009506041851351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96742191357358682778270269 36278321759009506041851351)
  ·
    refine ⟨54417482638514259062777027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36278321759009506041851351 54417482638514259062777027)
    ·
      refine ⟨81626223957771388594165541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54417482638514259062777027 81626223957771388594165541)
      ·
        refine ⟨15304916992082135361406039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81626223957771388594165541 15304916992082135361406039)
        ·
          refine ⟨22957375488123203042109059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15304916992082135361406039 22957375488123203042109059)
          ·
            refine ⟨34436063232184804563163589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22957375488123203042109059 34436063232184804563163589)
            ·
              refine ⟨6456761856034650855593173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34436063232184804563163589 6456761856034650855593173)
              ·
                refine ⟨151330356000812129427965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6456761856034650855593173 151330356000812129427965)
                ·
                  rfl

theorem cell22_3978650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 4, 7].length) (baseStart_3978650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3978650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3978650 prefixEnd_3978650 := by exact prefixLift 3978650
  have htrace : WordTrace (prefixWord ++ tailWord_3978650) baseStart_3978650 baseEnd_3978650 := by
    simpa [prefixWord, tailWord_3978650, baseEnd_3978650] using wordTrace_append hprefix tailTrace_3978650
  have hstable : (prefixWord ++ tailWord_3978650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3978650).length < 2 ^ (prefixWord ++ tailWord_3978650).sum := by decide
  have hdescent : baseEnd_3978650 < baseStart_3978650 := by decide
  rcases family_descends (prefixWord ++ tailWord_3978650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3978669 : List Nat := [1, 5, 2, 2, 1, 2, 2, 1, 2, 4]
def baseStart_3978669 : Nat := 118140960795 + 3978669 * 2 ^ 59
def prefixEnd_3978669 : Nat := 4983230072969 + 3 ^ 40 * 3978669 * 2
def baseEnd_3978669 : Nat := 1361979708095599448626627

theorem tailTrace_3978669 : CollatzResearch.WordTrace tailWord_3978669 prefixEnd_3978669 1361979708095599448626627 := by
  unfold tailWord_3978669
  simp only [CollatzResearch.WordTrace]
  refine ⟨145113980022969190412347061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96742653348646126941564707 145113980022969190412347061)
  ·
    refine ⟨13604435627153361601157537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 145113980022969190412347061 13604435627153361601157537)
    ·
      refine ⟨10203326720365021200868153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13604435627153361601157537 10203326720365021200868153)
      ·
        refine ⟨7652495040273765900651115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10203326720365021200868153 7652495040273765900651115)
        ·
          refine ⟨11478742560410648850976673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7652495040273765900651115 11478742560410648850976673)
          ·
            refine ⟨8609056920307986638232505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11478742560410648850976673 8609056920307986638232505)
            ·
              refine ⟨6456792690230989978674379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8609056920307986638232505 6456792690230989978674379)
              ·
                refine ⟨9685189035346484968011569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6456792690230989978674379 9685189035346484968011569)
                ·
                  refine ⟨7263891776509863726008677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9685189035346484968011569 7263891776509863726008677)
                  ·
                    refine ⟨1361979708095599448626627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7263891776509863726008677 1361979708095599448626627)
                    ·
                      rfl

theorem cell22_3978669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 2, 1, 2, 4].length) (baseStart_3978669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3978669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3978669 prefixEnd_3978669 := by exact prefixLift 3978669
  have htrace : WordTrace (prefixWord ++ tailWord_3978669) baseStart_3978669 baseEnd_3978669 := by
    simpa [prefixWord, tailWord_3978669, baseEnd_3978669] using wordTrace_append hprefix tailTrace_3978669
  have hstable : (prefixWord ++ tailWord_3978669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3978669).length < 2 ^ (prefixWord ++ tailWord_3978669).sum := by decide
  have hdescent : baseEnd_3978669 < baseStart_3978669 := by decide
  rcases family_descends (prefixWord ++ tailWord_3978669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3978690 : List Nat := [3, 5, 2, 1, 1, 1, 1, 4, 4]
def baseStart_3978690 : Nat := 118140960795 + 3978690 * 2 ^ 59
def prefixEnd_3978690 : Nat := 4983230072969 + 3 ^ 40 * 3978690 * 2
def baseEnd_3978690 : Nat := 453995632274920797950521

theorem tailTrace_3978690 : CollatzResearch.WordTrace tailWord_3978690 prefixEnd_3978690 453995632274920797950521 := by
  unfold tailWord_3978690
  simp only [CollatzResearch.WordTrace]
  refine ⟨36278686488973277749715381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96743163970595407332574349 36278686488973277749715381)
  ·
    refine ⟨3401126858341244789035817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 36278686488973277749715381 3401126858341244789035817)
    ·
      refine ⟨2550845143755933591776863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3401126858341244789035817 2550845143755933591776863)
      ·
        refine ⟨3826267715633900387665295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2550845143755933591776863 3826267715633900387665295)
        ·
          refine ⟨5739401573450850581497943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3826267715633900387665295 5739401573450850581497943)
          ·
            refine ⟨8609102360176275872246915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5739401573450850581497943 8609102360176275872246915)
            ·
              refine ⟨12913653540264413808370373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8609102360176275872246915 12913653540264413808370373)
              ·
                refine ⟨2421310038799577589069445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12913653540264413808370373 2421310038799577589069445)
                ·
                  refine ⟨453995632274920797950521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2421310038799577589069445 453995632274920797950521)
                  ·
                    rfl

theorem cell22_3978690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 4, 4].length) (baseStart_3978690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3978690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3978690 prefixEnd_3978690 := by exact prefixLift 3978690
  have htrace : WordTrace (prefixWord ++ tailWord_3978690) baseStart_3978690 baseEnd_3978690 := by
    simpa [prefixWord, tailWord_3978690, baseEnd_3978690] using wordTrace_append hprefix tailTrace_3978690
  have hstable : (prefixWord ++ tailWord_3978690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3978690).length < 2 ^ (prefixWord ++ tailWord_3978690).sum := by decide
  have hdescent : baseEnd_3978690 < baseStart_3978690 := by decide
  rcases family_descends (prefixWord ++ tailWord_3978690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3978733 : List Nat := [1, 5, 1, 3, 2, 1, 2, 3, 1, 3]
def baseStart_3978733 : Nat := 118140960795 + 3978733 * 2 ^ 59
def prefixEnd_3978733 : Nat := 4983230072969 + 3 ^ 40 * 3978733 * 2
def baseEnd_3978733 : Nat := 1362001616603524615026431

theorem tailTrace_3978733 : CollatzResearch.WordTrace tailWord_3978733 prefixEnd_3978733 1362001616603524615026431 := by
  unfold tailWord_3978733
  simp only [CollatzResearch.WordTrace]
  refine ⟨145116314294737329342676853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96744209529824886228451235 145116314294737329342676853)
  ·
    refine ⟨13604654465131624625875955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 145116314294737329342676853 13604654465131624625875955)
    ·
      refine ⟨20406981697697436938813933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13604654465131624625875955 20406981697697436938813933)
      ·
        refine ⟨7652618136636538852055225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20406981697697436938813933 7652618136636538852055225)
        ·
          refine ⟨5739463602477404139041419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7652618136636538852055225 5739463602477404139041419)
          ·
            refine ⟨8609195403716106208562129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5739463602477404139041419 8609195403716106208562129)
            ·
              refine ⟨6456896552787079656421597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8609195403716106208562129 6456896552787079656421597)
              ·
                refine ⟨2421336207295154871158099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6456896552787079656421597 2421336207295154871158099)
                ·
                  refine ⟨3632004310942732306737149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2421336207295154871158099 3632004310942732306737149)
                  ·
                    refine ⟨1362001616603524615026431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3632004310942732306737149 1362001616603524615026431)
                    ·
                      rfl

theorem cell22_3978733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 2, 3, 1, 3].length) (baseStart_3978733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3978733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3978733 prefixEnd_3978733 := by exact prefixLift 3978733
  have htrace : WordTrace (prefixWord ++ tailWord_3978733) baseStart_3978733 baseEnd_3978733 := by
    simpa [prefixWord, tailWord_3978733, baseEnd_3978733] using wordTrace_append hprefix tailTrace_3978733
  have hstable : (prefixWord ++ tailWord_3978733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3978733).length < 2 ^ (prefixWord ++ tailWord_3978733).sum := by decide
  have hdescent : baseEnd_3978733 < baseStart_3978733 := by decide
  rcases family_descends (prefixWord ++ tailWord_3978733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3978823 : List Nat := [1, 1, 4, 1, 5, 2, 2, 1, 2, 3]
def baseStart_3978823 : Nat := 118140960795 + 3978823 * 2 ^ 59
def prefixEnd_3978823 : Nat := 4983230072969 + 3 ^ 40 * 3978823 * 2
def baseEnd_3978823 : Nat := 1362032425442794380276155

theorem tailTrace_3978823 : CollatzResearch.WordTrace tailWord_3978823 prefixEnd_3978823 1362032425442794380276155 := by
  unfold tailWord_3978823
  simp only [CollatzResearch.WordTrace]
  refine ⟨145119596864411274713453123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96746397909607516475635415 145119596864411274713453123)
  ·
    refine ⟨217679395296616912070179685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145119596864411274713453123 217679395296616912070179685)
    ·
      refine ⟨40814886618115671013158691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 217679395296616912070179685 40814886618115671013158691)
      ·
        refine ⟨61222329927173506519738037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40814886618115671013158691 61222329927173506519738037)
        ·
          refine ⟨5739593430672516236225441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 61222329927173506519738037 5739593430672516236225441)
          ·
            refine ⟨4304695073004387177169081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5739593430672516236225441 4304695073004387177169081)
            ·
              refine ⟨3228521304753290382876811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4304695073004387177169081 3228521304753290382876811)
              ·
                refine ⟨4842781957129935574315217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3228521304753290382876811 4842781957129935574315217)
                ·
                  refine ⟨3632086467847451680736413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4842781957129935574315217 3632086467847451680736413)
                  ·
                    refine ⟨1362032425442794380276155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3632086467847451680736413 1362032425442794380276155)
                    ·
                      rfl

theorem cell22_3978823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 2, 1, 2, 3].length) (baseStart_3978823 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3978823 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3978823 prefixEnd_3978823 := by exact prefixLift 3978823
  have htrace : WordTrace (prefixWord ++ tailWord_3978823) baseStart_3978823 baseEnd_3978823 := by
    simpa [prefixWord, tailWord_3978823, baseEnd_3978823] using wordTrace_append hprefix tailTrace_3978823
  have hstable : (prefixWord ++ tailWord_3978823).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3978823).length < 2 ^ (prefixWord ++ tailWord_3978823).sum := by decide
  have hdescent : baseEnd_3978823 < baseStart_3978823 := by decide
  rcases family_descends (prefixWord ++ tailWord_3978823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3978864 : List Nat := [2, 1, 1, 1, 6, 2, 2, 2, 5]
def baseStart_3978864 : Nat := 118140960795 + 3978864 * 2 ^ 59
def prefixEnd_3978864 : Nat := 4983230072969 + 3 ^ 40 * 3978864 * 2
def baseEnd_3978864 : Nat := 454015486860227980000343

theorem tailTrace_3978864 : CollatzResearch.WordTrace tailWord_3978864 prefixEnd_3978864 454015486860227980000343 := by
  unfold tailWord_3978864
  simp only [CollatzResearch.WordTrace]
  refine ⟨72560546128631369357847823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96747394838175159143797097 72560546128631369357847823)
  ·
    refine ⟨108840819192947054036771735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72560546128631369357847823 108840819192947054036771735)
    ·
      refine ⟨163261228789420581055157603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108840819192947054036771735 163261228789420581055157603)
      ·
        refine ⟨244891843184130871582736405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163261228789420581055157603 244891843184130871582736405)
        ·
          refine ⟨11479305149256134605440769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 244891843184130871582736405 11479305149256134605440769)
          ·
            refine ⟨8609478861942100954080577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11479305149256134605440769 8609478861942100954080577)
            ·
              refine ⟨6457109146456575715560433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8609478861942100954080577 6457109146456575715560433)
              ·
                refine ⟨4842831859842431786670325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6457109146456575715560433 4842831859842431786670325)
                ·
                  refine ⟨454015486860227980000343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4842831859842431786670325 454015486860227980000343)
                  ·
                    rfl

theorem cell22_3978864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 2, 2, 5].length) (baseStart_3978864 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3978864 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3978864 prefixEnd_3978864 := by exact prefixLift 3978864
  have htrace : WordTrace (prefixWord ++ tailWord_3978864) baseStart_3978864 baseEnd_3978864 := by
    simpa [prefixWord, tailWord_3978864, baseEnd_3978864] using wordTrace_append hprefix tailTrace_3978864
  have hstable : (prefixWord ++ tailWord_3978864).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3978864).length < 2 ^ (prefixWord ++ tailWord_3978864).sum := by decide
  have hdescent : baseEnd_3978864 < baseStart_3978864 := by decide
  rcases family_descends (prefixWord ++ tailWord_3978864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3978892 : List Nat := [2, 2, 1, 2, 1, 1, 5, 2, 6]
def baseStart_3978892 : Nat := 118140960795 + 3978892 * 2 ^ 59
def prefixEnd_3978892 : Nat := 4983230072969 + 3 ^ 40 * 3978892 * 2
def baseEnd_3978892 : Nat := 454018681850967066766981

theorem tailTrace_3978892 : CollatzResearch.WordTrace tailWord_3978892 prefixEnd_3978892 454018681850967066766981 := by
  unfold tailWord_3978892
  simp only [CollatzResearch.WordTrace]
  refine ⟨72561056750580649748857465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96748075667440866331809953 72561056750580649748857465)
  ·
    refine ⟨54420792562935487311643099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72561056750580649748857465 54420792562935487311643099)
    ·
      refine ⟨81631188844403230967464649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54420792562935487311643099 81631188844403230967464649)
      ·
        refine ⟨61223391633302423225598487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81631188844403230967464649 61223391633302423225598487)
        ·
          refine ⟨91835087449953634838397731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61223391633302423225598487 91835087449953634838397731)
          ·
            refine ⟨137752631174930452257596597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91835087449953634838397731 137752631174930452257596597)
            ·
              refine ⟨12914309172649729899149681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 137752631174930452257596597 12914309172649729899149681)
              ·
                refine ⟨9685731879487297424362261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12914309172649729899149681 9685731879487297424362261)
                ·
                  refine ⟨454018681850967066766981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9685731879487297424362261 454018681850967066766981)
                  ·
                    rfl

theorem cell22_3978892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 2, 6].length) (baseStart_3978892 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3978892 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3978892 prefixEnd_3978892 := by exact prefixLift 3978892
  have htrace : WordTrace (prefixWord ++ tailWord_3978892) baseStart_3978892 baseEnd_3978892 := by
    simpa [prefixWord, tailWord_3978892, baseEnd_3978892] using wordTrace_append hprefix tailTrace_3978892
  have hstable : (prefixWord ++ tailWord_3978892).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3978892).length < 2 ^ (prefixWord ++ tailWord_3978892).sum := by decide
  have hdescent : baseEnd_3978892 < baseStart_3978892 := by decide
  rcases family_descends (prefixWord ++ tailWord_3978892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3978894 : List Nat := [4, 1, 1, 3, 1, 2, 2, 1, 3, 4]
def baseStart_3978894 : Nat := 118140960795 + 3978894 * 2 ^ 59
def prefixEnd_3978894 : Nat := 4983230072969 + 3 ^ 40 * 3978894 * 2
def baseEnd_3978894 : Nat := 1362056730193773861750937

theorem tailTrace_3978894 : CollatzResearch.WordTrace tailWord_3978894 prefixEnd_3978894 1362056730193773861750937 := by
  unfold tailWord_3978894
  simp only [CollatzResearch.WordTrace]
  refine ⟨18140273305894256729910967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96748124298102702559525157 18140273305894256729910967)
  ·
    refine ⟨27210409958841385094866451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18140273305894256729910967 27210409958841385094866451)
    ·
      refine ⟨40815614938262077642299677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27210409958841385094866451 40815614938262077642299677)
      ·
        refine ⟨15305855601848279115862379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40815614938262077642299677 15305855601848279115862379)
        ·
          refine ⟨22958783402772418673793569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15305855601848279115862379 22958783402772418673793569)
          ·
            refine ⟨17219087552079314005345177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22958783402772418673793569 17219087552079314005345177)
            ·
              refine ⟨12914315664059485504008883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17219087552079314005345177 12914315664059485504008883)
              ·
                refine ⟨19371473496089228256013325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12914315664059485504008883 19371473496089228256013325)
                ·
                  refine ⟨7264302561033460596004997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19371473496089228256013325 7264302561033460596004997)
                  ·
                    refine ⟨1362056730193773861750937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7264302561033460596004997 1362056730193773861750937)
                    ·
                      rfl

theorem cell22_3978894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 1, 3, 4].length) (baseStart_3978894 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3978894 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3978894 prefixEnd_3978894 := by exact prefixLift 3978894
  have htrace : WordTrace (prefixWord ++ tailWord_3978894) baseStart_3978894 baseEnd_3978894 := by
    simpa [prefixWord, tailWord_3978894, baseEnd_3978894] using wordTrace_append hprefix tailTrace_3978894
  have hstable : (prefixWord ++ tailWord_3978894).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3978894).length < 2 ^ (prefixWord ++ tailWord_3978894).sum := by decide
  have hdescent : baseEnd_3978894 < baseStart_3978894 := by decide
  rcases family_descends (prefixWord ++ tailWord_3978894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3978952 : List Nat := [2, 1, 3, 1, 2, 2, 1, 1, 2, 7]
def baseStart_3978952 : Nat := 118140960795 + 3978952 * 2 ^ 59
def prefixEnd_3978952 : Nat := 4983230072969 + 3 ^ 40 * 3978952 * 2
def baseEnd_3978952 : Nat := 1362076584779081043800759

theorem tailTrace_3978952 : CollatzResearch.WordTrace tailWord_3978952 prefixEnd_3978952 1362076584779081043800759 := by
  unfold tailWord_3978952
  simp only [CollatzResearch.WordTrace]
  refine ⟨72562150940471964872449555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96749534587295953163266073 72562150940471964872449555)
  ·
    refine ⟨108843226410707947308674333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72562150940471964872449555 108843226410707947308674333)
    ·
      refine ⟨40816209904015480240752875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108843226410707947308674333 40816209904015480240752875)
      ·
        refine ⟨61224314856023220361129313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40816209904015480240752875 61224314856023220361129313)
        ·
          refine ⟨45918236142017415270846985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61224314856023220361129313 45918236142017415270846985)
          ·
            refine ⟨34438677106513061453135239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45918236142017415270846985 34438677106513061453135239)
            ·
              refine ⟨51658015659769592179702859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34438677106513061453135239 51658015659769592179702859)
              ·
                refine ⟨77487023489654388269554289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51658015659769592179702859 77487023489654388269554289)
                ·
                  refine ⟨58115267617240791202165717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77487023489654388269554289 58115267617240791202165717)
                  ·
                    refine ⟨1362076584779081043800759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58115267617240791202165717 1362076584779081043800759)
                    ·
                      rfl

theorem cell22_3978952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 1, 2, 7].length) (baseStart_3978952 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3978952 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3978952 prefixEnd_3978952 := by exact prefixLift 3978952
  have htrace : WordTrace (prefixWord ++ tailWord_3978952) baseStart_3978952 baseEnd_3978952 := by
    simpa [prefixWord, tailWord_3978952, baseEnd_3978952] using wordTrace_append hprefix tailTrace_3978952
  have hstable : (prefixWord ++ tailWord_3978952).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3978952).length < 2 ^ (prefixWord ++ tailWord_3978952).sum := by decide
  have hdescent : baseEnd_3978952 < baseStart_3978952 := by decide
  rcases family_descends (prefixWord ++ tailWord_3978952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3978954 : List Nat := [3, 1, 2, 1, 5, 1, 1, 8]
def baseStart_3978954 : Nat := 118140960795 + 3978954 * 2 ^ 59
def prefixEnd_3978954 : Nat := 4983230072969 + 3 ^ 40 * 3978954 * 2
def baseEnd_3978954 : Nat := 151341918824439300583417

theorem tailTrace_3978954 : CollatzResearch.WordTrace tailWord_3978954 prefixEnd_3978954 151341918824439300583417 := by
  unfold tailWord_3978954
  simp only [CollatzResearch.WordTrace]
  refine ⟨36281093706734171021617979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96749583217957789390981277 36281093706734171021617979)
  ·
    refine ⟨54421640560101256532426969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36281093706734171021617979 54421640560101256532426969)
    ·
      refine ⟨40816230420075942399320227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54421640560101256532426969 40816230420075942399320227)
      ·
        refine ⟨61224345630113913598980341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40816230420075942399320227 61224345630113913598980341)
        ·
          refine ⟨5739782402823179399904407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 61224345630113913598980341 5739782402823179399904407)
          ·
            refine ⟨8609673604234769099856611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5739782402823179399904407 8609673604234769099856611)
            ·
              refine ⟨12914510406352153649784917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8609673604234769099856611 12914510406352153649784917)
              ·
                refine ⟨151341918824439300583417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12914510406352153649784917 151341918824439300583417)
                ·
                  rfl

theorem cell22_3978954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 8].length) (baseStart_3978954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3978954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3978954 prefixEnd_3978954 := by exact prefixLift 3978954
  have htrace : WordTrace (prefixWord ++ tailWord_3978954) baseStart_3978954 baseEnd_3978954 := by
    simpa [prefixWord, tailWord_3978954, baseEnd_3978954] using wordTrace_append hprefix tailTrace_3978954
  have hstable : (prefixWord ++ tailWord_3978954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3978954).length < 2 ^ (prefixWord ++ tailWord_3978954).sum := by decide
  have hdescent : baseEnd_3978954 < baseStart_3978954 := by decide
  rcases family_descends (prefixWord ++ tailWord_3978954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3978973 : List Nat := [1, 4, 3, 3, 1, 1, 1, 2, 2, 4]
def baseStart_3978973 : Nat := 118140960795 + 3978973 * 2 ^ 59
def prefixEnd_3978973 : Nat := 4983230072969 + 3 ^ 40 * 3978973 * 2
def baseEnd_3978973 : Nat := 1362083773508243989025695

theorem tailTrace_3978973 : CollatzResearch.WordTrace tailWord_3978973 prefixEnd_3978973 1362083773508243989025695 := by
  unfold tailWord_3978973
  simp only [CollatzResearch.WordTrace]
  refine ⟨145125067813867850331413573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96750045209245233554275715 145125067813867850331413573)
  ·
    refine ⟨27210950215100221937140045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 145125067813867850331413573 27210950215100221937140045)
    ·
      refine ⟨10204106330662583226427517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27210950215100221937140045 10204106330662583226427517)
      ·
        refine ⟨3826539873998468709910319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10204106330662583226427517 3826539873998468709910319)
        ·
          refine ⟨5739809810997703064865479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3826539873998468709910319 5739809810997703064865479)
          ·
            refine ⟨8609714716496554597298219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5739809810997703064865479 8609714716496554597298219)
            ·
              refine ⟨12914572074744831895947329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8609714716496554597298219 12914572074744831895947329)
              ·
                refine ⟨9685929056058623921960497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12914572074744831895947329 9685929056058623921960497)
                ·
                  refine ⟨7264446792043967941470373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9685929056058623921960497 7264446792043967941470373)
                  ·
                    refine ⟨1362083773508243989025695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7264446792043967941470373 1362083773508243989025695)
                    ·
                      rfl

theorem cell22_3978973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 2, 2, 4].length) (baseStart_3978973 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3978973 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3978973 prefixEnd_3978973 := by exact prefixLift 3978973
  have htrace : WordTrace (prefixWord ++ tailWord_3978973) baseStart_3978973 baseEnd_3978973 := by
    simpa [prefixWord, tailWord_3978973, baseEnd_3978973] using wordTrace_append hprefix tailTrace_3978973
  have hstable : (prefixWord ++ tailWord_3978973).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3978973).length < 2 ^ (prefixWord ++ tailWord_3978973).sum := by decide
  have hdescent : baseEnd_3978973 < baseStart_3978973 := by decide
  rcases family_descends (prefixWord ++ tailWord_3978973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3978986 : List Nat := [3, 1, 3, 1, 1, 1, 5, 1, 3, 3]
def baseStart_3978986 : Nat := 118140960795 + 3978986 * 2 ^ 59
def prefixEnd_3978986 : Nat := 4983230072969 + 3 ^ 40 * 3978986 * 2
def baseEnd_3978986 : Nat := 1362088223673916288450655

theorem tailTrace_3978986 : CollatzResearch.WordTrace tailWord_3978986 prefixEnd_3978986 1362088223673916288450655 := by
  unfold tailWord_3978986
  simp only [CollatzResearch.WordTrace]
  refine ⟨36281385490705188387909203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96750361308547169034424541 36281385490705188387909203)
  ·
    refine ⟨54422078236057782581863805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36281385490705188387909203 54422078236057782581863805)
    ·
      refine ⟨20408279338521668468198927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54422078236057782581863805 20408279338521668468198927)
      ·
        refine ⟨30612419007782502702298391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20408279338521668468198927 30612419007782502702298391)
        ·
          refine ⟨45918628511673754053447587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30612419007782502702298391 45918628511673754053447587)
          ·
            refine ⟨68877942767510631080171381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45918628511673754053447587 68877942767510631080171381)
            ·
              refine ⟨6457307134454121663766067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 68877942767510631080171381 6457307134454121663766067)
              ·
                refine ⟨9685960701681182495649101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6457307134454121663766067 9685960701681182495649101)
                ·
                  refine ⟨3632235263130443435868413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9685960701681182495649101 3632235263130443435868413)
                  ·
                    refine ⟨1362088223673916288450655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3632235263130443435868413 1362088223673916288450655)
                    ·
                      rfl

theorem cell22_3978986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 5, 1, 3, 3].length) (baseStart_3978986 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3978986 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3978986 prefixEnd_3978986 := by exact prefixLift 3978986
  have htrace : WordTrace (prefixWord ++ tailWord_3978986) baseStart_3978986 baseEnd_3978986 := by
    simpa [prefixWord, tailWord_3978986, baseEnd_3978986] using wordTrace_append hprefix tailTrace_3978986
  have hstable : (prefixWord ++ tailWord_3978986).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3978986).length < 2 ^ (prefixWord ++ tailWord_3978986).sum := by decide
  have hdescent : baseEnd_3978986 < baseStart_3978986 := by decide
  rcases family_descends (prefixWord ++ tailWord_3978986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3979027 : List Nat := [1, 1, 1, 2, 1, 3, 2, 1, 10]
def baseStart_3979027 : Nat := 118140960795 + 3979027 * 2 ^ 59
def prefixEnd_3979027 : Nat := 4983230072969 + 3 ^ 40 * 3979027 * 2
def baseEnd_3979027 : Nat := 454034086270601949391843

theorem tailTrace_3979027 : CollatzResearch.WordTrace tailWord_3979027 prefixEnd_3979027 454034086270601949391843 := by
  unfold tailWord_3979027
  simp only [CollatzResearch.WordTrace]
  refine ⟨145127037355672217553879335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96751358237114811702586223 145127037355672217553879335)
  ·
    refine ⟨217690556033508326330819003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145127037355672217553879335 217690556033508326330819003)
    ·
      refine ⟨326535834050262489496228505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217690556033508326330819003 326535834050262489496228505)
      ·
        refine ⟨244901875537696867122171379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 326535834050262489496228505 244901875537696867122171379)
        ·
          refine ⟨367352813306545300683257069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244901875537696867122171379 367352813306545300683257069)
          ·
            refine ⟨137757304989954487756221401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 367352813306545300683257069 137757304989954487756221401)
            ·
              refine ⟨103317978742465865817166051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137757304989954487756221401 103317978742465865817166051)
              ·
                refine ⟨154976968113698798725749077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103317978742465865817166051 154976968113698798725749077)
                ·
                  refine ⟨454034086270601949391843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 154976968113698798725749077 454034086270601949391843)
                  ·
                    rfl

theorem cell22_3979027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 1, 10].length) (baseStart_3979027 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3979027 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3979027 prefixEnd_3979027 := by exact prefixLift 3979027
  have htrace : WordTrace (prefixWord ++ tailWord_3979027) baseStart_3979027 baseEnd_3979027 := by
    simpa [prefixWord, tailWord_3979027, baseEnd_3979027] using wordTrace_append hprefix tailTrace_3979027
  have hstable : (prefixWord ++ tailWord_3979027).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3979027).length < 2 ^ (prefixWord ++ tailWord_3979027).sum := by decide
  have hdescent : baseEnd_3979027 < baseStart_3979027 := by decide
  rcases family_descends (prefixWord ++ tailWord_3979027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3979061 : List Nat := [1, 3, 3, 1, 4, 1, 1, 2, 6]
def baseStart_3979061 : Nat := 118140960795 + 3979061 * 2 ^ 59
def prefixEnd_3979061 : Nat := 4983230072969 + 3 ^ 40 * 3979061 * 2
def baseEnd_3979061 : Nat := 454037965902213697608475

theorem tailTrace_3979061 : CollatzResearch.WordTrace tailWord_3979061 prefixEnd_3979061 454037965902213697608475 := by
  unfold tailWord_3979061
  simp only [CollatzResearch.WordTrace]
  refine ⟨145128277437549041360617037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96752184958366027573744691 145128277437549041360617037)
  ·
    refine ⟨54423104039080890510231389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145128277437549041360617037 54423104039080890510231389)
    ·
      refine ⟨20408664014655333941336771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54423104039080890510231389 20408664014655333941336771)
      ·
        refine ⟨30612996021983000912005157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20408664014655333941336771 30612996021983000912005157)
        ·
          refine ⟨5739936754121812671000967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30612996021983000912005157 5739936754121812671000967)
          ·
            refine ⟨8609905131182719006501451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5739936754121812671000967 8609905131182719006501451)
            ·
              refine ⟨12914857696774078509752177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8609905131182719006501451 12914857696774078509752177)
              ·
                refine ⟨9686143272580558882314133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12914857696774078509752177 9686143272580558882314133)
                ·
                  refine ⟨454037965902213697608475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9686143272580558882314133 454037965902213697608475)
                  ·
                    rfl

theorem cell22_3979061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 2, 6].length) (baseStart_3979061 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3979061 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3979061 prefixEnd_3979061 := by exact prefixLift 3979061
  have htrace : WordTrace (prefixWord ++ tailWord_3979061) baseStart_3979061 baseEnd_3979061 := by
    simpa [prefixWord, tailWord_3979061, baseEnd_3979061] using wordTrace_append hprefix tailTrace_3979061
  have hstable : (prefixWord ++ tailWord_3979061).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3979061).length < 2 ^ (prefixWord ++ tailWord_3979061).sum := by decide
  have hdescent : baseEnd_3979061 < baseStart_3979061 := by decide
  rcases family_descends (prefixWord ++ tailWord_3979061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3979089 : List Nat := [1, 2, 2, 1, 5, 2, 9]
def baseStart_3979089 : Nat := 118140960795 + 3979089 * 2 ^ 59
def prefixEnd_3979089 : Nat := 4983230072969 + 3 ^ 40 * 3979089 * 2
def baseEnd_3979089 : Nat := 50449017876994753819457

theorem tailTrace_3979089 : CollatzResearch.WordTrace tailWord_3979089 prefixEnd_3979089 50449017876994753819457 := by
  unfold tailWord_3979089
  simp only [CollatzResearch.WordTrace]
  refine ⟨145129298681447602142636321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96752865787631734761757547 145129298681447602142636321)
  ·
    refine ⟨108846974011085701606977241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145129298681447602142636321 108846974011085701606977241)
    ·
      refine ⟨81635230508314276205232931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108846974011085701606977241 81635230508314276205232931)
      ·
        refine ⟨122452845762471414307849397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81635230508314276205232931 122452845762471414307849397)
        ·
          refine ⟨11479954290231695091360881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 122452845762471414307849397 11479954290231695091360881)
          ·
            refine ⟨8609965717673771318520661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11479954290231695091360881 8609965717673771318520661)
            ·
              refine ⟨50449017876994753819457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8609965717673771318520661 50449017876994753819457)
              ·
                rfl

theorem cell22_3979089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 9].length) (baseStart_3979089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3979089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3979089 prefixEnd_3979089 := by exact prefixLift 3979089
  have htrace : WordTrace (prefixWord ++ tailWord_3979089) baseStart_3979089 baseEnd_3979089 := by
    simpa [prefixWord, tailWord_3979089, baseEnd_3979089] using wordTrace_append hprefix tailTrace_3979089
  have hstable : (prefixWord ++ tailWord_3979089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3979089).length < 2 ^ (prefixWord ++ tailWord_3979089).sum := by decide
  have hdescent : baseEnd_3979089 < baseStart_3979089 := by decide
  rcases family_descends (prefixWord ++ tailWord_3979089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3979093 : List Nat := [1, 3, 2, 2, 2, 2, 3, 2, 2, 3]
def baseStart_3979093 : Nat := 118140960795 + 3979093 * 2 ^ 59
def prefixEnd_3979093 : Nat := 4983230072969 + 3 ^ 40 * 3979093 * 2
def baseEnd_3979093 : Nat := 1362124851960603676025327

theorem tailTrace_3979093 : CollatzResearch.WordTrace tailWord_3979093 prefixEnd_3979093 1362124851960603676025327 := by
  unfold tailWord_3979093
  simp only [CollatzResearch.WordTrace]
  refine ⟨145129444573433110825781933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96752963048955407217187955 145129444573433110825781933)
  ·
    refine ⟨54423541715037416559668225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145129444573433110825781933 54423541715037416559668225)
    ·
      refine ⟨40817656286278062419751169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54423541715037416559668225 40817656286278062419751169)
      ·
        refine ⟨30613242214708546814813377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40817656286278062419751169 30613242214708546814813377)
        ·
          refine ⟨22959931661031410111110033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30613242214708546814813377 22959931661031410111110033)
          ·
            refine ⟨17219948745773557583332525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22959931661031410111110033 17219948745773557583332525)
            ·
              refine ⟨6457480779665084093749697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17219948745773557583332525 6457480779665084093749697)
              ·
                refine ⟨4843110584748813070312273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6457480779665084093749697 4843110584748813070312273)
                ·
                  refine ⟨3632332938561609802734205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4843110584748813070312273 3632332938561609802734205)
                  ·
                    refine ⟨1362124851960603676025327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3632332938561609802734205 1362124851960603676025327)
                    ·
                      rfl

theorem cell22_3979093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 3, 2, 2, 3].length) (baseStart_3979093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3979093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3979093 prefixEnd_3979093 := by exact prefixLift 3979093
  have htrace : WordTrace (prefixWord ++ tailWord_3979093) baseStart_3979093 baseEnd_3979093 := by
    simpa [prefixWord, tailWord_3979093, baseEnd_3979093] using wordTrace_append hprefix tailTrace_3979093
  have hstable : (prefixWord ++ tailWord_3979093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3979093).length < 2 ^ (prefixWord ++ tailWord_3979093).sum := by decide
  have hdescent : baseEnd_3979093 < baseStart_3979093 := by decide
  rcases family_descends (prefixWord ++ tailWord_3979093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3979121 : List Nat := [1, 2, 2, 2, 1, 3, 1, 4, 3, 3]
def baseStart_3979121 : Nat := 118140960795 + 3979121 * 2 ^ 59
def prefixEnd_3979121 : Nat := 4983230072969 + 3 ^ 40 * 3979121 * 2
def baseEnd_3979121 : Nat := 1362134436932820936325241

theorem tailTrace_3979121 : CollatzResearch.WordTrace tailWord_3979121 prefixEnd_3979121 1362134436932820936325241 := by
  unfold tailWord_3979121
  simp only [CollatzResearch.WordTrace]
  refine ⟨145130465817331671607801217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96753643878221114405200811 145130465817331671607801217)
  ·
    refine ⟨108847849362998753705850913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145130465817331671607801217 108847849362998753705850913)
    ·
      refine ⟨81635887022249065279388185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108847849362998753705850913 81635887022249065279388185)
      ·
        refine ⟨61226915266686798959541139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81635887022249065279388185 61226915266686798959541139)
        ·
          refine ⟨91840372900030198439311709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61226915266686798959541139 91840372900030198439311709)
          ·
            refine ⟨34440139837511324414741891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91840372900030198439311709 34440139837511324414741891)
            ·
              refine ⟨51660209756266986622112837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34440139837511324414741891 51660209756266986622112837)
              ·
                refine ⟨9686289329300059991646157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51660209756266986622112837 9686289329300059991646157)
                ·
                  refine ⟨3632358498487522496867309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9686289329300059991646157 3632358498487522496867309)
                  ·
                    refine ⟨1362134436932820936325241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3632358498487522496867309 1362134436932820936325241)
                    ·
                      rfl

theorem cell22_3979121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 4, 3, 3].length) (baseStart_3979121 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3979121 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3979121 prefixEnd_3979121 := by exact prefixLift 3979121
  have htrace : WordTrace (prefixWord ++ tailWord_3979121) baseStart_3979121 baseEnd_3979121 := by
    simpa [prefixWord, tailWord_3979121, baseEnd_3979121] using wordTrace_append hprefix tailTrace_3979121
  have hstable : (prefixWord ++ tailWord_3979121).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3979121).length < 2 ^ (prefixWord ++ tailWord_3979121).sum := by decide
  have hdescent : baseEnd_3979121 < baseStart_3979121 := by decide
  rcases family_descends (prefixWord ++ tailWord_3979121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3979262 : List Nat := [4, 2, 2, 2, 1, 1, 3, 2, 2, 3]
def baseStart_3979262 : Nat := 118140960795 + 3979262 * 2 ^ 59
def prefixEnd_3979262 : Nat := 4983230072969 + 3 ^ 40 * 3979262 * 2
def baseEnd_3979262 : Nat := 1362182704114343568549809

theorem tailTrace_3979262 : CollatzResearch.WordTrace tailWord_3979262 prefixEnd_3979262 1362182704114343568549809 := by
  unfold tailWord_3979262
  simp only [CollatzResearch.WordTrace]
  refine ⟨18141951063727606586085505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96757072339880568459122693 18141951063727606586085505)
  ·
    refine ⟨13606463297795704939564129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18141951063727606586085505 13606463297795704939564129)
    ·
      refine ⟨10204847473346778704673097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13606463297795704939564129 10204847473346778704673097)
      ·
        refine ⟨7653635605010084028504823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10204847473346778704673097 7653635605010084028504823)
        ·
          refine ⟨11480453407515126042757235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7653635605010084028504823 11480453407515126042757235)
          ·
            refine ⟨17220680111272689064135853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11480453407515126042757235 17220680111272689064135853)
            ·
              refine ⟨6457755041727258399050945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17220680111272689064135853 6457755041727258399050945)
              ·
                refine ⟨4843316281295443799288209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6457755041727258399050945 4843316281295443799288209)
                ·
                  refine ⟨3632487210971582849466157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4843316281295443799288209 3632487210971582849466157)
                  ·
                    refine ⟨1362182704114343568549809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3632487210971582849466157 1362182704114343568549809)
                    ·
                      rfl

theorem cell22_3979262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 3, 2, 2, 3].length) (baseStart_3979262 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3979262 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3979262 prefixEnd_3979262 := by exact prefixLift 3979262
  have htrace : WordTrace (prefixWord ++ tailWord_3979262) baseStart_3979262 baseEnd_3979262 := by
    simpa [prefixWord, tailWord_3979262, baseEnd_3979262] using wordTrace_append hprefix tailTrace_3979262
  have hstable : (prefixWord ++ tailWord_3979262).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3979262).length < 2 ^ (prefixWord ++ tailWord_3979262).sum := by decide
  have hdescent : baseEnd_3979262 < baseStart_3979262 := by decide
  rcases family_descends (prefixWord ++ tailWord_3979262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3979331 : List Nat := [1, 1, 1, 3, 1, 2, 2, 5, 6]
def baseStart_3979331 : Nat := 118140960795 + 3979331 * 2 ^ 59
def prefixEnd_3979331 : Nat := 4983230072969 + 3 ^ 40 * 3979331 * 2
def baseEnd_3979331 : Nat := 454068774741483462858199

theorem tailTrace_3979331 : CollatzResearch.WordTrace tailWord_3979331 prefixEnd_3979331 454068774741483462858199 := by
  unfold tailWord_3979331
  simp only [CollatzResearch.WordTrace]
  refine ⟨145138125146570877472945847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96758750097713918315297231 145138125146570877472945847)
  ·
    refine ⟨217707187719856316209418771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145138125146570877472945847 217707187719856316209418771)
    ·
      refine ⟨326560781579784474314128157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217707187719856316209418771 326560781579784474314128157)
      ·
        refine ⟨122460293092419177867798059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 326560781579784474314128157 122460293092419177867798059)
        ·
          refine ⟨183690439638628766801697089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122460293092419177867798059 183690439638628766801697089)
          ·
            refine ⟨137767829728971575101272817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183690439638628766801697089 137767829728971575101272817)
            ·
              refine ⟨103325872296728681325954613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137767829728971575101272817 103325872296728681325954613)
              ·
                refine ⟨9686800527818313874308245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 103325872296728681325954613 9686800527818313874308245)
                ·
                  refine ⟨454068774741483462858199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9686800527818313874308245 454068774741483462858199)
                  ·
                    rfl

theorem cell22_3979331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 5, 6].length) (baseStart_3979331 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3979331 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3979331 prefixEnd_3979331 := by exact prefixLift 3979331
  have htrace : WordTrace (prefixWord ++ tailWord_3979331) baseStart_3979331 baseEnd_3979331 := by
    simpa [prefixWord, tailWord_3979331, baseEnd_3979331] using wordTrace_append hprefix tailTrace_3979331
  have hstable : (prefixWord ++ tailWord_3979331).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3979331).length < 2 ^ (prefixWord ++ tailWord_3979331).sum := by decide
  have hdescent : baseEnd_3979331 < baseStart_3979331 := by decide
  rcases family_descends (prefixWord ++ tailWord_3979331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3979363 : List Nat := [1, 1, 1, 5, 1, 1, 2, 1, 6, 3]
def baseStart_3979363 : Nat := 118140960795 + 3979363 * 2 ^ 59
def prefixEnd_3979363 : Nat := 4983230072969 + 3 ^ 40 * 3979363 * 2
def baseEnd_3979363 : Nat := 1362217278478412971774499

theorem tailTrace_3979363 : CollatzResearch.WordTrace tailWord_3979363 prefixEnd_3979363 1362217278478412971774499 := by
  unfold tailWord_3979363
  simp only [CollatzResearch.WordTrace]
  refine ⟨145139292282454946938110743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96759528188303297958740495 145139292282454946938110743)
  ·
    refine ⟨217708938423682420407166115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145139292282454946938110743 217708938423682420407166115)
    ·
      refine ⟨326563407635523630610749173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217708938423682420407166115 326563407635523630610749173)
      ·
        refine ⟨30615319465830340369757735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 326563407635523630610749173 30615319465830340369757735)
        ·
          refine ⟨45922979198745510554636603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30615319465830340369757735 45922979198745510554636603)
          ·
            refine ⟨68884468798118265831954905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45922979198745510554636603 68884468798118265831954905)
            ·
              refine ⟨51663351598588699373966179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68884468798118265831954905 51663351598588699373966179)
              ·
                refine ⟨77495027397883049060949269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51663351598588699373966179 77495027397883049060949269)
                ·
                  refine ⟨3632579409275767924731997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 77495027397883049060949269 3632579409275767924731997)
                  ·
                    refine ⟨1362217278478412971774499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3632579409275767924731997 1362217278478412971774499)
                    ·
                      rfl

theorem cell22_3979363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 1, 6, 3].length) (baseStart_3979363 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3979363 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3979363 prefixEnd_3979363 := by exact prefixLift 3979363
  have htrace : WordTrace (prefixWord ++ tailWord_3979363) baseStart_3979363 baseEnd_3979363 := by
    simpa [prefixWord, tailWord_3979363, baseEnd_3979363] using wordTrace_append hprefix tailTrace_3979363
  have hstable : (prefixWord ++ tailWord_3979363).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3979363).length < 2 ^ (prefixWord ++ tailWord_3979363).sum := by decide
  have hdescent : baseEnd_3979363 < baseStart_3979363 := by decide
  rcases family_descends (prefixWord ++ tailWord_3979363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3979376 : List Nat := [2, 1, 1, 1, 5, 12]
def baseStart_3979376 : Nat := 118140960795 + 3979376 * 2 ^ 59
def prefixEnd_3979376 : Nat := 4983230072969 + 3 ^ 40 * 3979376 * 2
def baseEnd_3979376 : Nat := 16817552205482534212339

theorem tailTrace_3979376 : CollatzResearch.WordTrace tailWord_3979376 prefixEnd_3979376 16817552205482534212339 := by
  unfold tailWord_3979376
  simp only [CollatzResearch.WordTrace]
  refine ⟨72569883215703925079166991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96759844287605233438889321 72569883215703925079166991)
  ·
    refine ⟨108854824823555887618750487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72569883215703925079166991 108854824823555887618750487)
    ·
      refine ⟨163282237235333831428125731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108854824823555887618750487 163282237235333831428125731)
      ·
        refine ⟨244923355853000747142188597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163282237235333831428125731 244923355853000747142188597)
        ·
          refine ⟨22961564611218820044580181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 244923355853000747142188597 22961564611218820044580181)
          ·
            refine ⟨16817552205482534212339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 22961564611218820044580181 16817552205482534212339)
            ·
              rfl

theorem cell22_3979376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 12].length) (baseStart_3979376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3979376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3979376 prefixEnd_3979376 := by exact prefixLift 3979376
  have htrace : WordTrace (prefixWord ++ tailWord_3979376) baseStart_3979376 baseEnd_3979376 := by
    simpa [prefixWord, tailWord_3979376, baseEnd_3979376] using wordTrace_append hprefix tailTrace_3979376
  have hstable : (prefixWord ++ tailWord_3979376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3979376).length < 2 ^ (prefixWord ++ tailWord_3979376).sum := by decide
  have hdescent : baseEnd_3979376 < baseStart_3979376 := by decide
  rcases family_descends (prefixWord ++ tailWord_3979376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3979382 : List Nat := [5, 1, 1, 2, 1, 3, 1, 4, 4]
def baseStart_3979382 : Nat := 118140960795 + 3979382 * 2 ^ 59
def prefixEnd_3979382 : Nat := 4983230072969 + 3 ^ 40 * 3979382 * 2
def baseEnd_3979382 : Nat := 454074594188901085183147

theorem tailTrace_3979382 : CollatzResearch.WordTrace tailWord_3979382 prefixEnd_3979382 454074594188901085183147 := by
  unfold tailWord_3979382
  simp only [CollatzResearch.WordTrace]
  refine ⟨9071249079336632073940775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 96759990179590742122034933 9071249079336632073940775)
  ·
    refine ⟨13606873619004948110911163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9071249079336632073940775 13606873619004948110911163)
    ·
      refine ⟨20410310428507422166366745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13606873619004948110911163 20410310428507422166366745)
      ·
        refine ⟨15307732821380566624775059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20410310428507422166366745 15307732821380566624775059)
        ·
          refine ⟨22961599232070849937162589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15307732821380566624775059 22961599232070849937162589)
          ·
            refine ⟨8610599712026568726435971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22961599232070849937162589 8610599712026568726435971)
            ·
              refine ⟨12915899568039853089653957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8610599712026568726435971 12915899568039853089653957)
              ·
                refine ⟨2421731169007472454310117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12915899568039853089653957 2421731169007472454310117)
                ·
                  refine ⟨454074594188901085183147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2421731169007472454310117 454074594188901085183147)
                  ·
                    rfl

theorem cell22_3979382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 4, 4].length) (baseStart_3979382 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3979382 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3979382 prefixEnd_3979382 := by exact prefixLift 3979382
  have htrace : WordTrace (prefixWord ++ tailWord_3979382) baseStart_3979382 baseEnd_3979382 := by
    simpa [prefixWord, tailWord_3979382, baseEnd_3979382] using wordTrace_append hprefix tailTrace_3979382
  have hstable : (prefixWord ++ tailWord_3979382).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3979382).length < 2 ^ (prefixWord ++ tailWord_3979382).sum := by decide
  have hdescent : baseEnd_3979382 < baseStart_3979382 := by decide
  rcases family_descends (prefixWord ++ tailWord_3979382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3979410 : List Nat := [3, 2, 3, 1, 1, 1, 5, 6]
def baseStart_3979410 : Nat := 118140960795 + 3979410 * 2 ^ 59
def prefixEnd_3979410 : Nat := 4983230072969 + 3 ^ 40 * 3979410 * 2
def baseEnd_3979410 : Nat := 151359263059880057316595

theorem tailTrace_3979410 : CollatzResearch.WordTrace tailWord_3979410 prefixEnd_3979410 151359263059880057316595 := by
  unfold tailWord_3979410
  simp only [CollatzResearch.WordTrace]
  refine ⟨36285251628321168491267921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96760671008856449310047789 36285251628321168491267921)
  ·
    refine ⟨27213938721240876368450941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36285251628321168491267921 27213938721240876368450941)
    ·
      refine ⟨10205227020465328638169103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27213938721240876368450941 10205227020465328638169103)
      ·
        refine ⟨15307840530697992957253655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10205227020465328638169103 15307840530697992957253655)
        ·
          refine ⟨22961760796046989435880483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15307840530697992957253655 22961760796046989435880483)
          ·
            refine ⟨34442641194070484153820725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22961760796046989435880483 34442641194070484153820725)
            ·
              refine ⟨3228997611944107889420693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34442641194070484153820725 3228997611944107889420693)
              ·
                refine ⟨151359263059880057316595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3228997611944107889420693 151359263059880057316595)
                ·
                  rfl

theorem cell22_3979410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 5, 6].length) (baseStart_3979410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3979410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3979410 prefixEnd_3979410 := by exact prefixLift 3979410
  have htrace : WordTrace (prefixWord ++ tailWord_3979410) baseStart_3979410 baseEnd_3979410 := by
    simpa [prefixWord, tailWord_3979410, baseEnd_3979410] using wordTrace_append hprefix tailTrace_3979410
  have hstable : (prefixWord ++ tailWord_3979410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3979410).length < 2 ^ (prefixWord ++ tailWord_3979410).sum := by decide
  have hdescent : baseEnd_3979410 < baseStart_3979410 := by decide
  rcases family_descends (prefixWord ++ tailWord_3979410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3979412 : List Nat := [2, 4, 2, 3, 1, 1, 1, 1, 1, 6]
def baseStart_3979412 : Nat := 118140960795 + 3979412 * 2 ^ 59
def prefixEnd_3979412 : Nat := 4983230072969 + 3 ^ 40 * 3979412 * 2
def baseEnd_3979412 : Nat := 1362234052179793177299349

theorem tailTrace_3979412 : CollatzResearch.WordTrace tailWord_3979412 prefixEnd_3979412 1362234052179793177299349 := by
  unfold tailWord_3979412
  simp only [CollatzResearch.WordTrace]
  refine ⟨72570539729638714153322245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96760719639518285537762993 72570539729638714153322245)
  ·
    refine ⟨13606976199307258903747921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72570539729638714153322245 13606976199307258903747921)
    ·
      refine ⟨10205232149480444177810941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13606976199307258903747921 10205232149480444177810941)
      ·
        refine ⟨3826962056055166566679103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10205232149480444177810941 3826962056055166566679103)
        ·
          refine ⟨5740443084082749850018655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3826962056055166566679103 5740443084082749850018655)
          ·
            refine ⟨8610664626124124775027983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5740443084082749850018655 8610664626124124775027983)
            ·
              refine ⟨12915996939186187162541975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8610664626124124775027983 12915996939186187162541975)
              ·
                refine ⟨19373995408779280743812963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12915996939186187162541975 19373995408779280743812963)
                ·
                  refine ⟨29060993113168921115719445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19373995408779280743812963 29060993113168921115719445)
                  ·
                    refine ⟨1362234052179793177299349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29060993113168921115719445 1362234052179793177299349)
                    ·
                      rfl

theorem cell22_3979412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 1, 1, 6].length) (baseStart_3979412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3979412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3979412 prefixEnd_3979412 := by exact prefixLift 3979412
  have htrace : WordTrace (prefixWord ++ tailWord_3979412) baseStart_3979412 baseEnd_3979412 := by
    simpa [prefixWord, tailWord_3979412, baseEnd_3979412] using wordTrace_append hprefix tailTrace_3979412
  have hstable : (prefixWord ++ tailWord_3979412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3979412).length < 2 ^ (prefixWord ++ tailWord_3979412).sum := by decide
  have hdescent : baseEnd_3979412 < baseStart_3979412 := by decide
  rcases family_descends (prefixWord ++ tailWord_3979412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3979431 : List Nat := [1, 1, 6, 2, 3, 1, 1, 2, 2, 3]
def baseStart_3979431 : Nat := 118140960795 + 3979431 * 2 ^ 59
def prefixEnd_3979431 : Nat := 4983230072969 + 3 ^ 40 * 3979431 * 2
def baseEnd_3979431 : Nat := 1362240556268083461074291

theorem tailTrace_3979431 : CollatzResearch.WordTrace tailWord_3979431 prefixEnd_3979431 1362240556268083461074291 := by
  unfold tailWord_3979431
  simp only [CollatzResearch.WordTrace]
  refine ⟨145141772446208594551586147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96761181630805729701057431 145141772446208594551586147)
  ·
    refine ⟨217712658669312891827379221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145141772446208594551586147 217712658669312891827379221)
    ·
      refine ⟨10205280875124041804408401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 217712658669312891827379221 10205280875124041804408401)
      ·
        refine ⟨7653960656343031353306301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10205280875124041804408401 7653960656343031353306301)
        ·
          refine ⟨2870235246128636757489863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7653960656343031353306301 2870235246128636757489863)
          ·
            refine ⟨4305352869192955136234795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2870235246128636757489863 4305352869192955136234795)
            ·
              refine ⟨6458029303789432704352193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4305352869192955136234795 6458029303789432704352193)
              ·
                refine ⟨4843521977842074528264145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6458029303789432704352193 4843521977842074528264145)
                ·
                  refine ⟨3632641483381555896198109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4843521977842074528264145 3632641483381555896198109)
                  ·
                    refine ⟨1362240556268083461074291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3632641483381555896198109 1362240556268083461074291)
                    ·
                      rfl

theorem cell22_3979431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 1, 2, 2, 3].length) (baseStart_3979431 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3979431 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3979431 prefixEnd_3979431 := by exact prefixLift 3979431
  have htrace : WordTrace (prefixWord ++ tailWord_3979431) baseStart_3979431 baseEnd_3979431 := by
    simpa [prefixWord, tailWord_3979431, baseEnd_3979431] using wordTrace_append hprefix tailTrace_3979431
  have hstable : (prefixWord ++ tailWord_3979431).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3979431).length < 2 ^ (prefixWord ++ tailWord_3979431).sum := by decide
  have hdescent : baseEnd_3979431 < baseStart_3979431 := by decide
  rcases family_descends (prefixWord ++ tailWord_3979431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3979442 : List Nat := [3, 2, 1, 1, 1, 3, 1, 6, 1, 3]
def baseStart_3979442 : Nat := 118140960795 + 3979442 * 2 ^ 59
def prefixEnd_3979442 : Nat := 4983230072969 + 3 ^ 40 * 3979442 * 2
def baseEnd_3979442 : Nat := 1362244321792883099049257

theorem tailTrace_3979442 : CollatzResearch.WordTrace tailWord_3979442 prefixEnd_3979442 1362244321792883099049257 := by
  unfold tailWord_3979442
  simp only [CollatzResearch.WordTrace]
  refine ⟨36285543412292185857559145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96761449099445828953491053 36285543412292185857559145)
  ·
    refine ⟨27214157559219139393169359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36285543412292185857559145 27214157559219139393169359)
    ·
      refine ⟨40821236338828709089754039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27214157559219139393169359 40821236338828709089754039)
      ·
        refine ⟨61231854508243063634631059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40821236338828709089754039 61231854508243063634631059)
        ·
          refine ⟨91847781762364595451946589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61231854508243063634631059 91847781762364595451946589)
          ·
            refine ⟨34442918160886723294479971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91847781762364595451946589 34442918160886723294479971)
            ·
              refine ⟨51664377241330084941719957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34442918160886723294479971 51664377241330084941719957)
              ·
                refine ⟨2421767683187347731643123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 51664377241330084941719957 2421767683187347731643123)
                ·
                  refine ⟨3632651524781021597464685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2421767683187347731643123 3632651524781021597464685)
                  ·
                    refine ⟨1362244321792883099049257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3632651524781021597464685 1362244321792883099049257)
                    ·
                      rfl

theorem cell22_3979442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 6, 1, 3].length) (baseStart_3979442 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3979442 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3979442 prefixEnd_3979442 := by exact prefixLift 3979442
  have htrace : WordTrace (prefixWord ++ tailWord_3979442) baseStart_3979442 baseEnd_3979442 := by
    simpa [prefixWord, tailWord_3979442, baseEnd_3979442] using wordTrace_append hprefix tailTrace_3979442
  have hstable : (prefixWord ++ tailWord_3979442).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3979442).length < 2 ^ (prefixWord ++ tailWord_3979442).sum := by decide
  have hdescent : baseEnd_3979442 < baseStart_3979442 := by decide
  rcases family_descends (prefixWord ++ tailWord_3979442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3979513 : List Nat := [1, 2, 1, 3, 1, 1, 2, 4, 1, 6]
def baseStart_3979513 : Nat := 118140960795 + 3979513 * 2 ^ 59
def prefixEnd_3979513 : Nat := 4983230072969 + 3 ^ 40 * 3979513 * 2
def baseEnd_3979513 : Nat := 1362268626543862580524039

theorem tailTrace_3979513 : CollatzResearch.WordTrace tailWord_3979513 prefixEnd_3979513 1362268626543862580524039 := by
  unfold tailWord_3979513
  simp only [CollatzResearch.WordTrace]
  refine ⟨145144763231911522556071193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96763175487941015037380795 145144763231911522556071193)
  ·
    refine ⟨108858572423933641917053395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145144763231911522556071193 108858572423933641917053395)
    ·
      refine ⟨163287858635900462875580093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108858572423933641917053395 163287858635900462875580093)
      ·
        refine ⟨61232946988462673578342535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163287858635900462875580093 61232946988462673578342535)
        ·
          refine ⟨91849420482694010367513803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61232946988462673578342535 91849420482694010367513803)
          ·
            refine ⟨137774130724041015551270705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91849420482694010367513803 137774130724041015551270705)
            ·
              refine ⟨103330598043030761663453029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137774130724041015551270705 103330598043030761663453029)
              ·
                refine ⟨19374487133068267811897443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 103330598043030761663453029 19374487133068267811897443)
                ·
                  refine ⟨29061730699602401717846165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19374487133068267811897443 29061730699602401717846165)
                  ·
                    refine ⟨1362268626543862580524039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29061730699602401717846165 1362268626543862580524039)
                    ·
                      rfl

theorem cell22_3979513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 4, 1, 6].length) (baseStart_3979513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3979513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3979513 prefixEnd_3979513 := by exact prefixLift 3979513
  have htrace : WordTrace (prefixWord ++ tailWord_3979513) baseStart_3979513 baseEnd_3979513 := by
    simpa [prefixWord, tailWord_3979513, baseEnd_3979513] using wordTrace_append hprefix tailTrace_3979513
  have hstable : (prefixWord ++ tailWord_3979513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3979513).length < 2 ^ (prefixWord ++ tailWord_3979513).sum := by decide
  have hdescent : baseEnd_3979513 < baseStart_3979513 := by decide
  rcases family_descends (prefixWord ++ tailWord_3979513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3979530 : List Nat := [3, 1, 2, 2, 1, 1, 3, 3, 2, 4]
def baseStart_3979530 : Nat := 118140960795 + 3979530 * 2 ^ 59
def prefixEnd_3979530 : Nat := 4983230072969 + 3 ^ 40 * 3979530 * 2
def baseEnd_3979530 : Nat := 1362274445991280202848987

theorem tailTrace_3979530 : CollatzResearch.WordTrace tailWord_3979530 prefixEnd_3979530 1362274445991280202848987 := by
  unfold tailWord_3979530
  simp only [CollatzResearch.WordTrace]
  refine ⟨36286345818212483614860011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96763588848566622972960029 36286345818212483614860011)
  ·
    refine ⟨54429518727318725422290017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36286345818212483614860011 54429518727318725422290017)
    ·
      refine ⟨40822139045489044066717513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54429518727318725422290017 40822139045489044066717513)
      ·
        refine ⟨30616604284116783050038135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40822139045489044066717513 30616604284116783050038135)
        ·
          refine ⟨45924906426175174575057203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30616604284116783050038135 45924906426175174575057203)
          ·
            refine ⟨68887359639262761862585805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45924906426175174575057203 68887359639262761862585805)
            ·
              refine ⟨25832759864723535698469677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68887359639262761862585805 25832759864723535698469677)
              ·
                refine ⟨9687284949271325886926129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25832759864723535698469677 9687284949271325886926129)
                ·
                  refine ⟨7265463711953494415194597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9687284949271325886926129 7265463711953494415194597)
                  ·
                    refine ⟨1362274445991280202848987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7265463711953494415194597 1362274445991280202848987)
                    ·
                      rfl

theorem cell22_3979530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 3, 2, 4].length) (baseStart_3979530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3979530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3979530 prefixEnd_3979530 := by exact prefixLift 3979530
  have htrace : WordTrace (prefixWord ++ tailWord_3979530) baseStart_3979530 baseEnd_3979530 := by
    simpa [prefixWord, tailWord_3979530, baseEnd_3979530] using wordTrace_append hprefix tailTrace_3979530
  have hstable : (prefixWord ++ tailWord_3979530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3979530).length < 2 ^ (prefixWord ++ tailWord_3979530).sum := by decide
  have hdescent : baseEnd_3979530 < baseStart_3979530 := by decide
  rcases family_descends (prefixWord ++ tailWord_3979530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3979577 : List Nat := [1, 2, 1, 6, 1, 1, 1, 1, 5, 3]
def baseStart_3979577 : Nat := 118140960795 + 3979577 * 2 ^ 59
def prefixEnd_3979577 : Nat := 4983230072969 + 3 ^ 40 * 3979577 * 2
def baseEnd_3979577 : Nat := 1362290535051787746923843

theorem tailTrace_3979577 : CollatzResearch.WordTrace tailWord_3979577 prefixEnd_3979577 1362290535051787746923843 := by
  unfold tailWord_3979577
  simp only [CollatzResearch.WordTrace]
  refine ⟨145147097503679661486400985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96764731669119774324267323 145147097503679661486400985)
  ·
    refine ⟨108860323127759746114800739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145147097503679661486400985 108860323127759746114800739)
    ·
      refine ⟨163290484691639619172201109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108860323127759746114800739 163290484691639619172201109)
      ·
        refine ⟨7654241469920607148696927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 163290484691639619172201109 7654241469920607148696927)
        ·
          refine ⟨11481362204880910723045391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7654241469920607148696927 11481362204880910723045391)
          ·
            refine ⟨17222043307321366084568087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11481362204880910723045391 17222043307321366084568087)
            ·
              refine ⟨25833064960982049126852131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17222043307321366084568087 25833064960982049126852131)
              ·
                refine ⟨38749597441473073690278197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25833064960982049126852131 38749597441473073690278197)
                ·
                  refine ⟨3632774760138100658463581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38749597441473073690278197 3632774760138100658463581)
                  ·
                    refine ⟨1362290535051787746923843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3632774760138100658463581 1362290535051787746923843)
                    ·
                      rfl

theorem cell22_3979577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 1, 5, 3].length) (baseStart_3979577 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3979577 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3979577 prefixEnd_3979577 := by exact prefixLift 3979577
  have htrace : WordTrace (prefixWord ++ tailWord_3979577) baseStart_3979577 baseEnd_3979577 := by
    simpa [prefixWord, tailWord_3979577, baseEnd_3979577] using wordTrace_append hprefix tailTrace_3979577
  have hstable : (prefixWord ++ tailWord_3979577).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3979577).length < 2 ^ (prefixWord ++ tailWord_3979577).sum := by decide
  have hdescent : baseEnd_3979577 < baseStart_3979577 := by decide
  rcases family_descends (prefixWord ++ tailWord_3979577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3979624 : List Nat := [2, 1, 4, 2, 2, 2, 3, 1, 5]
def baseStart_3979624 : Nat := 118140960795 + 3979624 * 2 ^ 59
def prefixEnd_3979624 : Nat := 4983230072969 + 3 ^ 40 * 3979624 * 2
def baseEnd_3979624 : Nat := 454102208037431763666233

theorem tailTrace_3979624 : CollatzResearch.WordTrace tailWord_3979624 prefixEnd_3979624 454102208037431763666233 := by
  unfold tailWord_3979624
  simp only [CollatzResearch.WordTrace]
  refine ⟨72574405867254694256680963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96765874489672925675574617 72574405867254694256680963)
  ·
    refine ⟨108861608800882041385021445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72574405867254694256680963 108861608800882041385021445)
    ·
      refine ⟨20411551650165382759691521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108861608800882041385021445 20411551650165382759691521)
      ·
        refine ⟨15308663737624037069768641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20411551650165382759691521 15308663737624037069768641)
        ·
          refine ⟨11481497803218027802326481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15308663737624037069768641 11481497803218027802326481)
          ·
            refine ⟨8611123352413520851744861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11481497803218027802326481 8611123352413520851744861)
            ·
              refine ⟨3229171257155070319404323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8611123352413520851744861 3229171257155070319404323)
              ·
                refine ⟨4843756885732605479106485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3229171257155070319404323 4843756885732605479106485)
                ·
                  refine ⟨454102208037431763666233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4843756885732605479106485 454102208037431763666233)
                  ·
                    rfl

theorem cell22_3979624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 3, 1, 5].length) (baseStart_3979624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3979624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3979624 prefixEnd_3979624 := by exact prefixLift 3979624
  have htrace : WordTrace (prefixWord ++ tailWord_3979624) baseStart_3979624 baseEnd_3979624 := by
    simpa [prefixWord, tailWord_3979624, baseEnd_3979624] using wordTrace_append hprefix tailTrace_3979624
  have hstable : (prefixWord ++ tailWord_3979624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3979624).length < 2 ^ (prefixWord ++ tailWord_3979624).sum := by decide
  have hdescent : baseEnd_3979624 < baseStart_3979624 := by decide
  rcases family_descends (prefixWord ++ tailWord_3979624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3979680 : List Nat := [2, 1, 1, 4, 1, 3, 1, 9]
def baseStart_3979680 : Nat := 118140960795 + 3979680 * 2 ^ 59
def prefixEnd_3979680 : Nat := 4983230072969 + 3 ^ 40 * 3979680 * 2
def baseEnd_3979680 : Nat := 151369532672969979066503

theorem tailTrace_3979680 : CollatzResearch.WordTrace tailWord_3979680 prefixEnd_3979680 151369532672969979066503 := by
  unfold tailWord_3979680
  simp only [CollatzResearch.WordTrace]
  refine ⟨72575427111153255038700247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96767236148204340051600329 72575427111153255038700247)
  ·
    refine ⟨108863140666729882558050371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72575427111153255038700247 108863140666729882558050371)
    ·
      refine ⟨163294711000094823837075557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108863140666729882558050371 163294711000094823837075557)
      ·
        refine ⟨30617758312517779469451667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 163294711000094823837075557 30617758312517779469451667)
        ·
          refine ⟨45926637468776669204177501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30617758312517779469451667 45926637468776669204177501)
          ·
            refine ⟨17222489050791250951566563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45926637468776669204177501 17222489050791250951566563)
            ·
              refine ⟨25833733576186876427349845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17222489050791250951566563 25833733576186876427349845)
              ·
                refine ⟨151369532672969979066503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 25833733576186876427349845 151369532672969979066503)
                ·
                  rfl

theorem cell22_3979680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 9].length) (baseStart_3979680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3979680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3979680 prefixEnd_3979680 := by exact prefixLift 3979680
  have htrace : WordTrace (prefixWord ++ tailWord_3979680) baseStart_3979680 baseEnd_3979680 := by
    simpa [prefixWord, tailWord_3979680, baseEnd_3979680] using wordTrace_append hprefix tailTrace_3979680
  have hstable : (prefixWord ++ tailWord_3979680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3979680).length < 2 ^ (prefixWord ++ tailWord_3979680).sum := by decide
  have hdescent : baseEnd_3979680 < baseStart_3979680 := by decide
  rcases family_descends (prefixWord ++ tailWord_3979680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3979682 : List Nat := [3, 3, 1, 2, 1, 1, 1, 2, 4, 4]
def baseStart_3979682 : Nat := 118140960795 + 3979682 * 2 ^ 59
def prefixEnd_3979682 : Nat := 4983230072969 + 3 ^ 40 * 3979682 * 2
def baseEnd_3979682 : Nat := 1362326478697602473048521

theorem tailTrace_3979682 : CollatzResearch.WordTrace tailWord_3979682 prefixEnd_3979682 1362326478697602473048521 := by
  unfold tailWord_3979682
  simp only [CollatzResearch.WordTrace]
  refine ⟨36287731792074816104743325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96767284778866176279315533 36287731792074816104743325)
  ·
    refine ⟨13607899422028056039278747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36287731792074816104743325 13607899422028056039278747)
    ·
      refine ⟨20411849133042084058918121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13607899422028056039278747 20411849133042084058918121)
      ·
        refine ⟨15308886849781563044188591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20411849133042084058918121 15308886849781563044188591)
        ·
          refine ⟨22963330274672344566282887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15308886849781563044188591 22963330274672344566282887)
          ·
            refine ⟨34444995412008516849424331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22963330274672344566282887 34444995412008516849424331)
            ·
              refine ⟨51667493118012775274136497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34444995412008516849424331 51667493118012775274136497)
              ·
                refine ⟨38750619838509581455602373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51667493118012775274136497 38750619838509581455602373)
                ·
                  refine ⟨7265741219720546522925445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38750619838509581455602373 7265741219720546522925445)
                  ·
                    refine ⟨1362326478697602473048521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7265741219720546522925445 1362326478697602473048521)
                    ·
                      rfl

theorem cell22_3979682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 2, 4, 4].length) (baseStart_3979682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3979682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3979682 prefixEnd_3979682 := by exact prefixLift 3979682
  have htrace : WordTrace (prefixWord ++ tailWord_3979682) baseStart_3979682 baseEnd_3979682 := by
    simpa [prefixWord, tailWord_3979682, baseEnd_3979682] using wordTrace_append hprefix tailTrace_3979682
  have hstable : (prefixWord ++ tailWord_3979682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3979682).length < 2 ^ (prefixWord ++ tailWord_3979682).sum := by decide
  have hdescent : baseEnd_3979682 < baseStart_3979682 := by decide
  rcases family_descends (prefixWord ++ tailWord_3979682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3979714 : List Nat := [3, 5, 2, 12]
def baseStart_3979714 : Nat := 118140960795 + 3979714 * 2 ^ 59
def prefixEnd_3979714 : Nat := 4983230072969 + 3 ^ 40 * 3979714 * 2
def baseEnd_3979714 : Nat := 1868775628191447265087

theorem tailTrace_3979714 : CollatzResearch.WordTrace tailWord_3979714 prefixEnd_3979714 1868775628191447265087 := by
  unfold tailWord_3979714
  simp only [CollatzResearch.WordTrace]
  refine ⟨36288023576045833471034549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96768062869455555922758797 36288023576045833471034549)
  ·
    refine ⟨3402002210254296887909489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 36288023576045833471034549 3402002210254296887909489)
    ·
      refine ⟨2551501657690722665932117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3402002210254296887909489 2551501657690722665932117)
      ·
        refine ⟨1868775628191447265087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 12 2551501657690722665932117 1868775628191447265087)
        ·
          rfl

theorem cell22_3979714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 12].length) (baseStart_3979714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3979714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3979714 prefixEnd_3979714 := by exact prefixLift 3979714
  have htrace : WordTrace (prefixWord ++ tailWord_3979714) baseStart_3979714 baseEnd_3979714 := by
    simpa [prefixWord, tailWord_3979714, baseEnd_3979714] using wordTrace_append hprefix tailTrace_3979714
  have hstable : (prefixWord ++ tailWord_3979714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3979714).length < 2 ^ (prefixWord ++ tailWord_3979714).sum := by decide
  have hdescent : baseEnd_3979714 < baseStart_3979714 := by decide
  rcases family_descends (prefixWord ++ tailWord_3979714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3979787 : List Nat := [1, 1, 1, 1, 7, 1, 1, 3, 6]
def baseStart_3979787 : Nat := 118140960795 + 3979787 * 2 ^ 59
def prefixEnd_3979787 : Nat := 4983230072969 + 3 ^ 40 * 3979787 * 2
def baseEnd_3979787 : Nat := 454120807447805733057733

theorem tailTrace_3979787 : CollatzResearch.WordTrace tailWord_3979787 prefixEnd_3979787 454120807447805733057733 := by
  unfold tailWord_3979787
  simp only [CollatzResearch.WordTrace]
  refine ⟨145154756832918867351545615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96769837888612578234363743 145154756832918867351545615)
  ·
    refine ⟨217732135249378301027318423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145154756832918867351545615 217732135249378301027318423)
    ·
      refine ⟨326598202874067451540977635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217732135249378301027318423 326598202874067451540977635)
      ·
        refine ⟨489897304311101177311466453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 326598202874067451540977635 489897304311101177311466453)
        ·
          refine ⟨11481968069791433843237495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 489897304311101177311466453 11481968069791433843237495)
          ·
            refine ⟨17222952104687150764856243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11481968069791433843237495 17222952104687150764856243)
            ·
              refine ⟨25834428157030726147284365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17222952104687150764856243 25834428157030726147284365)
              ·
                refine ⟨9687910558886522305231637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25834428157030726147284365 9687910558886522305231637)
                ·
                  refine ⟨454120807447805733057733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9687910558886522305231637 454120807447805733057733)
                  ·
                    rfl

theorem cell22_3979787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 3, 6].length) (baseStart_3979787 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3979787 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3979787 prefixEnd_3979787 := by exact prefixLift 3979787
  have htrace : WordTrace (prefixWord ++ tailWord_3979787) baseStart_3979787 baseEnd_3979787 := by
    simpa [prefixWord, tailWord_3979787, baseEnd_3979787] using wordTrace_append hprefix tailTrace_3979787
  have hstable : (prefixWord ++ tailWord_3979787).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3979787).length < 2 ^ (prefixWord ++ tailWord_3979787).sum := by decide
  have hdescent : baseEnd_3979787 < baseStart_3979787 := by decide
  rcases family_descends (prefixWord ++ tailWord_3979787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3979834 : List Nat := [3, 1, 1, 1, 3, 4, 1, 2, 2, 4]
def baseStart_3979834 : Nat := 118140960795 + 3979834 * 2 ^ 59
def prefixEnd_3979834 : Nat := 4983230072969 + 3 ^ 40 * 3979834 * 2
def baseEnd_3979834 : Nat := 1362378511403924743248055

theorem tailTrace_3979834 : CollatzResearch.WordTrace tailWord_3979834 prefixEnd_3979834 1362378511403924743248055 := by
  unfold tailWord_3979834
  simp only [CollatzResearch.WordTrace]
  refine ⟨36289117765937148594626639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96770980709165729585671037 36289117765937148594626639)
  ·
    refine ⟨54433676648905722891939959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36289117765937148594626639 54433676648905722891939959)
    ·
      refine ⟨81650514973358584337909939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54433676648905722891939959 81650514973358584337909939)
      ·
        refine ⟨122475772460037876506864909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81650514973358584337909939 122475772460037876506864909)
        ·
          refine ⟨45928414672514203690074341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122475772460037876506864909 45928414672514203690074341)
          ·
            refine ⟨8611577751096413191888939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45928414672514203690074341 8611577751096413191888939)
            ·
              refine ⟨12917366626644619787833409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8611577751096413191888939 12917366626644619787833409)
              ·
                refine ⟨9688024969983464840875057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12917366626644619787833409 9688024969983464840875057)
                ·
                  refine ⟨7266018727487598630656293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9688024969983464840875057 7266018727487598630656293)
                  ·
                    refine ⟨1362378511403924743248055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7266018727487598630656293 1362378511403924743248055)
                    ·
                      rfl

theorem cell22_3979834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 2, 2, 4].length) (baseStart_3979834 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3979834 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3979834 prefixEnd_3979834 := by exact prefixLift 3979834
  have htrace : WordTrace (prefixWord ++ tailWord_3979834) baseStart_3979834 baseEnd_3979834 := by
    simpa [prefixWord, tailWord_3979834, baseEnd_3979834] using wordTrace_append hprefix tailTrace_3979834
  have hstable : (prefixWord ++ tailWord_3979834).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3979834).length < 2 ^ (prefixWord ++ tailWord_3979834).sum := by decide
  have hdescent : baseEnd_3979834 < baseStart_3979834 := by decide
  rcases family_descends (prefixWord ++ tailWord_3979834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3979838 : List Nat := [4, 2, 1, 4, 1, 2, 1, 1, 6]
def baseStart_3979838 : Nat := 118140960795 + 3979838 * 2 ^ 59
def prefixEnd_3979838 : Nat := 4983230072969 + 3 ^ 40 * 3979838 * 2
def baseEnd_3979838 : Nat := 454126626895223355382681

theorem tailTrace_3979838 : CollatzResearch.WordTrace tailWord_3979838 prefixEnd_3979838 454126626895223355382681 := by
  unfold tailWord_3979838
  simp only [CollatzResearch.WordTrace]
  refine ⟨18144577119466762882706521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96771077970489402041101445 18144577119466762882706521)
  ·
    refine ⟨13608432839600072162029891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18144577119466762882706521 13608432839600072162029891)
    ·
      refine ⟨20412649259400108243044837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13608432839600072162029891 20412649259400108243044837)
      ·
        refine ⟨3827371736137520295570907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20412649259400108243044837 3827371736137520295570907)
        ·
          refine ⟨5741057604206280443356361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3827371736137520295570907 5741057604206280443356361)
          ·
            refine ⟨4305793203154710332517271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5741057604206280443356361 4305793203154710332517271)
            ·
              refine ⟨6458689804732065498775907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4305793203154710332517271 6458689804732065498775907)
              ·
                refine ⟨9688034707098098248163861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6458689804732065498775907 9688034707098098248163861)
                ·
                  refine ⟨454126626895223355382681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9688034707098098248163861 454126626895223355382681)
                  ·
                    rfl

theorem cell22_3979838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 1, 1, 6].length) (baseStart_3979838 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3979838 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3979838 prefixEnd_3979838 := by exact prefixLift 3979838
  have htrace : WordTrace (prefixWord ++ tailWord_3979838) baseStart_3979838 baseEnd_3979838 := by
    simpa [prefixWord, tailWord_3979838, baseEnd_3979838] using wordTrace_append hprefix tailTrace_3979838
  have hstable : (prefixWord ++ tailWord_3979838).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3979838).length < 2 ^ (prefixWord ++ tailWord_3979838).sum := by decide
  have hdescent : baseEnd_3979838 < baseStart_3979838 := by decide
  rcases family_descends (prefixWord ++ tailWord_3979838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3979853 : List Nat := [1, 6, 1, 1, 2, 2, 1, 3, 2, 3]
def baseStart_3979853 : Nat := 118140960795 + 3979853 * 2 ^ 59
def prefixEnd_3979853 : Nat := 4983230072969 + 3 ^ 40 * 3979853 * 2
def baseEnd_3979853 : Nat := 1362385015492215027022997

theorem tailTrace_3979853 : CollatzResearch.WordTrace tailWord_3979853 prefixEnd_3979853 1362385015492215027022997 := by
  unfold tailWord_3979853
  simp only [CollatzResearch.WordTrace]
  refine ⟨145157164050679760623448213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96771442700453173748965475 145157164050679760623448213)
  ·
    refine ⟨6804242064875613779224135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 145157164050679760623448213 6804242064875613779224135)
    ·
      refine ⟨10206363097313420668836203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6804242064875613779224135 10206363097313420668836203)
      ·
        refine ⟨15309544645970131003254305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10206363097313420668836203 15309544645970131003254305)
        ·
          refine ⟨11482158484477598252440729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15309544645970131003254305 11482158484477598252440729)
          ·
            refine ⟨8611618863358198689330547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11482158484477598252440729 8611618863358198689330547)
            ·
              refine ⟨12917428295037298033995821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8611618863358198689330547 12917428295037298033995821)
              ·
                refine ⟨4844035610638986762748433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12917428295037298033995821 4844035610638986762748433)
                ·
                  refine ⟨3633026707979240072061325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4844035610638986762748433 3633026707979240072061325)
                  ·
                    refine ⟨1362385015492215027022997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3633026707979240072061325 1362385015492215027022997)
                    ·
                      rfl

theorem cell22_3979853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 3, 2, 3].length) (baseStart_3979853 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3979853 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3979853 prefixEnd_3979853 := by exact prefixLift 3979853
  have htrace : WordTrace (prefixWord ++ tailWord_3979853) baseStart_3979853 baseEnd_3979853 := by
    simpa [prefixWord, tailWord_3979853, baseEnd_3979853] using wordTrace_append hprefix tailTrace_3979853
  have hstable : (prefixWord ++ tailWord_3979853).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3979853).length < 2 ^ (prefixWord ++ tailWord_3979853).sum := by decide
  have hdescent : baseEnd_3979853 < baseStart_3979853 := by decide
  rcases family_descends (prefixWord ++ tailWord_3979853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3979864 : List Nat := [2, 1, 2, 2, 1, 2, 2, 4, 3, 3]
def baseStart_3979864 : Nat := 118140960795 + 3979864 * 2 ^ 59
def prefixEnd_3979864 : Nat := 4983230072969 + 3 ^ 40 * 3979864 * 2
def baseEnd_3979864 : Nat := 1362388781017014664997963

theorem tailTrace_3979864 : CollatzResearch.WordTrace tailWord_3979864 prefixEnd_3979864 1362388781017014664997963 := by
  unfold tailWord_3979864
  simp only [CollatzResearch.WordTrace]
  refine ⟨72578782626819954751049323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96771710169093273001399097 72578782626819954751049323)
  ·
    refine ⟨108868173940229932126573985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72578782626819954751049323 108868173940229932126573985)
    ·
      refine ⟨81651130455172449094930489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108868173940229932126573985 81651130455172449094930489)
      ·
        refine ⟨61238347841379336821197867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81651130455172449094930489 61238347841379336821197867)
        ·
          refine ⟨91857521762069005231796801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61238347841379336821197867 91857521762069005231796801)
          ·
            refine ⟨68893141321551753923847601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91857521762069005231796801 68893141321551753923847601)
            ·
              refine ⟨51669855991163815442885701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68893141321551753923847601 51669855991163815442885701)
              ·
                refine ⟨9688097998343215395541069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51669855991163815442885701 9688097998343215395541069)
                ·
                  refine ⟨3633036749378705773327901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9688097998343215395541069 3633036749378705773327901)
                  ·
                    refine ⟨1362388781017014664997963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3633036749378705773327901 1362388781017014664997963)
                    ·
                      rfl

theorem cell22_3979864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 4, 3, 3].length) (baseStart_3979864 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3979864 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3979864 prefixEnd_3979864 := by exact prefixLift 3979864
  have htrace : WordTrace (prefixWord ++ tailWord_3979864) baseStart_3979864 baseEnd_3979864 := by
    simpa [prefixWord, tailWord_3979864, baseEnd_3979864] using wordTrace_append hprefix tailTrace_3979864
  have hstable : (prefixWord ++ tailWord_3979864).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3979864).length < 2 ^ (prefixWord ++ tailWord_3979864).sum := by decide
  have hdescent : baseEnd_3979864 < baseStart_3979864 := by decide
  rcases family_descends (prefixWord ++ tailWord_3979864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3979870 : List Nat := [4, 4, 1, 2, 1, 1, 1, 2, 1, 5]
def baseStart_3979870 : Nat := 118140960795 + 3979870 * 2 ^ 59
def prefixEnd_3979870 : Nat := 4983230072969 + 3 ^ 40 * 3979870 * 2
def baseEnd_3979870 : Nat := 1362390834939632649347945

theorem tailTrace_3979870 : CollatzResearch.WordTrace tailWord_3979870 prefixEnd_3979870 1362390834939632649347945 := by
  unfold tailWord_3979870
  simp only [CollatzResearch.WordTrace]
  refine ⟨18144723011452271565852133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96771856061078781684544709 18144723011452271565852133)
  ·
    refine ⟨3402135564647300918597275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18144723011452271565852133 3402135564647300918597275)
    ·
      refine ⟨5103203346970951377895913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3402135564647300918597275 5103203346970951377895913)
      ·
        refine ⟨3827402510228213533421935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5103203346970951377895913 3827402510228213533421935)
        ·
          refine ⟨5741103765342320300132903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3827402510228213533421935 5741103765342320300132903)
          ·
            refine ⟨8611655648013480450199355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5741103765342320300132903 8611655648013480450199355)
            ·
              refine ⟨12917483472020220675299033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8611655648013480450199355 12917483472020220675299033)
              ·
                refine ⟨9688112604015165506474275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12917483472020220675299033 9688112604015165506474275)
                ·
                  refine ⟨14532168906022748259711413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9688112604015165506474275 14532168906022748259711413)
                  ·
                    refine ⟨1362390834939632649347945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14532168906022748259711413 1362390834939632649347945)
                    ·
                      rfl

theorem cell22_3979870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 2, 1, 5].length) (baseStart_3979870 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3979870 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3979870 prefixEnd_3979870 := by exact prefixLift 3979870
  have htrace : WordTrace (prefixWord ++ tailWord_3979870) baseStart_3979870 baseEnd_3979870 := by
    simpa [prefixWord, tailWord_3979870, baseEnd_3979870] using wordTrace_append hprefix tailTrace_3979870
  have hstable : (prefixWord ++ tailWord_3979870).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3979870).length < 2 ^ (prefixWord ++ tailWord_3979870).sum := by decide
  have hdescent : baseEnd_3979870 < baseStart_3979870 := by decide
  rcases family_descends (prefixWord ++ tailWord_3979870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3979881 : List Nat := [1, 2, 1, 1, 1, 4, 1, 7, 1, 3]
def baseStart_3979881 : Nat := 118140960795 + 3979881 * 2 ^ 59
def prefixEnd_3979881 : Nat := 4983230072969 + 3 ^ 40 * 3979881 * 2
def baseEnd_3979881 : Nat := 1362394600464432287322911

theorem tailTrace_3979881 : CollatzResearch.WordTrace tailWord_3979881 prefixEnd_3979881 1362394600464432287322911 := by
  unfold tailWord_3979881
  simp only [CollatzResearch.WordTrace]
  refine ⟨145158185294578321405467497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96772123529718880936978331 145158185294578321405467497)
  ·
    refine ⟨108868638970933741054100623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145158185294578321405467497 108868638970933741054100623)
    ·
      refine ⟨163302958456400611581150935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108868638970933741054100623 163302958456400611581150935)
      ·
        refine ⟨244954437684600917371726403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163302958456400611581150935 244954437684600917371726403)
        ·
          refine ⟨367431656526901376057589605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244954437684600917371726403 367431656526901376057589605)
          ·
            refine ⟨68893435598794008010798051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 367431656526901376057589605 68893435598794008010798051)
            ·
              refine ⟨103340153398191012016197077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68893435598794008010798051 103340153398191012016197077)
              ·
                refine ⟨2422034845270101844129619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 103340153398191012016197077 2422034845270101844129619)
                ·
                  refine ⟨3633052267905152766194429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2422034845270101844129619 3633052267905152766194429)
                  ·
                    refine ⟨1362394600464432287322911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3633052267905152766194429 1362394600464432287322911)
                    ·
                      rfl

theorem cell22_3979881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 7, 1, 3].length) (baseStart_3979881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3979881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3979881 prefixEnd_3979881 := by exact prefixLift 3979881
  have htrace : WordTrace (prefixWord ++ tailWord_3979881) baseStart_3979881 baseEnd_3979881 := by
    simpa [prefixWord, tailWord_3979881, baseEnd_3979881] using wordTrace_append hprefix tailTrace_3979881
  have hstable : (prefixWord ++ tailWord_3979881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3979881).length < 2 ^ (prefixWord ++ tailWord_3979881).sum := by decide
  have hdescent : baseEnd_3979881 < baseStart_3979881 := by decide
  rcases family_descends (prefixWord ++ tailWord_3979881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3979909 : List Nat := [1, 3, 1, 1, 4, 3, 1, 1, 2, 5]
def baseStart_3979909 : Nat := 118140960795 + 3979909 * 2 ^ 59
def prefixEnd_3979909 : Nat := 4983230072969 + 3 ^ 40 * 3979909 * 2
def baseEnd_3979909 : Nat := 1362404185436649547622825

theorem tailTrace_3979909 : CollatzResearch.WordTrace tailWord_3979909 prefixEnd_3979909 1362404185436649547622825 := by
  unfold tailWord_3979909
  simp only [CollatzResearch.WordTrace]
  refine ⟨145159206538476882187486781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96772804358984588124991187 145159206538476882187486781)
  ·
    refine ⟨54434702451928830820307543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145159206538476882187486781 54434702451928830820307543)
    ·
      refine ⟨81652053677893246230461315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54434702451928830820307543 81652053677893246230461315)
      ·
        refine ⟨122478080516839869345691973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81652053677893246230461315 122478080516839869345691973)
        ·
          refine ⟨22964640096907475502317245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 122478080516839869345691973 22964640096907475502317245)
          ·
            refine ⟨8611740036340303313368967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22964640096907475502317245 8611740036340303313368967)
            ·
              refine ⟨12917610054510454970053451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8611740036340303313368967 12917610054510454970053451)
              ·
                refine ⟨19376415081765682455080177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12917610054510454970053451 19376415081765682455080177)
                ·
                  refine ⟨14532311311324261841310133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19376415081765682455080177 14532311311324261841310133)
                  ·
                    refine ⟨1362404185436649547622825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14532311311324261841310133 1362404185436649547622825)
                    ·
                      rfl

theorem cell22_3979909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 1, 2, 5].length) (baseStart_3979909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3979909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3979909 prefixEnd_3979909 := by exact prefixLift 3979909
  have htrace : WordTrace (prefixWord ++ tailWord_3979909) baseStart_3979909 baseEnd_3979909 := by
    simpa [prefixWord, tailWord_3979909, baseEnd_3979909] using wordTrace_append hprefix tailTrace_3979909
  have hstable : (prefixWord ++ tailWord_3979909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3979909).length < 2 ^ (prefixWord ++ tailWord_3979909).sum := by decide
  have hdescent : baseEnd_3979909 < baseStart_3979909 := by decide
  rcases family_descends (prefixWord ++ tailWord_3979909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3980044 : List Nat := [2, 2, 1, 2, 2, 1, 1, 2, 4, 5]
def baseStart_3980044 : Nat := 118140960795 + 3980044 * 2 ^ 59
def prefixEnd_3980044 : Nat := 4983230072969 + 3 ^ 40 * 3980044 * 2
def baseEnd_3980044 : Nat := 1362450398695554195497411

theorem tailTrace_3980044 : CollatzResearch.WordTrace tailWord_3980044 prefixEnd_3980044 1362450398695554195497411 := by
  unfold tailWord_3980044
  simp only [CollatzResearch.WordTrace]
  refine ⟨72582065196493900121825593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96776086928658533495767457 72582065196493900121825593)
  ·
    refine ⟨54436548897370425091369195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72582065196493900121825593 54436548897370425091369195)
    ·
      refine ⟨81654823346055637637053793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54436548897370425091369195 81654823346055637637053793)
      ·
        refine ⟨61241117509541728227790345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81654823346055637637053793 61241117509541728227790345)
        ·
          refine ⟨45930838132156296170842759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61241117509541728227790345 45930838132156296170842759)
          ·
            refine ⟨68896257198234444256264139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45930838132156296170842759 68896257198234444256264139)
            ·
              refine ⟨103344385797351666384396209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68896257198234444256264139 103344385797351666384396209)
              ·
                refine ⟨77508289348013749788297157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103344385797351666384396209 77508289348013749788297157)
                ·
                  refine ⟨14532804252752578085305717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77508289348013749788297157 14532804252752578085305717)
                  ·
                    refine ⟨1362450398695554195497411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14532804252752578085305717 1362450398695554195497411)
                    ·
                      rfl

theorem cell22_3980044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 4, 5].length) (baseStart_3980044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3980044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3980044 prefixEnd_3980044 := by exact prefixLift 3980044
  have htrace : WordTrace (prefixWord ++ tailWord_3980044) baseStart_3980044 baseEnd_3980044 := by
    simpa [prefixWord, tailWord_3980044, baseEnd_3980044] using wordTrace_append hprefix tailTrace_3980044
  have hstable : (prefixWord ++ tailWord_3980044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3980044).length < 2 ^ (prefixWord ++ tailWord_3980044).sum := by decide
  have hdescent : baseEnd_3980044 < baseStart_3980044 := by decide
  rcases family_descends (prefixWord ++ tailWord_3980044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3980059 : List Nat := [1, 1, 1, 1, 1, 1, 4, 1, 7, 4]
def baseStart_3980059 : Nat := 118140960795 + 3980059 * 2 ^ 59
def prefixEnd_3980059 : Nat := 4983230072969 + 3 ^ 40 * 3980059 * 2
def baseEnd_3980059 : Nat := 1362455533502099156372365

theorem tailTrace_3980059 : CollatzResearch.WordTrace tailWord_3980059 prefixEnd_3980059 1362455533502099156372365 := by
  unfold tailWord_3980059
  simp only [CollatzResearch.WordTrace]
  refine ⟨145164677487933457805447231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96776451658622305203631487 145164677487933457805447231)
  ·
    refine ⟨217747016231900186708170847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145164677487933457805447231 217747016231900186708170847)
    ·
      refine ⟨326620524347850280062256271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217747016231900186708170847 326620524347850280062256271)
      ·
        refine ⟨489930786521775420093384407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 326620524347850280062256271 489930786521775420093384407)
        ·
          refine ⟨734896179782663130140076611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 489930786521775420093384407 734896179782663130140076611)
          ·
            refine ⟨1102344269673994695210114917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 734896179782663130140076611 1102344269673994695210114917)
            ·
              refine ⟨206689550563874005351896547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1102344269673994695210114917 206689550563874005351896547)
              ·
                refine ⟨310034325845811008027844821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 206689550563874005351896547 310034325845811008027844821)
                ·
                  refine ⟨7266429512011195500652613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 310034325845811008027844821 7266429512011195500652613)
                  ·
                    refine ⟨1362455533502099156372365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7266429512011195500652613 1362455533502099156372365)
                    ·
                      rfl

theorem cell22_3980059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 7, 4].length) (baseStart_3980059 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3980059 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3980059 prefixEnd_3980059 := by exact prefixLift 3980059
  have htrace : WordTrace (prefixWord ++ tailWord_3980059) baseStart_3980059 baseEnd_3980059 := by
    simpa [prefixWord, tailWord_3980059, baseEnd_3980059] using wordTrace_append hprefix tailTrace_3980059
  have hstable : (prefixWord ++ tailWord_3980059).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3980059).length < 2 ^ (prefixWord ++ tailWord_3980059).sum := by decide
  have hdescent : baseEnd_3980059 < baseStart_3980059 := by decide
  rcases family_descends (prefixWord ++ tailWord_3980059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3980078 : List Nat := [4, 1, 3, 2, 1, 2, 1, 1, 2, 5]
def baseStart_3980078 : Nat := 118140960795 + 3980078 * 2 ^ 59
def prefixEnd_3980078 : Nat := 4983230072969 + 3 ^ 40 * 3980078 * 2
def baseEnd_3980078 : Nat := 1362462037590389440147307

theorem tailTrace_3980078 : CollatzResearch.WordTrace tailWord_3980078 prefixEnd_3980078 1362462037590389440147307 := by
  unfold tailWord_3980078
  simp only [CollatzResearch.WordTrace]
  refine ⟨18145671309358078006298611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96776913649909749366925925 18145671309358078006298611)
  ·
    refine ⟨27218506964037117009447917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18145671309358078006298611 27218506964037117009447917)
    ·
      refine ⟨10206940111513918878542969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27218506964037117009447917 10206940111513918878542969)
      ·
        refine ⟨7655205083635439158907227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10206940111513918878542969 7655205083635439158907227)
        ·
          refine ⟨11482807625453158738360841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7655205083635439158907227 11482807625453158738360841)
          ·
            refine ⟨8612105719089869053770631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11482807625453158738360841 8612105719089869053770631)
            ·
              refine ⟨12918158578634803580655947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8612105719089869053770631 12918158578634803580655947)
              ·
                refine ⟨19377237867952205370983921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12918158578634803580655947 19377237867952205370983921)
                ·
                  refine ⟨14532928400964154028237941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19377237867952205370983921 14532928400964154028237941)
                  ·
                    refine ⟨1362462037590389440147307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14532928400964154028237941 1362462037590389440147307)
                    ·
                      rfl

theorem cell22_3980078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 1, 2, 5].length) (baseStart_3980078 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3980078 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3980078 prefixEnd_3980078 := by exact prefixLift 3980078
  have htrace : WordTrace (prefixWord ++ tailWord_3980078) baseStart_3980078 baseEnd_3980078 := by
    simpa [prefixWord, tailWord_3980078, baseEnd_3980078] using wordTrace_append hprefix tailTrace_3980078
  have hstable : (prefixWord ++ tailWord_3980078).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3980078).length < 2 ^ (prefixWord ++ tailWord_3980078).sum := by decide
  have hdescent : baseEnd_3980078 < baseStart_3980078 := by decide
  rcases family_descends (prefixWord ++ tailWord_3980078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3980108 : List Nat := [2, 2, 1, 3, 3, 1, 1, 5, 4]
def baseStart_3980108 : Nat := 118140960795 + 3980108 * 2 ^ 59
def prefixEnd_3980108 : Nat := 4983230072969 + 3 ^ 40 * 3980108 * 2
def baseEnd_3980108 : Nat := 454157435734493120632405

theorem tailTrace_3980108 : CollatzResearch.WordTrace tailWord_3980108 prefixEnd_3980108 454157435734493120632405 := by
  unfold tailWord_3980108
  simp only [CollatzResearch.WordTrace]
  refine ⟨72583232332377969586990489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96777643109837292782653985 72583232332377969586990489)
  ·
    refine ⟨54437424249283477190242867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72583232332377969586990489 54437424249283477190242867)
    ·
      refine ⟨81656136373925215785364301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54437424249283477190242867 81656136373925215785364301)
      ·
        refine ⟨30621051140221955919511613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81656136373925215785364301 30621051140221955919511613)
        ·
          refine ⟨11482894177583233469816855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30621051140221955919511613 11482894177583233469816855)
          ·
            refine ⟨17224341266374850204725283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11482894177583233469816855 17224341266374850204725283)
            ·
              refine ⟨25836511899562275307087925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17224341266374850204725283 25836511899562275307087925)
              ·
                refine ⟨2422172990583963310039493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25836511899562275307087925 2422172990583963310039493)
                ·
                  refine ⟨454157435734493120632405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2422172990583963310039493 454157435734493120632405)
                  ·
                    rfl

theorem cell22_3980108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 5, 4].length) (baseStart_3980108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3980108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3980108 prefixEnd_3980108 := by exact prefixLift 3980108
  have htrace : WordTrace (prefixWord ++ tailWord_3980108) baseStart_3980108 baseEnd_3980108 := by
    simpa [prefixWord, tailWord_3980108, baseEnd_3980108] using wordTrace_append hprefix tailTrace_3980108
  have hstable : (prefixWord ++ tailWord_3980108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3980108).length < 2 ^ (prefixWord ++ tailWord_3980108).sum := by decide
  have hdescent : baseEnd_3980108 < baseStart_3980108 := by decide
  rcases family_descends (prefixWord ++ tailWord_3980108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3980140 : List Nat := [2, 2, 1, 1, 4, 1, 5, 1, 2, 3]
def baseStart_3980140 : Nat := 118140960795 + 3980140 * 2 ^ 59
def prefixEnd_3980140 : Nat := 4983230072969 + 3 ^ 40 * 3980140 * 2
def baseEnd_3980140 : Nat := 1362483261457441945097117

theorem tailTrace_3980140 : CollatzResearch.WordTrace tailWord_3980140 prefixEnd_3980140 1362483261457441945097117 := by
  unfold tailWord_3980140
  simp only [CollatzResearch.WordTrace]
  refine ⟨72583815900320004319572937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96778421200426672426097249 72583815900320004319572937)
  ·
    refine ⟨54437861925240003239679703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72583815900320004319572937 54437861925240003239679703)
    ·
      refine ⟨81656792887860004859519555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54437861925240003239679703 81656792887860004859519555)
      ·
        refine ⟨122485189331790007289279333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81656792887860004859519555 122485189331790007289279333)
        ·
          refine ⟨22965972999710626366739875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 122485189331790007289279333 22965972999710626366739875)
          ·
            refine ⟨34448959499565939550109813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22965972999710626366739875 34448959499565939550109813)
            ·
              refine ⟨3229589953084306832822795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34448959499565939550109813 3229589953084306832822795)
              ·
                refine ⟨4844384929626460249234193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3229589953084306832822795 4844384929626460249234193)
                ·
                  refine ⟨3633288697219845186925645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4844384929626460249234193 3633288697219845186925645)
                  ·
                    refine ⟨1362483261457441945097117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3633288697219845186925645 1362483261457441945097117)
                    ·
                      rfl

theorem cell22_3980140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 3].length) (baseStart_3980140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3980140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3980140 prefixEnd_3980140 := by exact prefixLift 3980140
  have htrace : WordTrace (prefixWord ++ tailWord_3980140) baseStart_3980140 baseEnd_3980140 := by
    simpa [prefixWord, tailWord_3980140, baseEnd_3980140] using wordTrace_append hprefix tailTrace_3980140
  have hstable : (prefixWord ++ tailWord_3980140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3980140).length < 2 ^ (prefixWord ++ tailWord_3980140).sum := by decide
  have hdescent : baseEnd_3980140 < baseStart_3980140 := by decide
  rcases family_descends (prefixWord ++ tailWord_3980140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3980153 : List Nat := [1, 2, 1, 3, 2, 5, 2, 6]
def baseStart_3980153 : Nat := 118140960795 + 3980153 * 2 ^ 59
def prefixEnd_3980153 : Nat := 4983230072969 + 3 ^ 40 * 3980153 * 2
def baseEnd_3980153 : Nat := 151387523513679360502453

theorem tailTrace_3980153 : CollatzResearch.WordTrace tailWord_3980153 prefixEnd_3980153 151387523513679360502453 := by
  unfold tailWord_3980153
  simp only [CollatzResearch.WordTrace]
  refine ⟨145168105949592911859369113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96778737299728607906246075 145168105949592911859369113)
  ·
    refine ⟨108876079462194683894526835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145168105949592911859369113 108876079462194683894526835)
    ·
      refine ⟨163314119193292025841790253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108876079462194683894526835 163314119193292025841790253)
      ·
        refine ⟨61242794697484509690671345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163314119193292025841790253 61242794697484509690671345)
        ·
          refine ⟨45932096023113382268003509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61242794697484509690671345 45932096023113382268003509)
          ·
            refine ⟨4306134002166879587625329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 45932096023113382268003509 4306134002166879587625329)
            ·
              refine ⟨3229600501625159690718997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4306134002166879587625329 3229600501625159690718997)
              ·
                refine ⟨151387523513679360502453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3229600501625159690718997 151387523513679360502453)
                ·
                  rfl

theorem cell22_3980153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 2, 6].length) (baseStart_3980153 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3980153 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3980153 prefixEnd_3980153 := by exact prefixLift 3980153
  have htrace : WordTrace (prefixWord ++ tailWord_3980153) baseStart_3980153 baseEnd_3980153 := by
    simpa [prefixWord, tailWord_3980153, baseEnd_3980153] using wordTrace_append hprefix tailTrace_3980153
  have hstable : (prefixWord ++ tailWord_3980153).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3980153).length < 2 ^ (prefixWord ++ tailWord_3980153).sum := by decide
  have hdescent : baseEnd_3980153 < baseStart_3980153 := by decide
  rcases family_descends (prefixWord ++ tailWord_3980153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3980181 : List Nat := [1, 3, 2, 1, 1, 4, 2, 1, 7]
def baseStart_3980181 : Nat := 118140960795 + 3980181 * 2 ^ 59
def prefixEnd_3980181 : Nat := 4983230072969 + 3 ^ 40 * 3980181 * 2
def baseEnd_3980181 : Nat := 454165765531777168273997

theorem tailTrace_3980181 : CollatzResearch.WordTrace tailWord_3980181 prefixEnd_3980181 454165765531777168273997 := by
  unfold tailWord_3980181
  simp only [CollatzResearch.WordTrace]
  refine ⟨145169127193491472641388397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96779418128994315094258931 145169127193491472641388397)
  ·
    refine ⟨54438422697559302240520649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145169127193491472641388397 54438422697559302240520649)
    ·
      refine ⟨40828817023169476680390487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54438422697559302240520649 40828817023169476680390487)
      ·
        refine ⟨61243225534754215020585731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40828817023169476680390487 61243225534754215020585731)
        ·
          refine ⟨91864838302131322530878597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61243225534754215020585731 91864838302131322530878597)
          ·
            refine ⟨17224657181649622974539737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 91864838302131322530878597 17224657181649622974539737)
            ·
              refine ⟨12918492886237217230904803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17224657181649622974539737 12918492886237217230904803)
              ·
                refine ⟨19377739329355825846357205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12918492886237217230904803 19377739329355825846357205)
                ·
                  refine ⟨454165765531777168273997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19377739329355825846357205 454165765531777168273997)
                  ·
                    rfl

theorem cell22_3980181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 1, 7].length) (baseStart_3980181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3980181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3980181 prefixEnd_3980181 := by exact prefixLift 3980181
  have htrace : WordTrace (prefixWord ++ tailWord_3980181) baseStart_3980181 baseEnd_3980181 := by
    simpa [prefixWord, tailWord_3980181, baseEnd_3980181] using wordTrace_append hprefix tailTrace_3980181
  have hstable : (prefixWord ++ tailWord_3980181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3980181).length < 2 ^ (prefixWord ++ tailWord_3980181).sum := by decide
  have hdescent : baseEnd_3980181 < baseStart_3980181 := by decide
  rcases family_descends (prefixWord ++ tailWord_3980181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3980196 : List Nat := [2, 3, 1, 2, 1, 2, 2, 1, 1, 7]
def baseStart_3980196 : Nat := 118140960795 + 3980196 * 2 ^ 59
def prefixEnd_3980196 : Nat := 4983230072969 + 3 ^ 40 * 3980196 * 2
def baseEnd_3980196 : Nat := 1362502431401876465696945

theorem tailTrace_3980196 : CollatzResearch.WordTrace tailWord_3980196 prefixEnd_3980196 1362502431401876465696945 := by
  unfold tailWord_3980196
  simp only [CollatzResearch.WordTrace]
  refine ⟨72584837144218565101592221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96779782858958086802122961 72584837144218565101592221)
  ·
    refine ⟨27219313929081961913097083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72584837144218565101592221 27219313929081961913097083)
    ·
      refine ⟨40828970893622942869645625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27219313929081961913097083 40828970893622942869645625)
      ·
        refine ⟨30621728170217207152234219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40828970893622942869645625 30621728170217207152234219)
        ·
          refine ⟨45932592255325810728351329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30621728170217207152234219 45932592255325810728351329)
          ·
            refine ⟨34449444191494358046263497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45932592255325810728351329 34449444191494358046263497)
            ·
              refine ⟨25837083143620768534697623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34449444191494358046263497 25837083143620768534697623)
              ·
                refine ⟨38755624715431152802046435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25837083143620768534697623 38755624715431152802046435)
                ·
                  refine ⟨58133437073146729203069653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38755624715431152802046435 58133437073146729203069653)
                  ·
                    refine ⟨1362502431401876465696945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58133437073146729203069653 1362502431401876465696945)
                    ·
                      rfl

theorem cell22_3980196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 1, 1, 7].length) (baseStart_3980196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3980196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3980196 prefixEnd_3980196 := by exact prefixLift 3980196
  have htrace : WordTrace (prefixWord ++ tailWord_3980196) baseStart_3980196 baseEnd_3980196 := by
    simpa [prefixWord, tailWord_3980196, baseEnd_3980196] using wordTrace_append hprefix tailTrace_3980196
  have hstable : (prefixWord ++ tailWord_3980196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3980196).length < 2 ^ (prefixWord ++ tailWord_3980196).sum := by decide
  have hdescent : baseEnd_3980196 < baseStart_3980196 := by decide
  rcases family_descends (prefixWord ++ tailWord_3980196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3980241 : List Nat := [1, 2, 2, 1, 2, 1, 3, 2, 3, 5]
def baseStart_3980241 : Nat := 118140960795 + 3980241 * 2 ^ 59
def prefixEnd_3980241 : Nat := 4983230072969 + 3 ^ 40 * 3980241 * 2
def baseEnd_3980241 : Nat := 1362517835821511348321807

theorem tailTrace_3980241 : CollatzResearch.WordTrace tailWord_3980241 prefixEnd_3980241 1362517835821511348321807 := by
  unfold tailWord_3980241
  simp only [CollatzResearch.WordTrace]
  refine ⟨145171315573274102888572577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96780877048849401925715051 145171315573274102888572577)
  ·
    refine ⟨108878486679955577166429433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145171315573274102888572577 108878486679955577166429433)
    ·
      refine ⟨81658865009966682874822075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108878486679955577166429433 81658865009966682874822075)
      ·
        refine ⟨122488297514950024312233113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81658865009966682874822075 122488297514950024312233113)
        ·
          refine ⟨91866223136212518234174835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122488297514950024312233113 91866223136212518234174835)
          ·
            refine ⟨137799334704318777351262253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91866223136212518234174835 137799334704318777351262253)
            ·
              refine ⟨51674750514119541506723345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 137799334704318777351262253 51674750514119541506723345)
              ·
                refine ⟨38756062885589656130042509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51674750514119541506723345 38756062885589656130042509)
                ·
                  refine ⟨14533523582096121048765941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38756062885589656130042509 14533523582096121048765941)
                  ·
                    refine ⟨1362517835821511348321807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14533523582096121048765941 1362517835821511348321807)
                    ·
                      rfl

theorem cell22_3980241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 2, 3, 5].length) (baseStart_3980241 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3980241 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3980241 prefixEnd_3980241 := by exact prefixLift 3980241
  have htrace : WordTrace (prefixWord ++ tailWord_3980241) baseStart_3980241 baseEnd_3980241 := by
    simpa [prefixWord, tailWord_3980241, baseEnd_3980241] using wordTrace_append hprefix tailTrace_3980241
  have hstable : (prefixWord ++ tailWord_3980241).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3980241).length < 2 ^ (prefixWord ++ tailWord_3980241).sum := by decide
  have hdescent : baseEnd_3980241 < baseStart_3980241 := by decide
  rcases family_descends (prefixWord ++ tailWord_3980241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3980273 : List Nat := [1, 2, 2, 2, 4, 2, 1, 1, 1, 6]
def baseStart_3980273 : Nat := 118140960795 + 3980273 * 2 ^ 59
def prefixEnd_3980273 : Nat := 4983230072969 + 3 ^ 40 * 3980273 * 2
def baseEnd_3980273 : Nat := 1362528790075473931521709

theorem tailTrace_3980273 : CollatzResearch.WordTrace tailWord_3980273 prefixEnd_3980273 1362528790075473931521709 := by
  unfold tailWord_3980273
  simp only [CollatzResearch.WordTrace]
  refine ⟨145172482709158172353737473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96781655139438781569158315 145172482709158172353737473)
  ·
    refine ⟨108879362031868629265303105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145172482709158172353737473 108879362031868629265303105)
    ·
      refine ⟨81659521523901471948977329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108879362031868629265303105 81659521523901471948977329)
      ·
        refine ⟨61244641142926103961732997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81659521523901471948977329 61244641142926103961732997)
        ·
          refine ⟨11483370214298644492824937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61244641142926103961732997 11483370214298644492824937)
          ·
            refine ⟨8612527660723983369618703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11483370214298644492824937 8612527660723983369618703)
            ·
              refine ⟨12918791491085975054428055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8612527660723983369618703 12918791491085975054428055)
              ·
                refine ⟨19378187236628962581642083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12918791491085975054428055 19378187236628962581642083)
                ·
                  refine ⟨29067280854943443872463125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19378187236628962581642083 29067280854943443872463125)
                  ·
                    refine ⟨1362528790075473931521709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29067280854943443872463125 1362528790075473931521709)
                    ·
                      rfl

theorem cell22_3980273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 1, 1, 6].length) (baseStart_3980273 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3980273 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3980273 prefixEnd_3980273 := by exact prefixLift 3980273
  have htrace : WordTrace (prefixWord ++ tailWord_3980273) baseStart_3980273 baseEnd_3980273 := by
    simpa [prefixWord, tailWord_3980273, baseEnd_3980273] using wordTrace_append hprefix tailTrace_3980273
  have hstable : (prefixWord ++ tailWord_3980273).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3980273).length < 2 ^ (prefixWord ++ tailWord_3980273).sum := by decide
  have hdescent : baseEnd_3980273 < baseStart_3980273 := by decide
  rcases family_descends (prefixWord ++ tailWord_3980273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3980350 : List Nat := [4, 2, 1, 3, 1, 1, 2, 1, 7]
def baseStart_3980350 : Nat := 118140960795 + 3980350 * 2 ^ 59
def prefixEnd_3980350 : Nat := 4983230072969 + 3 ^ 40 * 3980350 * 2
def baseEnd_3980350 : Nat := 454185049583023799115491

theorem tailTrace_3980350 : CollatzResearch.WordTrace tailWord_3980350 prefixEnd_3980350 454185049583023799115491 := by
  unfold tailWord_3980350
  simp only [CollatzResearch.WordTrace]
  refine ⟨18146911391234901813036313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96783527419919476336193669 18146911391234901813036313)
  ·
    refine ⟨13610183543426176359777235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18146911391234901813036313 13610183543426176359777235)
    ·
      refine ⟨20415275315139264539665853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13610183543426176359777235 20415275315139264539665853)
      ·
        refine ⟨7655728243177224202374695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20415275315139264539665853 7655728243177224202374695)
        ·
          refine ⟨11483592364765836303562043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7655728243177224202374695 11483592364765836303562043)
          ·
            refine ⟨17225388547148754455343065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11483592364765836303562043 17225388547148754455343065)
            ·
              refine ⟨12919041410361565841507299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17225388547148754455343065 12919041410361565841507299)
              ·
                refine ⟨19378562115542348762260949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12919041410361565841507299 19378562115542348762260949)
                ·
                  refine ⟨454185049583023799115491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19378562115542348762260949 454185049583023799115491)
                  ·
                    rfl

theorem cell22_3980350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 1, 7].length) (baseStart_3980350 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3980350 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3980350 prefixEnd_3980350 := by exact prefixLift 3980350
  have htrace : WordTrace (prefixWord ++ tailWord_3980350) baseStart_3980350 baseEnd_3980350 := by
    simpa [prefixWord, tailWord_3980350, baseEnd_3980350] using wordTrace_append hprefix tailTrace_3980350
  have hstable : (prefixWord ++ tailWord_3980350).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3980350).length < 2 ^ (prefixWord ++ tailWord_3980350).sum := by decide
  have hdescent : baseEnd_3980350 < baseStart_3980350 := by decide
  rcases family_descends (prefixWord ++ tailWord_3980350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3980380 : List Nat := [2, 2, 4, 1, 1, 1, 3, 1, 3, 4]
def baseStart_3980380 : Nat := 118140960795 + 3980380 * 2 ^ 59
def prefixEnd_3980380 : Nat := 4983230072969 + 3 ^ 40 * 3980380 * 2
def baseEnd_3980380 : Nat := 1362565418362161319096381

theorem tailTrace_3980380 : CollatzResearch.WordTrace tailWord_3980380 prefixEnd_3980380 1362565418362161319096381 := by
  unfold tailWord_3980380
  simp only [CollatzResearch.WordTrace]
  refine ⟨72588192659885264813941297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96784256879847019751921729 72588192659885264813941297)
  ·
    refine ⟨54441144494913948610455973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72588192659885264813941297 54441144494913948610455973)
    ·
      refine ⟨10207714592796365364460495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54441144494913948610455973 10207714592796365364460495)
      ·
        refine ⟨15311571889194548046690743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10207714592796365364460495 15311571889194548046690743)
        ·
          refine ⟨22967357833791822070036115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15311571889194548046690743 22967357833791822070036115)
          ·
            refine ⟨34451036750687733105054173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22967357833791822070036115 34451036750687733105054173)
            ·
              refine ⟨12919138781507899914395315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34451036750687733105054173 12919138781507899914395315)
              ·
                refine ⟨19378708172261849871592973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12919138781507899914395315 19378708172261849871592973)
                ·
                  refine ⟨7267015564598193701847365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19378708172261849871592973 7267015564598193701847365)
                  ·
                    refine ⟨1362565418362161319096381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7267015564598193701847365 1362565418362161319096381)
                    ·
                      rfl

theorem cell22_3980380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 1, 3, 4].length) (baseStart_3980380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3980380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3980380 prefixEnd_3980380 := by exact prefixLift 3980380
  have htrace : WordTrace (prefixWord ++ tailWord_3980380) baseStart_3980380 baseEnd_3980380 := by
    simpa [prefixWord, tailWord_3980380, baseEnd_3980380] using wordTrace_append hprefix tailTrace_3980380
  have hstable : (prefixWord ++ tailWord_3980380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3980380).length < 2 ^ (prefixWord ++ tailWord_3980380).sum := by decide
  have hdescent : baseEnd_3980380 < baseStart_3980380 := by decide
  rcases family_descends (prefixWord ++ tailWord_3980380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3980393 : List Nat := [1, 2, 1, 1, 1, 6, 1, 1, 3, 5]
def baseStart_3980393 : Nat := 118140960795 + 3980393 * 2 ^ 59
def prefixEnd_3980393 : Nat := 4983230072969 + 3 ^ 40 * 3980393 * 2
def baseEnd_3980393 : Nat := 1362569868527833618521341

theorem tailTrace_3980393 : CollatzResearch.WordTrace tailWord_3980393 prefixEnd_3980393 1362569868527833618521341 := by
  unfold tailWord_3980393
  simp only [CollatzResearch.WordTrace]
  refine ⟨145176859468723432848105833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96784572979148955232070555 145176859468723432848105833)
  ·
    refine ⟨108882644601542574636079375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145176859468723432848105833 108882644601542574636079375)
    ·
      refine ⟨163323966902313861954119063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108882644601542574636079375 163323966902313861954119063)
      ·
        refine ⟨244985950353470792931178595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163323966902313861954119063 244985950353470792931178595)
        ·
          refine ⟨367478925530206189396767893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244985950353470792931178595 367478925530206189396767893)
          ·
            refine ⟨17225574634228415127973495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 367478925530206189396767893 17225574634228415127973495)
            ·
              refine ⟨25838361951342622691960243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17225574634228415127973495 25838361951342622691960243)
              ·
                refine ⟨38757542927013934037940365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25838361951342622691960243 38757542927013934037940365)
                ·
                  refine ⟨14534078597630225264227637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38757542927013934037940365 14534078597630225264227637)
                  ·
                    refine ⟨1362569868527833618521341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14534078597630225264227637 1362569868527833618521341)
                    ·
                      rfl

theorem cell22_3980393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 1, 3, 5].length) (baseStart_3980393 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3980393 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3980393 prefixEnd_3980393 := by exact prefixLift 3980393
  have htrace : WordTrace (prefixWord ++ tailWord_3980393) baseStart_3980393 baseEnd_3980393 := by
    simpa [prefixWord, tailWord_3980393, baseEnd_3980393] using wordTrace_append hprefix tailTrace_3980393
  have hstable : (prefixWord ++ tailWord_3980393).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3980393).length < 2 ^ (prefixWord ++ tailWord_3980393).sum := by decide
  have hdescent : baseEnd_3980393 < baseStart_3980393 := by decide
  rcases family_descends (prefixWord ++ tailWord_3980393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3980405 : List Nat := [1, 3, 4, 3, 2, 1, 2, 2, 1, 3]
def baseStart_3980405 : Nat := 118140960795 + 3980405 * 2 ^ 59
def prefixEnd_3980405 : Nat := 4983230072969 + 3 ^ 40 * 3980405 * 2
def baseEnd_3980405 : Nat := 1362573976373069587221305

theorem tailTrace_3980405 : CollatzResearch.WordTrace tailWord_3980405 prefixEnd_3980405 1362573976373069587221305 := by
  unfold tailWord_3980405
  simp only [CollatzResearch.WordTrace]
  refine ⟨145177297144679958897542669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96784864763119972598361779 145177297144679958897542669)
  ·
    refine ⟨54441486429254984586578501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145177297144679958897542669 54441486429254984586578501)
    ·
      refine ⟨10207778705485309609983469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54441486429254984586578501 10207778705485309609983469)
      ·
        refine ⟨3827917014556991103743801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10207778705485309609983469 3827917014556991103743801)
        ·
          refine ⟨2870937760917743327807851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3827917014556991103743801 2870937760917743327807851)
          ·
            refine ⟨4306406641376614991711777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2870937760917743327807851 4306406641376614991711777)
            ·
              refine ⟨3229804981032461243783833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4306406641376614991711777 3229804981032461243783833)
              ·
                refine ⟨2422353735774345932837875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3229804981032461243783833 2422353735774345932837875)
                ·
                  refine ⟨3633530603661518899256813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2422353735774345932837875 3633530603661518899256813)
                  ·
                    refine ⟨1362573976373069587221305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3633530603661518899256813 1362573976373069587221305)
                    ·
                      rfl

theorem cell22_3980405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 2, 2, 1, 3].length) (baseStart_3980405 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3980405 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3980405 prefixEnd_3980405 := by exact prefixLift 3980405
  have htrace : WordTrace (prefixWord ++ tailWord_3980405) baseStart_3980405 baseEnd_3980405 := by
    simpa [prefixWord, tailWord_3980405, baseEnd_3980405] using wordTrace_append hprefix tailTrace_3980405
  have hstable : (prefixWord ++ tailWord_3980405).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3980405).length < 2 ^ (prefixWord ++ tailWord_3980405).sum := by decide
  have hdescent : baseEnd_3980405 < baseStart_3980405 := by decide
  rcases family_descends (prefixWord ++ tailWord_3980405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3980442 : List Nat := [3, 1, 1, 5, 1, 1, 3, 1, 2, 4]
def baseStart_3980442 : Nat := 118140960795 + 3980442 * 2 ^ 59
def prefixEnd_3980442 : Nat := 4983230072969 + 3 ^ 40 * 3980442 * 2
def baseEnd_3980442 : Nat := 1362586642229213824046191

theorem tailTrace_3980442 : CollatzResearch.WordTrace tailWord_3980442 prefixEnd_3980442 1362586642229213824046191 := by
  unfold tailWord_3980442
  simp only [CollatzResearch.WordTrace]
  refine ⟨36294661661386478554159895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96785764430363942811093053 36294661661386478554159895)
  ·
    refine ⟨54441992492079717831239843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36294661661386478554159895 54441992492079717831239843)
    ·
      refine ⟨81662988738119576746859765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54441992492079717831239843 81662988738119576746859765)
      ·
        refine ⟨7655905194198710320018103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 81662988738119576746859765 7655905194198710320018103)
        ·
          refine ⟨11483857791298065480027155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7655905194198710320018103 11483857791298065480027155)
          ·
            refine ⟨17225786686947098220040733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11483857791298065480027155 17225786686947098220040733)
            ·
              refine ⟨6459670007605161832515275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17225786686947098220040733 6459670007605161832515275)
              ·
                refine ⟨9689505011407742748772913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6459670007605161832515275 9689505011407742748772913)
                ·
                  refine ⟨7267128758555807061579685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9689505011407742748772913 7267128758555807061579685)
                  ·
                    refine ⟨1362586642229213824046191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7267128758555807061579685 1362586642229213824046191)
                    ·
                      rfl

theorem cell22_3980442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 3, 1, 2, 4].length) (baseStart_3980442 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3980442 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3980442 prefixEnd_3980442 := by exact prefixLift 3980442
  have htrace : WordTrace (prefixWord ++ tailWord_3980442) baseStart_3980442 baseEnd_3980442 := by
    simpa [prefixWord, tailWord_3980442, baseEnd_3980442] using wordTrace_append hprefix tailTrace_3980442
  have hstable : (prefixWord ++ tailWord_3980442).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3980442).length < 2 ^ (prefixWord ++ tailWord_3980442).sum := by decide
  have hdescent : baseEnd_3980442 < baseStart_3980442 := by decide
  rcases family_descends (prefixWord ++ tailWord_3980442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3980461 : List Nat := [1, 5, 2, 1, 3, 2, 1, 2, 2, 3]
def baseStart_3980461 : Nat := 118140960795 + 3980461 * 2 ^ 59
def prefixEnd_3980461 : Nat := 4983230072969 + 3 ^ 40 * 3980461 * 2
def baseEnd_3980461 : Nat := 1362593146317504107821133

theorem tailTrace_3980461 : CollatzResearch.WordTrace tailWord_3980461 prefixEnd_3980461 1362593146317504107821133 := by
  unfold tailWord_3980461
  simp only [CollatzResearch.WordTrace]
  refine ⟨145179339632477080461581237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96786226421651386974387491 145179339632477080461581237)
  ·
    refine ⟨13610563090544726293273241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 145179339632477080461581237 13610563090544726293273241)
    ·
      refine ⟨10207922317908544719954931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13610563090544726293273241 10207922317908544719954931)
      ·
        refine ⟨15311883476862817079932397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10207922317908544719954931 15311883476862817079932397)
        ·
          refine ⟨5741956303823556404974649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15311883476862817079932397 5741956303823556404974649)
          ·
            refine ⟨4306467227867667303730987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5741956303823556404974649 4306467227867667303730987)
            ·
              refine ⟨6459700841801500955596481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4306467227867667303730987 6459700841801500955596481)
              ·
                refine ⟨4844775631351125716697361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6459700841801500955596481 4844775631351125716697361)
                ·
                  refine ⟨3633581723513344287523021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4844775631351125716697361 3633581723513344287523021)
                  ·
                    refine ⟨1362593146317504107821133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3633581723513344287523021 1362593146317504107821133)
                    ·
                      rfl

theorem cell22_3980461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 1, 2, 2, 3].length) (baseStart_3980461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3980461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3980461 prefixEnd_3980461 := by exact prefixLift 3980461
  have htrace : WordTrace (prefixWord ++ tailWord_3980461) baseStart_3980461 baseEnd_3980461 := by
    simpa [prefixWord, tailWord_3980461, baseEnd_3980461] using wordTrace_append hprefix tailTrace_3980461
  have hstable : (prefixWord ++ tailWord_3980461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3980461).length < 2 ^ (prefixWord ++ tailWord_3980461).sum := by decide
  have hdescent : baseEnd_3980461 < baseStart_3980461 := by decide
  rcases family_descends (prefixWord ++ tailWord_3980461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3980483 : List Nat := [1, 1, 1, 3, 1, 1, 1, 5, 1, 7]
def baseStart_3980483 : Nat := 118140960795 + 3980483 * 2 ^ 59
def prefixEnd_3980483 : Nat := 4983230072969 + 3 ^ 40 * 3980483 * 2
def baseEnd_3980483 : Nat := 1362600677367103383771065

theorem tailTrace_3980483 : CollatzResearch.WordTrace tailWord_3980483 prefixEnd_3980483 1362600677367103383771065 := by
  unfold tailWord_3980483
  simp only [CollatzResearch.WordTrace]
  refine ⟨145180142038397378218882103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96786761358931585479254735 145180142038397378218882103)
  ·
    refine ⟨217770213057596067328323155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145180142038397378218882103 217770213057596067328323155)
    ·
      refine ⟨326655319586394100992484733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217770213057596067328323155 326655319586394100992484733)
      ·
        refine ⟨122495744844897787872181775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 326655319586394100992484733 122495744844897787872181775)
        ·
          refine ⟨183743617267346681808272663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122495744844897787872181775 183743617267346681808272663)
          ·
            refine ⟨275615425901020022712408995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183743617267346681808272663 275615425901020022712408995)
            ·
              refine ⟨413423138851530034068613493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 275615425901020022712408995 413423138851530034068613493)
              ·
                refine ⟨38758419267330940693932515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 413423138851530034068613493 38758419267330940693932515)
                ·
                  refine ⟨58137628900996411040898773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38758419267330940693932515 58137628900996411040898773)
                  ·
                    refine ⟨1362600677367103383771065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58137628900996411040898773 1362600677367103383771065)
                    ·
                      rfl

theorem cell22_3980483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 5, 1, 7].length) (baseStart_3980483 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3980483 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3980483 prefixEnd_3980483 := by exact prefixLift 3980483
  have htrace : WordTrace (prefixWord ++ tailWord_3980483) baseStart_3980483 baseEnd_3980483 := by
    simpa [prefixWord, tailWord_3980483, baseEnd_3980483] using wordTrace_append hprefix tailTrace_3980483
  have hstable : (prefixWord ++ tailWord_3980483).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3980483).length < 2 ^ (prefixWord ++ tailWord_3980483).sum := by decide
  have hdescent : baseEnd_3980483 < baseStart_3980483 := by decide
  rcases family_descends (prefixWord ++ tailWord_3980483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3980575 : List Nat := [1, 1, 2, 4, 4, 10]
def baseStart_3980575 : Nat := 118140960795 + 3980575 * 2 ^ 59
def prefixEnd_3980575 : Nat := 4983230072969 + 3 ^ 40 * 3980575 * 2
def baseEnd_3980575 : Nat := 16822619393175874203343

theorem tailTrace_3980575 : CollatzResearch.WordTrace tailWord_3980575 prefixEnd_3980575 16822619393175874203343 := by
  unfold tailWord_3980575
  simp only [CollatzResearch.WordTrace]
  refine ⟨145183497554064077931231179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96788998369376051954154119 145183497554064077931231179)
  ·
    refine ⟨217775246331096116896846769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145183497554064077931231179 217775246331096116896846769)
    ·
      refine ⟨163331434748322087672635077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217775246331096116896846769 163331434748322087672635077)
      ·
        refine ⟨30624644015310391438619077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 163331434748322087672635077 30624644015310391438619077)
        ·
          refine ⟨5742120752870698394741077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30624644015310391438619077 5742120752870698394741077)
          ·
            refine ⟨16822619393175874203343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5742120752870698394741077 16822619393175874203343)
            ·
              rfl

theorem cell22_3980575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 10].length) (baseStart_3980575 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3980575 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3980575 prefixEnd_3980575 := by exact prefixLift 3980575
  have htrace : WordTrace (prefixWord ++ tailWord_3980575) baseStart_3980575 baseEnd_3980575 := by
    simpa [prefixWord, tailWord_3980575, baseEnd_3980575] using wordTrace_append hprefix tailTrace_3980575
  have hstable : (prefixWord ++ tailWord_3980575).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3980575).length < 2 ^ (prefixWord ++ tailWord_3980575).sum := by decide
  have hdescent : baseEnd_3980575 < baseStart_3980575 := by decide
  rcases family_descends (prefixWord ++ tailWord_3980575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3980579 : List Nat := [1, 1, 1, 4, 2, 4, 2, 2, 2, 3]
def baseStart_3980579 : Nat := 118140960795 + 3980579 * 2 ^ 59
def prefixEnd_3980579 : Nat := 4983230072969 + 3 ^ 40 * 3980579 * 2
def baseEnd_3980579 : Nat := 1362633540128991133370771

theorem tailTrace_3980579 : CollatzResearch.WordTrace tailWord_3980579 prefixEnd_3980579 1362633540128991133370771 := by
  unfold tailWord_3980579
  simp only [CollatzResearch.WordTrace]
  refine ⟨145183643446049586614376791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96789095630699724409584527 145183643446049586614376791)
  ·
    refine ⟨217775465169074379921565187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145183643446049586614376791 217775465169074379921565187)
    ·
      refine ⟨326663197753611569882347781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217775465169074379921565187 326663197753611569882347781)
      ·
        refine ⟨61249349578802169352940209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 326663197753611569882347781 61249349578802169352940209)
        ·
          refine ⟨45937012184101627014705157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61249349578802169352940209 45937012184101627014705157)
          ·
            refine ⟨8613189784519055065257217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45937012184101627014705157 8613189784519055065257217)
            ·
              refine ⟨6459892338389291298942913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8613189784519055065257217 6459892338389291298942913)
              ·
                refine ⟨4844919253791968474207185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6459892338389291298942913 4844919253791968474207185)
                ·
                  refine ⟨3633689440343976355655389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4844919253791968474207185 3633689440343976355655389)
                  ·
                    refine ⟨1362633540128991133370771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3633689440343976355655389 1362633540128991133370771)
                    ·
                      rfl

theorem cell22_3980579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 2, 2, 2, 3].length) (baseStart_3980579 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3980579 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3980579 prefixEnd_3980579 := by exact prefixLift 3980579
  have htrace : WordTrace (prefixWord ++ tailWord_3980579) baseStart_3980579 baseEnd_3980579 := by
    simpa [prefixWord, tailWord_3980579, baseEnd_3980579] using wordTrace_append hprefix tailTrace_3980579
  have hstable : (prefixWord ++ tailWord_3980579).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3980579).length < 2 ^ (prefixWord ++ tailWord_3980579).sum := by decide
  have hdescent : baseEnd_3980579 < baseStart_3980579 := by decide
  rcases family_descends (prefixWord ++ tailWord_3980579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3980581 : List Nat := [1, 3, 1, 2, 4, 3, 2, 2, 4]
def baseStart_3980581 : Nat := 118140960795 + 3980581 * 2 ^ 59
def prefixEnd_3980581 : Nat := 4983230072969 + 3 ^ 40 * 3980581 * 2
def baseEnd_3980581 : Nat := 454211408256621264940255

theorem tailTrace_3980581 : CollatzResearch.WordTrace tailWord_3980581 prefixEnd_3980581 454211408256621264940255 := by
  unfold tailWord_3980581
  simp only [CollatzResearch.WordTrace]
  refine ⟨145183716392042340955949597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96789144261361560637299731 145183716392042340955949597)
  ·
    refine ⟨54443893647015877858481099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145183716392042340955949597 54443893647015877858481099)
    ·
      refine ⟨81665840470523816787721649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54443893647015877858481099 81665840470523816787721649)
      ·
        refine ⟨61249380352892862590791237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81665840470523816787721649 61249380352892862590791237)
        ·
          refine ⟨11484258816167411735773357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61249380352892862590791237 11484258816167411735773357)
          ·
            refine ⟨4306597056062779400915009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11484258816167411735773357 4306597056062779400915009)
            ·
              refine ⟨3229947792047084550686257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4306597056062779400915009 3229947792047084550686257)
              ·
                refine ⟨2422460844035313413014693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3229947792047084550686257 2422460844035313413014693)
                ·
                  refine ⟨454211408256621264940255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2422460844035313413014693 454211408256621264940255)
                  ·
                    rfl

theorem cell22_3980581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 2, 2, 4].length) (baseStart_3980581 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3980581 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3980581 prefixEnd_3980581 := by exact prefixLift 3980581
  have htrace : WordTrace (prefixWord ++ tailWord_3980581) baseStart_3980581 baseEnd_3980581 := by
    simpa [prefixWord, tailWord_3980581, baseEnd_3980581] using wordTrace_append hprefix tailTrace_3980581
  have hstable : (prefixWord ++ tailWord_3980581).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3980581).length < 2 ^ (prefixWord ++ tailWord_3980581).sum := by decide
  have hdescent : baseEnd_3980581 < baseStart_3980581 := by decide
  rcases family_descends (prefixWord ++ tailWord_3980581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3980607 : List Nat := [1, 1, 2, 2, 4, 2, 1, 1, 5, 3]
def baseStart_3980607 : Nat := 118140960795 + 3980607 * 2 ^ 59
def prefixEnd_3980607 : Nat := 4983230072969 + 3 ^ 40 * 3980607 * 2
def baseEnd_3980607 : Nat := 1362643125101208393670685

theorem tailTrace_3980607 : CollatzResearch.WordTrace tailWord_3980607 prefixEnd_3980607 1362643125101208393670685 := by
  unfold tailWord_3980607
  simp only [CollatzResearch.WordTrace]
  refine ⟨145184664689948147396396075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96789776459965431597597383 145184664689948147396396075)
  ·
    refine ⟨217776997034922221094594113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145184664689948147396396075 217776997034922221094594113)
    ·
      refine ⟨163332747776191665820945585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217776997034922221094594113 163332747776191665820945585)
      ·
        refine ⟨122499560832143749365709189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163332747776191665820945585 122499560832143749365709189)
        ·
          refine ⟨22968667656026953006070473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 122499560832143749365709189 22968667656026953006070473)
          ·
            refine ⟨17226500742020214754552855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22968667656026953006070473 17226500742020214754552855)
            ·
              refine ⟨25839751113030322131829283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17226500742020214754552855 25839751113030322131829283)
              ·
                refine ⟨38759626669545483197743925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25839751113030322131829283 38759626669545483197743925)
                ·
                  refine ⟨3633715000269889049788493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38759626669545483197743925 3633715000269889049788493)
                  ·
                    refine ⟨1362643125101208393670685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3633715000269889049788493 1362643125101208393670685)
                    ·
                      rfl

theorem cell22_3980607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 1, 5, 3].length) (baseStart_3980607 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3980607 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3980607 prefixEnd_3980607 := by exact prefixLift 3980607
  have htrace : WordTrace (prefixWord ++ tailWord_3980607) baseStart_3980607 baseEnd_3980607 := by
    simpa [prefixWord, tailWord_3980607, baseEnd_3980607] using wordTrace_append hprefix tailTrace_3980607
  have hstable : (prefixWord ++ tailWord_3980607).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3980607).length < 2 ^ (prefixWord ++ tailWord_3980607).sum := by decide
  have hdescent : baseEnd_3980607 < baseStart_3980607 := by decide
  rcases family_descends (prefixWord ++ tailWord_3980607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3980609 : List Nat := [1, 2, 5, 2, 1, 2, 3, 6]
def baseStart_3980609 : Nat := 118140960795 + 3980609 * 2 ^ 59
def prefixEnd_3980609 : Nat := 4983230072969 + 3 ^ 40 * 3980609 * 2
def baseEnd_3980609 : Nat := 151404867749120117235631

theorem tailTrace_3980609 : CollatzResearch.WordTrace tailWord_3980609 prefixEnd_3980609 151404867749120117235631 := by
  unfold tailWord_3980609
  simp only [CollatzResearch.WordTrace]
  refine ⟨145184737635940901737968881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96789825090627267825312587 145184737635940901737968881)
  ·
    refine ⟨108888553226955676303476661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145184737635940901737968881 108888553226955676303476661)
    ·
      refine ⟨10208301865027094653450937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 108888553226955676303476661 10208301865027094653450937)
      ·
        refine ⟨7656226398770320990088203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10208301865027094653450937 7656226398770320990088203)
        ·
          refine ⟨11484339598155481485132305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7656226398770320990088203 11484339598155481485132305)
          ·
            refine ⟨8613254698616611113849229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11484339598155481485132305 8613254698616611113849229)
            ·
              refine ⟨3229970511981229167693461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8613254698616611113849229 3229970511981229167693461)
              ·
                refine ⟨151404867749120117235631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3229970511981229167693461 151404867749120117235631)
                ·
                  rfl

theorem cell22_3980609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 3, 6].length) (baseStart_3980609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3980609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3980609 prefixEnd_3980609 := by exact prefixLift 3980609
  have htrace : WordTrace (prefixWord ++ tailWord_3980609) baseStart_3980609 baseEnd_3980609 := by
    simpa [prefixWord, tailWord_3980609, baseEnd_3980609] using wordTrace_append hprefix tailTrace_3980609
  have hstable : (prefixWord ++ tailWord_3980609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3980609).length < 2 ^ (prefixWord ++ tailWord_3980609).sum := by decide
  have hdescent : baseEnd_3980609 < baseStart_3980609 := by decide
  rcases family_descends (prefixWord ++ tailWord_3980609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3980630 : List Nat := [5, 2, 3, 1, 1, 1, 1, 1, 4, 3]
def baseStart_3980630 : Nat := 118140960795 + 3980630 * 2 ^ 59
def prefixEnd_3980630 : Nat := 4983230072969 + 3 ^ 40 * 3980630 * 2
def baseEnd_3980630 : Nat := 1362650998471244000345615

theorem tailTrace_3980630 : CollatzResearch.WordTrace tailWord_3980630 prefixEnd_3980630 1362650998471244000345615 := by
  unfold tailWord_3980630
  simp only [CollatzResearch.WordTrace]
  refine ⟨9074093973054051395280209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 96790335712576548216322229 9074093973054051395280209)
  ·
    refine ⟨6805570479790538546460157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9074093973054051395280209 6805570479790538546460157)
    ·
      refine ⟨2552088929921451954922559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6805570479790538546460157 2552088929921451954922559)
      ·
        refine ⟨3828133394882177932383839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2552088929921451954922559 3828133394882177932383839)
        ·
          refine ⟨5742200092323266898575759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3828133394882177932383839 5742200092323266898575759)
          ·
            refine ⟨8613300138484900347863639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5742200092323266898575759 8613300138484900347863639)
            ·
              refine ⟨12919950207727350521795459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8613300138484900347863639 12919950207727350521795459)
              ·
                refine ⟨19379925311591025782693189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12919950207727350521795459 19379925311591025782693189)
                ·
                  refine ⟨3633735995923317334254973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19379925311591025782693189 3633735995923317334254973)
                  ·
                    refine ⟨1362650998471244000345615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3633735995923317334254973 1362650998471244000345615)
                    ·
                      rfl

theorem cell22_3980630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_3980630 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3980630 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3980630 prefixEnd_3980630 := by exact prefixLift 3980630
  have htrace : WordTrace (prefixWord ++ tailWord_3980630) baseStart_3980630 baseEnd_3980630 := by
    simpa [prefixWord, tailWord_3980630, baseEnd_3980630] using wordTrace_append hprefix tailTrace_3980630
  have hstable : (prefixWord ++ tailWord_3980630).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3980630).length < 2 ^ (prefixWord ++ tailWord_3980630).sum := by decide
  have hdescent : baseEnd_3980630 < baseStart_3980630 := by decide
  rcases family_descends (prefixWord ++ tailWord_3980630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3980652 : List Nat := [2, 2, 1, 1, 5, 1, 2, 1, 2, 5]
def baseStart_3980652 : Nat := 118140960795 + 3980652 * 2 ^ 59
def prefixEnd_3980652 : Nat := 4983230072969 + 3 ^ 40 * 3980652 * 2
def baseEnd_3980652 : Nat := 1362658529520843276295547

theorem tailTrace_3980652 : CollatzResearch.WordTrace tailWord_3980652 prefixEnd_3980652 1362658529520843276295547 := by
  unfold tailWord_3980652
  simp only [CollatzResearch.WordTrace]
  refine ⟨72593152987392560040892105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96790870649856746721189473 72593152987392560040892105)
  ·
    refine ⟨54444864740544420030669079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72593152987392560040892105 54444864740544420030669079)
    ·
      refine ⟨81667297110816630046003619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54444864740544420030669079 81667297110816630046003619)
      ·
        refine ⟨122500945666224945069005429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81667297110816630046003619 122500945666224945069005429)
        ·
          refine ⟨11484463656208588600219259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 122500945666224945069005429 11484463656208588600219259)
          ·
            refine ⟨17226695484312882900328889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11484463656208588600219259 17226695484312882900328889)
            ·
              refine ⟨12920021613234662175246667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17226695484312882900328889 12920021613234662175246667)
              ·
                refine ⟨19380032419851993262870001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12920021613234662175246667 19380032419851993262870001)
                ·
                  refine ⟨14535024314888994947152501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19380032419851993262870001 14535024314888994947152501)
                  ·
                    refine ⟨1362658529520843276295547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14535024314888994947152501 1362658529520843276295547)
                    ·
                      rfl

theorem cell22_3980652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 5].length) (baseStart_3980652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3980652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3980652 prefixEnd_3980652 := by exact prefixLift 3980652
  have htrace : WordTrace (prefixWord ++ tailWord_3980652) baseStart_3980652 baseEnd_3980652 := by
    simpa [prefixWord, tailWord_3980652, baseEnd_3980652] using wordTrace_append hprefix tailTrace_3980652
  have hstable : (prefixWord ++ tailWord_3980652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3980652).length < 2 ^ (prefixWord ++ tailWord_3980652).sum := by decide
  have hdescent : baseEnd_3980652 < baseStart_3980652 := by decide
  rcases family_descends (prefixWord ++ tailWord_3980652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3980757 : List Nat := [1, 3, 2, 3, 1, 1, 1, 1, 1, 8]
def baseStart_3980757 : Nat := 118140960795 + 3980757 * 2 ^ 59
def prefixEnd_3980757 : Nat := 4983230072969 + 3 ^ 40 * 3980757 * 2
def baseEnd_3980757 : Nat := 1362694473166658002420225

theorem tailTrace_3980757 : CollatzResearch.WordTrace tailWord_3980757 prefixEnd_3980757 1362694473166658002420225 := by
  unfold tailWord_3980757
  simp only [CollatzResearch.WordTrace]
  refine ⟨145190135639404723014356525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96793423759603148676237683 145190135639404723014356525)
  ·
    refine ⟨54446300864776771130383697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145190135639404723014356525 54446300864776771130383697)
    ·
      refine ⟨40834725648582578347787773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54446300864776771130383697 40834725648582578347787773)
      ·
        refine ⟨15313022118218466880420415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40834725648582578347787773 15313022118218466880420415)
        ·
          refine ⟨22969533177327700320630623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15313022118218466880420415 22969533177327700320630623)
          ·
            refine ⟨34454299765991550480945935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22969533177327700320630623 34454299765991550480945935)
            ·
              refine ⟨51681449648987325721418903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34454299765991550480945935 51681449648987325721418903)
              ·
                refine ⟨77522174473480988582128355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51681449648987325721418903 77522174473480988582128355)
                ·
                  refine ⟨116283261710221482873192533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77522174473480988582128355 116283261710221482873192533)
                  ·
                    refine ⟨1362694473166658002420225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 116283261710221482873192533 1362694473166658002420225)
                    ·
                      rfl

theorem cell22_3980757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 1, 1, 8].length) (baseStart_3980757 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3980757 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3980757 prefixEnd_3980757 := by exact prefixLift 3980757
  have htrace : WordTrace (prefixWord ++ tailWord_3980757) baseStart_3980757 baseEnd_3980757 := by
    simpa [prefixWord, tailWord_3980757, baseEnd_3980757] using wordTrace_append hprefix tailTrace_3980757
  have hstable : (prefixWord ++ tailWord_3980757).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3980757).length < 2 ^ (prefixWord ++ tailWord_3980757).sum := by decide
  have hdescent : baseEnd_3980757 < baseStart_3980757 := by decide
  rcases family_descends (prefixWord ++ tailWord_3980757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3980834 : List Nat := [3, 3, 1, 1, 1, 1, 4, 2, 6]
def baseStart_3980834 : Nat := 118140960795 + 3980834 * 2 ^ 59
def prefixEnd_3980834 : Nat := 4983230072969 + 3 ^ 40 * 3980834 * 2
def baseEnd_3980834 : Nat := 454240277280085156081663

theorem tailTrace_3980834 : CollatzResearch.WordTrace tailWord_3980834 prefixEnd_3980834 454240277280085156081663 := by
  unfold tailWord_3980834
  simp only [CollatzResearch.WordTrace]
  refine ⟨36298236015031441291227389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96795296040083843443273037 36298236015031441291227389)
  ·
    refine ⟨13611838505636790484210271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36298236015031441291227389 13611838505636790484210271)
    ·
      refine ⟨20417757758455185726315407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13611838505636790484210271 20417757758455185726315407)
      ·
        refine ⟨30626636637682778589473111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20417757758455185726315407 30626636637682778589473111)
        ·
          refine ⟨45939954956524167884209667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30626636637682778589473111 45939954956524167884209667)
          ·
            refine ⟨68909932434786251826314501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45939954956524167884209667 68909932434786251826314501)
            ·
              refine ⟨12920612331522422217433969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68909932434786251826314501 12920612331522422217433969)
              ·
                refine ⟨9690459248641816663075477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12920612331522422217433969 9690459248641816663075477)
                ·
                  refine ⟨454240277280085156081663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9690459248641816663075477 454240277280085156081663)
                  ·
                    rfl

theorem cell22_3980834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 2, 6].length) (baseStart_3980834 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3980834 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3980834 prefixEnd_3980834 := by exact prefixLift 3980834
  have htrace : WordTrace (prefixWord ++ tailWord_3980834) baseStart_3980834 baseEnd_3980834 := by
    simpa [prefixWord, tailWord_3980834, baseEnd_3980834] using wordTrace_append hprefix tailTrace_3980834
  have hstable : (prefixWord ++ tailWord_3980834).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3980834).length < 2 ^ (prefixWord ++ tailWord_3980834).sum := by decide
  have hdescent : baseEnd_3980834 < baseStart_3980834 := by decide
  rcases family_descends (prefixWord ++ tailWord_3980834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3980851 : List Nat := [1, 1, 1, 2, 4, 3, 3, 3, 4]
def baseStart_3980851 : Nat := 118140960795 + 3980851 * 2 ^ 59
def prefixEnd_3980851 : Nat := 4983230072969 + 3 ^ 40 * 3980851 * 2
def baseEnd_3980851 : Nat := 454242217095891030189979

theorem tailTrace_3980851 : CollatzResearch.WordTrace tailWord_3980851 prefixEnd_3980851 454242217095891030189979 := by
  unfold tailWord_3980851
  simp only [CollatzResearch.WordTrace]
  refine ⟨145193564101064177068278407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96795709400709451378852271 145193564101064177068278407)
  ·
    refine ⟨217790346151596265602417611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145193564101064177068278407 217790346151596265602417611)
    ·
      refine ⟨326685519227394398403626417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217790346151596265602417611 326685519227394398403626417)
      ·
        refine ⟨245014139420545798802719813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 326685519227394398403626417 245014139420545798802719813)
        ·
          refine ⟨45940151141352337275509965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 245014139420545798802719813 45940151141352337275509965)
          ·
            refine ⟨17227556678007126478316237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45940151141352337275509965 17227556678007126478316237)
            ·
              refine ⟨6460333754252672429368589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17227556678007126478316237 6460333754252672429368589)
              ·
                refine ⟨2422625157844752161013221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6460333754252672429368589 2422625157844752161013221)
                ·
                  refine ⟨454242217095891030189979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2422625157844752161013221 454242217095891030189979)
                  ·
                    rfl

theorem cell22_3980851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 3, 3, 4].length) (baseStart_3980851 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3980851 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3980851 prefixEnd_3980851 := by exact prefixLift 3980851
  have htrace : WordTrace (prefixWord ++ tailWord_3980851) baseStart_3980851 baseEnd_3980851 := by
    simpa [prefixWord, tailWord_3980851, baseEnd_3980851] using wordTrace_append hprefix tailTrace_3980851
  have hstable : (prefixWord ++ tailWord_3980851).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3980851).length < 2 ^ (prefixWord ++ tailWord_3980851).sum := by decide
  have hdescent : baseEnd_3980851 < baseStart_3980851 := by decide
  rcases family_descends (prefixWord ++ tailWord_3980851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3980928 : List Nat := [2, 1, 1, 2, 1, 4, 3, 4, 1, 3]
def baseStart_3980928 : Nat := 118140960795 + 3980928 * 2 ^ 59
def prefixEnd_3980928 : Nat := 4983230072969 + 3 ^ 40 * 3980928 * 2
def baseEnd_3980928 : Nat := 1362753009961270556394701

theorem tailTrace_3980928 : CollatzResearch.WordTrace tailWord_3980928 prefixEnd_3980928 1362753009961270556394701 := by
  unfold tailWord_3980928
  simp only [CollatzResearch.WordTrace]
  refine ⟨72598186260892609609415719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96797581681190146145887625 72598186260892609609415719)
  ·
    refine ⟨108897279391338914414123579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72598186260892609609415719 108897279391338914414123579)
    ·
      refine ⟨163345919087008371621185369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108897279391338914414123579 163345919087008371621185369)
      ·
        refine ⟨122509439315256278715889027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163345919087008371621185369 122509439315256278715889027)
        ·
          refine ⟨183764158972884418073833541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122509439315256278715889027 183764158972884418073833541)
          ·
            refine ⟨34455779807415828388843789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 183764158972884418073833541 34455779807415828388843789)
            ·
              refine ⟨12920917427780935645816421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34455779807415828388843789 12920917427780935645816421)
              ·
                refine ⟨2422672017708925433590579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12920917427780935645816421 2422672017708925433590579)
                ·
                  refine ⟨3634008026563388150385869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2422672017708925433590579 3634008026563388150385869)
                  ·
                    refine ⟨1362753009961270556394701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3634008026563388150385869 1362753009961270556394701)
                    ·
                      rfl

theorem cell22_3980928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 4, 1, 3].length) (baseStart_3980928 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3980928 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3980928 prefixEnd_3980928 := by exact prefixLift 3980928
  have htrace : WordTrace (prefixWord ++ tailWord_3980928) baseStart_3980928 baseEnd_3980928 := by
    simpa [prefixWord, tailWord_3980928, baseEnd_3980928] using wordTrace_append hprefix tailTrace_3980928
  have hstable : (prefixWord ++ tailWord_3980928).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3980928).length < 2 ^ (prefixWord ++ tailWord_3980928).sum := by decide
  have hdescent : baseEnd_3980928 < baseStart_3980928 := by decide
  rcases family_descends (prefixWord ++ tailWord_3980928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3980939 : List Nat := [1, 1, 1, 1, 4, 1, 5, 1, 2, 5]
def baseStart_3980939 : Nat := 118140960795 + 3980939 * 2 ^ 59
def prefixEnd_3980939 : Nat := 4983230072969 + 3 ^ 40 * 3980939 * 2
def baseEnd_3980939 : Nat := 1362756775486070194369667

theorem tailTrace_3980939 : CollatzResearch.WordTrace tailWord_3980939 prefixEnd_3980939 1362756775486070194369667 := by
  unfold tailWord_3980939
  simp only [CollatzResearch.WordTrace]
  refine ⟨145196773724745368097481871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96797849149830245398321247 145196773724745368097481871)
  ·
    refine ⟨217795160587118052146222807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145196773724745368097481871 217795160587118052146222807)
    ·
      refine ⟨326692740880677078219334211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217795160587118052146222807 326692740880677078219334211)
      ·
        refine ⟨490039111321015617329001317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 326692740880677078219334211 490039111321015617329001317)
        ·
          refine ⟨91882333372690428249187747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 490039111321015617329001317 91882333372690428249187747)
          ·
            refine ⟨137823500059035642373781621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91882333372690428249187747 137823500059035642373781621)
            ·
              refine ⟨12920953130534591472542027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 137823500059035642373781621 12920953130534591472542027)
              ·
                refine ⟨19381429695801887208813041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12920953130534591472542027 19381429695801887208813041)
                ·
                  refine ⟨14536072271851415406609781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19381429695801887208813041 14536072271851415406609781)
                  ·
                    refine ⟨1362756775486070194369667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14536072271851415406609781 1362756775486070194369667)
                    ·
                      rfl

theorem cell22_3980939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 1, 2, 5].length) (baseStart_3980939 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3980939 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3980939 prefixEnd_3980939 := by exact prefixLift 3980939
  have htrace : WordTrace (prefixWord ++ tailWord_3980939) baseStart_3980939 baseEnd_3980939 := by
    simpa [prefixWord, tailWord_3980939, baseEnd_3980939] using wordTrace_append hprefix tailTrace_3980939
  have hstable : (prefixWord ++ tailWord_3980939).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3980939).length < 2 ^ (prefixWord ++ tailWord_3980939).sum := by decide
  have hdescent : baseEnd_3980939 < baseStart_3980939 := by decide
  rcases family_descends (prefixWord ++ tailWord_3980939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3980984 : List Nat := [2, 1, 2, 1, 2, 1, 1, 4, 3, 5]
def baseStart_3980984 : Nat := 118140960795 + 3980984 * 2 ^ 59
def prefixEnd_3980984 : Nat := 4983230072969 + 3 ^ 40 * 3980984 * 2
def baseEnd_3980984 : Nat := 1362772179905705076994529

theorem tailTrace_3980984 : CollatzResearch.WordTrace tailWord_3980984 prefixEnd_3980984 1362772179905705076994529 := by
  unfold tailWord_3980984
  simp only [CollatzResearch.WordTrace]
  refine ⟨72599207504791170391435003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96798943339721560521913337 72599207504791170391435003)
  ·
    refine ⟨108898811257186755587152505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72599207504791170391435003 108898811257186755587152505)
    ·
      refine ⟨81674108442890066690364379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108898811257186755587152505 81674108442890066690364379)
      ·
        refine ⟨122511162664335100035546569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81674108442890066690364379 122511162664335100035546569)
        ·
          refine ⟨91883371998251325026659927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122511162664335100035546569 91883371998251325026659927)
          ·
            refine ⟨137825057997376987539989891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91883371998251325026659927 137825057997376987539989891)
            ·
              refine ⟨206737586996065481309984837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137825057997376987539989891 206737586996065481309984837)
              ·
                refine ⟨38763297561762277745622157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 206737586996065481309984837 38763297561762277745622157)
                ·
                  refine ⟨14536236585660854154608309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38763297561762277745622157 14536236585660854154608309)
                  ·
                    refine ⟨1362772179905705076994529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14536236585660854154608309 1362772179905705076994529)
                    ·
                      rfl

theorem cell22_3980984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 4, 3, 5].length) (baseStart_3980984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3980984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3980984 prefixEnd_3980984 := by exact prefixLift 3980984
  have htrace : WordTrace (prefixWord ++ tailWord_3980984) baseStart_3980984 baseEnd_3980984 := by
    simpa [prefixWord, tailWord_3980984, baseEnd_3980984] using wordTrace_append hprefix tailTrace_3980984
  have hstable : (prefixWord ++ tailWord_3980984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3980984).length < 2 ^ (prefixWord ++ tailWord_3980984).sum := by decide
  have hdescent : baseEnd_3980984 < baseStart_3980984 := by decide
  rcases family_descends (prefixWord ++ tailWord_3980984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3980986 : List Nat := [3, 1, 1, 1, 2, 5, 2, 1, 6]
def baseStart_3980986 : Nat := 118140960795 + 3980986 * 2 ^ 59
def prefixEnd_3980986 : Nat := 4983230072969 + 3 ^ 40 * 3980986 * 2
def baseEnd_3980986 : Nat := 454257621515525912814841

theorem tailTrace_3980986 : CollatzResearch.WordTrace tailWord_3980986 prefixEnd_3980986 454257621515525912814841 := by
  unfold tailWord_3980986
  simp only [CollatzResearch.WordTrace]
  refine ⟨36299621988893773781110703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96798991970383396749628541 36299621988893773781110703)
  ·
    refine ⟨54449432983340660671666055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36299621988893773781110703 54449432983340660671666055)
    ·
      refine ⟨81674149475010991007499083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54449432983340660671666055 81674149475010991007499083)
      ·
        refine ⟨122511224212516486511248625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81674149475010991007499083 122511224212516486511248625)
        ·
          refine ⟨91883418159387364883436469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122511224212516486511248625 91883418159387364883436469)
          ·
            refine ⟨8614070452442565457822169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 91883418159387364883436469 8614070452442565457822169)
            ·
              refine ⟨6460552839331924093366627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8614070452442565457822169 6460552839331924093366627)
              ·
                refine ⟨9690829258997886140049941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6460552839331924093366627 9690829258997886140049941)
                ·
                  refine ⟨454257621515525912814841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9690829258997886140049941 454257621515525912814841)
                  ·
                    rfl

theorem cell22_3980986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 2, 1, 6].length) (baseStart_3980986 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3980986 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3980986 prefixEnd_3980986 := by exact prefixLift 3980986
  have htrace : WordTrace (prefixWord ++ tailWord_3980986) baseStart_3980986 baseEnd_3980986 := by
    simpa [prefixWord, tailWord_3980986, baseEnd_3980986] using wordTrace_append hprefix tailTrace_3980986
  have hstable : (prefixWord ++ tailWord_3980986).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3980986).length < 2 ^ (prefixWord ++ tailWord_3980986).sum := by decide
  have hdescent : baseEnd_3980986 < baseStart_3980986 := by decide
  rcases family_descends (prefixWord ++ tailWord_3980986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3980999 : List Nat := [1, 1, 4, 1, 1, 1, 3, 1, 3, 6]
def baseStart_3980999 : Nat := 118140960795 + 3980999 * 2 ^ 59
def prefixEnd_3980999 : Nat := 4983230072969 + 3 ^ 40 * 3980999 * 2
def baseEnd_3980999 : Nat := 1362777314712250037869483

theorem tailTrace_3980999 : CollatzResearch.WordTrace tailWord_3980999 prefixEnd_3980999 1362777314712250037869483 := by
  unfold tailWord_3980999
  simp only [CollatzResearch.WordTrace]
  refine ⟨145198962104527998344666051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96799308069685332229777367 145198962104527998344666051)
  ·
    refine ⟨217798443156791997516999077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145198962104527998344666051 217798443156791997516999077)
    ·
      refine ⟨40837208091898499534437327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 217798443156791997516999077 40837208091898499534437327)
      ·
        refine ⟨61255812137847749301655991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40837208091898499534437327 61255812137847749301655991)
        ·
          refine ⟨91883718206771623952483987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61255812137847749301655991 91883718206771623952483987)
          ·
            refine ⟨137825577310157435928725981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91883718206771623952483987 137825577310157435928725981)
            ·
              refine ⟨51684591491309038473272243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 137825577310157435928725981 51684591491309038473272243)
              ·
                refine ⟨77526887236963557709908365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51684591491309038473272243 77526887236963557709908365)
                ·
                  refine ⟨29072582713861334141215637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77526887236963557709908365 29072582713861334141215637)
                  ·
                    refine ⟨1362777314712250037869483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29072582713861334141215637 1362777314712250037869483)
                    ·
                      rfl

theorem cell22_3980999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 1, 3, 6].length) (baseStart_3980999 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3980999 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3980999 prefixEnd_3980999 := by exact prefixLift 3980999
  have htrace : WordTrace (prefixWord ++ tailWord_3980999) baseStart_3980999 baseEnd_3980999 := by
    simpa [prefixWord, tailWord_3980999, baseEnd_3980999] using wordTrace_append hprefix tailTrace_3980999
  have hstable : (prefixWord ++ tailWord_3980999).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3980999).length < 2 ^ (prefixWord ++ tailWord_3980999).sum := by decide
  have hdescent : baseEnd_3980999 < baseStart_3980999 := by decide
  rcases family_descends (prefixWord ++ tailWord_3980999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3981005 : List Nat := [1, 6, 2, 1, 1, 1, 1, 4, 1, 4]
def baseStart_3981005 : Nat := 118140960795 + 3981005 * 2 ^ 59
def prefixEnd_3981005 : Nat := 4983230072969 + 3 ^ 40 * 3981005 * 2
def baseEnd_3981005 : Nat := 1362779368634868022219465

theorem tailTrace_3981005 : CollatzResearch.WordTrace tailWord_3981005 prefixEnd_3981005 1362779368634868022219465 := by
  unfold tailWord_3981005
  simp only [CollatzResearch.WordTrace]
  refine ⟨145199180942506261369384469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96799453961670840912922979 145199180942506261369384469)
  ·
    refine ⟨6806211606679981001689897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 145199180942506261369384469 6806211606679981001689897)
    ·
      refine ⟨5104658705009985751267423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6806211606679981001689897 5104658705009985751267423)
      ·
        refine ⟨7656988057514978626901135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5104658705009985751267423 7656988057514978626901135)
        ·
          refine ⟨11485482086272467940351703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7656988057514978626901135 11485482086272467940351703)
          ·
            refine ⟨17228223129408701910527555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11485482086272467940351703 17228223129408701910527555)
            ·
              refine ⟨25842334694113052865791333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17228223129408701910527555 25842334694113052865791333)
              ·
                refine ⟨4845437755146197412335875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25842334694113052865791333 4845437755146197412335875)
                ·
                  refine ⟨7268156632719296118503813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4845437755146197412335875 7268156632719296118503813)
                  ·
                    refine ⟨1362779368634868022219465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7268156632719296118503813 1362779368634868022219465)
                    ·
                      rfl

theorem cell22_3981005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_3981005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3981005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3981005 prefixEnd_3981005 := by exact prefixLift 3981005
  have htrace : WordTrace (prefixWord ++ tailWord_3981005) baseStart_3981005 baseEnd_3981005 := by
    simpa [prefixWord, tailWord_3981005, baseEnd_3981005] using wordTrace_append hprefix tailTrace_3981005
  have hstable : (prefixWord ++ tailWord_3981005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3981005).length < 2 ^ (prefixWord ++ tailWord_3981005).sum := by decide
  have hdescent : baseEnd_3981005 < baseStart_3981005 := by decide
  rcases family_descends (prefixWord ++ tailWord_3981005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3981016 : List Nat := [2, 1, 2, 2, 3, 1, 2, 3, 2, 4]
def baseStart_3981016 : Nat := 118140960795 + 3981016 * 2 ^ 59
def prefixEnd_3981016 : Nat := 4983230072969 + 3 ^ 40 * 3981016 * 2
def baseEnd_3981016 : Nat := 1362783134159667660194431

theorem tailTrace_3981016 : CollatzResearch.WordTrace tailWord_3981016 prefixEnd_3981016 1362783134159667660194431 := by
  unfold tailWord_3981016
  simp only [CollatzResearch.WordTrace]
  refine ⟨72599791072733205124017451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96799721430310940165356601 72599791072733205124017451)
  ·
    refine ⟨108899686609099807686026177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72599791072733205124017451 108899686609099807686026177)
    ·
      refine ⟨81674764956824855764519633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108899686609099807686026177 81674764956824855764519633)
      ·
        refine ⟨61256073717618641823389725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81674764956824855764519633 61256073717618641823389725)
        ·
          refine ⟨22971027644106990683771147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61256073717618641823389725 22971027644106990683771147)
          ·
            refine ⟨34456541466160486025656721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22971027644106990683771147 34456541466160486025656721)
            ·
              refine ⟨25842406099620364519242541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34456541466160486025656721 25842406099620364519242541)
              ·
                refine ⟨9690902287357636694715953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25842406099620364519242541 9690902287357636694715953)
                ·
                  refine ⟨7268176715518227521036965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9690902287357636694715953 7268176715518227521036965)
                  ·
                    refine ⟨1362783134159667660194431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7268176715518227521036965 1362783134159667660194431)
                    ·
                      rfl

theorem cell22_3981016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 3, 2, 4].length) (baseStart_3981016 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3981016 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3981016 prefixEnd_3981016 := by exact prefixLift 3981016
  have htrace : WordTrace (prefixWord ++ tailWord_3981016) baseStart_3981016 baseEnd_3981016 := by
    simpa [prefixWord, tailWord_3981016, baseEnd_3981016] using wordTrace_append hprefix tailTrace_3981016
  have hstable : (prefixWord ++ tailWord_3981016).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3981016).length < 2 ^ (prefixWord ++ tailWord_3981016).sum := by decide
  have hdescent : baseEnd_3981016 < baseStart_3981016 := by decide
  rcases family_descends (prefixWord ++ tailWord_3981016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3981069 : List Nat := [1, 7, 2, 1, 1, 1, 1, 2, 1, 5]
def baseStart_3981069 : Nat := 118140960795 + 3981069 * 2 ^ 59
def prefixEnd_3981069 : Nat := 4983230072969 + 3 ^ 40 * 3981069 * 2
def baseEnd_3981069 : Nat := 1362801277142793188619269

theorem tailTrace_3981069 : CollatzResearch.WordTrace tailWord_3981069 prefixEnd_3981069 1362801277142793188619269 := by
  unfold tailWord_3981069
  simp only [CollatzResearch.WordTrace]
  refine ⟨145201515214274400299714261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96801010142849600199809507 145201515214274400299714261)
  ·
    refine ⟨3403160512834556257024553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 145201515214274400299714261 3403160512834556257024553)
    ·
      refine ⟨2552370384625917192768415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3403160512834556257024553 2552370384625917192768415)
      ·
        refine ⟨3828555576938875789152623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2552370384625917192768415 3828555576938875789152623)
        ·
          refine ⟨5742833365408313683728935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3828555576938875789152623 5742833365408313683728935)
          ·
            refine ⟨8614250048112470525593403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5742833365408313683728935 8614250048112470525593403)
            ·
              refine ⟨12921375072168705788390105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8614250048112470525593403 12921375072168705788390105)
              ·
                refine ⟨9691031304126529341292579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12921375072168705788390105 9691031304126529341292579)
                ·
                  refine ⟨14536546956189794011938869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9691031304126529341292579 14536546956189794011938869)
                  ·
                    refine ⟨1362801277142793188619269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14536546956189794011938869 1362801277142793188619269)
                    ·
                      rfl

theorem cell22_3981069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_3981069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3981069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3981069 prefixEnd_3981069 := by exact prefixLift 3981069
  have htrace : WordTrace (prefixWord ++ tailWord_3981069) baseStart_3981069 baseEnd_3981069 := by
    simpa [prefixWord, tailWord_3981069, baseEnd_3981069] using wordTrace_append hprefix tailTrace_3981069
  have hstable : (prefixWord ++ tailWord_3981069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3981069).length < 2 ^ (prefixWord ++ tailWord_3981069).sum := by decide
  have hdescent : baseEnd_3981069 < baseStart_3981069 := by decide
  rcases family_descends (prefixWord ++ tailWord_3981069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3981093 : List Nat := [1, 3, 1, 2, 3, 3, 2, 2, 5]
def baseStart_3981093 : Nat := 118140960795 + 3981093 * 2 ^ 59
def prefixEnd_3981093 : Nat := 4983230072969 + 3 ^ 40 * 3981093 * 2
def baseEnd_3981093 : Nat := 454269830944421708673065

theorem tailTrace_3981093 : CollatzResearch.WordTrace tailWord_3981093 prefixEnd_3981093 454269830944421708673065 := by
  unfold tailWord_3981093
  simp only [CollatzResearch.WordTrace]
  refine ⟨145202390566187452398587933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96801593710791634932391955 145202390566187452398587933)
  ·
    refine ⟨54450896462320294649470475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145202390566187452398587933 54450896462320294649470475)
    ·
      refine ⟨81676344693480441974205713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54450896462320294649470475 81676344693480441974205713)
      ·
        refine ⟨61257258520110331480654285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81676344693480441974205713 61257258520110331480654285)
        ·
          refine ⟨22971471945041374305245357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61257258520110331480654285 22971471945041374305245357)
          ·
            refine ⟨8614301979390515364467009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22971471945041374305245357 8614301979390515364467009)
            ·
              refine ⟨6460726484542886523350257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8614301979390515364467009 6460726484542886523350257)
              ·
                refine ⟨4845544863407164892512693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6460726484542886523350257 4845544863407164892512693)
                ·
                  refine ⟨454269830944421708673065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4845544863407164892512693 454269830944421708673065)
                  ·
                    rfl

theorem cell22_3981093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 2, 2, 5].length) (baseStart_3981093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3981093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3981093 prefixEnd_3981093 := by exact prefixLift 3981093
  have htrace : WordTrace (prefixWord ++ tailWord_3981093) baseStart_3981093 baseEnd_3981093 := by
    simpa [prefixWord, tailWord_3981093, baseEnd_3981093] using wordTrace_append hprefix tailTrace_3981093
  have hstable : (prefixWord ++ tailWord_3981093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3981093).length < 2 ^ (prefixWord ++ tailWord_3981093).sum := by decide
  have hdescent : baseEnd_3981093 < baseStart_3981093 := by decide
  rcases family_descends (prefixWord ++ tailWord_3981093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3981108 : List Nat := [2, 5, 1, 1, 2, 1, 1, 1, 1, 7]
def baseStart_3981108 : Nat := 118140960795 + 3981108 * 2 ^ 59
def prefixEnd_3981108 : Nat := 4983230072969 + 3 ^ 40 * 3981108 * 2
def baseEnd_3981108 : Nat := 1362814627639810086894149

theorem tailTrace_3981108 : CollatzResearch.WordTrace tailWord_3981108 prefixEnd_3981108 1362814627639810086894149 := by
  unfold tailWord_3981108
  simp only [CollatzResearch.WordTrace]
  refine ⟨72601468830566554980191989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96801958440755406640255985 72601468830566554980191989)
  ·
    refine ⟨6806387702865614529392999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 72601468830566554980191989 6806387702865614529392999)
    ·
      refine ⟨10209581554298421794089499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6806387702865614529392999 10209581554298421794089499)
      ·
        refine ⟨15314372331447632691134249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10209581554298421794089499 15314372331447632691134249)
        ·
          refine ⟨11485779248585724518350687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15314372331447632691134249 11485779248585724518350687)
          ·
            refine ⟨17228668872878586777526031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11485779248585724518350687 17228668872878586777526031)
            ·
              refine ⟨25843003309317880166289047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17228668872878586777526031 25843003309317880166289047)
              ·
                refine ⟨38764504963976820249433571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25843003309317880166289047 38764504963976820249433571)
                ·
                  refine ⟨58146757445965230374150357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38764504963976820249433571 58146757445965230374150357)
                  ·
                    refine ⟨1362814627639810086894149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58146757445965230374150357 1362814627639810086894149)
                    ·
                      rfl

theorem cell22_3981108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 1, 1, 7].length) (baseStart_3981108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3981108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3981108 prefixEnd_3981108 := by exact prefixLift 3981108
  have htrace : WordTrace (prefixWord ++ tailWord_3981108) baseStart_3981108 baseEnd_3981108 := by
    simpa [prefixWord, tailWord_3981108, baseEnd_3981108] using wordTrace_append hprefix tailTrace_3981108
  have hstable : (prefixWord ++ tailWord_3981108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3981108).length < 2 ^ (prefixWord ++ tailWord_3981108).sum := by decide
  have hdescent : baseEnd_3981108 < baseStart_3981108 := by decide
  rcases family_descends (prefixWord ++ tailWord_3981108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3981110 : List Nat := [5, 1, 2, 2, 1, 1, 2, 3, 5]
def baseStart_3981110 : Nat := 118140960795 + 3981110 * 2 ^ 59
def prefixEnd_3981110 : Nat := 4983230072969 + 3 ^ 40 * 3981110 * 2
def baseEnd_3981110 : Nat := 454271770760227582781381

theorem tailTrace_3981110 : CollatzResearch.WordTrace tailWord_3981110 prefixEnd_3981110 454271770760227582781381 := by
  unfold tailWord_3981110
  simp only [CollatzResearch.WordTrace]
  refine ⟨9075188162945366518872299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 96802007071417242867971189 9075188162945366518872299)
  ·
    refine ⟨13612782244418049778308449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9075188162945366518872299 13612782244418049778308449)
    ·
      refine ⟨10209586683313537333731337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13612782244418049778308449 10209586683313537333731337)
      ·
        refine ⟨7657190012485153000298503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10209586683313537333731337 7657190012485153000298503)
        ·
          refine ⟨11485785018727729500447755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7657190012485153000298503 11485785018727729500447755)
          ·
            refine ⟨17228677528091594250671633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11485785018727729500447755 17228677528091594250671633)
            ·
              refine ⟨12921508146068695688003725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17228677528091594250671633 12921508146068695688003725)
              ·
                refine ⟨4845565554775760883001397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12921508146068695688003725 4845565554775760883001397)
                ·
                  refine ⟨454271770760227582781381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4845565554775760883001397 454271770760227582781381)
                  ·
                    rfl

theorem cell22_3981110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 3, 5].length) (baseStart_3981110 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3981110 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3981110 prefixEnd_3981110 := by exact prefixLift 3981110
  have htrace : WordTrace (prefixWord ++ tailWord_3981110) baseStart_3981110 baseEnd_3981110 := by
    simpa [prefixWord, tailWord_3981110, baseEnd_3981110] using wordTrace_append hprefix tailTrace_3981110
  have hstable : (prefixWord ++ tailWord_3981110).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3981110).length < 2 ^ (prefixWord ++ tailWord_3981110).sum := by decide
  have hdescent : baseEnd_3981110 < baseStart_3981110 := by decide
  rcases family_descends (prefixWord ++ tailWord_3981110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3981140 : List Nat := [2, 4, 1, 1, 3, 2, 1, 3, 1, 4]
def baseStart_3981140 : Nat := 118140960795 + 3981140 * 2 ^ 59
def prefixEnd_3981140 : Nat := 4983230072969 + 3 ^ 40 * 3981140 * 2
def baseEnd_3981140 : Nat := 1362825581893772670094051

theorem tailTrace_3981140 : CollatzResearch.WordTrace tailWord_3981140 prefixEnd_3981140 1362825581893772670094051 := by
  unfold tailWord_3981140
  simp only [CollatzResearch.WordTrace]
  refine ⟨72602052398508589712774437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96802736531344786283699249 72602052398508589712774437)
  ·
    refine ⟨13612884824720360571145207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72602052398508589712774437 13612884824720360571145207)
    ·
      refine ⟨20419327237080540856717811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13612884824720360571145207 20419327237080540856717811)
      ·
        refine ⟨30628990855620811285076717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20419327237080540856717811 30628990855620811285076717)
        ·
          refine ⟨11485871570857804231903769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30628990855620811285076717 11485871570857804231903769)
          ·
            refine ⟨8614403678143353173927827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11485871570857804231903769 8614403678143353173927827)
            ·
              refine ⟨12921605517215029760891741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8614403678143353173927827 12921605517215029760891741)
              ·
                refine ⟨4845602068955636160334403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12921605517215029760891741 4845602068955636160334403)
                ·
                  refine ⟨7268403103433454240501605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4845602068955636160334403 7268403103433454240501605)
                  ·
                    refine ⟨1362825581893772670094051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7268403103433454240501605 1362825581893772670094051)
                    ·
                      rfl

theorem cell22_3981140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 3, 1, 4].length) (baseStart_3981140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3981140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3981140 prefixEnd_3981140 := by exact prefixLift 3981140
  have htrace : WordTrace (prefixWord ++ tailWord_3981140) baseStart_3981140 baseEnd_3981140 := by
    simpa [prefixWord, tailWord_3981140, baseEnd_3981140] using wordTrace_append hprefix tailTrace_3981140
  have hstable : (prefixWord ++ tailWord_3981140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3981140).length < 2 ^ (prefixWord ++ tailWord_3981140).sum := by decide
  have hdescent : baseEnd_3981140 < baseStart_3981140 := by decide
  rcases family_descends (prefixWord ++ tailWord_3981140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3981153 : List Nat := [1, 2, 3, 1, 1, 1, 5, 1, 4, 3]
def baseStart_3981153 : Nat := 118140960795 + 3981153 * 2 ^ 59
def prefixEnd_3981153 : Nat := 4983230072969 + 3 ^ 40 * 3981153 * 2
def baseEnd_3981153 : Nat := 1362830032059444969519011

theorem tailTrace_3981153 : CollatzResearch.WordTrace tailWord_3981153 prefixEnd_3981153 1362830032059444969519011 := by
  unfold tailWord_3981153
  simp only [CollatzResearch.WordTrace]
  refine ⟨145204578945970082645772113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96803052630646721763848075 145204578945970082645772113)
  ·
    refine ⟨108903434209477561984329085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145204578945970082645772113 108903434209477561984329085)
    ·
      refine ⟨40838787828554085744123407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108903434209477561984329085 40838787828554085744123407)
      ·
        refine ⟨61258181742831128616185111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40838787828554085744123407 61258181742831128616185111)
        ·
          refine ⟨91887272614246692924277667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61258181742831128616185111 91887272614246692924277667)
          ·
            refine ⟨137830908921370039386416501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91887272614246692924277667 137830908921370039386416501)
            ·
              refine ⟨12921647711378441192476547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 137830908921370039386416501 12921647711378441192476547)
              ·
                refine ⟨19382471567067661788714821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12921647711378441192476547 19382471567067661788714821)
                ·
                  refine ⟨3634213418825186585384029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19382471567067661788714821 3634213418825186585384029)
                  ·
                    refine ⟨1362830032059444969519011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3634213418825186585384029 1362830032059444969519011)
                    ·
                      rfl

theorem cell22_3981153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 1, 4, 3].length) (baseStart_3981153 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3981153 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3981153 prefixEnd_3981153 := by exact prefixLift 3981153
  have htrace : WordTrace (prefixWord ++ tailWord_3981153) baseStart_3981153 baseEnd_3981153 := by
    simpa [prefixWord, tailWord_3981153, baseEnd_3981153] using wordTrace_append hprefix tailTrace_3981153
  have hstable : (prefixWord ++ tailWord_3981153).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3981153).length < 2 ^ (prefixWord ++ tailWord_3981153).sum := by decide
  have hdescent : baseEnd_3981153 < baseStart_3981153 := by decide
  rcases family_descends (prefixWord ++ tailWord_3981153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3981181 : List Nat := [1, 4, 1, 1, 2, 1, 1, 1, 1, 9]
def baseStart_3981181 : Nat := 118140960795 + 3981181 * 2 ^ 59
def prefixEnd_3981181 : Nat := 4983230072969 + 3 ^ 40 * 3981181 * 2
def baseEnd_3981181 : Nat := 1362839617031662229818925

theorem tailTrace_3981181 : CollatzResearch.WordTrace tailWord_3981181 prefixEnd_3981181 1362839617031662229818925 := by
  unfold tailWord_3981181
  simp only [CollatzResearch.WordTrace]
  refine ⟨145205600189868643427791397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96803733459912428951860931 145205600189868643427791397)
  ·
    refine ⟨27226050035600370642710887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 145205600189868643427791397 27226050035600370642710887)
    ·
      refine ⟨40839075053400555964066331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27226050035600370642710887 40839075053400555964066331)
      ·
        refine ⟨61258612580100833946099497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40839075053400555964066331 61258612580100833946099497)
        ·
          refine ⟨45943959435075625459574623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61258612580100833946099497 45943959435075625459574623)
          ·
            refine ⟨68915939152613438189361935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45943959435075625459574623 68915939152613438189361935)
            ·
              refine ⟨103373908728920157284042903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68915939152613438189361935 103373908728920157284042903)
              ·
                refine ⟨155060863093380235926064355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103373908728920157284042903 155060863093380235926064355)
                ·
                  refine ⟨232591294640070353889096533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 155060863093380235926064355 232591294640070353889096533)
                  ·
                    refine ⟨1362839617031662229818925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 232591294640070353889096533 1362839617031662229818925)
                    ·
                      rfl

theorem cell22_3981181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 1, 1, 9].length) (baseStart_3981181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3981181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3981181 prefixEnd_3981181 := by exact prefixLift 3981181
  have htrace : WordTrace (prefixWord ++ tailWord_3981181) baseStart_3981181 baseEnd_3981181 := by
    simpa [prefixWord, tailWord_3981181, baseEnd_3981181] using wordTrace_append hprefix tailTrace_3981181
  have hstable : (prefixWord ++ tailWord_3981181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3981181).length < 2 ^ (prefixWord ++ tailWord_3981181).sum := by decide
  have hdescent : baseEnd_3981181 < baseStart_3981181 := by decide
  rcases family_descends (prefixWord ++ tailWord_3981181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3981196 : List Nat := [2, 2, 1, 2, 1, 2, 1, 2, 1, 8]
def baseStart_3981196 : Nat := 118140960795 + 3981196 * 2 ^ 59
def prefixEnd_3981196 : Nat := 4983230072969 + 3 ^ 40 * 3981196 * 2
def baseEnd_3981196 : Nat := 1362844751838207190693879

theorem tailTrace_3981196 : CollatzResearch.WordTrace tailWord_3981196 prefixEnd_3981196 1362844751838207190693879 := by
  unfold tailWord_3981196
  simp only [CollatzResearch.WordTrace]
  refine ⟨72603073642407150494793721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96804098189876200659724961 72603073642407150494793721)
  ·
    refine ⟨54452305231805362871095291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72603073642407150494793721 54452305231805362871095291)
    ·
      refine ⟨81678457847708044306642937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54452305231805362871095291 81678457847708044306642937)
      ·
        refine ⟨61258843385781033229982203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81678457847708044306642937 61258843385781033229982203)
        ·
          refine ⟨91888265078671549844973305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61258843385781033229982203 91888265078671549844973305)
          ·
            refine ⟨68916198809003662383729979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91888265078671549844973305 68916198809003662383729979)
            ·
              refine ⟨103374298213505493575594969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68916198809003662383729979 103374298213505493575594969)
              ·
                refine ⟨77530723660129120181696227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103374298213505493575594969 77530723660129120181696227)
                ·
                  refine ⟨116296085490193680272544341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77530723660129120181696227 116296085490193680272544341)
                  ·
                    refine ⟨1362844751838207190693879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 116296085490193680272544341 1362844751838207190693879)
                    ·
                      rfl

theorem cell22_3981196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 1, 8].length) (baseStart_3981196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3981196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3981196 prefixEnd_3981196 := by exact prefixLift 3981196
  have htrace : WordTrace (prefixWord ++ tailWord_3981196) baseStart_3981196 baseEnd_3981196 := by
    simpa [prefixWord, tailWord_3981196, baseEnd_3981196] using wordTrace_append hprefix tailTrace_3981196
  have hstable : (prefixWord ++ tailWord_3981196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3981196).length < 2 ^ (prefixWord ++ tailWord_3981196).sum := by decide
  have hdescent : baseEnd_3981196 < baseStart_3981196 := by decide
  rcases family_descends (prefixWord ++ tailWord_3981196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3981206 : List Nat := [5, 3, 1, 1, 3, 1, 1, 1, 6]
def baseStart_3981206 : Nat := 118140960795 + 3981206 * 2 ^ 59
def prefixEnd_3981206 : Nat := 4983230072969 + 3 ^ 40 * 3981206 * 2
def baseEnd_3981206 : Nat := 454282725014190165981283

theorem tailTrace_3981206 : CollatzResearch.WordTrace tailWord_3981206 prefixEnd_3981206 454282725014190165981283 := by
  unfold tailWord_3981206
  simp only [CollatzResearch.WordTrace]
  refine ⟨9075407000923629543590717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 96804341343185381798300981 9075407000923629543590717)
  ·
    refine ⟨3403277625346361078846519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9075407000923629543590717 3403277625346361078846519)
    ·
      refine ⟨5104916438019541618269779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3403277625346361078846519 5104916438019541618269779)
      ·
        refine ⟨7657374657029312427404669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5104916438019541618269779 7657374657029312427404669)
        ·
          refine ⟨2871515496385992160276751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7657374657029312427404669 2871515496385992160276751)
          ·
            refine ⟨4307273244578988240415127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2871515496385992160276751 4307273244578988240415127)
            ·
              refine ⟨6460909866868482360622691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4307273244578988240415127 6460909866868482360622691)
              ·
                refine ⟨9691364800302723540934037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6460909866868482360622691 9691364800302723540934037)
                ·
                  refine ⟨454282725014190165981283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9691364800302723540934037 454282725014190165981283)
                  ·
                    rfl

theorem cell22_3981206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 1, 1, 6].length) (baseStart_3981206 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3981206 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3981206 prefixEnd_3981206 := by exact prefixLift 3981206
  have htrace : WordTrace (prefixWord ++ tailWord_3981206) baseStart_3981206 baseEnd_3981206 := by
    simpa [prefixWord, tailWord_3981206, baseEnd_3981206] using wordTrace_append hprefix tailTrace_3981206
  have hstable : (prefixWord ++ tailWord_3981206).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3981206).length < 2 ^ (prefixWord ++ tailWord_3981206).sum := by decide
  have hdescent : baseEnd_3981206 < baseStart_3981206 := by decide
  rcases family_descends (prefixWord ++ tailWord_3981206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3981322 : List Nat := [3, 1, 2, 2, 4, 1, 1, 1, 4, 3]
def baseStart_3981322 : Nat := 118140960795 + 3981322 * 2 ^ 59
def prefixEnd_3981322 : Nat := 4983230072969 + 3 ^ 40 * 3981322 * 2
def baseEnd_3981322 : Nat := 1362887884213184862043493

theorem tailTrace_3981322 : CollatzResearch.WordTrace tailWord_3981322 prefixEnd_3981322 1362887884213184862043493 := by
  unfold tailWord_3981322
  simp only [CollatzResearch.WordTrace]
  refine ⟨36302685720589456127168555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96807161921571883005782813 36302685720589456127168555)
  ·
    refine ⟨54454028580884184190752833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36302685720589456127168555 54454028580884184190752833)
    ·
      refine ⟨40840521435663138143064625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54454028580884184190752833 40840521435663138143064625)
      ·
        refine ⟨30630391076747353607298469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40840521435663138143064625 30630391076747353607298469)
        ·
          refine ⟨5743198326890128801368463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30630391076747353607298469 5743198326890128801368463)
          ·
            refine ⟨8614797490335193202052695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5743198326890128801368463 8614797490335193202052695)
            ·
              refine ⟨12922196235502789803079043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8614797490335193202052695 12922196235502789803079043)
              ·
                refine ⟨19383294353254184704618565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12922196235502789803079043 19383294353254184704618565)
                ·
                  refine ⟨3634367691235159632115981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19383294353254184704618565 3634367691235159632115981)
                  ·
                    refine ⟨1362887884213184862043493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3634367691235159632115981 1362887884213184862043493)
                    ·
                      rfl

theorem cell22_3981322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 1, 4, 3].length) (baseStart_3981322 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3981322 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3981322 prefixEnd_3981322 := by exact prefixLift 3981322
  have htrace : WordTrace (prefixWord ++ tailWord_3981322) baseStart_3981322 baseEnd_3981322 := by
    simpa [prefixWord, tailWord_3981322, baseEnd_3981322] using wordTrace_append hprefix tailTrace_3981322
  have hstable : (prefixWord ++ tailWord_3981322).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3981322).length < 2 ^ (prefixWord ++ tailWord_3981322).sum := by decide
  have hdescent : baseEnd_3981322 < baseStart_3981322 := by decide
  rcases family_descends (prefixWord ++ tailWord_3981322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3981352 : List Nat := [2, 1, 5, 3, 1, 1, 1, 8]
def baseStart_3981352 : Nat := 118140960795 + 3981352 * 2 ^ 59
def prefixEnd_3981352 : Nat := 4983230072969 + 3 ^ 40 * 3981352 * 2
def baseEnd_3981352 : Nat := 151433128202919420421489

theorem tailTrace_3981352 : CollatzResearch.WordTrace tailWord_3981352 prefixEnd_3981352 151433128202919420421489 := by
  unfold tailWord_3981352
  simp only [CollatzResearch.WordTrace]
  refine ⟨72605918536124569816133155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96807891381499426421510873 72605918536124569816133155)
  ·
    refine ⟨108908877804186854724199733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72605918536124569816133155 108908877804186854724199733)
    ·
      refine ⟨10210207294142517630393725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 108908877804186854724199733 10210207294142517630393725)
      ·
        refine ⟨3828827735303444111397647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10210207294142517630393725 3828827735303444111397647)
        ·
          refine ⟨5743241602955166167096471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3828827735303444111397647 5743241602955166167096471)
          ·
            refine ⟨8614862404432749250644707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5743241602955166167096471 8614862404432749250644707)
            ·
              refine ⟨12922293606649123875967061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8614862404432749250644707 12922293606649123875967061)
              ·
                refine ⟨151433128202919420421489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12922293606649123875967061 151433128202919420421489)
                ·
                  rfl

theorem cell22_3981352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 8].length) (baseStart_3981352 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3981352 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3981352 prefixEnd_3981352 := by exact prefixLift 3981352
  have htrace : WordTrace (prefixWord ++ tailWord_3981352) baseStart_3981352 baseEnd_3981352 := by
    simpa [prefixWord, tailWord_3981352, baseEnd_3981352] using wordTrace_append hprefix tailTrace_3981352
  have hstable : (prefixWord ++ tailWord_3981352).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3981352).length < 2 ^ (prefixWord ++ tailWord_3981352).sum := by decide
  have hdescent : baseEnd_3981352 < baseStart_3981352 := by decide
  rcases family_descends (prefixWord ++ tailWord_3981352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3981363 : List Nat := [1, 1, 1, 2, 4, 1, 3, 2, 7]
def baseStart_3981363 : Nat := 118140960795 + 3981363 * 2 ^ 59
def prefixEnd_3981363 : Nat := 4983230072969 + 3 ^ 40 * 3981363 * 2
def baseEnd_3981363 : Nat := 454300639783691473922789

theorem tailTrace_3981363 : CollatzResearch.WordTrace tailWord_3981363 prefixEnd_3981363 454300639783691473922789 := by
  unfold tailWord_3981363
  simp only [CollatzResearch.WordTrace]
  refine ⟨145212238275209288510916743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96808158850139525673944495 145212238275209288510916743)
  ·
    refine ⟨217818357412813932766375115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145212238275209288510916743 217818357412813932766375115)
    ·
      refine ⟨326727536119220899149562673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217818357412813932766375115 326727536119220899149562673)
      ·
        refine ⟨245045652089415674362172005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 326727536119220899149562673 245045652089415674362172005)
        ·
          refine ⟨45946059766765438942907251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 245045652089415674362172005 45946059766765438942907251)
          ·
            refine ⟨68919089650148158414360877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45946059766765438942907251 68919089650148158414360877)
            ·
              refine ⟨25844658618805559405385329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68919089650148158414360877 25844658618805559405385329)
              ·
                refine ⟨19383493964104169554038997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25844658618805559405385329 19383493964104169554038997)
                ·
                  refine ⟨454300639783691473922789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19383493964104169554038997 454300639783691473922789)
                  ·
                    rfl

theorem cell22_3981363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 2, 7].length) (baseStart_3981363 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3981363 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3981363 prefixEnd_3981363 := by exact prefixLift 3981363
  have htrace : WordTrace (prefixWord ++ tailWord_3981363) baseStart_3981363 baseEnd_3981363 := by
    simpa [prefixWord, tailWord_3981363, baseEnd_3981363] using wordTrace_append hprefix tailTrace_3981363
  have hstable : (prefixWord ++ tailWord_3981363).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3981363).length < 2 ^ (prefixWord ++ tailWord_3981363).sum := by decide
  have hdescent : baseEnd_3981363 < baseStart_3981363 := by decide
  rcases family_descends (prefixWord ++ tailWord_3981363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3981382 : List Nat := [6, 1, 1, 1, 1, 1, 2, 1, 2, 6]
def baseStart_3981382 : Nat := 118140960795 + 3981382 * 2 ^ 59
def prefixEnd_3981382 : Nat := 4983230072969 + 3 ^ 40 * 3981382 * 2
def baseEnd_3981382 : Nat := 1362908423439364705543309

theorem tailTrace_3981382 : CollatzResearch.WordTrace tailWord_3981382 prefixEnd_3981382 1362908423439364705543309 := by
  unfold tailWord_3981382
  simp only [CollatzResearch.WordTrace]
  refine ⟨4537904101941889211120575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 96808620841426969837238933 4537904101941889211120575)
  ·
    refine ⟨6806856152912833816680863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4537904101941889211120575 6806856152912833816680863)
    ·
      refine ⟨10210284229369250725021295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6806856152912833816680863 10210284229369250725021295)
      ·
        refine ⟨15315426344053876087531943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10210284229369250725021295 15315426344053876087531943)
        ·
          refine ⟨22973139516080814131297915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15315426344053876087531943 22973139516080814131297915)
          ·
            refine ⟨34459709274121221196946873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22973139516080814131297915 34459709274121221196946873)
            ·
              refine ⟨25844781955590915897710155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34459709274121221196946873 25844781955590915897710155)
              ·
                refine ⟨38767172933386373846565233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25844781955590915897710155 38767172933386373846565233)
                ·
                  refine ⟨29075379700039780384923925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38767172933386373846565233 29075379700039780384923925)
                  ·
                    refine ⟨1362908423439364705543309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29075379700039780384923925 1362908423439364705543309)
                    ·
                      rfl

theorem cell22_3981382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 1, 2, 6].length) (baseStart_3981382 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3981382 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3981382 prefixEnd_3981382 := by exact prefixLift 3981382
  have htrace : WordTrace (prefixWord ++ tailWord_3981382) baseStart_3981382 baseEnd_3981382 := by
    simpa [prefixWord, tailWord_3981382, baseEnd_3981382] using wordTrace_append hprefix tailTrace_3981382
  have hstable : (prefixWord ++ tailWord_3981382).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3981382).length < 2 ^ (prefixWord ++ tailWord_3981382).sum := by decide
  have hdescent : baseEnd_3981382 < baseStart_3981382 := by decide
  rcases family_descends (prefixWord ++ tailWord_3981382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3981393 : List Nat := [1, 2, 2, 1, 3, 1, 1, 1, 2, 8]
def baseStart_3981393 : Nat := 118140960795 + 3981393 * 2 ^ 59
def prefixEnd_3981393 : Nat := 4983230072969 + 3 ^ 40 * 3981393 * 2
def baseEnd_3981393 : Nat := 1362912188964164343518275

theorem tailTrace_3981393 : CollatzResearch.WordTrace tailWord_3981393 prefixEnd_3981393 1362912188964164343518275 := by
  unfold tailWord_3981393
  simp only [CollatzResearch.WordTrace]
  refine ⟨145213332465100603634508833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96808888310067069089672555 145213332465100603634508833)
  ·
    refine ⟨108909999348825452725881625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145213332465100603634508833 108909999348825452725881625)
    ·
      refine ⟨81682499511619089544411219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108909999348825452725881625 81682499511619089544411219)
      ·
        refine ⟨122523749267428634316616829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81682499511619089544411219 122523749267428634316616829)
        ·
          refine ⟨45946405975285737868731311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122523749267428634316616829 45946405975285737868731311)
          ·
            refine ⟨68919608962928606803096967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45946405975285737868731311 68919608962928606803096967)
            ·
              refine ⟨103379413444392910204645451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68919608962928606803096967 103379413444392910204645451)
              ·
                refine ⟨155069120166589365306968177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103379413444392910204645451 155069120166589365306968177)
                ·
                  refine ⟨116301840124942023980226133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 155069120166589365306968177 116301840124942023980226133)
                  ·
                    refine ⟨1362912188964164343518275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 116301840124942023980226133 1362912188964164343518275)
                    ·
                      rfl

theorem cell22_3981393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 1, 2, 8].length) (baseStart_3981393 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3981393 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3981393 prefixEnd_3981393 := by exact prefixLift 3981393
  have htrace : WordTrace (prefixWord ++ tailWord_3981393) baseStart_3981393 baseEnd_3981393 := by
    simpa [prefixWord, tailWord_3981393, baseEnd_3981393] using wordTrace_append hprefix tailTrace_3981393
  have hstable : (prefixWord ++ tailWord_3981393).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3981393).length < 2 ^ (prefixWord ++ tailWord_3981393).sum := by decide
  have hdescent : baseEnd_3981393 < baseStart_3981393 := by decide
  rcases family_descends (prefixWord ++ tailWord_3981393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3981397 : List Nat := [1, 3, 2, 2, 1, 3, 4, 1, 5]
def baseStart_3981397 : Nat := 118140960795 + 3981397 * 2 ^ 59
def prefixEnd_3981397 : Nat := 4983230072969 + 3 ^ 40 * 3981397 * 2
def baseEnd_3981397 : Nat := 454304519415303222139421

theorem tailTrace_3981397 : CollatzResearch.WordTrace tailWord_3981397 prefixEnd_3981397 454304519415303222139421 := by
  unfold tailWord_3981397
  simp only [CollatzResearch.WordTrace]
  refine ⟨145213478357086112317654445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96808985571390741545102963 145213478357086112317654445)
  ·
    refine ⟨54455054383907292119120417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145213478357086112317654445 54455054383907292119120417)
    ·
      refine ⟨40841290787930469089340313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54455054383907292119120417 40841290787930469089340313)
      ·
        refine ⟨30630968090947851817005235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40841290787930469089340313 30630968090947851817005235)
        ·
          refine ⟨45946452136421777725507853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30630968090947851817005235 45946452136421777725507853)
          ·
            refine ⟨17229919551158166647065445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45946452136421777725507853 17229919551158166647065445)
            ·
              refine ⟨3230609915842156246324771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17229919551158166647065445 3230609915842156246324771)
              ·
                refine ⟨4845914873763234369487157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3230609915842156246324771 4845914873763234369487157)
                ·
                  refine ⟨454304519415303222139421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4845914873763234369487157 454304519415303222139421)
                  ·
                    rfl

theorem cell22_3981397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 4, 1, 5].length) (baseStart_3981397 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3981397 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3981397 prefixEnd_3981397 := by exact prefixLift 3981397
  have htrace : WordTrace (prefixWord ++ tailWord_3981397) baseStart_3981397 baseEnd_3981397 := by
    simpa [prefixWord, tailWord_3981397, baseEnd_3981397] using wordTrace_append hprefix tailTrace_3981397
  have hstable : (prefixWord ++ tailWord_3981397).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3981397).length < 2 ^ (prefixWord ++ tailWord_3981397).sum := by decide
  have hdescent : baseEnd_3981397 < baseStart_3981397 := by decide
  rcases family_descends (prefixWord ++ tailWord_3981397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3981472 : List Nat := [2, 1, 1, 4, 2, 2, 3, 1, 2, 4]
def baseStart_3981472 : Nat := 118140960795 + 3981472 * 2 ^ 59
def prefixEnd_3981472 : Nat := 4983230072969 + 3 ^ 40 * 3981472 * 2
def baseEnd_3981472 : Nat := 1362939232278634470793033

theorem tailTrace_3981472 : CollatzResearch.WordTrace tailWord_3981472 prefixEnd_3981472 1362939232278634470793033 := by
  unfold tailWord_3981472
  simp only [CollatzResearch.WordTrace]
  refine ⟨72608106915907200063317335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96810809221209600084423113 72608106915907200063317335)
  ·
    refine ⟨108912160373860800094976003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72608106915907200063317335 108912160373860800094976003)
    ·
      refine ⟨163368240560791200142464005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108912160373860800094976003 163368240560791200142464005)
      ·
        refine ⟨30631545105148350026712001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 163368240560791200142464005 30631545105148350026712001)
        ·
          refine ⟨22973658828861262520034001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30631545105148350026712001 22973658828861262520034001)
          ·
            refine ⟨17230244121645946890025501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22973658828861262520034001 17230244121645946890025501)
            ·
              refine ⟨6461341545617230083759563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17230244121645946890025501 6461341545617230083759563)
              ·
                refine ⟨9692012318425845125639345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6461341545617230083759563 9692012318425845125639345)
                ·
                  refine ⟨7269009238819383844229509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9692012318425845125639345 7269009238819383844229509)
                  ·
                    refine ⟨1362939232278634470793033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7269009238819383844229509 1362939232278634470793033)
                    ·
                      rfl

theorem cell22_3981472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 3, 1, 2, 4].length) (baseStart_3981472 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3981472 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3981472 prefixEnd_3981472 := by exact prefixLift 3981472
  have htrace : WordTrace (prefixWord ++ tailWord_3981472) baseStart_3981472 baseEnd_3981472 := by
    simpa [prefixWord, tailWord_3981472, baseEnd_3981472] using wordTrace_append hprefix tailTrace_3981472
  have hstable : (prefixWord ++ tailWord_3981472).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3981472).length < 2 ^ (prefixWord ++ tailWord_3981472).sum := by decide
  have hdescent : baseEnd_3981472 < baseStart_3981472 := by decide
  rcases family_descends (prefixWord ++ tailWord_3981472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3981530 : List Nat := [3, 1, 1, 2, 2, 1, 2, 2, 1, 7]
def baseStart_3981530 : Nat := 118140960795 + 3981530 * 2 ^ 59
def prefixEnd_3981530 : Nat := 4983230072969 + 3 ^ 40 * 3981530 * 2
def baseEnd_3981530 : Nat := 1362959086863941652842855

theorem tailTrace_3981530 : CollatzResearch.WordTrace tailWord_3981530 prefixEnd_3981530 1362959086863941652842855 := by
  unfold tailWord_3981530
  simp only [CollatzResearch.WordTrace]
  refine ⟨36304582316401069008061511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96812219510402850688164029 36304582316401069008061511)
  ·
    refine ⟨54456873474601603512092267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36304582316401069008061511 54456873474601603512092267)
    ·
      refine ⟨81685310211902405268138401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54456873474601603512092267 81685310211902405268138401)
      ·
        refine ⟨61263982658926803951103801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81685310211902405268138401 61263982658926803951103801)
        ·
          refine ⟨45947986994195102963327851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61263982658926803951103801 45947986994195102963327851)
          ·
            refine ⟨68921980491292654444991777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45947986994195102963327851 68921980491292654444991777)
            ·
              refine ⟨51691485368469490833743833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68921980491292654444991777 51691485368469490833743833)
              ·
                refine ⟨38768614026352118125307875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51691485368469490833743833 38768614026352118125307875)
                ·
                  refine ⟨58152921039528177187961813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38768614026352118125307875 58152921039528177187961813)
                  ·
                    refine ⟨1362959086863941652842855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58152921039528177187961813 1362959086863941652842855)
                    ·
                      rfl

theorem cell22_3981530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 2, 1, 7].length) (baseStart_3981530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3981530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3981530 prefixEnd_3981530 := by exact prefixLift 3981530
  have htrace : WordTrace (prefixWord ++ tailWord_3981530) baseStart_3981530 baseEnd_3981530 := by
    simpa [prefixWord, tailWord_3981530, baseEnd_3981530] using wordTrace_append hprefix tailTrace_3981530
  have hstable : (prefixWord ++ tailWord_3981530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3981530).length < 2 ^ (prefixWord ++ tailWord_3981530).sum := by decide
  have hdescent : baseEnd_3981530 < baseStart_3981530 := by decide
  rcases family_descends (prefixWord ++ tailWord_3981530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3981538 : List Nat := [3, 3, 4, 1, 2, 1, 8]
def baseStart_3981538 : Nat := 118140960795 + 3981538 * 2 ^ 59
def prefixEnd_3981538 : Nat := 4983230072969 + 3 ^ 40 * 3981538 * 2
def baseEnd_3981538 : Nat := 50480067608423418468253

theorem tailTrace_3981538 : CollatzResearch.WordTrace tailWord_3981538 prefixEnd_3981538 50480067608423418468253 := by
  unfold tailWord_3981538
  simp only [CollatzResearch.WordTrace]
  refine ⟨36304655262393823349634317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96812414033050195599024845 36304655262393823349634317)
  ·
    refine ⟨13614245723397683756112869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36304655262393823349634317 13614245723397683756112869)
    ·
      refine ⟨2552671073137065704271163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13614245723397683756112869 2552671073137065704271163)
      ·
        refine ⟨3829006609705598556406745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2552671073137065704271163 3829006609705598556406745)
        ·
          refine ⟨2871754957279198917305059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3829006609705598556406745 2871754957279198917305059)
          ·
            refine ⟨4307632435918798375957589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2871754957279198917305059 4307632435918798375957589)
            ·
              refine ⟨50480067608423418468253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4307632435918798375957589 50480067608423418468253)
              ·
                rfl

theorem cell22_3981538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 8].length) (baseStart_3981538 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3981538 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3981538 prefixEnd_3981538 := by exact prefixLift 3981538
  have htrace : WordTrace (prefixWord ++ tailWord_3981538) baseStart_3981538 baseEnd_3981538 := by
    simpa [prefixWord, tailWord_3981538, baseEnd_3981538] using wordTrace_append hprefix tailTrace_3981538
  have hstable : (prefixWord ++ tailWord_3981538).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3981538).length < 2 ^ (prefixWord ++ tailWord_3981538).sum := by decide
  have hdescent : baseEnd_3981538 < baseStart_3981538 := by decide
  rcases family_descends (prefixWord ++ tailWord_3981538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3981592 : List Nat := [2, 1, 2, 3, 1, 2, 3, 2, 1, 5]
def baseStart_3981592 : Nat := 118140960795 + 3981592 * 2 ^ 59
def prefixEnd_3981592 : Nat := 4983230072969 + 3 ^ 40 * 3981592 * 2
def baseEnd_3981592 : Nat := 1362980310730994157792665

theorem tailTrace_3981592 : CollatzResearch.WordTrace tailWord_3981592 prefixEnd_3981592 1362980310730994157792665 := by
  unfold tailWord_3981592
  simp only [CollatzResearch.WordTrace]
  refine ⟨72610295295689830310501515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96813727060919773747335353 72610295295689830310501515)
  ·
    refine ⟨108915442943534745465752273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72610295295689830310501515 108915442943534745465752273)
    ·
      refine ⟨81686582207651059099314205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108915442943534745465752273 81686582207651059099314205)
      ·
        refine ⟨30632468327869147162242827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81686582207651059099314205 30632468327869147162242827)
        ·
          refine ⟨45948702491803720743364241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30632468327869147162242827 45948702491803720743364241)
          ·
            refine ⟨34461526868852790557523181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45948702491803720743364241 34461526868852790557523181)
            ·
              refine ⟨12923072575819796459071193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34461526868852790557523181 12923072575819796459071193)
              ·
                refine ⟨9692304431864847344303395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12923072575819796459071193 9692304431864847344303395)
                ·
                  refine ⟨14538456647797271016455093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9692304431864847344303395 14538456647797271016455093)
                  ·
                    refine ⟨1362980310730994157792665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14538456647797271016455093 1362980310730994157792665)
                    ·
                      rfl

theorem cell22_3981592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 2, 1, 5].length) (baseStart_3981592 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3981592 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3981592 prefixEnd_3981592 := by exact prefixLift 3981592
  have htrace : WordTrace (prefixWord ++ tailWord_3981592) baseStart_3981592 baseEnd_3981592 := by
    simpa [prefixWord, tailWord_3981592, baseEnd_3981592] using wordTrace_append hprefix tailTrace_3981592
  have hstable : (prefixWord ++ tailWord_3981592).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3981592).length < 2 ^ (prefixWord ++ tailWord_3981592).sum := by decide
  have hdescent : baseEnd_3981592 < baseStart_3981592 := by decide
  rcases family_descends (prefixWord ++ tailWord_3981592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3981605 : List Nat := [1, 3, 1, 2, 15]
def baseStart_3981605 : Nat := 118140960795 + 3981605 * 2 ^ 59
def prefixEnd_3981605 : Nat := 4983230072969 + 3 ^ 40 * 3981605 * 2
def baseEnd_3981605 : Nat := 5608990785582989535875

theorem tailTrace_3981605 : CollatzResearch.WordTrace tailWord_3981605 prefixEnd_3981605 5608990785582989535875 := by
  unfold tailWord_3981605
  simp only [CollatzResearch.WordTrace]
  refine ⟨145221064740332563841226269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96814043160221709227484179 145221064740332563841226269)
  ·
    refine ⟨54457899277624711440459851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145221064740332563841226269 54457899277624711440459851)
    ·
      refine ⟨81686848916437067160689777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54457899277624711440459851 81686848916437067160689777)
      ·
        refine ⟨61265136687327800370517333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81686848916437067160689777 61265136687327800370517333)
        ·
          refine ⟨5608990785582989535875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 15 61265136687327800370517333 5608990785582989535875)
          ·
            rfl

theorem cell22_3981605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 15].length) (baseStart_3981605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3981605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3981605 prefixEnd_3981605 := by exact prefixLift 3981605
  have htrace : WordTrace (prefixWord ++ tailWord_3981605) baseStart_3981605 baseEnd_3981605 := by
    simpa [prefixWord, tailWord_3981605, baseEnd_3981605] using wordTrace_append hprefix tailTrace_3981605
  have hstable : (prefixWord ++ tailWord_3981605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3981605).length < 2 ^ (prefixWord ++ tailWord_3981605).sum := by decide
  have hdescent : baseEnd_3981605 < baseStart_3981605 := by decide
  rcases family_descends (prefixWord ++ tailWord_3981605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3981660 : List Nat := [2, 2, 4, 3, 1, 2, 1, 2, 2, 3]
def baseStart_3981660 : Nat := 118140960795 + 3981660 * 2 ^ 59
def prefixEnd_3981660 : Nat := 4983230072969 + 3 ^ 40 * 3981660 * 2
def baseEnd_3981660 : Nat := 1363003588520664647092457

theorem tailTrace_3981660 : CollatzResearch.WordTrace tailWord_3981660 prefixEnd_3981660 1363003588520664647092457 := by
  unfold tailWord_3981660
  simp only [CollatzResearch.WordTrace]
  refine ⟨72611535377566654117239217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96815380503422205489652289 72611535377566654117239217)
  ·
    refine ⟨54458651533174990587929413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72611535377566654117239217 54458651533174990587929413)
    ·
      refine ⟨10210997162470310735236765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54458651533174990587929413 10210997162470310735236765)
      ·
        refine ⟨3829123935926366525713787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10210997162470310735236765 3829123935926366525713787)
        ·
          refine ⟨5743685903889549788570681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3829123935926366525713787 5743685903889549788570681)
          ·
            refine ⟨4307764427917162341428011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5743685903889549788570681 4307764427917162341428011)
            ·
              refine ⟨6461646641875743512142017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4307764427917162341428011 6461646641875743512142017)
              ·
                refine ⟨4846234981406807634106513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6461646641875743512142017 4846234981406807634106513)
                ·
                  refine ⟨3634676236055105725579885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4846234981406807634106513 3634676236055105725579885)
                  ·
                    refine ⟨1363003588520664647092457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3634676236055105725579885 1363003588520664647092457)
                    ·
                      rfl

theorem cell22_3981660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 1, 2, 2, 3].length) (baseStart_3981660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3981660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3981660 prefixEnd_3981660 := by exact prefixLift 3981660
  have htrace : WordTrace (prefixWord ++ tailWord_3981660) baseStart_3981660 baseEnd_3981660 := by
    simpa [prefixWord, tailWord_3981660, baseEnd_3981660] using wordTrace_append hprefix tailTrace_3981660
  have hstable : (prefixWord ++ tailWord_3981660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3981660).length < 2 ^ (prefixWord ++ tailWord_3981660).sum := by decide
  have hdescent : baseEnd_3981660 < baseStart_3981660 := by decide
  rcases family_descends (prefixWord ++ tailWord_3981660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3981667 : List Nat := [1, 1, 1, 5, 2, 1, 3, 1, 7]
def baseStart_3981667 : Nat := 118140960795 + 3981667 * 2 ^ 59
def prefixEnd_3981667 : Nat := 4983230072969 + 3 ^ 40 * 3981667 * 2
def baseEnd_3981667 : Nat := 454335328254572987389145

theorem tailTrace_3981667 : CollatzResearch.WordTrace tailWord_3981667 prefixEnd_3981667 454335328254572987389145 := by
  unfold tailWord_3981667
  simp only [CollatzResearch.WordTrace]
  refine ⟨145223326066107948429983255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96815550710738632286655503 145223326066107948429983255)
  ·
    refine ⟨217834989099161922644974883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145223326066107948429983255 217834989099161922644974883)
    ·
      refine ⟨326752483648742883967462325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217834989099161922644974883 326752483648742883967462325)
      ·
        refine ⟨30633045342069645371949593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 326752483648742883967462325 30633045342069645371949593)
        ·
          refine ⟨22974784006552234028962195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30633045342069645371949593 22974784006552234028962195)
          ·
            refine ⟨34462176009828351043443293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22974784006552234028962195 34462176009828351043443293)
            ·
              refine ⟨12923316003685631641291235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34462176009828351043443293 12923316003685631641291235)
              ·
                refine ⟨19384974005528447461936853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12923316003685631641291235 19384974005528447461936853)
                ·
                  refine ⟨454335328254572987389145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19384974005528447461936853 454335328254572987389145)
                  ·
                    rfl

theorem cell22_3981667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 1, 7].length) (baseStart_3981667 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3981667 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3981667 prefixEnd_3981667 := by exact prefixLift 3981667
  have htrace : WordTrace (prefixWord ++ tailWord_3981667) baseStart_3981667 baseEnd_3981667 := by
    simpa [prefixWord, tailWord_3981667, baseEnd_3981667] using wordTrace_append hprefix tailTrace_3981667
  have hstable : (prefixWord ++ tailWord_3981667).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3981667).length < 2 ^ (prefixWord ++ tailWord_3981667).sum := by decide
  have hdescent : baseEnd_3981667 < baseStart_3981667 := by decide
  rcases family_descends (prefixWord ++ tailWord_3981667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3981671 : List Nat := [1, 1, 5, 1, 3, 2, 2, 1, 3, 3]
def baseStart_3981671 : Nat := 118140960795 + 3981671 * 2 ^ 59
def prefixEnd_3981671 : Nat := 4983230072969 + 3 ^ 40 * 3981671 * 2
def baseEnd_3981671 : Nat := 1363007354045464285067423

theorem tailTrace_3981671 : CollatzResearch.WordTrace tailWord_3981671 prefixEnd_3981671 1363007354045464285067423 := by
  unfold tailWord_3981671
  simp only [CollatzResearch.WordTrace]
  refine ⟨145223471958093457113128867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96815647972062304742085911 145223471958093457113128867)
  ·
    refine ⟨217835207937140185669693301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145223471958093457113128867 217835207937140185669693301)
    ·
      refine ⟨20422050744106892406533747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 217835207937140185669693301 20422050744106892406533747)
      ·
        refine ⟨30633076116160338609800621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20422050744106892406533747 30633076116160338609800621)
        ·
          refine ⟨11487403543560126978675233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30633076116160338609800621 11487403543560126978675233)
          ·
            refine ⟨8615552657670095234006425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11487403543560126978675233 8615552657670095234006425)
            ·
              refine ⟨6461664493252571425504819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8615552657670095234006425 6461664493252571425504819)
              ·
                refine ⟨9692496739878857138257229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6461664493252571425504819 9692496739878857138257229)
                ·
                  refine ⟨3634686277454571426846461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9692496739878857138257229 3634686277454571426846461)
                  ·
                    refine ⟨1363007354045464285067423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3634686277454571426846461 1363007354045464285067423)
                    ·
                      rfl

theorem cell22_3981671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 2, 1, 3, 3].length) (baseStart_3981671 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3981671 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3981671 prefixEnd_3981671 := by exact prefixLift 3981671
  have htrace : WordTrace (prefixWord ++ tailWord_3981671) baseStart_3981671 baseEnd_3981671 := by
    simpa [prefixWord, tailWord_3981671, baseEnd_3981671] using wordTrace_append hprefix tailTrace_3981671
  have hstable : (prefixWord ++ tailWord_3981671).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3981671).length < 2 ^ (prefixWord ++ tailWord_3981671).sum := by decide
  have hdescent : baseEnd_3981671 < baseStart_3981671 := by decide
  rcases family_descends (prefixWord ++ tailWord_3981671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3981780 : List Nat := [2, 4, 1, 2, 2, 3, 2, 2, 4]
def baseStart_3981780 : Nat := 118140960795 + 3981780 * 2 ^ 59
def prefixEnd_3981780 : Nat := 4983230072969 + 3 ^ 40 * 3981780 * 2
def baseEnd_3981780 : Nat := 454348222324341444697363

theorem tailTrace_3981780 : CollatzResearch.WordTrace tailWord_3981780 prefixEnd_3981780 454348222324341444697363 := by
  unfold tailWord_3981780
  simp only [CollatzResearch.WordTrace]
  refine ⟨72613723757349284364423397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96818298343132379152564529 72613723757349284364423397)
  ·
    refine ⟨13615073204502990818329387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72613723757349284364423397 13615073204502990818329387)
    ·
      refine ⟨20422609806754486227494081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13615073204502990818329387 20422609806754486227494081)
      ·
        refine ⟨15316957355065864670620561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20422609806754486227494081 15316957355065864670620561)
        ·
          refine ⟨11487718016299398502965421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15316957355065864670620561 11487718016299398502965421)
          ·
            refine ⟨4307894256112274438612033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11487718016299398502965421 4307894256112274438612033)
            ·
              refine ⟨3230920692084205828959025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4307894256112274438612033 3230920692084205828959025)
              ·
                refine ⟨2423190519063154371719269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3230920692084205828959025 2423190519063154371719269)
                ·
                  refine ⟨454348222324341444697363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2423190519063154371719269 454348222324341444697363)
                  ·
                    rfl

theorem cell22_3981780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 2, 2, 4].length) (baseStart_3981780 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3981780 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3981780 prefixEnd_3981780 := by exact prefixLift 3981780
  have htrace : WordTrace (prefixWord ++ tailWord_3981780) baseStart_3981780 baseEnd_3981780 := by
    simpa [prefixWord, tailWord_3981780, baseEnd_3981780] using wordTrace_append hprefix tailTrace_3981780
  have hstable : (prefixWord ++ tailWord_3981780).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3981780).length < 2 ^ (prefixWord ++ tailWord_3981780).sum := by decide
  have hdescent : baseEnd_3981780 < baseStart_3981780 := by decide
  rcases family_descends (prefixWord ++ tailWord_3981780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3981806 : List Nat := [4, 1, 2, 1, 2, 2, 1, 1, 5, 3]
def baseStart_3981806 : Nat := 118140960795 + 3981806 * 2 ^ 59
def prefixEnd_3981806 : Nat := 4983230072969 + 3 ^ 40 * 3981806 * 2
def baseEnd_3981806 : Nat := 1363053567304368932942009

theorem tailTrace_3981806 : CollatzResearch.WordTrace tailWord_3981806 prefixEnd_3981806 1363053567304368932942009 := by
  unfold tailWord_3981806
  simp only [CollatzResearch.WordTrace]
  refine ⟨18153549476575546896161659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96818930541736250112862181 18153549476575546896161659)
  ·
    refine ⟨27230324214863320344242489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18153549476575546896161659 27230324214863320344242489)
    ·
      refine ⟨20422743161147490258181867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27230324214863320344242489 20422743161147490258181867)
      ·
        refine ⟨30634114741721235387272801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20422743161147490258181867 30634114741721235387272801)
        ·
          refine ⟨22975586056290926540454601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30634114741721235387272801 22975586056290926540454601)
          ·
            refine ⟨17231689542218194905340951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22975586056290926540454601 17231689542218194905340951)
            ·
              refine ⟨25847534313327292358011427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17231689542218194905340951 25847534313327292358011427)
              ·
                refine ⟨38771301469990938537017141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25847534313327292358011427 38771301469990938537017141)
                ·
                  refine ⟨3634809512811650487845357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38771301469990938537017141 3634809512811650487845357)
                  ·
                    refine ⟨1363053567304368932942009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3634809512811650487845357 1363053567304368932942009)
                    ·
                      rfl

theorem cell22_3981806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 1, 5, 3].length) (baseStart_3981806 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3981806 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3981806 prefixEnd_3981806 := by exact prefixLift 3981806
  have htrace : WordTrace (prefixWord ++ tailWord_3981806) baseStart_3981806 baseEnd_3981806 := by
    simpa [prefixWord, tailWord_3981806, baseEnd_3981806] using wordTrace_append hprefix tailTrace_3981806
  have hstable : (prefixWord ++ tailWord_3981806).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3981806).length < 2 ^ (prefixWord ++ tailWord_3981806).sum := by decide
  have hdescent : baseEnd_3981806 < baseStart_3981806 := by decide
  rcases family_descends (prefixWord ++ tailWord_3981806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3981810 : List Nat := [3, 2, 1, 4, 3, 1, 1, 1, 2, 4]
def baseStart_3981810 : Nat := 118140960795 + 3981810 * 2 ^ 59
def prefixEnd_3981810 : Nat := 4983230072969 + 3 ^ 40 * 3981810 * 2
def baseEnd_3981810 : Nat := 1363054936586114255841997

theorem tailTrace_3981810 : CollatzResearch.WordTrace tailWord_3981810 prefixEnd_3981810 1363054936586114255841997 := by
  unfold tailWord_3981810
  simp only [CollatzResearch.WordTrace]
  refine ⟨36307135426147470963109721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96819027803059922568292589 36307135426147470963109721)
  ·
    refine ⟨27230351569610603222332291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36307135426147470963109721 27230351569610603222332291)
    ·
      refine ⟨40845527354415904833498437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27230351569610603222332291 40845527354415904833498437)
      ·
        refine ⟨7658536378952982156280957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40845527354415904833498437 7658536378952982156280957)
        ·
          refine ⟨2871951142107368308605359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7658536378952982156280957 2871951142107368308605359)
          ·
            refine ⟨4307926713161052462908039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2871951142107368308605359 4307926713161052462908039)
            ·
              refine ⟨6461890069741578694362059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4307926713161052462908039 6461890069741578694362059)
              ·
                refine ⟨9692835104612368041543089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6461890069741578694362059 9692835104612368041543089)
                ·
                  refine ⟨7269626328459276031157317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9692835104612368041543089 7269626328459276031157317)
                  ·
                    refine ⟨1363054936586114255841997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7269626328459276031157317 1363054936586114255841997)
                    ·
                      rfl

theorem cell22_3981810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 1, 1, 2, 4].length) (baseStart_3981810 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3981810 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3981810 prefixEnd_3981810 := by exact prefixLift 3981810
  have htrace : WordTrace (prefixWord ++ tailWord_3981810) baseStart_3981810 baseEnd_3981810 := by
    simpa [prefixWord, tailWord_3981810, baseEnd_3981810] using wordTrace_append hprefix tailTrace_3981810
  have hstable : (prefixWord ++ tailWord_3981810).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3981810).length < 2 ^ (prefixWord ++ tailWord_3981810).sum := by decide
  have hdescent : baseEnd_3981810 < baseStart_3981810 := by decide
  rcases family_descends (prefixWord ++ tailWord_3981810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3981823 : List Nat := [1, 1, 2, 2, 1, 2, 6, 3, 1, 3]
def baseStart_3981823 : Nat := 118140960795 + 3981823 * 2 ^ 59
def prefixEnd_3981823 : Nat := 4983230072969 + 3 ^ 40 * 3981823 * 2
def baseEnd_3981823 : Nat := 1363059386751786555266957

theorem tailTrace_3981823 : CollatzResearch.WordTrace tailWord_3981823 prefixEnd_3981823 1363059386751786555266957 := by
  unfold tailWord_3981823
  simp only [CollatzResearch.WordTrace]
  refine ⟨145229015853542787072662123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96819343902361858048441415 145229015853542787072662123)
  ·
    refine ⟨217843523780314180608993185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145229015853542787072662123 217843523780314180608993185)
    ·
      refine ⟨163382642835235635456744889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217843523780314180608993185 163382642835235635456744889)
      ·
        refine ⟨122536982126426726592558667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163382642835235635456744889 122536982126426726592558667)
        ·
          refine ⟨183805473189640089888838001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122536982126426726592558667 183805473189640089888838001)
          ·
            refine ⟨137854104892230067416628501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183805473189640089888838001 137854104892230067416628501)
            ·
              refine ⟨6461911166823284410154461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 137854104892230067416628501 6461911166823284410154461)
              ·
                refine ⟨2423216687558731653807923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6461911166823284410154461 2423216687558731653807923)
                ·
                  refine ⟨3634825031338097480711885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2423216687558731653807923 3634825031338097480711885)
                  ·
                    refine ⟨1363059386751786555266957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3634825031338097480711885 1363059386751786555266957)
                    ·
                      rfl

theorem cell22_3981823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 6, 3, 1, 3].length) (baseStart_3981823 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3981823 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3981823 prefixEnd_3981823 := by exact prefixLift 3981823
  have htrace : WordTrace (prefixWord ++ tailWord_3981823) baseStart_3981823 baseEnd_3981823 := by
    simpa [prefixWord, tailWord_3981823, baseEnd_3981823] using wordTrace_append hprefix tailTrace_3981823
  have hstable : (prefixWord ++ tailWord_3981823).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3981823).length < 2 ^ (prefixWord ++ tailWord_3981823).sum := by decide
  have hdescent : baseEnd_3981823 < baseStart_3981823 := by decide
  rcases family_descends (prefixWord ++ tailWord_3981823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3981834 : List Nat := [3, 1, 2, 2, 2, 1, 1, 1, 4, 5]
def baseStart_3981834 : Nat := 118140960795 + 3981834 * 2 ^ 59
def prefixEnd_3981834 : Nat := 4983230072969 + 3 ^ 40 * 3981834 * 2
def baseEnd_3981834 : Nat := 1363063152276586193241923

theorem tailTrace_3981834 : CollatzResearch.WordTrace tailWord_3981834 prefixEnd_3981834 1363063152276586193241923 := by
  unfold tailWord_3981834
  simp only [CollatzResearch.WordTrace]
  refine ⟨36307354264125733987828139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96819611371001957300875037 36307354264125733987828139)
  ·
    refine ⟨54461031396188600981742209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36307354264125733987828139 54461031396188600981742209)
    ·
      refine ⟨40845773547141450736306657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54461031396188600981742209 40845773547141450736306657)
      ·
        refine ⟨30634330160356088052229993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40845773547141450736306657 30634330160356088052229993)
        ·
          refine ⟨22975747620267066039172495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30634330160356088052229993 22975747620267066039172495)
          ·
            refine ⟨34463621430400599058758743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22975747620267066039172495 34463621430400599058758743)
            ·
              refine ⟨51695432145600898588138115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34463621430400599058758743 51695432145600898588138115)
              ·
                refine ⟨77543148218401347882207173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51695432145600898588138115 77543148218401347882207173)
                ·
                  refine ⟨14539340290950252727913845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77543148218401347882207173 14539340290950252727913845)
                  ·
                    refine ⟨1363063152276586193241923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14539340290950252727913845 1363063152276586193241923)
                    ·
                      rfl

theorem cell22_3981834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 1, 4, 5].length) (baseStart_3981834 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3981834 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3981834 prefixEnd_3981834 := by exact prefixLift 3981834
  have htrace : WordTrace (prefixWord ++ tailWord_3981834) baseStart_3981834 baseEnd_3981834 := by
    simpa [prefixWord, tailWord_3981834, baseEnd_3981834] using wordTrace_append hprefix tailTrace_3981834
  have hstable : (prefixWord ++ tailWord_3981834).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3981834).length < 2 ^ (prefixWord ++ tailWord_3981834).sum := by decide
  have hdescent : baseEnd_3981834 < baseStart_3981834 := by decide
  rcases family_descends (prefixWord ++ tailWord_3981834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3981836 : List Nat := [2, 2, 1, 2, 4, 1, 3, 2, 5]
def baseStart_3981836 : Nat := 118140960795 + 3981836 * 2 ^ 59
def prefixEnd_3981836 : Nat := 4983230072969 + 3 ^ 40 * 3981836 * 2
def baseEnd_3981836 : Nat := 454354612305819618230639

theorem tailTrace_3981836 : CollatzResearch.WordTrace tailWord_3981836 prefixEnd_3981836 454354612305819618230639 := by
  unfold tailWord_3981836
  simp only [CollatzResearch.WordTrace]
  refine ⟨72614745001247845146442681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96819660001663793528590241 72614745001247845146442681)
  ·
    refine ⟨54461058750935883859832011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72614745001247845146442681 54461058750935883859832011)
    ·
      refine ⟨81691588126403825789748017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54461058750935883859832011 81691588126403825789748017)
      ·
        refine ⟨61268691094802869342311013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81691588126403825789748017 61268691094802869342311013)
        ·
          refine ⟨11487879580275538001683315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61268691094802869342311013 11487879580275538001683315)
          ·
            refine ⟨17231819370413307002524973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11487879580275538001683315 17231819370413307002524973)
            ·
              refine ⟨6461932263904990125946865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17231819370413307002524973 6461932263904990125946865)
              ·
                refine ⟨4846449197928742594460149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6461932263904990125946865 4846449197928742594460149)
                ·
                  refine ⟨454354612305819618230639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4846449197928742594460149 454354612305819618230639)
                  ·
                    rfl

theorem cell22_3981836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 3, 2, 5].length) (baseStart_3981836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3981836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3981836 prefixEnd_3981836 := by exact prefixLift 3981836
  have htrace : WordTrace (prefixWord ++ tailWord_3981836) baseStart_3981836 baseEnd_3981836 := by
    simpa [prefixWord, tailWord_3981836, baseEnd_3981836] using wordTrace_append hprefix tailTrace_3981836
  have hstable : (prefixWord ++ tailWord_3981836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3981836).length < 2 ^ (prefixWord ++ tailWord_3981836).sum := by decide
  have hdescent : baseEnd_3981836 < baseStart_3981836 := by decide
  rcases family_descends (prefixWord ++ tailWord_3981836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3981853 : List Nat := [1, 4, 2, 2, 1, 3, 3, 1, 5]
def baseStart_3981853 : Nat := 118140960795 + 3981853 * 2 ^ 59
def prefixEnd_3981853 : Nat := 4983230072969 + 3 ^ 40 * 3981853 * 2
def baseEnd_3981853 : Nat := 454356552121625492338955

theorem tailTrace_3981853 : CollatzResearch.WordTrace tailWord_3981853 prefixEnd_3981853 454356552121625492338955 := by
  unfold tailWord_3981853
  simp only [CollatzResearch.WordTrace]
  refine ⟨145230110043434102196254213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96820073362289401464169475 145230110043434102196254213)
  ·
    refine ⟨27230645633143894161797665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 145230110043434102196254213 27230645633143894161797665)
    ·
      refine ⟨20422984224857920621348249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27230645633143894161797665 20422984224857920621348249)
      ·
        refine ⟨15317238168643440466011187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20422984224857920621348249 15317238168643440466011187)
        ·
          refine ⟨22975857252965160699016781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15317238168643440466011187 22975857252965160699016781)
          ·
            refine ⟨8615946469861935262131293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22975857252965160699016781 8615946469861935262131293)
            ·
              refine ⟨3230979926198225723299235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8615946469861935262131293 3230979926198225723299235)
              ·
                refine ⟨4846469889297338584948853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3230979926198225723299235 4846469889297338584948853)
                ·
                  refine ⟨454356552121625492338955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4846469889297338584948853 454356552121625492338955)
                  ·
                    rfl

theorem cell22_3981853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 3, 1, 5].length) (baseStart_3981853 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3981853 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3981853 prefixEnd_3981853 := by exact prefixLift 3981853
  have htrace : WordTrace (prefixWord ++ tailWord_3981853) baseStart_3981853 baseEnd_3981853 := by
    simpa [prefixWord, tailWord_3981853, baseEnd_3981853] using wordTrace_append hprefix tailTrace_3981853
  have hstable : (prefixWord ++ tailWord_3981853).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3981853).length < 2 ^ (prefixWord ++ tailWord_3981853).sum := by decide
  have hdescent : baseEnd_3981853 < baseStart_3981853 := by decide
  rcases family_descends (prefixWord ++ tailWord_3981853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3981879 : List Nat := [1, 1, 3, 1, 2, 3, 2, 1, 3, 5]
def baseStart_3981879 : Nat := 118140960795 + 3981879 * 2 ^ 59
def prefixEnd_3981879 : Nat := 4983230072969 + 3 ^ 40 * 3981879 * 2
def baseEnd_3981879 : Nat := 1363078556696221075866785

theorem tailTrace_3981879 : CollatzResearch.WordTrace tailWord_3981879 prefixEnd_3981879 1363078556696221075866785 := by
  unfold tailWord_3981879
  simp only [CollatzResearch.WordTrace]
  refine ⟨145231058341339908636700691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96820705560893272424467127 145231058341339908636700691)
  ·
    refine ⟨217846587512009862955051037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145231058341339908636700691 217846587512009862955051037)
    ·
      refine ⟨81692470317003698608144139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 217846587512009862955051037 81692470317003698608144139)
      ·
        refine ⟨122538705475505547912216209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81692470317003698608144139 122538705475505547912216209)
        ·
          refine ⟨91904029106629160934162157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122538705475505547912216209 91904029106629160934162157)
          ·
            refine ⟨34464010914985935350310809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91904029106629160934162157 34464010914985935350310809)
            ·
              refine ⟨25848008186239451512733107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34464010914985935350310809 25848008186239451512733107)
              ·
                refine ⟨38772012279359177269099661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25848008186239451512733107 38772012279359177269099661)
                ·
                  refine ⟨14539504604759691475912373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38772012279359177269099661 14539504604759691475912373)
                  ·
                    refine ⟨1363078556696221075866785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14539504604759691475912373 1363078556696221075866785)
                    ·
                      rfl

theorem cell22_3981879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 1, 3, 5].length) (baseStart_3981879 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3981879 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3981879 prefixEnd_3981879 := by exact prefixLift 3981879
  have htrace : WordTrace (prefixWord ++ tailWord_3981879) baseStart_3981879 baseEnd_3981879 := by
    simpa [prefixWord, tailWord_3981879, baseEnd_3981879] using wordTrace_append hprefix tailTrace_3981879
  have hstable : (prefixWord ++ tailWord_3981879).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3981879).length < 2 ^ (prefixWord ++ tailWord_3981879).sum := by decide
  have hdescent : baseEnd_3981879 < baseStart_3981879 := by decide
  rcases family_descends (prefixWord ++ tailWord_3981879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3981909 : List Nat := [1, 3, 2, 2, 1, 1, 3, 9]
def baseStart_3981909 : Nat := 118140960795 + 3981909 * 2 ^ 59
def prefixEnd_3981909 : Nat := 4983230072969 + 3 ^ 40 * 3981909 * 2
def baseEnd_3981909 : Nat := 151454314034367888624077

theorem tailTrace_3981909 : CollatzResearch.WordTrace tailWord_3981909 prefixEnd_3981909 151454314034367888624077 := by
  unfold tailWord_3981909
  simp only [CollatzResearch.WordTrace]
  refine ⟨145232152531231223760292781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96821435020820815840195187 145232152531231223760292781)
  ·
    refine ⟨54462057199211708910109793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145232152531231223760292781 54462057199211708910109793)
    ·
      refine ⟨40846542899408781682582345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54462057199211708910109793 40846542899408781682582345)
      ·
        refine ⟨30634907174556586261936759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40846542899408781682582345 30634907174556586261936759)
        ·
          refine ⟨45952360761834879392905139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30634907174556586261936759 45952360761834879392905139)
          ·
            refine ⟨68928541142752319089357709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45952360761834879392905139 68928541142752319089357709)
            ·
              refine ⟨25848202928532119658509141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68928541142752319089357709 25848202928532119658509141)
              ·
                refine ⟨151454314034367888624077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 25848202928532119658509141 151454314034367888624077)
                ·
                  rfl

theorem cell22_3981909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 9].length) (baseStart_3981909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3981909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3981909 prefixEnd_3981909 := by exact prefixLift 3981909
  have htrace : WordTrace (prefixWord ++ tailWord_3981909) baseStart_3981909 baseEnd_3981909 := by
    simpa [prefixWord, tailWord_3981909, baseEnd_3981909] using wordTrace_append hprefix tailTrace_3981909
  have hstable : (prefixWord ++ tailWord_3981909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3981909).length < 2 ^ (prefixWord ++ tailWord_3981909).sum := by decide
  have hdescent : baseEnd_3981909 < baseStart_3981909 := by decide
  rcases family_descends (prefixWord ++ tailWord_3981909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3981956 : List Nat := [2, 3, 2, 1, 3, 1, 1, 1, 2, 6]
def baseStart_3981956 : Nat := 118140960795 + 3981956 * 2 ^ 59
def prefixEnd_3981956 : Nat := 4983230072969 + 3 ^ 40 * 3981956 * 2
def baseEnd_3981956 : Nat := 1363104915369818541691549

theorem tailTrace_3981956 : CollatzResearch.WordTrace tailWord_3981956 prefixEnd_3981956 1363104915369818541691549 := by
  unfold tailWord_3981956
  simp only [CollatzResearch.WordTrace]
  refine ⟨72616933381030475393626861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96822577841373967191502481 72616933381030475393626861)
  ·
    refine ⟨27231350017886428272610073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72616933381030475393626861 27231350017886428272610073)
    ·
      refine ⟨20423512513414821204457555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27231350017886428272610073 20423512513414821204457555)
      ·
        refine ⟨30635268770122231806686333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20423512513414821204457555 30635268770122231806686333)
        ·
          refine ⟨11488225788795836927507375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30635268770122231806686333 11488225788795836927507375)
          ·
            refine ⟨17232338683193755391261063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11488225788795836927507375 17232338683193755391261063)
            ·
              refine ⟨25848508024790633086891595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17232338683193755391261063 25848508024790633086891595)
              ·
                refine ⟨38772762037185949630337393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25848508024790633086891595 38772762037185949630337393)
                ·
                  refine ⟨29079571527889462222753045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38772762037185949630337393 29079571527889462222753045)
                  ·
                    refine ⟨1363104915369818541691549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29079571527889462222753045 1363104915369818541691549)
                    ·
                      rfl

theorem cell22_3981956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 1, 2, 6].length) (baseStart_3981956 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3981956 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3981956 prefixEnd_3981956 := by exact prefixLift 3981956
  have htrace : WordTrace (prefixWord ++ tailWord_3981956) baseStart_3981956 baseEnd_3981956 := by
    simpa [prefixWord, tailWord_3981956, baseEnd_3981956] using wordTrace_append hprefix tailTrace_3981956
  have hstable : (prefixWord ++ tailWord_3981956).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3981956).length < 2 ^ (prefixWord ++ tailWord_3981956).sum := by decide
  have hdescent : baseEnd_3981956 < baseStart_3981956 := by decide
  rcases family_descends (prefixWord ++ tailWord_3981956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3982005 : List Nat := [1, 3, 3, 3, 1, 3, 1, 2, 5]
def baseStart_3982005 : Nat := 118140960795 + 3982005 * 2 ^ 59
def prefixEnd_3982005 : Nat := 4983230072969 + 3 ^ 40 * 3982005 * 2
def baseEnd_3982005 : Nat := 454373896357066249072133

theorem tailTrace_3982005 : CollatzResearch.WordTrace tailWord_3982005 prefixEnd_3982005 454373896357066249072133 := by
  unfold tailWord_3982005
  simp only [CollatzResearch.WordTrace]
  refine ⟨145235653938883432155787469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96823769292588954770524979 145235653938883432155787469)
  ·
    refine ⟨54463370227081287058420301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145235653938883432155787469 54463370227081287058420301)
    ·
      refine ⟨20423763835155482646907613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54463370227081287058420301 20423763835155482646907613)
      ·
        refine ⟨7658911438183305992590355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20423763835155482646907613 7658911438183305992590355)
        ·
          refine ⟨11488367157274958988885533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7658911438183305992590355 11488367157274958988885533)
          ·
            refine ⟨4308137683978109620832075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11488367157274958988885533 4308137683978109620832075)
            ·
              refine ⟨6462206525967164431248113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4308137683978109620832075 6462206525967164431248113)
              ·
                refine ⟨4846654894475373323436085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6462206525967164431248113 4846654894475373323436085)
                ·
                  refine ⟨454373896357066249072133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4846654894475373323436085 454373896357066249072133)
                  ·
                    rfl

theorem cell22_3982005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 1, 2, 5].length) (baseStart_3982005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3982005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3982005 prefixEnd_3982005 := by exact prefixLift 3982005
  have htrace : WordTrace (prefixWord ++ tailWord_3982005) baseStart_3982005 baseEnd_3982005 := by
    simpa [prefixWord, tailWord_3982005, baseEnd_3982005] using wordTrace_append hprefix tailTrace_3982005
  have hstable : (prefixWord ++ tailWord_3982005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3982005).length < 2 ^ (prefixWord ++ tailWord_3982005).sum := by decide
  have hdescent : baseEnd_3982005 < baseStart_3982005 := by decide
  rcases family_descends (prefixWord ++ tailWord_3982005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3982016 : List Nat := [2, 1, 1, 2, 4, 2, 1, 3, 6]
def baseStart_3982016 : Nat := 118140960795 + 3982016 * 2 ^ 59
def prefixEnd_3982016 : Nat := 4983230072969 + 3 ^ 40 * 3982016 * 2
def baseEnd_3982016 : Nat := 454375151531999461730455

theorem tailTrace_3982016 : CollatzResearch.WordTrace tailWord_3982016 prefixEnd_3982016 454375151531999461730455 := by
  unfold tailWord_3982016
  simp only [CollatzResearch.WordTrace]
  refine ⟨72618027570921790517218951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96824036761229054022958601 72618027570921790517218951)
  ·
    refine ⟨108927041356382685775828427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72618027570921790517218951 108927041356382685775828427)
    ·
      refine ⟨163390562034574028663742641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108927041356382685775828427 163390562034574028663742641)
      ·
        refine ⟨122542921525930521497806981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163390562034574028663742641 122542921525930521497806981)
        ·
          refine ⟨22976797786111972780838809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 122542921525930521497806981 22976797786111972780838809)
          ·
            refine ⟨17232598339583979585629107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22976797786111972780838809 17232598339583979585629107)
            ·
              refine ⟨25848897509375969378443661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17232598339583979585629107 25848897509375969378443661)
              ·
                refine ⟨9693336566015988516916373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25848897509375969378443661 9693336566015988516916373)
                ·
                  refine ⟨454375151531999461730455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9693336566015988516916373 454375151531999461730455)
                  ·
                    rfl

theorem cell22_3982016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 3, 6].length) (baseStart_3982016 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3982016 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3982016 prefixEnd_3982016 := by exact prefixLift 3982016
  have htrace : WordTrace (prefixWord ++ tailWord_3982016) baseStart_3982016 baseEnd_3982016 := by
    simpa [prefixWord, tailWord_3982016, baseEnd_3982016] using wordTrace_append hprefix tailTrace_3982016
  have hstable : (prefixWord ++ tailWord_3982016).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3982016).length < 2 ^ (prefixWord ++ tailWord_3982016).sum := by decide
  have hdescent : baseEnd_3982016 < baseStart_3982016 := by decide
  rcases family_descends (prefixWord ++ tailWord_3982016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3982063 : List Nat := [1, 1, 2, 1, 5, 3, 1, 2, 2, 4]
def baseStart_3982063 : Nat := 118140960795 + 3982063 * 2 ^ 59
def prefixEnd_3982063 : Nat := 4983230072969 + 3 ^ 40 * 3982063 * 2
def baseEnd_3982063 : Nat := 1363141543656505929266221

theorem tailTrace_3982063 : CollatzResearch.WordTrace tailWord_3982063 prefixEnd_3982063 1363141543656505929266221 := by
  unfold tailWord_3982063
  simp only [CollatzResearch.WordTrace]
  refine ⟨145237769372673308061398843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96825179581782205374265895 145237769372673308061398843)
  ·
    refine ⟨217856654059009962092098265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145237769372673308061398843 217856654059009962092098265)
    ·
      refine ⟨163392490544257471569073699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217856654059009962092098265 163392490544257471569073699)
      ·
        refine ⟨245088735816386207353610549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163392490544257471569073699 245088735816386207353610549)
        ·
          refine ⟨22977068982786206939400989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 245088735816386207353610549 22977068982786206939400989)
          ·
            refine ⟨8616400868544827602275371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22977068982786206939400989 8616400868544827602275371)
            ·
              refine ⟨12924601302817241403413057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8616400868544827602275371 12924601302817241403413057)
              ·
                refine ⟨9693450977112931052559793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12924601302817241403413057 9693450977112931052559793)
                ·
                  refine ⟨7270088232834698289419845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9693450977112931052559793 7270088232834698289419845)
                  ·
                    refine ⟨1363141543656505929266221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7270088232834698289419845 1363141543656505929266221)
                    ·
                      rfl

theorem cell22_3982063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 2, 2, 4].length) (baseStart_3982063 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3982063 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3982063 prefixEnd_3982063 := by exact prefixLift 3982063
  have htrace : WordTrace (prefixWord ++ tailWord_3982063) baseStart_3982063 baseEnd_3982063 := by
    simpa [prefixWord, tailWord_3982063, baseEnd_3982063] using wordTrace_append hprefix tailTrace_3982063
  have hstable : (prefixWord ++ tailWord_3982063).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3982063).length < 2 ^ (prefixWord ++ tailWord_3982063).sum := by decide
  have hdescent : baseEnd_3982063 < baseStart_3982063 := by decide
  rcases family_descends (prefixWord ++ tailWord_3982063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3982078 : List Nat := [4, 2, 2, 1, 2, 1, 1, 9]
def baseStart_3982078 : Nat := 118140960795 + 3982078 * 2 ^ 59
def prefixEnd_3982078 : Nat := 4983230072969 + 3 ^ 40 * 3982078 * 2
def baseEnd_3982078 : Nat := 151460742051450098904575

theorem tailTrace_3982078 : CollatzResearch.WordTrace tailWord_3982078 prefixEnd_3982078 151460742051450098904575 := by
  unfold tailWord_3982078
  simp only [CollatzResearch.WordTrace]
  refine ⟨18154789558452370702899361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96825544311745977082129925 18154789558452370702899361)
  ·
    refine ⟨13616092168839278027174521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18154789558452370702899361 13616092168839278027174521)
    ·
      refine ⟨10212069126629458520380891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13616092168839278027174521 10212069126629458520380891)
      ·
        refine ⟨15318103689944187780571337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10212069126629458520380891 15318103689944187780571337)
        ·
          refine ⟨11488577767458140835428503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15318103689944187780571337 11488577767458140835428503)
          ·
            refine ⟨17232866651187211253142755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11488577767458140835428503 17232866651187211253142755)
            ·
              refine ⟨25849299976780816879714133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17232866651187211253142755 25849299976780816879714133)
              ·
                refine ⟨151460742051450098904575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 25849299976780816879714133 151460742051450098904575)
                ·
                  rfl

theorem cell22_3982078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 9].length) (baseStart_3982078 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3982078 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3982078 prefixEnd_3982078 := by exact prefixLift 3982078
  have htrace : WordTrace (prefixWord ++ tailWord_3982078) baseStart_3982078 baseEnd_3982078 := by
    simpa [prefixWord, tailWord_3982078, baseEnd_3982078] using wordTrace_append hprefix tailTrace_3982078
  have hstable : (prefixWord ++ tailWord_3982078).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3982078).length < 2 ^ (prefixWord ++ tailWord_3982078).sum := by decide
  have hdescent : baseEnd_3982078 < baseStart_3982078 := by decide
  rcases family_descends (prefixWord ++ tailWord_3982078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3982082 : List Nat := [3, 4, 1, 1, 1, 3, 1, 3, 2, 3]
def baseStart_3982082 : Nat := 118140960795 + 3982082 * 2 ^ 59
def prefixEnd_3982082 : Nat := 4983230072969 + 3 ^ 40 * 3982082 * 2
def baseEnd_3982082 : Nat := 1363148047744796213041163

theorem tailTrace_3982082 : CollatzResearch.WordTrace tailWord_3982082 prefixEnd_3982082 1363148047744796213041163 := by
  unfold tailWord_3982082
  simp only [CollatzResearch.WordTrace]
  refine ⟨36309615589901118576585125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96825641573069649537560333 36309615589901118576585125)
  ·
    refine ⟨6808052923106459733109711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36309615589901118576585125 6808052923106459733109711)
    ·
      refine ⟨10212079384659689599664567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6808052923106459733109711 10212079384659689599664567)
      ·
        refine ⟨15318119076989534399496851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10212079384659689599664567 15318119076989534399496851)
        ·
          refine ⟨22977178615484301599245277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15318119076989534399496851 22977178615484301599245277)
          ·
            refine ⟨8616441980806613099716979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22977178615484301599245277 8616441980806613099716979)
            ·
              refine ⟨12924662971209919649575469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8616441980806613099716979 12924662971209919649575469)
              ·
                refine ⟨4846748614203719868590801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12924662971209919649575469 4846748614203719868590801)
                ·
                  refine ⟨3635061460652789901443101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4846748614203719868590801 3635061460652789901443101)
                  ·
                    refine ⟨1363148047744796213041163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3635061460652789901443101 1363148047744796213041163)
                    ·
                      rfl

theorem cell22_3982082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 3, 2, 3].length) (baseStart_3982082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3982082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3982082 prefixEnd_3982082 := by exact prefixLift 3982082
  have htrace : WordTrace (prefixWord ++ tailWord_3982082) baseStart_3982082 baseEnd_3982082 := by
    simpa [prefixWord, tailWord_3982082, baseEnd_3982082] using wordTrace_append hprefix tailTrace_3982082
  have hstable : (prefixWord ++ tailWord_3982082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3982082).length < 2 ^ (prefixWord ++ tailWord_3982082).sum := by decide
  have hdescent : baseEnd_3982082 < baseStart_3982082 := by decide
  rcases family_descends (prefixWord ++ tailWord_3982082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3982121 : List Nat := [1, 2, 1, 1, 1, 1, 1, 5, 4, 5]
def baseStart_3982121 : Nat := 118140960795 + 3982121 * 2 ^ 59
def prefixEnd_3982121 : Nat := 4983230072969 + 3 ^ 40 * 3982121 * 2
def baseEnd_3982121 : Nat := 1363161398241813111316043

theorem tailTrace_3982121 : CollatzResearch.WordTrace tailWord_3982121 prefixEnd_3982121 1363161398241813111316043 := by
  unfold tailWord_3982121
  simp only [CollatzResearch.WordTrace]
  refine ⟨145239884806463183967010217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96826589870975455978006811 145239884806463183967010217)
  ·
    refine ⟨108929913604847387975257663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145239884806463183967010217 108929913604847387975257663)
    ·
      refine ⟨163394870407271081962886495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108929913604847387975257663 163394870407271081962886495)
      ·
        refine ⟨245092305610906622944329743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163394870407271081962886495 245092305610906622944329743)
        ·
          refine ⟨367638458416359934416494615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245092305610906622944329743 367638458416359934416494615)
          ·
            refine ⟨551457687624539901624741923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 367638458416359934416494615 551457687624539901624741923)
            ·
              refine ⟨827186531436809852437112885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 551457687624539901624741923 827186531436809852437112885)
              ·
                refine ⟨77548737322200923665979333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 827186531436809852437112885 77548737322200923665979333)
                ·
                  refine ⟨14540388247912673187371125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77548737322200923665979333 14540388247912673187371125)
                  ·
                    refine ⟨1363161398241813111316043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14540388247912673187371125 1363161398241813111316043)
                    ·
                      rfl

theorem cell22_3982121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 5, 4, 5].length) (baseStart_3982121 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3982121 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3982121 prefixEnd_3982121 := by exact prefixLift 3982121
  have htrace : WordTrace (prefixWord ++ tailWord_3982121) baseStart_3982121 baseEnd_3982121 := by
    simpa [prefixWord, tailWord_3982121, baseEnd_3982121] using wordTrace_append hprefix tailTrace_3982121
  have hstable : (prefixWord ++ tailWord_3982121).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3982121).length < 2 ^ (prefixWord ++ tailWord_3982121).sum := by decide
  have hdescent : baseEnd_3982121 < baseStart_3982121 := by decide
  rcases family_descends (prefixWord ++ tailWord_3982121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3982153 : List Nat := [1, 2, 1, 1, 2, 5, 2, 1, 3, 4]
def baseStart_3982153 : Nat := 118140960795 + 3982153 * 2 ^ 59
def prefixEnd_3982153 : Nat := 4983230072969 + 3 ^ 40 * 3982153 * 2
def baseEnd_3982153 : Nat := 1363172352495775694515945

theorem tailTrace_3982153 : CollatzResearch.WordTrace tailWord_3982153 prefixEnd_3982153 1363172352495775694515945 := by
  unfold tailWord_3982153
  simp only [CollatzResearch.WordTrace]
  refine ⟨145241051942347253432175113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96827367961564835621450075 145241051942347253432175113)
  ·
    refine ⟨108930788956760440074131335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145241051942347253432175113 108930788956760440074131335)
    ·
      refine ⟨163396183435140660111197003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108930788956760440074131335 163396183435140660111197003)
      ·
        refine ⟨245094275152710990166795505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163396183435140660111197003 245094275152710990166795505)
        ·
          refine ⟨183820706364533242625096629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 245094275152710990166795505 183820706364533242625096629)
          ·
            refine ⟨17233191221674991496102809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 183820706364533242625096629 17233191221674991496102809)
            ·
              refine ⟨12924893416256243622077107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17233191221674991496102809 12924893416256243622077107)
              ·
                refine ⟨19387340124384365433115661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12924893416256243622077107 19387340124384365433115661)
                ·
                  refine ⟨7270252546644137037418373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19387340124384365433115661 7270252546644137037418373)
                  ·
                    refine ⟨1363172352495775694515945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7270252546644137037418373 1363172352495775694515945)
                    ·
                      rfl

theorem cell22_3982153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 1, 3, 4].length) (baseStart_3982153 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3982153 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3982153 prefixEnd_3982153 := by exact prefixLift 3982153
  have htrace : WordTrace (prefixWord ++ tailWord_3982153) baseStart_3982153 baseEnd_3982153 := by
    simpa [prefixWord, tailWord_3982153, baseEnd_3982153] using wordTrace_append hprefix tailTrace_3982153
  have hstable : (prefixWord ++ tailWord_3982153).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3982153).length < 2 ^ (prefixWord ++ tailWord_3982153).sum := by decide
  have hdescent : baseEnd_3982153 < baseStart_3982153 := by decide
  rcases family_descends (prefixWord ++ tailWord_3982153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3982170 : List Nat := [3, 1, 1, 2, 1, 5, 1, 3, 1, 4]
def baseStart_3982170 : Nat := 118140960795 + 3982170 * 2 ^ 59
def prefixEnd_3982170 : Nat := 4983230072969 + 3 ^ 40 * 3982170 * 2
def baseEnd_3982170 : Nat := 1363178171943193316840893

theorem tailTrace_3982170 : CollatzResearch.WordTrace tailWord_3982170 prefixEnd_3982170 1363178171943193316840893 := by
  unfold tailWord_3982170
  simp only [CollatzResearch.WordTrace]
  refine ⟨36310417995821416333885991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96827781322190443557029309 36310417995821416333885991)
  ·
    refine ⟨54465626993732124500828987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36310417995821416333885991 54465626993732124500828987)
    ·
      refine ⟨81698440490598186751243481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54465626993732124500828987 81698440490598186751243481)
      ·
        refine ⟨61273830367948640063432611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81698440490598186751243481 61273830367948640063432611)
        ·
          refine ⟨91910745551922960095148917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61273830367948640063432611 91910745551922960095148917)
          ·
            refine ⟨8616632395492777508920211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 91910745551922960095148917 8616632395492777508920211)
            ·
              refine ⟨12924948593239166263380317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8616632395492777508920211 12924948593239166263380317)
              ·
                refine ⟨4846855722464687348767619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12924948593239166263380317 4846855722464687348767619)
                ·
                  refine ⟨7270283583697031023151429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4846855722464687348767619 7270283583697031023151429)
                  ·
                    refine ⟨1363178171943193316840893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7270283583697031023151429 1363178171943193316840893)
                    ·
                      rfl

theorem cell22_3982170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 3, 1, 4].length) (baseStart_3982170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3982170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3982170 prefixEnd_3982170 := by exact prefixLift 3982170
  have htrace : WordTrace (prefixWord ++ tailWord_3982170) baseStart_3982170 baseEnd_3982170 := by
    simpa [prefixWord, tailWord_3982170, baseEnd_3982170] using wordTrace_append hprefix tailTrace_3982170
  have hstable : (prefixWord ++ tailWord_3982170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3982170).length < 2 ^ (prefixWord ++ tailWord_3982170).sum := by decide
  have hdescent : baseEnd_3982170 < baseStart_3982170 := by decide
  rcases family_descends (prefixWord ++ tailWord_3982170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3982213 : List Nat := [1, 3, 1, 1, 3, 4, 1, 8]
def baseStart_3982213 : Nat := 118140960795 + 3982213 * 2 ^ 59
def prefixEnd_3982213 : Nat := 4983230072969 + 3 ^ 40 * 3982213 * 2
def baseEnd_3982213 : Nat := 151465876857995059779529

theorem tailTrace_3982213 : CollatzResearch.WordTrace tailWord_3982213 prefixEnd_3982213 151465876857995059779529 := by
  unfold tailWord_3982213
  simp only [CollatzResearch.WordTrace]
  refine ⟨145243240322129883679359293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96828826881419922452906195 145243240322129883679359293)
  ·
    refine ⟨54466215120798706379759735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145243240322129883679359293 54466215120798706379759735)
    ·
      refine ⟨81699322681198059569639603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54466215120798706379759735 81699322681198059569639603)
      ·
        refine ⟨122548984021797089354459405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81699322681198059569639603 122548984021797089354459405)
        ·
          refine ⟨45955869008173908507922277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122548984021797089354459405 45955869008173908507922277)
          ·
            refine ⟨8616725439032607845235427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45955869008173908507922277 8616725439032607845235427)
            ·
              refine ⟨12925088158548911767853141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8616725439032607845235427 12925088158548911767853141)
              ·
                refine ⟨151465876857995059779529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12925088158548911767853141 151465876857995059779529)
                ·
                  rfl

theorem cell22_3982213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 8].length) (baseStart_3982213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3982213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3982213 prefixEnd_3982213 := by exact prefixLift 3982213
  have htrace : WordTrace (prefixWord ++ tailWord_3982213) baseStart_3982213 baseEnd_3982213 := by
    simpa [prefixWord, tailWord_3982213, baseEnd_3982213] using wordTrace_append hprefix tailTrace_3982213
  have hstable : (prefixWord ++ tailWord_3982213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3982213).length < 2 ^ (prefixWord ++ tailWord_3982213).sum := by decide
  have hdescent : baseEnd_3982213 < baseStart_3982213 := by decide
  rcases family_descends (prefixWord ++ tailWord_3982213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3982292 : List Nat := [2, 4, 1, 2, 1, 3, 2, 2, 5]
def baseStart_3982292 : Nat := 118140960795 + 3982292 * 2 ^ 59
def prefixEnd_3982292 : Nat := 4983230072969 + 3 ^ 40 * 3982292 * 2
def baseEnd_3982292 : Nat := 454406645012141888430173

theorem tailTrace_3982292 : CollatzResearch.WordTrace tailWord_3982292 prefixEnd_3982292 454406645012141888430173 := by
  unfold tailWord_3982292
  simp only [CollatzResearch.WordTrace]
  refine ⟨72623060844421840085742565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96830747792562453447656753 72623060844421840085742565)
  ·
    refine ⟨13616823908329095016076731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72623060844421840085742565 13616823908329095016076731)
    ·
      refine ⟨20425235862493642524115097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13616823908329095016076731 20425235862493642524115097)
      ·
        refine ⟨15318926896870231893086323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20425235862493642524115097 15318926896870231893086323)
        ·
          refine ⟨22978390345305347839629485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15318926896870231893086323 22978390345305347839629485)
          ·
            refine ⟨8616896379489505439861057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22978390345305347839629485 8616896379489505439861057)
            ·
              refine ⟨6462672284617129079895793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8616896379489505439861057 6462672284617129079895793)
              ·
                refine ⟨4847004213462846809921845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6462672284617129079895793 4847004213462846809921845)
                ·
                  refine ⟨454406645012141888430173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4847004213462846809921845 454406645012141888430173)
                  ·
                    rfl

theorem cell22_3982292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 2, 2, 5].length) (baseStart_3982292 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3982292 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3982292 prefixEnd_3982292 := by exact prefixLift 3982292
  have htrace : WordTrace (prefixWord ++ tailWord_3982292) baseStart_3982292 baseEnd_3982292 := by
    simpa [prefixWord, tailWord_3982292, baseEnd_3982292] using wordTrace_append hprefix tailTrace_3982292
  have hstable : (prefixWord ++ tailWord_3982292).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3982292).length < 2 ^ (prefixWord ++ tailWord_3982292).sum := by decide
  have hdescent : baseEnd_3982292 < baseStart_3982292 := by decide
  rcases family_descends (prefixWord ++ tailWord_3982292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3982296 : List Nat := [2, 1, 2, 2, 2, 5, 2, 2, 1, 3]
def baseStart_3982296 : Nat := 118140960795 + 3982296 * 2 ^ 59
def prefixEnd_3982296 : Nat := 4983230072969 + 3 ^ 40 * 3982296 * 2
def baseEnd_3982296 : Nat := 1363221304318170988190507

theorem tailTrace_3982296 : CollatzResearch.WordTrace tailWord_3982296 prefixEnd_3982296 1363221304318170988190507 := by
  unfold tailWord_3982296
  simp only [CollatzResearch.WordTrace]
  refine ⟨72623133790414594427315371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96830845053886125903087161 72623133790414594427315371)
  ·
    refine ⟨108934700685621891640973057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72623133790414594427315371 108934700685621891640973057)
    ·
      refine ⟨81701025514216418730729793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108934700685621891640973057 81701025514216418730729793)
      ·
        refine ⟨61275769135662314048047345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81701025514216418730729793 61275769135662314048047345)
        ·
          refine ⟨45956826851746735536035509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61275769135662314048047345 45956826851746735536035509)
          ·
            refine ⟨4308452517351256456503329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 45956826851746735536035509 4308452517351256456503329)
            ·
              refine ⟨3231339388013442342377497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4308452517351256456503329 3231339388013442342377497)
              ·
                refine ⟨2423504541010081756783123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3231339388013442342377497 2423504541010081756783123)
                ·
                  refine ⟨3635256811515122635174685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2423504541010081756783123 3635256811515122635174685)
                  ·
                    refine ⟨1363221304318170988190507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3635256811515122635174685 1363221304318170988190507)
                    ·
                      rfl

theorem cell22_3982296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 2, 2, 1, 3].length) (baseStart_3982296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3982296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3982296 prefixEnd_3982296 := by exact prefixLift 3982296
  have htrace : WordTrace (prefixWord ++ tailWord_3982296) baseStart_3982296 baseEnd_3982296 := by
    simpa [prefixWord, tailWord_3982296, baseEnd_3982296] using wordTrace_append hprefix tailTrace_3982296
  have hstable : (prefixWord ++ tailWord_3982296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3982296).length < 2 ^ (prefixWord ++ tailWord_3982296).sum := by decide
  have hdescent : baseEnd_3982296 < baseStart_3982296 := by decide
  rcases family_descends (prefixWord ++ tailWord_3982296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3982337 : List Nat := [1, 2, 4, 1, 2, 2, 1, 5, 4]
def baseStart_3982337 : Nat := 118140960795 + 3982337 * 2 ^ 59
def prefixEnd_3982337 : Nat := 4983230072969 + 3 ^ 40 * 3982337 * 2
def baseEnd_3982337 : Nat := 454411779818686849305127

theorem tailTrace_3982337 : CollatzResearch.WordTrace tailWord_3982337 prefixEnd_3982337 454411779818686849305127 := by
  unfold tailWord_3982337
  simp only [CollatzResearch.WordTrace]
  refine ⟨145247762973680652856873265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96831841982453768571248843 145247762973680652856873265)
  ·
    refine ⟨108935822230260489642654949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145247762973680652856873265 108935822230260489642654949)
    ·
      refine ⟨20425466668173841807997803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108935822230260489642654949 20425466668173841807997803)
      ·
        refine ⟨30638200002260762711996705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20425466668173841807997803 30638200002260762711996705)
        ·
          refine ⟨22978650001695572033997529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30638200002260762711996705 22978650001695572033997529)
          ·
            refine ⟨17233987501271679025498147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22978650001695572033997529 17233987501271679025498147)
            ·
              refine ⟨25850981251907518538247221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17233987501271679025498147 25850981251907518538247221)
              ·
                refine ⟨2423529492366329862960677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25850981251907518538247221 2423529492366329862960677)
                ·
                  refine ⟨454411779818686849305127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2423529492366329862960677 454411779818686849305127)
                  ·
                    rfl

theorem cell22_3982337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 5, 4].length) (baseStart_3982337 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3982337 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3982337 prefixEnd_3982337 := by exact prefixLift 3982337
  have htrace : WordTrace (prefixWord ++ tailWord_3982337) baseStart_3982337 baseEnd_3982337 := by
    simpa [prefixWord, tailWord_3982337, baseEnd_3982337] using wordTrace_append hprefix tailTrace_3982337
  have hstable : (prefixWord ++ tailWord_3982337).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3982337).length < 2 ^ (prefixWord ++ tailWord_3982337).sum := by decide
  have hdescent : baseEnd_3982337 < baseStart_3982337 := by decide
  rcases family_descends (prefixWord ++ tailWord_3982337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3982410 : List Nat := [3, 1, 2, 1, 1, 2, 4, 1, 7]
def baseStart_3982410 : Nat := 118140960795 + 3982410 * 2 ^ 59
def prefixEnd_3982410 : Nat := 4983230072969 + 3 ^ 40 * 3982410 * 2
def baseEnd_3982410 : Nat := 454420109615970896946719

theorem tailTrace_3982410 : CollatzResearch.WordTrace tailWord_3982410 prefixEnd_3982410 454420109615970896946719 := by
  unfold tailWord_3982410
  simp only [CollatzResearch.WordTrace]
  refine ⟨36312606375604046581070171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96833617001610790882853789 36312606375604046581070171)
  ·
    refine ⟨54468909563406069871605257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36312606375604046581070171 54468909563406069871605257)
    ·
      refine ⟨40851682172554552403703943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54468909563406069871605257 40851682172554552403703943)
      ·
        refine ⟨61277523258831828605555915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40851682172554552403703943 61277523258831828605555915)
        ·
          refine ⟨91916284888247742908333873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61277523258831828605555915 91916284888247742908333873)
          ·
            refine ⟨68937213666185807181250405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91916284888247742908333873 68937213666185807181250405)
            ·
              refine ⟨12925727562409838846484451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68937213666185807181250405 12925727562409838846484451)
              ·
                refine ⟨19388591343614758269726677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12925727562409838846484451 19388591343614758269726677)
                ·
                  refine ⟨454420109615970896946719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19388591343614758269726677 454420109615970896946719)
                  ·
                    rfl

theorem cell22_3982410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 1, 7].length) (baseStart_3982410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3982410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3982410 prefixEnd_3982410 := by exact prefixLift 3982410
  have htrace : WordTrace (prefixWord ++ tailWord_3982410) baseStart_3982410 baseEnd_3982410 := by
    simpa [prefixWord, tailWord_3982410, baseEnd_3982410] using wordTrace_append hprefix tailTrace_3982410
  have hstable : (prefixWord ++ tailWord_3982410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3982410).length < 2 ^ (prefixWord ++ tailWord_3982410).sum := by decide
  have hdescent : baseEnd_3982410 < baseStart_3982410 := by decide
  rcases family_descends (prefixWord ++ tailWord_3982410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3982487 : List Nat := [1, 1, 3, 3, 3, 1, 1, 3, 1, 5]
def baseStart_3982487 : Nat := 118140960795 + 3982487 * 2 ^ 59
def prefixEnd_3982487 : Nat := 4983230072969 + 3 ^ 40 * 3982487 * 2
def baseEnd_3982487 : Nat := 1363286687521510156664921

theorem tailTrace_3982487 : CollatzResearch.WordTrace tailWord_3982487 prefixEnd_3982487 1363286687521510156664921 := by
  unfold tailWord_3982487
  simp only [CollatzResearch.WordTrace]
  refine ⟨145253233923137228474833715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96835489282091485649889143 145253233923137228474833715)
  ·
    refine ⟨217879850884705842712250573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145253233923137228474833715 217879850884705842712250573)
    ·
      refine ⟨81704944081764691017093965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 217879850884705842712250573 81704944081764691017093965)
      ·
        refine ⟨30639354030661759131410237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81704944081764691017093965 30639354030661759131410237)
        ·
          refine ⟨11489757761498159674278839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30639354030661759131410237 11489757761498159674278839)
          ·
            refine ⟨17234636642247239511418259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11489757761498159674278839 17234636642247239511418259)
            ·
              refine ⟨25851954963370859267127389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17234636642247239511418259 25851954963370859267127389)
              ·
                refine ⟨9694483111264072225172771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25851954963370859267127389 9694483111264072225172771)
                ·
                  refine ⟨14541724666896108337759157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9694483111264072225172771 14541724666896108337759157)
                  ·
                    refine ⟨1363286687521510156664921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14541724666896108337759157 1363286687521510156664921)
                    ·
                      rfl

theorem cell22_3982487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 3, 1, 5].length) (baseStart_3982487 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3982487 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3982487 prefixEnd_3982487 := by exact prefixLift 3982487
  have htrace : WordTrace (prefixWord ++ tailWord_3982487) baseStart_3982487 baseEnd_3982487 := by
    simpa [prefixWord, tailWord_3982487, baseEnd_3982487] using wordTrace_append hprefix tailTrace_3982487
  have hstable : (prefixWord ++ tailWord_3982487).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3982487).length < 2 ^ (prefixWord ++ tailWord_3982487).sum := by decide
  have hdescent : baseEnd_3982487 < baseStart_3982487 := by decide
  rcases family_descends (prefixWord ++ tailWord_3982487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3982506 : List Nat := [3, 1, 5, 1, 1, 1, 1, 5, 4]
def baseStart_3982506 : Nat := 118140960795 + 3982506 * 2 ^ 59
def prefixEnd_3982506 : Nat := 4983230072969 + 3 ^ 40 * 3982506 * 2
def baseEnd_3982506 : Nat := 454431063869933480146621

theorem tailTrace_3982506 : CollatzResearch.WordTrace tailWord_3982506 prefixEnd_3982506 454431063869933480146621 := by
  unfold tailWord_3982506
  simp only [CollatzResearch.WordTrace]
  refine ⟨36313481727517098679943843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96835951273378929813183581 36313481727517098679943843)
  ·
    refine ⟨54470222591275648019915765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36313481727517098679943843 54470222591275648019915765)
    ·
      refine ⟨5106583367932092001867103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 54470222591275648019915765 5106583367932092001867103)
      ·
        refine ⟨7659875051898138002800655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5106583367932092001867103 7659875051898138002800655)
        ·
          refine ⟨11489812577847207004200983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7659875051898138002800655 11489812577847207004200983)
          ·
            refine ⟨17234718866770810506301475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11489812577847207004200983 17234718866770810506301475)
            ·
              refine ⟨25852078300156215759452213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17234718866770810506301475 25852078300156215759452213)
              ·
                refine ⟨2423632340639645227448645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25852078300156215759452213 2423632340639645227448645)
                ·
                  refine ⟨454431063869933480146621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2423632340639645227448645 454431063869933480146621)
                  ·
                    rfl

theorem cell22_3982506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 5, 4].length) (baseStart_3982506 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3982506 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3982506 prefixEnd_3982506 := by exact prefixLift 3982506
  have htrace : WordTrace (prefixWord ++ tailWord_3982506) baseStart_3982506 baseEnd_3982506 := by
    simpa [prefixWord, tailWord_3982506, baseEnd_3982506] using wordTrace_append hprefix tailTrace_3982506
  have hstable : (prefixWord ++ tailWord_3982506).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3982506).length < 2 ^ (prefixWord ++ tailWord_3982506).sum := by decide
  have hdescent : baseEnd_3982506 < baseStart_3982506 := by decide
  rcases family_descends (prefixWord ++ tailWord_3982506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3982521 : List Nat := [1, 2, 1, 4, 1, 5, 1, 2, 2, 3]
def baseStart_3982521 : Nat := 118140960795 + 3982521 * 2 ^ 59
def prefixEnd_3982521 : Nat := 4983230072969 + 3 ^ 40 * 3982521 * 2
def baseEnd_3982521 : Nat := 1363298326416345401314817

theorem tailTrace_3982521 : CollatzResearch.WordTrace tailWord_3982521 prefixEnd_3982521 1363298326416345401314817 := by
  unfold tailWord_3982521
  simp only [CollatzResearch.WordTrace]
  refine ⟨145254474005014052281571417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96836316003342701521047611 145254474005014052281571417)
  ·
    refine ⟨108940855503760539211178563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145254474005014052281571417 108940855503760539211178563)
    ·
      refine ⟨163411283255640808816767845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108940855503760539211178563 163411283255640808816767845)
      ·
        refine ⟨30639615610432651653143971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 163411283255640808816767845 30639615610432651653143971)
        ·
          refine ⟨45959423415648977479715957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30639615610432651653143971 45959423415648977479715957)
          ·
            refine ⟨4308695945217091638723371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 45959423415648977479715957 4308695945217091638723371)
            ·
              refine ⟨6463043917825637458085057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4308695945217091638723371 6463043917825637458085057)
              ·
                refine ⟨4847282938369228093563793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6463043917825637458085057 4847282938369228093563793)
                ·
                  refine ⟨3635462203776921070172845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4847282938369228093563793 3635462203776921070172845)
                  ·
                    refine ⟨1363298326416345401314817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3635462203776921070172845 1363298326416345401314817)
                    ·
                      rfl

theorem cell22_3982521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 1, 2, 2, 3].length) (baseStart_3982521 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3982521 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3982521 prefixEnd_3982521 := by exact prefixLift 3982521
  have htrace : WordTrace (prefixWord ++ tailWord_3982521) baseStart_3982521 baseEnd_3982521 := by
    simpa [prefixWord, tailWord_3982521, baseEnd_3982521] using wordTrace_append hprefix tailTrace_3982521
  have hstable : (prefixWord ++ tailWord_3982521).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3982521).length < 2 ^ (prefixWord ++ tailWord_3982521).sum := by decide
  have hdescent : baseEnd_3982521 < baseStart_3982521 := by decide
  rcases family_descends (prefixWord ++ tailWord_3982521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3982592 : List Nat := [2, 1, 1, 2, 1, 1, 3, 4, 3, 4]
def baseStart_3982592 : Nat := 118140960795 + 3982592 * 2 ^ 59
def prefixEnd_3982592 : Nat := 4983230072969 + 3 ^ 40 * 3982592 * 2
def baseEnd_3982592 : Nat := 1363322631167324882789599

theorem tailTrace_3982592 : CollatzResearch.WordTrace tailWord_3982592 prefixEnd_3982592 1363322631167324882789599 := by
  unfold tailWord_3982592
  simp only [CollatzResearch.WordTrace]
  refine ⟨72628531793878415703703015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96838042391837887604937353 72628531793878415703703015)
  ·
    refine ⟨108942797690817623555554523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72628531793878415703703015 108942797690817623555554523)
    ·
      refine ⟨163414196536226435333331785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108942797690817623555554523 163414196536226435333331785)
      ·
        refine ⟨122560647402169826499998839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163414196536226435333331785 122560647402169826499998839)
        ·
          refine ⟨183840971103254739749998259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122560647402169826499998839 183840971103254739749998259)
          ·
            refine ⟨275761456654882109624997389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183840971103254739749998259 275761456654882109624997389)
            ·
              refine ⟨103410546245580791109374021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 275761456654882109624997389 103410546245580791109374021)
              ·
                refine ⟨19389477421046398333007629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 103410546245580791109374021 19389477421046398333007629)
                ·
                  refine ⟨7271054032892399374877861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19389477421046398333007629 7271054032892399374877861)
                  ·
                    refine ⟨1363322631167324882789599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7271054032892399374877861 1363322631167324882789599)
                    ·
                      rfl

theorem cell22_3982592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 4, 3, 4].length) (baseStart_3982592 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3982592 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3982592 prefixEnd_3982592 := by exact prefixLift 3982592
  have htrace : WordTrace (prefixWord ++ tailWord_3982592) baseStart_3982592 baseEnd_3982592 := by
    simpa [prefixWord, tailWord_3982592, baseEnd_3982592] using wordTrace_append hprefix tailTrace_3982592
  have hstable : (prefixWord ++ tailWord_3982592).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3982592).length < 2 ^ (prefixWord ++ tailWord_3982592).sum := by decide
  have hdescent : baseEnd_3982592 < baseStart_3982592 := by decide
  rcases family_descends (prefixWord ++ tailWord_3982592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3982596 : List Nat := [2, 3, 2, 2, 2, 1, 4, 1, 5]
def baseStart_3982596 : Nat := 118140960795 + 3982596 * 2 ^ 59
def prefixEnd_3982596 : Nat := 4983230072969 + 3 ^ 40 * 3982596 * 2
def baseEnd_3982596 : Nat := 454441333483023401896529

theorem tailTrace_3982596 : CollatzResearch.WordTrace tailWord_3982596 prefixEnd_3982596 454441333483023401896529 := by
  unfold tailWord_3982596
  simp only [CollatzResearch.WordTrace]
  refine ⟨72628604739871170045275821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96838139653161560060367761 72628604739871170045275821)
  ·
    refine ⟨27235726777451688766978433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72628604739871170045275821 27235726777451688766978433)
    ·
      refine ⟨20426795083088766575233825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27235726777451688766978433 20426795083088766575233825)
      ·
        refine ⟨15320096312316574931425369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20426795083088766575233825 15320096312316574931425369)
        ·
          refine ⟨11490072234237431198569027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15320096312316574931425369 11490072234237431198569027)
          ·
            refine ⟨17235108351356146797853541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11490072234237431198569027 17235108351356146797853541)
            ·
              refine ⟨3231582815879277524597539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17235108351356146797853541 3231582815879277524597539)
              ·
                refine ⟨4847374223818916286896309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3231582815879277524597539 4847374223818916286896309)
                ·
                  refine ⟨454441333483023401896529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4847374223818916286896309 454441333483023401896529)
                  ·
                    rfl

theorem cell22_3982596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 4, 1, 5].length) (baseStart_3982596 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3982596 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3982596 prefixEnd_3982596 := by exact prefixLift 3982596
  have htrace : WordTrace (prefixWord ++ tailWord_3982596) baseStart_3982596 baseEnd_3982596 := by
    simpa [prefixWord, tailWord_3982596, baseEnd_3982596] using wordTrace_append hprefix tailTrace_3982596
  have hstable : (prefixWord ++ tailWord_3982596).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3982596).length < 2 ^ (prefixWord ++ tailWord_3982596).sum := by decide
  have hdescent : baseEnd_3982596 < baseStart_3982596 := by decide
  rcases family_descends (prefixWord ++ tailWord_3982596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3982641 : List Nat := [1, 2, 2, 3, 3, 2, 1, 4, 4]
def baseStart_3982641 : Nat := 118140960795 + 3982641 * 2 ^ 59
def prefixEnd_3982641 : Nat := 4983230072969 + 3 ^ 40 * 3982641 * 2
def baseEnd_3982641 : Nat := 454446468289568362771483

theorem tailTrace_3982641 : CollatzResearch.WordTrace tailWord_3982641 prefixEnd_3982641 454446468289568362771483 := by
  unfold tailWord_3982641
  simp only [CollatzResearch.WordTrace]
  refine ⟨145258850764579312775939777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96839233843052875183959851 145258850764579312775939777)
  ·
    refine ⟨108944138073434484581954833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145258850764579312775939777 108944138073434484581954833)
    ·
      refine ⟨81708103555075863436466125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108944138073434484581954833 81708103555075863436466125)
      ·
        refine ⟨30640538833153448788674797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81708103555075863436466125 30640538833153448788674797)
        ·
          refine ⟨11490202062432543295753049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30640538833153448788674797 11490202062432543295753049)
          ·
            refine ⟨8617651546824407471814787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11490202062432543295753049 8617651546824407471814787)
            ·
              refine ⟨12926477320236611207722181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8617651546824407471814787 12926477320236611207722181)
              ·
                refine ⟨2423714497544364601447909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12926477320236611207722181 2423714497544364601447909)
                ·
                  refine ⟨454446468289568362771483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2423714497544364601447909 454446468289568362771483)
                  ·
                    rfl

theorem cell22_3982641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 4, 4].length) (baseStart_3982641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3982641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3982641 prefixEnd_3982641 := by exact prefixLift 3982641
  have htrace : WordTrace (prefixWord ++ tailWord_3982641) baseStart_3982641 baseEnd_3982641 := by
    simpa [prefixWord, tailWord_3982641, baseEnd_3982641] using wordTrace_append hprefix tailTrace_3982641
  have hstable : (prefixWord ++ tailWord_3982641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3982641).length < 2 ^ (prefixWord ++ tailWord_3982641).sum := by decide
  have hdescent : baseEnd_3982641 < baseStart_3982641 := by decide
  rcases family_descends (prefixWord ++ tailWord_3982641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3982654 : List Nat := [4, 2, 1, 2, 1, 1, 2, 2, 1, 6]
def baseStart_3982654 : Nat := 118140960795 + 3982654 * 2 ^ 59
def prefixEnd_3982654 : Nat := 4983230072969 + 3 ^ 40 * 3982654 * 2
def baseEnd_3982654 : Nat := 1363343855034377387739409

theorem tailTrace_3982654 : CollatzResearch.WordTrace tailWord_3982654 prefixEnd_3982654 1363343855034377387739409 := by
  unfold tailWord_3982654
  simp only [CollatzResearch.WordTrace]
  refine ⟨18157415614191526999520377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96839549942354810664108677 18157415614191526999520377)
  ·
    refine ⟨13618061710643645249640283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18157415614191526999520377 13618061710643645249640283)
    ·
      refine ⟨20427092565965467874460425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13618061710643645249640283 20427092565965467874460425)
      ·
        refine ⟨15320319424474100905845319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20427092565965467874460425 15320319424474100905845319)
        ·
          refine ⟨22980479136711151358767979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15320319424474100905845319 22980479136711151358767979)
          ·
            refine ⟨34470718705066727038151969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22980479136711151358767979 34470718705066727038151969)
            ·
              refine ⟨25853039028800045278613977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34470718705066727038151969 25853039028800045278613977)
              ·
                refine ⟨19389779271600033958960483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25853039028800045278613977 19389779271600033958960483)
                ·
                  refine ⟨29084668907400050938440725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19389779271600033958960483 29084668907400050938440725)
                  ·
                    refine ⟨1363343855034377387739409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29084668907400050938440725 1363343855034377387739409)
                    ·
                      rfl

theorem cell22_3982654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 2, 1, 6].length) (baseStart_3982654 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3982654 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3982654 prefixEnd_3982654 := by exact prefixLift 3982654
  have htrace : WordTrace (prefixWord ++ tailWord_3982654) baseStart_3982654 baseEnd_3982654 := by
    simpa [prefixWord, tailWord_3982654, baseEnd_3982654] using wordTrace_append hprefix tailTrace_3982654
  have hstable : (prefixWord ++ tailWord_3982654).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3982654).length < 2 ^ (prefixWord ++ tailWord_3982654).sum := by decide
  have hdescent : baseEnd_3982654 < baseStart_3982654 := by decide
  rcases family_descends (prefixWord ++ tailWord_3982654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3982701 : List Nat := [1, 5, 1, 1, 1, 3, 1, 3, 3, 3]
def baseStart_3982701 : Nat := 118140960795 + 3982701 * 2 ^ 59
def prefixEnd_3982701 : Nat := 4983230072969 + 3 ^ 40 * 3982701 * 2
def baseEnd_3982701 : Nat := 1363359944094884931814265

theorem tailTrace_3982701 : CollatzResearch.WordTrace tailWord_3982701 prefixEnd_3982701 1363359944094884931814265 := by
  unfold tailWord_3982701
  simp only [CollatzResearch.WordTrace]
  refine ⟨145261039144361943023123957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96840692762907962015415971 145261039144361943023123957)
  ·
    refine ⟨13618222419783932158417871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 145261039144361943023123957 13618222419783932158417871)
    ·
      refine ⟨20427333629675898237626807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13618222419783932158417871 20427333629675898237626807)
      ·
        refine ⟨30641000444513847356440211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20427333629675898237626807 30641000444513847356440211)
        ·
          refine ⟨45961500666770771034660317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30641000444513847356440211 45961500666770771034660317)
          ·
            refine ⟨17235562750039039137997619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45961500666770771034660317 17235562750039039137997619)
            ·
              refine ⟨25853344125058558706996429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17235562750039039137997619 25853344125058558706996429)
              ·
                refine ⟨9695004046896959515123661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25853344125058558706996429 9695004046896959515123661)
                ·
                  refine ⟨3635626517586359818171373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9695004046896959515123661 3635626517586359818171373)
                  ·
                    refine ⟨1363359944094884931814265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3635626517586359818171373 1363359944094884931814265)
                    ·
                      rfl

theorem cell22_3982701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 3, 3, 3].length) (baseStart_3982701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3982701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3982701 prefixEnd_3982701 := by exact prefixLift 3982701
  have htrace : WordTrace (prefixWord ++ tailWord_3982701) baseStart_3982701 baseEnd_3982701 := by
    simpa [prefixWord, tailWord_3982701, baseEnd_3982701] using wordTrace_append hprefix tailTrace_3982701
  have hstable : (prefixWord ++ tailWord_3982701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3982701).length < 2 ^ (prefixWord ++ tailWord_3982701).sum := by decide
  have hdescent : baseEnd_3982701 < baseStart_3982701 := by decide
  rcases family_descends (prefixWord ++ tailWord_3982701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3982765 : List Nat := [1, 5, 2, 2, 1, 3, 2, 1, 5]
def baseStart_3982765 : Nat := 118140960795 + 3982765 * 2 ^ 59
def prefixEnd_3982765 : Nat := 4983230072969 + 3 ^ 40 * 3982765 * 2
def baseEnd_3982765 : Nat := 454460617534270032738023

theorem tailTrace_3982765 : CollatzResearch.WordTrace tailWord_3982765 prefixEnd_3982765 454460617534270032738023 := by
  unfold tailWord_3982765
  simp only [CollatzResearch.WordTrace]
  refine ⟨145263373416130081953453749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96842248944086721302302499 145263373416130081953453749)
  ·
    refine ⟨13618441257762195183136289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 145263373416130081953453749 13618441257762195183136289)
    ·
      refine ⟨10213830943321646387352217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13618441257762195183136289 10213830943321646387352217)
      ·
        refine ⟨7660373207491234790514163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10213830943321646387352217 7660373207491234790514163)
        ·
          refine ⟨11490559811236852185771245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7660373207491234790514163 11490559811236852185771245)
          ·
            refine ⟨4308959929213819569664217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11490559811236852185771245 4308959929213819569664217)
            ·
              refine ⟨3231719946910364677248163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4308959929213819569664217 3231719946910364677248163)
              ·
                refine ⟨4847579920365547015872245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3231719946910364677248163 4847579920365547015872245)
                ·
                  refine ⟨454460617534270032738023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4847579920365547015872245 454460617534270032738023)
                  ·
                    rfl

theorem cell22_3982765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 2, 1, 5].length) (baseStart_3982765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3982765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3982765 prefixEnd_3982765 := by exact prefixLift 3982765
  have htrace : WordTrace (prefixWord ++ tailWord_3982765) baseStart_3982765 baseEnd_3982765 := by
    simpa [prefixWord, tailWord_3982765, baseEnd_3982765] using wordTrace_append hprefix tailTrace_3982765
  have hstable : (prefixWord ++ tailWord_3982765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3982765).length < 2 ^ (prefixWord ++ tailWord_3982765).sum := by decide
  have hdescent : baseEnd_3982765 < baseStart_3982765 := by decide
  rcases family_descends (prefixWord ++ tailWord_3982765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3982804 : List Nat := [2, 4, 1, 2, 13]
def baseStart_3982804 : Nat := 118140960795 + 3982804 * 2 ^ 59
def prefixEnd_3982804 : Nat := 4983230072969 + 3 ^ 40 * 3982804 * 2
def baseEnd_3982804 : Nat := 5610679848147436199543

theorem tailTrace_3982804 : CollatzResearch.WordTrace tailWord_3982804 prefixEnd_3982804 5610679848147436199543 := by
  unfold tailWord_3982804
  simp only [CollatzResearch.WordTrace]
  refine ⟨72632397931494395807061733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96843197241992527742748977 72632397931494395807061733)
  ·
    refine ⟨13618574612155199213824075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72632397931494395807061733 13618574612155199213824075)
    ·
      refine ⟨20427861918232798820736113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13618574612155199213824075 20427861918232798820736113)
      ·
        refine ⟨15320896438674599115552085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20427861918232798820736113 15320896438674599115552085)
        ·
          refine ⟨5610679848147436199543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 15320896438674599115552085 5610679848147436199543)
          ·
            rfl

theorem cell22_3982804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 13].length) (baseStart_3982804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3982804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3982804 prefixEnd_3982804 := by exact prefixLift 3982804
  have htrace : WordTrace (prefixWord ++ tailWord_3982804) baseStart_3982804 baseEnd_3982804 := by
    simpa [prefixWord, tailWord_3982804, baseEnd_3982804] using wordTrace_append hprefix tailTrace_3982804
  have hstable : (prefixWord ++ tailWord_3982804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3982804).length < 2 ^ (prefixWord ++ tailWord_3982804).sum := by decide
  have hdescent : baseEnd_3982804 < baseStart_3982804 := by decide
  rcases family_descends (prefixWord ++ tailWord_3982804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3982810 : List Nat := [3, 1, 1, 2, 3, 4, 2, 2, 4]
def baseStart_3982810 : Nat := 118140960795 + 3982810 * 2 ^ 59
def prefixEnd_3982810 : Nat := 4983230072969 + 3 ^ 40 * 3982810 * 2
def baseEnd_3982810 : Nat := 454465752340814993612977

theorem tailTrace_3982810 : CollatzResearch.WordTrace tailWord_3982810 prefixEnd_3982810 454465752340814993612977 := by
  unfold tailWord_3982810
  simp only [CollatzResearch.WordTrace]
  refine ⟨36316253675241763659710471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96843343133978036425894589 36316253675241763659710471)
  ·
    refine ⟨54474380512862645489565707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36316253675241763659710471 54474380512862645489565707)
    ·
      refine ⟨81711570769293968234348561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54474380512862645489565707 81711570769293968234348561)
      ·
        refine ⟨61283678076970476175761421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81711570769293968234348561 61283678076970476175761421)
        ·
          refine ⟨22981379278863928565910533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61283678076970476175761421 22981379278863928565910533)
          ·
            refine ⟨4309008614786986606108225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22981379278863928565910533 4309008614786986606108225)
            ·
              refine ⟨3231756461090239954581169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4309008614786986606108225 3231756461090239954581169)
              ·
                refine ⟨2423817345817679965935877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3231756461090239954581169 2423817345817679965935877)
                ·
                  refine ⟨454465752340814993612977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2423817345817679965935877 454465752340814993612977)
                  ·
                    rfl

theorem cell22_3982810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 2, 2, 4].length) (baseStart_3982810 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3982810 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3982810 prefixEnd_3982810 := by exact prefixLift 3982810
  have htrace : WordTrace (prefixWord ++ tailWord_3982810) baseStart_3982810 baseEnd_3982810 := by
    simpa [prefixWord, tailWord_3982810, baseEnd_3982810] using wordTrace_append hprefix tailTrace_3982810
  have hstable : (prefixWord ++ tailWord_3982810).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3982810).length < 2 ^ (prefixWord ++ tailWord_3982810).sum := by decide
  have hdescent : baseEnd_3982810 < baseStart_3982810 := by decide
  rcases family_descends (prefixWord ++ tailWord_3982810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3982821 : List Nat := [1, 3, 1, 5, 1, 1, 3, 7]
def baseStart_3982821 : Nat := 118140960795 + 3982821 * 2 ^ 59
def prefixEnd_3982821 : Nat := 4983230072969 + 3 ^ 40 * 3982821 * 2
def baseEnd_3982821 : Nat := 151489002505249402090433

theorem tailTrace_3982821 : CollatzResearch.WordTrace tailWord_3982821 prefixEnd_3982821 151489002505249402090433 := by
  unfold tailWord_3982821
  simp only [CollatzResearch.WordTrace]
  refine ⟨145265415903927203517492317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96843610602618135678328211 145265415903927203517492317)
  ·
    refine ⟨54474530963972701319059619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145265415903927203517492317 54474530963972701319059619)
    ·
      refine ⟨81711796445959051978589429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54474530963972701319059619 81711796445959051978589429)
      ·
        refine ⟨7660480916808661122992759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 81711796445959051978589429 7660480916808661122992759)
        ·
          refine ⟨11490721375212991684489139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7660480916808661122992759 11490721375212991684489139)
          ·
            refine ⟨17236082062819487526733709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11490721375212991684489139 17236082062819487526733709)
            ·
              refine ⟨6463530773557307822525141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17236082062819487526733709 6463530773557307822525141)
              ·
                refine ⟨151489002505249402090433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6463530773557307822525141 151489002505249402090433)
                ·
                  rfl

theorem cell22_3982821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 3, 7].length) (baseStart_3982821 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3982821 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3982821 prefixEnd_3982821 := by exact prefixLift 3982821
  have htrace : WordTrace (prefixWord ++ tailWord_3982821) baseStart_3982821 baseEnd_3982821 := by
    simpa [prefixWord, tailWord_3982821, baseEnd_3982821] using wordTrace_append hprefix tailTrace_3982821
  have hstable : (prefixWord ++ tailWord_3982821).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3982821).length < 2 ^ (prefixWord ++ tailWord_3982821).sum := by decide
  have hdescent : baseEnd_3982821 < baseStart_3982821 := by decide
  rcases family_descends (prefixWord ++ tailWord_3982821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3982838 : List Nat := [5, 1, 1, 1, 2, 3, 3, 6]
def baseStart_3982838 : Nat := 118140960795 + 3982838 * 2 ^ 59
def prefixEnd_3982838 : Nat := 4983230072969 + 3 ^ 40 * 3982838 * 2
def baseEnd_3982838 : Nat := 151489649110518026793205

theorem tailTrace_3982838 : CollatzResearch.WordTrace tailWord_3982838 prefixEnd_3982838 151489649110518026793205 := by
  unfold tailWord_3982838
  simp only [CollatzResearch.WordTrace]
  refine ⟨9079127246554100963803823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 96844023963243743613907445 9079127246554100963803823)
  ·
    refine ⟨13618690869831151445705735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9079127246554100963803823 13618690869831151445705735)
    ·
      refine ⟨20428036304746727168558603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13618690869831151445705735 20428036304746727168558603)
      ·
        refine ⟨30642054457120090752837905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20428036304746727168558603 30642054457120090752837905)
        ·
          refine ⟨22981540842840068064628429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30642054457120090752837905 22981540842840068064628429)
          ·
            refine ⟨8618077816065025524235661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22981540842840068064628429 8618077816065025524235661)
            ·
              refine ⟨3231779181024384571588373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8618077816065025524235661 3231779181024384571588373)
              ·
                refine ⟨151489649110518026793205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3231779181024384571588373 151489649110518026793205)
                ·
                  rfl

theorem cell22_3982838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 3, 6].length) (baseStart_3982838 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3982838 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3982838 prefixEnd_3982838 := by exact prefixLift 3982838
  have htrace : WordTrace (prefixWord ++ tailWord_3982838) baseStart_3982838 baseEnd_3982838 := by
    simpa [prefixWord, tailWord_3982838, baseEnd_3982838] using wordTrace_append hprefix tailTrace_3982838
  have hstable : (prefixWord ++ tailWord_3982838).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3982838).length < 2 ^ (prefixWord ++ tailWord_3982838).sum := by decide
  have hdescent : baseEnd_3982838 < baseStart_3982838 := by decide
  rcases family_descends (prefixWord ++ tailWord_3982838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3982881 : List Nat := [1, 2, 3, 2, 2, 2, 2, 1, 2, 5]
def baseStart_3982881 : Nat := 118140960795 + 3982881 * 2 ^ 59
def prefixEnd_3982881 : Nat := 4983230072969 + 3 ^ 40 * 3982881 * 2
def baseEnd_3982881 : Nat := 1363421561773424462313713

theorem tailTrace_3982881 : CollatzResearch.WordTrace tailWord_3982881 prefixEnd_3982881 1363421561773424462313713 := by
  unfold tailWord_3982881
  simp only [CollatzResearch.WordTrace]
  refine ⟨145267604283709833764676497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96845069522473222509784331 145267604283709833764676497)
  ·
    refine ⟨108950703212782375323507373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145267604283709833764676497 108950703212782375323507373)
    ·
      refine ⟨40856513704793390746315265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108950703212782375323507373 40856513704793390746315265)
      ·
        refine ⟨30642385278595043059736449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40856513704793390746315265 30642385278595043059736449)
        ·
          refine ⟨22981788958946282294802337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30642385278595043059736449 22981788958946282294802337)
          ·
            refine ⟨17236341719209711721101753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22981788958946282294802337 17236341719209711721101753)
            ·
              refine ⟨12927256289407283790826315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17236341719209711721101753 12927256289407283790826315)
              ·
                refine ⟨19390884434110925686239473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12927256289407283790826315 19390884434110925686239473)
                ·
                  refine ⟨14543163325583194264679605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19390884434110925686239473 14543163325583194264679605)
                  ·
                    refine ⟨1363421561773424462313713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14543163325583194264679605 1363421561773424462313713)
                    ·
                      rfl

theorem cell22_3982881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 1, 2, 5].length) (baseStart_3982881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3982881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3982881 prefixEnd_3982881 := by exact prefixLift 3982881
  have htrace : WordTrace (prefixWord ++ tailWord_3982881) baseStart_3982881 baseEnd_3982881 := by
    simpa [prefixWord, tailWord_3982881, baseEnd_3982881] using wordTrace_append hprefix tailTrace_3982881
  have hstable : (prefixWord ++ tailWord_3982881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3982881).length < 2 ^ (prefixWord ++ tailWord_3982881).sum := by decide
  have hdescent : baseEnd_3982881 < baseStart_3982881 := by decide
  rcases family_descends (prefixWord ++ tailWord_3982881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3982913 : List Nat := [1, 2, 5, 1, 1, 1, 1, 5, 1, 4]
def baseStart_3982913 : Nat := 118140960795 + 3982913 * 2 ^ 59
def prefixEnd_3982913 : Nat := 4983230072969 + 3 ^ 40 * 3982913 * 2
def baseEnd_3982913 : Nat := 1363432516027387045513615

theorem tailTrace_3982913 : CollatzResearch.WordTrace tailWord_3982913 prefixEnd_3982913 1363432516027387045513615 := by
  unfold tailWord_3982913
  simp only [CollatzResearch.WordTrace]
  refine ⟨145268771419593903229841393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96845847613062602153227595 145268771419593903229841393)
  ·
    refine ⟨108951578564695427422381045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145268771419593903229841393 108951578564695427422381045)
    ·
      refine ⟨10214210490440196320848223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 108951578564695427422381045 10214210490440196320848223)
      ·
        refine ⟨15321315735660294481272335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10214210490440196320848223 15321315735660294481272335)
        ·
          refine ⟨22981973603490441721908503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15321315735660294481272335 22981973603490441721908503)
          ·
            refine ⟨34472960405235662582862755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22981973603490441721908503 34472960405235662582862755)
            ·
              refine ⟨51709440607853493874294133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34472960405235662582862755 51709440607853493874294133)
              ·
                refine ⟨4847760056986265050715075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51709440607853493874294133 4847760056986265050715075)
                ·
                  refine ⟨7271640085479397576072613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4847760056986265050715075 7271640085479397576072613)
                  ·
                    refine ⟨1363432516027387045513615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7271640085479397576072613 1363432516027387045513615)
                    ·
                      rfl

theorem cell22_3982913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 5, 1, 4].length) (baseStart_3982913 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3982913 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3982913 prefixEnd_3982913 := by exact prefixLift 3982913
  have htrace : WordTrace (prefixWord ++ tailWord_3982913) baseStart_3982913 baseEnd_3982913 := by
    simpa [prefixWord, tailWord_3982913, baseEnd_3982913] using wordTrace_append hprefix tailTrace_3982913
  have hstable : (prefixWord ++ tailWord_3982913).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3982913).length < 2 ^ (prefixWord ++ tailWord_3982913).sum := by decide
  have hdescent : baseEnd_3982913 < baseStart_3982913 := by decide
  rcases family_descends (prefixWord ++ tailWord_3982913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3982988 : List Nat := [2, 2, 1, 2, 1, 1, 4, 3, 3, 3]
def baseStart_3982988 : Nat := 118140960795 + 3982988 * 2 ^ 59
def prefixEnd_3982988 : Nat := 4983230072969 + 3 ^ 40 * 3982988 * 2
def baseEnd_3982988 : Nat := 1363458190060111849888385

theorem tailTrace_3982988 : CollatzResearch.WordTrace tailWord_3982988 prefixEnd_3982988 1363458190060111849888385 := by
  unfold tailWord_3982988
  simp only [CollatzResearch.WordTrace]
  refine ⟨72635753447161095519410809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96847671262881460692547745 72635753447161095519410809)
  ·
    refine ⟨54476815085370821639558107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72635753447161095519410809 54476815085370821639558107)
    ·
      refine ⟨81715222628056232459337161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54476815085370821639558107 81715222628056232459337161)
      ·
        refine ⟨61286416971042174344502871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81715222628056232459337161 61286416971042174344502871)
        ·
          refine ⟨91929625456563261516754307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61286416971042174344502871 91929625456563261516754307)
          ·
            refine ⟨137894438184844892275131461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91929625456563261516754307 137894438184844892275131461)
            ·
              refine ⟨25855207159658417301587149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 137894438184844892275131461 25855207159658417301587149)
              ·
                refine ⟨9695702684871906488095181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25855207159658417301587149 9695702684871906488095181)
                ·
                  refine ⟨3635888506826964933035693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9695702684871906488095181 3635888506826964933035693)
                  ·
                    refine ⟨1363458190060111849888385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3635888506826964933035693 1363458190060111849888385)
                    ·
                      rfl

theorem cell22_3982988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 3, 3, 3].length) (baseStart_3982988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3982988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3982988 prefixEnd_3982988 := by exact prefixLift 3982988
  have htrace : WordTrace (prefixWord ++ tailWord_3982988) baseStart_3982988 baseEnd_3982988 := by
    simpa [prefixWord, tailWord_3982988, baseEnd_3982988] using wordTrace_append hprefix tailTrace_3982988
  have hstable : (prefixWord ++ tailWord_3982988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3982988).length < 2 ^ (prefixWord ++ tailWord_3982988).sum := by decide
  have hdescent : baseEnd_3982988 < baseStart_3982988 := by decide
  rcases family_descends (prefixWord ++ tailWord_3982988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3983052 : List Nat := [2, 2, 1, 5, 2, 1, 3, 1, 5]
def baseStart_3983052 : Nat := 118140960795 + 3983052 * 2 ^ 59
def prefixEnd_3983052 : Nat := 4983230072969 + 3 ^ 40 * 3983052 * 2
def baseEnd_3983052 : Nat := 454493366189345672096063

theorem tailTrace_3983052 : CollatzResearch.WordTrace tailWord_3983052 prefixEnd_3983052 454493366189345672096063 := by
  unfold tailWord_3983052
  simp only [CollatzResearch.WordTrace]
  refine ⟨72636920583045164984575705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96849227444060219979434273 72636920583045164984575705)
  ·
    refine ⟨54477690437283873738431779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72636920583045164984575705 54477690437283873738431779)
    ·
      refine ⟨81716535655925810607647669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54477690437283873738431779 81716535655925810607647669)
      ·
        refine ⟨7660925217743044744466969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 81716535655925810607647669 7660925217743044744466969)
        ·
          refine ⟨5745693913307283558350227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7660925217743044744466969 5745693913307283558350227)
          ·
            refine ⟨8618540869960925337525341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5745693913307283558350227 8618540869960925337525341)
            ·
              refine ⟨3231952826235347001572003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8618540869960925337525341 3231952826235347001572003)
              ·
                refine ⟨4847929239353020502358005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3231952826235347001572003 4847929239353020502358005)
                ·
                  refine ⟨454493366189345672096063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4847929239353020502358005 454493366189345672096063)
                  ·
                    rfl

theorem cell22_3983052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 3, 1, 5].length) (baseStart_3983052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3983052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3983052 prefixEnd_3983052 := by exact prefixLift 3983052
  have htrace : WordTrace (prefixWord ++ tailWord_3983052) baseStart_3983052 baseEnd_3983052 := by
    simpa [prefixWord, tailWord_3983052, baseEnd_3983052] using wordTrace_append hprefix tailTrace_3983052
  have hstable : (prefixWord ++ tailWord_3983052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3983052).length < 2 ^ (prefixWord ++ tailWord_3983052).sum := by decide
  have hdescent : baseEnd_3983052 < baseStart_3983052 := by decide
  rcases family_descends (prefixWord ++ tailWord_3983052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3983065 : List Nat := [1, 2, 1, 2, 3, 4, 2, 2, 1, 4]
def baseStart_3983065 : Nat := 118140960795 + 3983065 * 2 ^ 59
def prefixEnd_3983065 : Nat := 4983230072969 + 3 ^ 40 * 3983065 * 2
def baseEnd_3983065 : Nat := 1363484548733709315713149

theorem tailTrace_3983065 : CollatzResearch.WordTrace tailWord_3983065 prefixEnd_3983065 1363484548733709315713149 := by
  unfold tailWord_3983065
  simp only [CollatzResearch.WordTrace]
  refine ⟨145274315315043233189374649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96849543543362155459583099 145274315315043233189374649)
  ·
    refine ⟨108955736486282424892030987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145274315315043233189374649 108955736486282424892030987)
    ·
      refine ⟨163433604729423637338046481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108955736486282424892030987 163433604729423637338046481)
      ·
        refine ⟨122575203547067728003534861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163433604729423637338046481 122575203547067728003534861)
        ·
          refine ⟨45965701330150398001325573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122575203547067728003534861 45965701330150398001325573)
          ·
            refine ⟨8618568999403199625248545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45965701330150398001325573 8618568999403199625248545)
            ·
              refine ⟨6463926749552399718936409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8618568999403199625248545 6463926749552399718936409)
              ·
                refine ⟨4847945062164299789202307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6463926749552399718936409 4847945062164299789202307)
                ·
                  refine ⟨7271917593246449683803461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4847945062164299789202307 7271917593246449683803461)
                  ·
                    refine ⟨1363484548733709315713149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7271917593246449683803461 1363484548733709315713149)
                    ·
                      rfl

theorem cell22_3983065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 2, 2, 1, 4].length) (baseStart_3983065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3983065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3983065 prefixEnd_3983065 := by exact prefixLift 3983065
  have htrace : WordTrace (prefixWord ++ tailWord_3983065) baseStart_3983065 baseEnd_3983065 := by
    simpa [prefixWord, tailWord_3983065, baseEnd_3983065] using wordTrace_append hprefix tailTrace_3983065
  have hstable : (prefixWord ++ tailWord_3983065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3983065).length < 2 ^ (prefixWord ++ tailWord_3983065).sum := by decide
  have hdescent : baseEnd_3983065 < baseStart_3983065 := by decide
  rcases family_descends (prefixWord ++ tailWord_3983065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3983091 : List Nat := [1, 1, 1, 2, 2, 3, 12]
def baseStart_3983091 : Nat := 118140960795 + 3983091 * 2 ^ 59
def prefixEnd_3983091 : Nat := 4983230072969 + 3 ^ 40 * 3983091 * 2
def baseEnd_3983091 : Nat := 50499757372779774613447

theorem tailTrace_3983091 : CollatzResearch.WordTrace tailWord_3983091 prefixEnd_3983091 50499757372779774613447 := by
  unfold tailWord_3983091
  simp only [CollatzResearch.WordTrace]
  refine ⟨145275263612949039629821127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96850175741966026419880751 145275263612949039629821127)
  ·
    refine ⟨217912895419423559444731691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145275263612949039629821127 217912895419423559444731691)
    ·
      refine ⟨326869343129135339167097537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217912895419423559444731691 326869343129135339167097537)
      ·
        refine ⟨245152007346851504375323153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 326869343129135339167097537 245152007346851504375323153)
        ·
          refine ⟨183864005510138628281492365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 245152007346851504375323153 183864005510138628281492365)
          ·
            refine ⟨68949002066301985605559637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 183864005510138628281492365 68949002066301985605559637)
            ·
              refine ⟨50499757372779774613447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 68949002066301985605559637 50499757372779774613447)
              ·
                rfl

theorem cell22_3983091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 12].length) (baseStart_3983091 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3983091 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3983091 prefixEnd_3983091 := by exact prefixLift 3983091
  have htrace : WordTrace (prefixWord ++ tailWord_3983091) baseStart_3983091 baseEnd_3983091 := by
    simpa [prefixWord, tailWord_3983091, baseEnd_3983091] using wordTrace_append hprefix tailTrace_3983091
  have hstable : (prefixWord ++ tailWord_3983091).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3983091).length < 2 ^ (prefixWord ++ tailWord_3983091).sum := by decide
  have hdescent : baseEnd_3983091 < baseStart_3983091 := by decide
  rcases family_descends (prefixWord ++ tailWord_3983091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3983108 : List Nat := [2, 3, 2, 2, 1, 2, 1, 9]
def baseStart_3983108 : Nat := 118140960795 + 3983108 * 2 ^ 59
def prefixEnd_3983108 : Nat := 4983230072969 + 3 ^ 40 * 3983108 * 2
def baseEnd_3983108 : Nat := 151499918723607948543113

theorem tailTrace_3983108 : CollatzResearch.WordTrace tailWord_3983108 prefixEnd_3983108 151499918723607948543113 := by
  unfold tailWord_3983108
  simp only [CollatzResearch.WordTrace]
  refine ⟨72637941826943725766594989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96850589102591634355459985 72637941826943725766594989)
  ·
    refine ⟨27239228185103897162473121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72637941826943725766594989 27239228185103897162473121)
    ·
      refine ⟨20429421138827922871854841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27239228185103897162473121 20429421138827922871854841)
      ·
        refine ⟨15322065854120942153891131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20429421138827922871854841 15322065854120942153891131)
        ·
          refine ⟨22983098781181413230836697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15322065854120942153891131 22983098781181413230836697)
          ·
            refine ⟨17237324085886059923127523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22983098781181413230836697 17237324085886059923127523)
            ·
              refine ⟨25855986128829089884691285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17237324085886059923127523 25855986128829089884691285)
              ·
                refine ⟨151499918723607948543113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 25855986128829089884691285 151499918723607948543113)
                ·
                  rfl

theorem cell22_3983108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 9].length) (baseStart_3983108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3983108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3983108 prefixEnd_3983108 := by exact prefixLift 3983108
  have htrace : WordTrace (prefixWord ++ tailWord_3983108) baseStart_3983108 baseEnd_3983108 := by
    simpa [prefixWord, tailWord_3983108, baseEnd_3983108] using wordTrace_append hprefix tailTrace_3983108
  have hstable : (prefixWord ++ tailWord_3983108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3983108).length < 2 ^ (prefixWord ++ tailWord_3983108).sum := by decide
  have hdescent : baseEnd_3983108 < baseStart_3983108 := by decide
  rcases family_descends (prefixWord ++ tailWord_3983108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3983174 : List Nat := [6, 1, 1, 2, 1, 1, 1, 1, 5, 3]
def baseStart_3983174 : Nat := 118140960795 + 3983174 * 2 ^ 59
def prefixEnd_3983174 : Nat := 4983230072969 + 3 ^ 40 * 3983174 * 2
def baseEnd_3983174 : Nat := 1363521861661269364737815

theorem tailTrace_3983174 : CollatzResearch.WordTrace tailWord_3983174 prefixEnd_3983174 1363521861661269364737815 := by
  unfold tailWord_3983174
  simp only [CollatzResearch.WordTrace]
  refine ⟨4539946589739010775159143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 96852193914432229870061717 4539946589739010775159143)
  ·
    refine ⟨6809919884608516162738715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4539946589739010775159143 6809919884608516162738715)
    ·
      refine ⟨10214879826912774244108073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6809919884608516162738715 10214879826912774244108073)
      ·
        refine ⟨7661159870184580683081055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10214879826912774244108073 7661159870184580683081055)
        ·
          refine ⟨11491739805276871024621583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7661159870184580683081055 11491739805276871024621583)
          ·
            refine ⟨17237609707915306536932375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11491739805276871024621583 17237609707915306536932375)
            ·
              refine ⟨25856414561872959805398563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17237609707915306536932375 25856414561872959805398563)
              ·
                refine ⟨38784621842809439708097845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25856414561872959805398563 38784621842809439708097845)
                ·
                  refine ⟨3636058297763384972634173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38784621842809439708097845 3636058297763384972634173)
                  ·
                    refine ⟨1363521861661269364737815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3636058297763384972634173 1363521861661269364737815)
                    ·
                      rfl

theorem cell22_3983174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 1, 5, 3].length) (baseStart_3983174 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3983174 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3983174 prefixEnd_3983174 := by exact prefixLift 3983174
  have htrace : WordTrace (prefixWord ++ tailWord_3983174) baseStart_3983174 baseEnd_3983174 := by
    simpa [prefixWord, tailWord_3983174, baseEnd_3983174] using wordTrace_append hprefix tailTrace_3983174
  have hstable : (prefixWord ++ tailWord_3983174).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3983174).length < 2 ^ (prefixWord ++ tailWord_3983174).sum := by decide
  have hdescent : baseEnd_3983174 < baseStart_3983174 := by decide
  rcases family_descends (prefixWord ++ tailWord_3983174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3983204 : List Nat := [2, 3, 1, 1, 6, 1, 1, 2, 5]
def baseStart_3983204 : Nat := 118140960795 + 3983204 * 2 ^ 59
def prefixEnd_3983204 : Nat := 4983230072969 + 3 ^ 40 * 3983204 * 2
def baseEnd_3983204 : Nat := 454510710424786428829241

theorem tailTrace_3983204 : CollatzResearch.WordTrace tailWord_3983204 prefixEnd_3983204 454510710424786428829241 := by
  unfold tailWord_3983204
  simp only [CollatzResearch.WordTrace]
  refine ⟨72639692530769829964342333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96852923374359773285789777 72639692530769829964342333)
  ·
    refine ⟨27239884699038686236628375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72639692530769829964342333 27239884699038686236628375)
    ·
      refine ⟨40859827048558029354942563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27239884699038686236628375 40859827048558029354942563)
      ·
        refine ⟨61289740572837044032413845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40859827048558029354942563 61289740572837044032413845)
        ·
          refine ⟨2872956589351736439019399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 61289740572837044032413845 2872956589351736439019399)
          ·
            refine ⟨4309434884027604658529099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2872956589351736439019399 4309434884027604658529099)
            ·
              refine ⟨6464152326041406987793649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4309434884027604658529099 6464152326041406987793649)
              ·
                refine ⟨4848114244531055240845237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6464152326041406987793649 4848114244531055240845237)
                ·
                  refine ⟨454510710424786428829241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4848114244531055240845237 454510710424786428829241)
                  ·
                    rfl

theorem cell22_3983204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 1, 2, 5].length) (baseStart_3983204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3983204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3983204 prefixEnd_3983204 := by exact prefixLift 3983204
  have htrace : WordTrace (prefixWord ++ tailWord_3983204) baseStart_3983204 baseEnd_3983204 := by
    simpa [prefixWord, tailWord_3983204, baseEnd_3983204] using wordTrace_append hprefix tailTrace_3983204
  have hstable : (prefixWord ++ tailWord_3983204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3983204).length < 2 ^ (prefixWord ++ tailWord_3983204).sum := by decide
  have hdescent : baseEnd_3983204 < baseStart_3983204 := by decide
  rcases family_descends (prefixWord ++ tailWord_3983204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3983260 : List Nat := [2, 2, 3, 3, 1, 1, 10]
def baseStart_3983260 : Nat := 118140960795 + 3983260 * 2 ^ 59
def prefixEnd_3983260 : Nat := 4983230072969 + 3 ^ 40 * 3983260 * 2
def baseEnd_3983260 : Nat := 50501900045140511373613

theorem tailTrace_3983260 : CollatzResearch.WordTrace tailWord_3983260 prefixEnd_3983260 50501900045140511373613 := by
  unfold tailWord_3983260
  simp only [CollatzResearch.WordTrace]
  refine ⟨72640713774668390746361617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96854285032891187661815489 72640713774668390746361617)
  ·
    refine ⟨54480535331001293059771213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72640713774668390746361617 54480535331001293059771213)
    ·
      refine ⟨20430200749125484897414205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54480535331001293059771213 20430200749125484897414205)
      ·
        refine ⟨7661325280922056836530327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20430200749125484897414205 7661325280922056836530327)
        ·
          refine ⟨11491987921383085254795491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7661325280922056836530327 11491987921383085254795491)
          ·
            refine ⟨17237981882074627882193237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11491987921383085254795491 17237981882074627882193237)
            ·
              refine ⟨50501900045140511373613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 17237981882074627882193237 50501900045140511373613)
              ·
                rfl

theorem cell22_3983260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 10].length) (baseStart_3983260 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3983260 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3983260 prefixEnd_3983260 := by exact prefixLift 3983260
  have htrace : WordTrace (prefixWord ++ tailWord_3983260) baseStart_3983260 baseEnd_3983260 := by
    simpa [prefixWord, tailWord_3983260, baseEnd_3983260] using wordTrace_append hprefix tailTrace_3983260
  have hstable : (prefixWord ++ tailWord_3983260).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3983260).length < 2 ^ (prefixWord ++ tailWord_3983260).sum := by decide
  have hdescent : baseEnd_3983260 < baseStart_3983260 := by decide
  rcases family_descends (prefixWord ++ tailWord_3983260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3983266 : List Nat := [3, 3, 1, 2, 3, 1, 3, 2, 4]
def baseStart_3983266 : Nat := 118140960795 + 3983266 * 2 ^ 59
def prefixEnd_3983266 : Nat := 4983230072969 + 3 ^ 40 * 3983266 * 2
def baseEnd_3983266 : Nat := 454517785047137263812511

theorem tailTrace_3983266 : CollatzResearch.WordTrace tailWord_3983266 prefixEnd_3983266 454517785047137263812511 := by
  unfold tailWord_3983266
  simp only [CollatzResearch.WordTrace]
  refine ⟨36320411596828761129360413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96854430924876696344961101 36320411596828761129360413)
  ·
    refine ⟨13620154348810785423510155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36320411596828761129360413 13620154348810785423510155)
    ·
      refine ⟨20430231523216178135265233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13620154348810785423510155 20430231523216178135265233)
      ·
        refine ⟨15322673642412133601448925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20430231523216178135265233 15322673642412133601448925)
        ·
          refine ⟨5746002615904550100543347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15322673642412133601448925 5746002615904550100543347)
          ·
            refine ⟨8619003923856825150815021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5746002615904550100543347 8619003923856825150815021)
            ·
              refine ⟨3232126471446309431555633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8619003923856825150815021 3232126471446309431555633)
              ·
                refine ⟨2424094853584732073666725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3232126471446309431555633 2424094853584732073666725)
                ·
                  refine ⟨454517785047137263812511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2424094853584732073666725 454517785047137263812511)
                  ·
                    rfl

theorem cell22_3983266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 3, 2, 4].length) (baseStart_3983266 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3983266 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3983266 prefixEnd_3983266 := by exact prefixLift 3983266
  have htrace : WordTrace (prefixWord ++ tailWord_3983266) baseStart_3983266 baseEnd_3983266 := by
    simpa [prefixWord, tailWord_3983266, baseEnd_3983266] using wordTrace_append hprefix tailTrace_3983266
  have hstable : (prefixWord ++ tailWord_3983266).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3983266).length < 2 ^ (prefixWord ++ tailWord_3983266).sum := by decide
  have hdescent : baseEnd_3983266 < baseStart_3983266 := by decide
  rcases family_descends (prefixWord ++ tailWord_3983266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3983281 : List Nat := [1, 2, 2, 4, 2, 3, 2, 1, 2, 3]
def baseStart_3983281 : Nat := 118140960795 + 3983281 * 2 ^ 59
def prefixEnd_3983281 : Nat := 4983230072969 + 3 ^ 40 * 3983281 * 2
def baseEnd_3983281 : Nat := 1363558489947956752312487

theorem tailTrace_3983281 : CollatzResearch.WordTrace tailWord_3983281 prefixEnd_3983281 1363558489947956752312487 := by
  unfold tailWord_3983281
  simp only [CollatzResearch.WordTrace]
  refine ⟨145282193482260702079237697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96854795654840468052825131 145282193482260702079237697)
  ·
    refine ⟨108961645111695526559428273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145282193482260702079237697 108961645111695526559428273)
    ·
      refine ⟨81721233833771644919571205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108961645111695526559428273 81721233833771644919571205)
      ·
        refine ⟨15322731343832183422419601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81721233833771644919571205 15322731343832183422419601)
        ·
          refine ⟨11492048507874137566814701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15322731343832183422419601 11492048507874137566814701)
          ·
            refine ⟨4309518190452801587555513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11492048507874137566814701 4309518190452801587555513)
            ·
              refine ⟨3232138642839601190666635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4309518190452801587555513 3232138642839601190666635)
              ·
                refine ⟨4848207964259401785999953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3232138642839601190666635 4848207964259401785999953)
                ·
                  refine ⟨3636155973194551339499965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4848207964259401785999953 3636155973194551339499965)
                  ·
                    refine ⟨1363558489947956752312487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3636155973194551339499965 1363558489947956752312487)
                    ·
                      rfl

theorem cell22_3983281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 2, 1, 2, 3].length) (baseStart_3983281 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3983281 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3983281 prefixEnd_3983281 := by exact prefixLift 3983281
  have htrace : WordTrace (prefixWord ++ tailWord_3983281) baseStart_3983281 baseEnd_3983281 := by
    simpa [prefixWord, tailWord_3983281, baseEnd_3983281] using wordTrace_append hprefix tailTrace_3983281
  have hstable : (prefixWord ++ tailWord_3983281).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3983281).length < 2 ^ (prefixWord ++ tailWord_3983281).sum := by decide
  have hdescent : baseEnd_3983281 < baseStart_3983281 := by decide
  rcases family_descends (prefixWord ++ tailWord_3983281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3983320 : List Nat := [2, 1, 2, 2, 2, 2, 2, 2, 2, 5]
def baseStart_3983320 : Nat := 118140960795 + 3983320 * 2 ^ 59
def prefixEnd_3983320 : Nat := 4983230072969 + 3 ^ 40 * 3983320 * 2
def baseEnd_3983320 : Nat := 1363571840444973650587367

theorem tailTrace_3983320 : CollatzResearch.WordTrace tailWord_3983320 prefixEnd_3983320 1363571840444973650587367 := by
  unfold tailWord_3983320
  simp only [CollatzResearch.WordTrace]
  refine ⟨72641807964559705869953707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96855743952746274493271609 72641807964559705869953707)
  ·
    refine ⟨108962711946839558804930561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72641807964559705869953707 108962711946839558804930561)
    ·
      refine ⟨81722033960129669103697921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108962711946839558804930561 81722033960129669103697921)
      ·
        refine ⟨61291525470097251827773441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81722033960129669103697921 61291525470097251827773441)
        ·
          refine ⟨45968644102572938870830081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61291525470097251827773441 45968644102572938870830081)
          ·
            refine ⟨34476483076929704153122561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45968644102572938870830081 34476483076929704153122561)
            ·
              refine ⟨25857362307697278114841921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34476483076929704153122561 25857362307697278114841921)
              ·
                refine ⟨19393021730772958586131441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25857362307697278114841921 19393021730772958586131441)
                ·
                  refine ⟨14544766298079718939598581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19393021730772958586131441 14544766298079718939598581)
                  ·
                    refine ⟨1363571840444973650587367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14544766298079718939598581 1363571840444973650587367)
                    ·
                      rfl

theorem cell22_3983320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 2, 2, 5].length) (baseStart_3983320 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3983320 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3983320 prefixEnd_3983320 := by exact prefixLift 3983320
  have htrace : WordTrace (prefixWord ++ tailWord_3983320) baseStart_3983320 baseEnd_3983320 := by
    simpa [prefixWord, tailWord_3983320, baseEnd_3983320] using wordTrace_append hprefix tailTrace_3983320
  have hstable : (prefixWord ++ tailWord_3983320).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3983320).length < 2 ^ (prefixWord ++ tailWord_3983320).sum := by decide
  have hdescent : baseEnd_3983320 < baseStart_3983320 := by decide
  rcases family_descends (prefixWord ++ tailWord_3983320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3983395 : List Nat := [1, 1, 1, 4, 3, 1, 2, 9]
def baseStart_3983395 : Nat := 118140960795 + 3983395 * 2 ^ 59
def prefixEnd_3983395 : Nat := 4983230072969 + 3 ^ 40 * 3983395 * 2
def baseEnd_3983395 : Nat := 151510834941966494995793

theorem tailTrace_3983395 : CollatzResearch.WordTrace tailWord_3983395 prefixEnd_3983395 151510834941966494995793 := by
  unfold tailWord_3983395
  simp only [CollatzResearch.WordTrace]
  refine ⟨145286351403847699548887639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96857567602565133032591759 145286351403847699548887639)
  ·
    refine ⟨217929527105771549323331459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145286351403847699548887639 217929527105771549323331459)
    ·
      refine ⟨326894290658657323984997189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217929527105771549323331459 326894290658657323984997189)
      ·
        refine ⟨61292679498498248247186973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 326894290658657323984997189 61292679498498248247186973)
        ·
          refine ⟨22984754811936843092695115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61292679498498248247186973 22984754811936843092695115)
          ·
            refine ⟨34477132217905264639042673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22984754811936843092695115 34477132217905264639042673)
            ·
              refine ⟨25857849163428948479282005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34477132217905264639042673 25857849163428948479282005)
              ·
                refine ⟨151510834941966494995793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 25857849163428948479282005 151510834941966494995793)
                ·
                  rfl

theorem cell22_3983395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 9].length) (baseStart_3983395 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3983395 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3983395 prefixEnd_3983395 := by exact prefixLift 3983395
  have htrace : WordTrace (prefixWord ++ tailWord_3983395) baseStart_3983395 baseEnd_3983395 := by
    simpa [prefixWord, tailWord_3983395, baseEnd_3983395] using wordTrace_append hprefix tailTrace_3983395
  have hstable : (prefixWord ++ tailWord_3983395).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3983395).length < 2 ^ (prefixWord ++ tailWord_3983395).sum := by decide
  have hdescent : baseEnd_3983395 < baseStart_3983395 := by decide
  rcases family_descends (prefixWord ++ tailWord_3983395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3983414 : List Nat := [5, 1, 2, 1, 1, 1, 2, 3, 2, 4]
def baseStart_3983414 : Nat := 118140960795 + 3983414 * 2 ^ 59
def prefixEnd_3983414 : Nat := 4983230072969 + 3 ^ 40 * 3983414 * 2
def baseEnd_3983414 : Nat := 1363604018565988738737079

theorem tailTrace_3983414 : CollatzResearch.WordTrace tailWord_3983414 prefixEnd_3983414 1363604018565988738737079 := by
  unfold tailWord_3983414
  simp only [CollatzResearch.WordTrace]
  refine ⟨9080440274423679112114331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 96858029593852577195886197 9080440274423679112114331)
  ·
    refine ⟨13620660411635518668171497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9080440274423679112114331 13620660411635518668171497)
    ·
      refine ⟨10215495308726639001128623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13620660411635518668171497 10215495308726639001128623)
      ·
        refine ⟨15323242963089958501692935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10215495308726639001128623 15323242963089958501692935)
        ·
          refine ⟨22984864444634937752539403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15323242963089958501692935 22984864444634937752539403)
          ·
            refine ⟨34477296666952406628809105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22984864444634937752539403 34477296666952406628809105)
            ·
              refine ⟨25857972500214304971606829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34477296666952406628809105 25857972500214304971606829)
              ·
                refine ⟨9696739687580364364352561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25857972500214304971606829 9696739687580364364352561)
                ·
                  refine ⟨7272554765685273273264421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9696739687580364364352561 7272554765685273273264421)
                  ·
                    refine ⟨1363604018565988738737079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7272554765685273273264421 1363604018565988738737079)
                    ·
                      rfl

theorem cell22_3983414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 3, 2, 4].length) (baseStart_3983414 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3983414 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3983414 prefixEnd_3983414 := by exact prefixLift 3983414
  have htrace : WordTrace (prefixWord ++ tailWord_3983414) baseStart_3983414 baseEnd_3983414 := by
    simpa [prefixWord, tailWord_3983414, baseEnd_3983414] using wordTrace_append hprefix tailTrace_3983414
  have hstable : (prefixWord ++ tailWord_3983414).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3983414).length < 2 ^ (prefixWord ++ tailWord_3983414).sum := by decide
  have hdescent : baseEnd_3983414 < baseStart_3983414 := by decide
  rcases family_descends (prefixWord ++ tailWord_3983414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3983446 : List Nat := [5, 2, 2, 1, 1, 2, 2, 7]
def baseStart_3983446 : Nat := 118140960795 + 3983446 * 2 ^ 59
def prefixEnd_3983446 : Nat := 4983230072969 + 3 ^ 40 * 3983446 * 2
def baseEnd_3983446 : Nat := 151512774757772369104109

theorem tailTrace_3983446 : CollatzResearch.WordTrace tailWord_3983446 prefixEnd_3983446 151512774757772369104109 := by
  unfold tailWord_3983446
  simp only [CollatzResearch.WordTrace]
  refine ⟨9080513220416433453687137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 96858807684441956839329461 9080513220416433453687137)
  ·
    refine ⟨6810384915312325090265353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9080513220416433453687137 6810384915312325090265353)
    ·
      refine ⟨5107788686484243817699015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6810384915312325090265353 5107788686484243817699015)
      ·
        refine ⟨7661683029726365726548523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5107788686484243817699015 7661683029726365726548523)
        ·
          refine ⟨11492524544589548589822785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7661683029726365726548523 11492524544589548589822785)
          ·
            refine ⟨8619393408442161442367089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11492524544589548589822785 8619393408442161442367089)
            ·
              refine ⟨6464545056331621081775317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8619393408442161442367089 6464545056331621081775317)
              ·
                refine ⟨151512774757772369104109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6464545056331621081775317 151512774757772369104109)
                ·
                  rfl

theorem cell22_3983446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 2, 7].length) (baseStart_3983446 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3983446 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3983446 prefixEnd_3983446 := by exact prefixLift 3983446
  have htrace : WordTrace (prefixWord ++ tailWord_3983446) baseStart_3983446 baseEnd_3983446 := by
    simpa [prefixWord, tailWord_3983446, baseEnd_3983446] using wordTrace_append hprefix tailTrace_3983446
  have hstable : (prefixWord ++ tailWord_3983446).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3983446).length < 2 ^ (prefixWord ++ tailWord_3983446).sum := by decide
  have hdescent : baseEnd_3983446 < baseStart_3983446 := by decide
  rcases family_descends (prefixWord ++ tailWord_3983446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3983519 : List Nat := [1, 1, 2, 6, 1, 2, 1, 2, 6]
def baseStart_3983519 : Nat := 118140960795 + 3983519 * 2 ^ 59
def prefixEnd_3983519 : Nat := 4983230072969 + 3 ^ 40 * 3983519 * 2
def baseEnd_3983519 : Nat := 454546654070601154953919

theorem tailTrace_3983519 : CollatzResearch.WordTrace tailWord_3983519 prefixEnd_3983519 454546654070601154953919 := by
  unfold tailWord_3983519
  simp only [CollatzResearch.WordTrace]
  refine ⟨145290874055398468726401611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96860582703598979150934407 145290874055398468726401611)
  ·
    refine ⟨217936311083097703089602417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145290874055398468726401611 217936311083097703089602417)
    ·
      refine ⟨163452233312323277317201813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217936311083097703089602417 163452233312323277317201813)
      ·
        refine ⟨7661823436515153624243835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 163452233312323277317201813 7661823436515153624243835)
        ·
          refine ⟨11492735154772730436365753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7661823436515153624243835 11492735154772730436365753)
          ·
            refine ⟨8619551366079547827274315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11492735154772730436365753 8619551366079547827274315)
            ·
              refine ⟨12929327049119321740911473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8619551366079547827274315 12929327049119321740911473)
              ·
                refine ⟨9696995286839491305683605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12929327049119321740911473 9696995286839491305683605)
                ·
                  refine ⟨454546654070601154953919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9696995286839491305683605 454546654070601154953919)
                  ·
                    rfl

theorem cell22_3983519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 2, 6].length) (baseStart_3983519 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3983519 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3983519 prefixEnd_3983519 := by exact prefixLift 3983519
  have htrace : WordTrace (prefixWord ++ tailWord_3983519) baseStart_3983519 baseEnd_3983519 := by
    simpa [prefixWord, tailWord_3983519, baseEnd_3983519] using wordTrace_append hprefix tailTrace_3983519
  have hstable : (prefixWord ++ tailWord_3983519).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3983519).length < 2 ^ (prefixWord ++ tailWord_3983519).sum := by decide
  have hdescent : baseEnd_3983519 < baseStart_3983519 := by decide
  rcases family_descends (prefixWord ++ tailWord_3983519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3983577 : List Nat := [1, 2, 1, 2, 3, 1, 2, 2, 2, 6]
def baseStart_3983577 : Nat := 118140960795 + 3983577 * 2 ^ 59
def prefixEnd_3983577 : Nat := 4983230072969 + 3 ^ 40 * 3983577 * 2
def baseEnd_3983577 : Nat := 1363659816797110646911579

theorem tailTrace_3983577 : CollatzResearch.WordTrace tailWord_3983577 prefixEnd_3983577 1363659816797110646911579 := by
  unfold tailWord_3983577
  simp only [CollatzResearch.WordTrace]
  refine ⟨145292989489188344632012985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96861992992792229754675323 145292989489188344632012985)
  ·
    refine ⟨108969742116891258474009739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145292989489188344632012985 108969742116891258474009739)
    ·
      refine ⟨163454613175336887711014609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108969742116891258474009739 163454613175336887711014609)
      ·
        refine ⟨122590959881502665783260957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163454613175336887711014609 122590959881502665783260957)
        ·
          refine ⟨45971609955563499668722859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122590959881502665783260957 45971609955563499668722859)
          ·
            refine ⟨68957414933345249503084289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45971609955563499668722859 68957414933345249503084289)
            ·
              refine ⟨51718061200008937127313217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68957414933345249503084289 51718061200008937127313217)
              ·
                refine ⟨38788545900006702845484913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51718061200008937127313217 38788545900006702845484913)
                ·
                  refine ⟨29091409425005027134113685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38788545900006702845484913 29091409425005027134113685)
                  ·
                    refine ⟨1363659816797110646911579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29091409425005027134113685 1363659816797110646911579)
                    ·
                      rfl

theorem cell22_3983577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 2, 2, 6].length) (baseStart_3983577 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3983577 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3983577 prefixEnd_3983577 := by exact prefixLift 3983577
  have htrace : WordTrace (prefixWord ++ tailWord_3983577) baseStart_3983577 baseEnd_3983577 := by
    simpa [prefixWord, tailWord_3983577, baseEnd_3983577] using wordTrace_append hprefix tailTrace_3983577
  have hstable : (prefixWord ++ tailWord_3983577).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3983577).length < 2 ^ (prefixWord ++ tailWord_3983577).sum := by decide
  have hdescent : baseEnd_3983577 < baseStart_3983577 := by decide
  rcases family_descends (prefixWord ++ tailWord_3983577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3983581 : List Nat := [1, 4, 3, 2, 1, 1, 4, 6]
def baseStart_3983581 : Nat := 118140960795 + 3983581 * 2 ^ 59
def prefixEnd_3983581 : Nat := 4983230072969 + 3 ^ 40 * 3983581 * 2
def baseEnd_3983581 : Nat := 151517909564317329979063

theorem tailTrace_3983581 : CollatzResearch.WordTrace tailWord_3983581 prefixEnd_3983581 151517909564317329979063 := by
  unfold tailWord_3983581
  simp only [CollatzResearch.WordTrace]
  refine ⟨145293135381173853315158597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96862090254115902210105731 145293135381173853315158597)
  ·
    refine ⟨27242462883970097496592237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 145293135381173853315158597 27242462883970097496592237)
    ·
      refine ⟨10215923581488786561222089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27242462883970097496592237 10215923581488786561222089)
      ·
        refine ⟨7661942686116589920916567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10215923581488786561222089 7661942686116589920916567)
        ·
          refine ⟨11492914029174884881374851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7661942686116589920916567 11492914029174884881374851)
          ·
            refine ⟨17239371043762327322062277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11492914029174884881374851 17239371043762327322062277)
            ·
              refine ⟨3232382070705436372886677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17239371043762327322062277 3232382070705436372886677)
              ·
                refine ⟨151517909564317329979063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3232382070705436372886677 151517909564317329979063)
                ·
                  rfl

theorem cell22_3983581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 4, 6].length) (baseStart_3983581 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3983581 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3983581 prefixEnd_3983581 := by exact prefixLift 3983581
  have htrace : WordTrace (prefixWord ++ tailWord_3983581) baseStart_3983581 baseEnd_3983581 := by
    simpa [prefixWord, tailWord_3983581, baseEnd_3983581] using wordTrace_append hprefix tailTrace_3983581
  have hstable : (prefixWord ++ tailWord_3983581).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3983581).length < 2 ^ (prefixWord ++ tailWord_3983581).sum := by decide
  have hdescent : baseEnd_3983581 < baseStart_3983581 := by decide
  rcases family_descends (prefixWord ++ tailWord_3983581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3983626 : List Nat := [3, 1, 2, 2, 1, 1, 6, 1, 5]
def baseStart_3983626 : Nat := 118140960795 + 3983626 * 2 ^ 59
def prefixEnd_3983626 : Nat := 4983230072969 + 3 ^ 40 * 3983626 * 2
def baseEnd_3983626 : Nat := 454558863499496950812143

theorem tailTrace_3983626 : CollatzResearch.WordTrace tailWord_3983626 prefixEnd_3983626 454558863499496950812143 := by
  unfold tailWord_3983626
  simp only [CollatzResearch.WordTrace]
  refine ⟨36323694166502706500136683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96863184444007217333697821 36323694166502706500136683)
  ·
    refine ⟨54485541249754059750205025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36323694166502706500136683 54485541249754059750205025)
    ·
      refine ⟨40864155937315544812653769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54485541249754059750205025 40864155937315544812653769)
      ·
        refine ⟨30648116952986658609490327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40864155937315544812653769 30648116952986658609490327)
        ·
          refine ⟨45972175429479987914235491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30648116952986658609490327 45972175429479987914235491)
          ·
            refine ⟨68958263144219981871353237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45972175429479987914235491 68958263144219981871353237)
            ·
              refine ⟨3232418584885311650219683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 68958263144219981871353237 3232418584885311650219683)
              ·
                refine ⟨4848627877327967475329525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3232418584885311650219683 4848627877327967475329525)
                ·
                  refine ⟨454558863499496950812143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4848627877327967475329525 454558863499496950812143)
                  ·
                    rfl

theorem cell22_3983626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 6, 1, 5].length) (baseStart_3983626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3983626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3983626 prefixEnd_3983626 := by exact prefixLift 3983626
  have htrace : WordTrace (prefixWord ++ tailWord_3983626) baseStart_3983626 baseEnd_3983626 := by
    simpa [prefixWord, tailWord_3983626, baseEnd_3983626] using wordTrace_append hprefix tailTrace_3983626
  have hstable : (prefixWord ++ tailWord_3983626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3983626).length < 2 ^ (prefixWord ++ tailWord_3983626).sum := by decide
  have hdescent : baseEnd_3983626 < baseStart_3983626 := by decide
  rcases family_descends (prefixWord ++ tailWord_3983626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3983669 : List Nat := [1, 3, 3, 1, 2, 1, 1, 2, 3, 5]
def baseStart_3983669 : Nat := 118140960795 + 3983669 * 2 ^ 59
def prefixEnd_3983669 : Nat := 4983230072969 + 3 ^ 40 * 3983669 * 2
def baseEnd_3983669 : Nat := 1363691310277253073611297

theorem tailTrace_3983669 : CollatzResearch.WordTrace tailWord_3983669 prefixEnd_3983669 1363691310277253073611297 := by
  unfold tailWord_3983669
  simp only [CollatzResearch.WordTrace]
  refine ⟨145296345004855044344362061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96864230003236696229574707 145296345004855044344362061)
  ·
    refine ⟨54486129376820641629135773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145296345004855044344362061 54486129376820641629135773)
    ·
      refine ⟨20432298516307740610925915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54486129376820641629135773 20432298516307740610925915)
      ·
        refine ⟨30648447774461610916388873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20432298516307740610925915 30648447774461610916388873)
        ·
          refine ⟨22986335830846208187291655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30648447774461610916388873 22986335830846208187291655)
          ·
            refine ⟨34479503746269312280937483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22986335830846208187291655 34479503746269312280937483)
            ·
              refine ⟨51719255619403968421406225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34479503746269312280937483 51719255619403968421406225)
              ·
                refine ⟨38789441714552976316054669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51719255619403968421406225 38789441714552976316054669)
                ·
                  refine ⟨14546040642957366118520501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38789441714552976316054669 14546040642957366118520501)
                  ·
                    refine ⟨1363691310277253073611297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14546040642957366118520501 1363691310277253073611297)
                    ·
                      rfl

theorem cell22_3983669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 2, 3, 5].length) (baseStart_3983669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3983669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3983669 prefixEnd_3983669 := by exact prefixLift 3983669
  have htrace : WordTrace (prefixWord ++ tailWord_3983669) baseStart_3983669 baseEnd_3983669 := by
    simpa [prefixWord, tailWord_3983669, baseEnd_3983669] using wordTrace_append hprefix tailTrace_3983669
  have hstable : (prefixWord ++ tailWord_3983669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3983669).length < 2 ^ (prefixWord ++ tailWord_3983669).sum := by decide
  have hdescent : baseEnd_3983669 < baseStart_3983669 := by decide
  rcases family_descends (prefixWord ++ tailWord_3983669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3983701 : List Nat := [1, 3, 2, 2, 4, 1, 1, 1, 1, 6]
def baseStart_3983701 : Nat := 118140960795 + 3983701 * 2 ^ 59
def prefixEnd_3983701 : Nat := 4983230072969 + 3 ^ 40 * 3983701 * 2
def baseEnd_3983701 : Nat := 1363702264531215656811199

theorem tailTrace_3983701 : CollatzResearch.WordTrace tailWord_3983701 prefixEnd_3983701 1363702264531215656811199 := by
  unfold tailWord_3983701
  simp only [CollatzResearch.WordTrace]
  refine ⟨145297512140739113809526957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96865008093826075873017971 145297512140739113809526957)
  ·
    refine ⟨54486567052777167678572609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145297512140739113809526957 54486567052777167678572609)
    ·
      refine ⟨40864925289582875758929457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54486567052777167678572609 40864925289582875758929457)
      ·
        refine ⟨30648693967187156819197093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40864925289582875758929457 30648693967187156819197093)
        ·
          refine ⟨5746630118847591903599455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30648693967187156819197093 5746630118847591903599455)
          ·
            refine ⟨8619945178271387855399183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5746630118847591903599455 8619945178271387855399183)
            ·
              refine ⟨12929917767407081783098775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8619945178271387855399183 12929917767407081783098775)
              ·
                refine ⟨19394876651110622674648163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12929917767407081783098775 19394876651110622674648163)
                ·
                  refine ⟨29092314976665934011972245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19394876651110622674648163 29092314976665934011972245)
                  ·
                    refine ⟨1363702264531215656811199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29092314976665934011972245 1363702264531215656811199)
                    ·
                      rfl

theorem cell22_3983701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 1, 1, 6].length) (baseStart_3983701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3983701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3983701 prefixEnd_3983701 := by exact prefixLift 3983701
  have htrace : WordTrace (prefixWord ++ tailWord_3983701) baseStart_3983701 baseEnd_3983701 := by
    simpa [prefixWord, tailWord_3983701, baseEnd_3983701] using wordTrace_append hprefix tailTrace_3983701
  have hstable : (prefixWord ++ tailWord_3983701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3983701).length < 2 ^ (prefixWord ++ tailWord_3983701).sum := by decide
  have hdescent : baseEnd_3983701 < baseStart_3983701 := by decide
  rcases family_descends (prefixWord ++ tailWord_3983701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3983720 : List Nat := [2, 1, 4, 2, 2, 3, 1, 2, 2, 3]
def baseStart_3983720 : Nat := 118140960795 + 3983720 * 2 ^ 59
def prefixEnd_3983720 : Nat := 4983230072969 + 3 ^ 40 * 3983720 * 2
def baseEnd_3983720 : Nat := 1363708768619505940586141

theorem tailTrace_3983720 : CollatzResearch.WordTrace tailWord_3983720 prefixEnd_3983720 1363708768619505940586141 := by
  unfold tailWord_3983720
  simp only [CollatzResearch.WordTrace]
  refine ⟨72649102563835140027234307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96865470085113520036312409 72649102563835140027234307)
  ·
    refine ⟨108973653845752710040851461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72649102563835140027234307 108973653845752710040851461)
    ·
      refine ⟨20432560096078633132659649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108973653845752710040851461 20432560096078633132659649)
      ·
        refine ⟨15324420072058974849494737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20432560096078633132659649 15324420072058974849494737)
        ·
          refine ⟨11493315054044231137121053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15324420072058974849494737 11493315054044231137121053)
          ·
            refine ⟨4309993145266586676420395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11493315054044231137121053 4309993145266586676420395)
            ·
              refine ⟨6464989717899880014630593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4309993145266586676420395 6464989717899880014630593)
              ·
                refine ⟨4848742288424910010972945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6464989717899880014630593 4848742288424910010972945)
                ·
                  refine ⟨3636556716318682508229709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4848742288424910010972945 3636556716318682508229709)
                  ·
                    refine ⟨1363708768619505940586141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3636556716318682508229709 1363708768619505940586141)
                    ·
                      rfl

theorem cell22_3983720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 1, 2, 2, 3].length) (baseStart_3983720 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3983720 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3983720 prefixEnd_3983720 := by exact prefixLift 3983720
  have htrace : WordTrace (prefixWord ++ tailWord_3983720) baseStart_3983720 baseEnd_3983720 := by
    simpa [prefixWord, tailWord_3983720, baseEnd_3983720] using wordTrace_append hprefix tailTrace_3983720
  have hstable : (prefixWord ++ tailWord_3983720).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3983720).length < 2 ^ (prefixWord ++ tailWord_3983720).sum := by decide
  have hdescent : baseEnd_3983720 < baseStart_3983720 := by decide
  rcases family_descends (prefixWord ++ tailWord_3983720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3983806 : List Nat := [4, 2, 1, 1, 1, 1, 2, 4, 6]
def baseStart_3983806 : Nat := 118140960795 + 3983806 * 2 ^ 59
def prefixEnd_3983806 : Nat := 4983230072969 + 3 ^ 40 * 3983806 * 2
def baseEnd_3983806 : Nat := 454579402725676794311959

theorem tailTrace_3983806 : CollatzResearch.WordTrace tailWord_3983806 prefixEnd_3983806 454579402725676794311959 := by
  unfold tailWord_3983806
  simp only [CollatzResearch.WordTrace]
  refine ⟨18162667725669839592762409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96867561203572477828066181 18162667725669839592762409)
  ·
    refine ⟨13622000794252379694571807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18162667725669839592762409 13622000794252379694571807)
    ·
      refine ⟨20433001191378569541857711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13622000794252379694571807 20433001191378569541857711)
      ·
        refine ⟨30649501787067854312786567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20433001191378569541857711 30649501787067854312786567)
        ·
          refine ⟨45974252680601781469179851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30649501787067854312786567 45974252680601781469179851)
          ·
            refine ⟨68961379020902672203769777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45974252680601781469179851 68961379020902672203769777)
            ·
              refine ⟨51721034265677004152827333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68961379020902672203769777 51721034265677004152827333)
              ·
                refine ⟨9697693924814438278655125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51721034265677004152827333 9697693924814438278655125)
                ·
                  refine ⟨454579402725676794311959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9697693924814438278655125 454579402725676794311959)
                  ·
                    rfl

theorem cell22_3983806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 4, 6].length) (baseStart_3983806 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3983806 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3983806 prefixEnd_3983806 := by exact prefixLift 3983806
  have htrace : WordTrace (prefixWord ++ tailWord_3983806) baseStart_3983806 baseEnd_3983806 := by
    simpa [prefixWord, tailWord_3983806, baseEnd_3983806] using wordTrace_append hprefix tailTrace_3983806
  have hstable : (prefixWord ++ tailWord_3983806).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3983806).length < 2 ^ (prefixWord ++ tailWord_3983806).sum := by decide
  have hdescent : baseEnd_3983806 < baseStart_3983806 := by decide
  rcases family_descends (prefixWord ++ tailWord_3983806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3983885 : List Nat := [1, 7, 1, 1, 1, 2, 9]
def baseStart_3983885 : Nat := 118140960795 + 3983885 * 2 ^ 59
def prefixEnd_3983885 : Nat := 4983230072969 + 3 ^ 40 * 3983885 * 2
def baseEnd_3983885 : Nat := 50509824129314833711505

theorem tailTrace_3983885 : CollatzResearch.WordTrace tailWord_3983885 prefixEnd_3983885 50509824129314833711505 := by
  unfold tailWord_3983885
  simp only [CollatzResearch.WordTrace]
  refine ⟨145304223172072513234225109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96869482114715008822816739 145304223172072513234225109)
  ·
    refine ⟨3405567730595449528927151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 145304223172072513234225109 3405567730595449528927151)
    ·
      refine ⟨5108351595893174293390727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3405567730595449528927151 5108351595893174293390727)
      ·
        refine ⟨7662527393839761440086091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5108351595893174293390727 7662527393839761440086091)
        ·
          refine ⟨11493791090759642160129137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7662527393839761440086091 11493791090759642160129137)
          ·
            refine ⟨8620343318069731620096853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11493791090759642160129137 8620343318069731620096853)
            ·
              refine ⟨50509824129314833711505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8620343318069731620096853 50509824129314833711505)
              ·
                rfl

theorem cell22_3983885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 9].length) (baseStart_3983885 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3983885 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3983885 prefixEnd_3983885 := by exact prefixLift 3983885
  have htrace : WordTrace (prefixWord ++ tailWord_3983885) baseStart_3983885 baseEnd_3983885 := by
    simpa [prefixWord, tailWord_3983885, baseEnd_3983885] using wordTrace_append hprefix tailTrace_3983885
  have hstable : (prefixWord ++ tailWord_3983885).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3983885).length < 2 ^ (prefixWord ++ tailWord_3983885).sum := by decide
  have hdescent : baseEnd_3983885 < baseStart_3983885 := by decide
  rcases family_descends (prefixWord ++ tailWord_3983885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3983900 : List Nat := [2, 2, 3, 1, 2, 3, 2, 1, 3, 3]
def baseStart_3983900 : Nat := 118140960795 + 3983900 * 2 ^ 59
def prefixEnd_3983900 : Nat := 4983230072969 + 3 ^ 40 * 3983900 * 2
def baseEnd_3983900 : Nat := 1363770386298045471085589

theorem tailTrace_3983900 : CollatzResearch.WordTrace tailWord_3983900 prefixEnd_3983900 1363770386298045471085589 := by
  unfold tailWord_3983900
  simp only [CollatzResearch.WordTrace]
  refine ⟨72652385133509085398010577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96869846844678780530680769 72652385133509085398010577)
  ·
    refine ⟨54489288850131814048507933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72652385133509085398010577 54489288850131814048507933)
    ·
      refine ⟨20433483318799430268190475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54489288850131814048507933 20433483318799430268190475)
      ·
        refine ⟨30650224978199145402285713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20433483318799430268190475 30650224978199145402285713)
        ·
          refine ⟨22987668733649359051714285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30650224978199145402285713 22987668733649359051714285)
          ·
            refine ⟨8620375775118509644392857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22987668733649359051714285 8620375775118509644392857)
            ·
              refine ⟨6465281831338882233294643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8620375775118509644392857 6465281831338882233294643)
              ·
                refine ⟨9697922747008323349941965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6465281831338882233294643 9697922747008323349941965)
                ·
                  refine ⟨3636721030128121256228237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9697922747008323349941965 3636721030128121256228237)
                  ·
                    refine ⟨1363770386298045471085589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3636721030128121256228237 1363770386298045471085589)
                    ·
                      rfl

theorem cell22_3983900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 2, 1, 3, 3].length) (baseStart_3983900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3983900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3983900 prefixEnd_3983900 := by exact prefixLift 3983900
  have htrace : WordTrace (prefixWord ++ tailWord_3983900) baseStart_3983900 baseEnd_3983900 := by
    simpa [prefixWord, tailWord_3983900, baseEnd_3983900] using wordTrace_append hprefix tailTrace_3983900
  have hstable : (prefixWord ++ tailWord_3983900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3983900).length < 2 ^ (prefixWord ++ tailWord_3983900).sum := by decide
  have hdescent : baseEnd_3983900 < baseStart_3983900 := by decide
  rcases family_descends (prefixWord ++ tailWord_3983900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3983964 : List Nat := [2, 2, 4, 1, 4, 1, 2, 1, 5]
def baseStart_3983964 : Nat := 118140960795 + 3983964 * 2 ^ 59
def prefixEnd_3983964 : Nat := 4983230072969 + 3 ^ 40 * 3983964 * 2
def baseEnd_3983964 : Nat := 454597431601990212495131

theorem tailTrace_3983964 : CollatzResearch.WordTrace tailWord_3983964 prefixEnd_3983964 454597431601990212495131 := by
  unfold tailWord_3983964
  simp only [CollatzResearch.WordTrace]
  refine ⟨72653552269393154863175473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96871403025857539817567297 72653552269393154863175473)
  ·
    refine ⟨54490164202044866147381605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72653552269393154863175473 54490164202044866147381605)
    ·
      refine ⟨10216905787883412402634051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54490164202044866147381605 10216905787883412402634051)
      ·
        refine ⟨15325358681825118603951077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10216905787883412402634051 15325358681825118603951077)
        ·
          refine ⟨2873504752842209738240827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15325358681825118603951077 2873504752842209738240827)
          ·
            refine ⟨4310257129263314607361241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2873504752842209738240827 4310257129263314607361241)
            ·
              refine ⟨3232692846947485955520931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4310257129263314607361241 3232692846947485955520931)
              ·
                refine ⟨4849039270421228933281397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3232692846947485955520931 4849039270421228933281397)
                ·
                  refine ⟨454597431601990212495131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4849039270421228933281397 454597431601990212495131)
                  ·
                    rfl

theorem cell22_3983964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 2, 1, 5].length) (baseStart_3983964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3983964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3983964 prefixEnd_3983964 := by exact prefixLift 3983964
  have htrace : WordTrace (prefixWord ++ tailWord_3983964) baseStart_3983964 baseEnd_3983964 := by
    simpa [prefixWord, tailWord_3983964, baseEnd_3983964] using wordTrace_append hprefix tailTrace_3983964
  have hstable : (prefixWord ++ tailWord_3983964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3983964).length < 2 ^ (prefixWord ++ tailWord_3983964).sum := by decide
  have hdescent : baseEnd_3983964 < baseStart_3983964 := by decide
  rcases family_descends (prefixWord ++ tailWord_3983964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3984002 : List Nat := [3, 4, 3, 1, 2, 1, 2, 2, 1, 3]
def baseStart_3984002 : Nat := 118140960795 + 3984002 * 2 ^ 59
def prefixEnd_3984002 : Nat := 4983230072969 + 3 ^ 40 * 3984002 * 2
def baseEnd_3984002 : Nat := 1363805302982551205035277

theorem tailTrace_3984002 : CollatzResearch.WordTrace tailWord_3984002 prefixEnd_3984002 1363805302982551205035277 := by
  unfold tailWord_3984002
  simp only [CollatzResearch.WordTrace]
  refine ⟨36327122628162160554058565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96872327008432428144156173 36327122628162160554058565)
  ·
    refine ⟨6811335492780405103885981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36327122628162160554058565 6811335492780405103885981)
    ·
      refine ⟨2554250809792651913957243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6811335492780405103885981 2554250809792651913957243)
      ·
        refine ⟨3831376214688977870935865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2554250809792651913957243 3831376214688977870935865)
        ·
          refine ⟨2873532161016733403201899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3831376214688977870935865 2873532161016733403201899)
          ·
            refine ⟨4310298241525100104802849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2873532161016733403201899 4310298241525100104802849)
            ·
              refine ⟨3232723681143825078602137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4310298241525100104802849 3232723681143825078602137)
              ·
                refine ⟨2424542760857868808951603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3232723681143825078602137 2424542760857868808951603)
                ·
                  refine ⟨3636814141286803213427405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2424542760857868808951603 3636814141286803213427405)
                  ·
                    refine ⟨1363805302982551205035277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3636814141286803213427405 1363805302982551205035277)
                    ·
                      rfl

theorem cell22_3984002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_3984002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3984002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3984002 prefixEnd_3984002 := by exact prefixLift 3984002
  have htrace : WordTrace (prefixWord ++ tailWord_3984002) baseStart_3984002 baseEnd_3984002 := by
    simpa [prefixWord, tailWord_3984002, baseEnd_3984002] using wordTrace_append hprefix tailTrace_3984002
  have hstable : (prefixWord ++ tailWord_3984002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3984002).length < 2 ^ (prefixWord ++ tailWord_3984002).sum := by decide
  have hdescent : baseEnd_3984002 < baseStart_3984002 := by decide
  rcases family_descends (prefixWord ++ tailWord_3984002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3984020 : List Nat := [2, 4, 2, 2, 1, 1, 3, 7]
def baseStart_3984020 : Nat := 118140960795 + 3984020 * 2 ^ 59
def prefixEnd_3984020 : Nat := 4983230072969 + 3 ^ 40 * 3984020 * 2
def baseEnd_3984020 : Nat := 151534607194489462009469

theorem tailTrace_3984020 : CollatzResearch.WordTrace tailWord_3984020 prefixEnd_3984020 151534607194489462009469 := by
  unfold tailWord_3984020
  simp only [CollatzResearch.WordTrace]
  refine ⟨72654573513291715645194757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96872764684388954193593009 72654573513291715645194757)
  ·
    refine ⟨13622732533742196683474017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72654573513291715645194757 13622732533742196683474017)
    ·
      refine ⟨10217049400306647512605513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13622732533742196683474017 10217049400306647512605513)
      ·
        refine ⟨7662787050229985634454135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10217049400306647512605513 7662787050229985634454135)
        ·
          refine ⟨11494180575344978451681203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7662787050229985634454135 11494180575344978451681203)
          ·
            refine ⟨17241270863017467677521805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11494180575344978451681203 17241270863017467677521805)
            ·
              refine ⟨6465476573631550379070677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17241270863017467677521805 6465476573631550379070677)
              ·
                refine ⟨151534607194489462009469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6465476573631550379070677 151534607194489462009469)
                ·
                  rfl

theorem cell22_3984020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 3, 7].length) (baseStart_3984020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3984020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3984020 prefixEnd_3984020 := by exact prefixLift 3984020
  have htrace : WordTrace (prefixWord ++ tailWord_3984020) baseStart_3984020 baseEnd_3984020 := by
    simpa [prefixWord, tailWord_3984020, baseEnd_3984020] using wordTrace_append hprefix tailTrace_3984020
  have hstable : (prefixWord ++ tailWord_3984020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3984020).length < 2 ^ (prefixWord ++ tailWord_3984020).sum := by decide
  have hdescent : baseEnd_3984020 < baseStart_3984020 := by decide
  rcases family_descends (prefixWord ++ tailWord_3984020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
